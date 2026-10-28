#!/usr/bin/env python3
"""ProofForge judge: decide statuses for one candidate workspace.

Pipeline:
  1. tree check       protected files in the workspace match spec/locked.json
  2. impl scan        candidate source has no code overrides or meta-programming
  3. fresh container  locked project + candidate files only, never built before
  4. comparator       `lake comparator --paranoid` with bubblewrap: Lean default and
                      paranoid kernels plus lean4lean, nanoda, con-leche, con-ron
                      (mandatory for VERIFIED)
  5. leanchecker      kernel replay of the solution module
  6. (optional) binary build + property tests are run by binary_check.py

Usage: judge.py <workspace-dir | candidate.lean> [--task T] [--json out.json]
The task (harness/task.py) defaults to the flagship payout component in formal/.
A bare .lean file is treated as a workspace containing only candidate/Solution.lean.
Statuses come only from exit codes recorded here; nothing a model writes is trusted.
"""
import argparse, contextlib, fcntl, hashlib, json, os, pathlib, re, shlex, shutil, signal, subprocess, sys, tempfile, threading, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import task as taskmod  # noqa: E402

IMAGE = "proofforge-lean:4.35.0"
CANDIDATE_GLOBS = ["candidate/Solution.lean", "candidate/Lib/**/*.lean"]
# Constructs that can make compiled code differ from what the kernel checked, or that
# run arbitrary code during elaboration. Defense in depth; Comparator is the authority.
FORBIDDEN = [
    r"implemented_by", r"\bextern\b", r"\bunsafe\b", r"@\[\s*export", r"\bmacro\b",
    r"\belab\b", r"\bsyntax\b", r"\binitialize\b", r"\bbuiltin_initialize\b",
    r"#eval", r"\brun_cmd\b", r"\brun_elab\b", r"\brun_meta\b", r"\bnative_decide\b",
    r"\bset_option\b", r"\bopaque\b", r"\baxiom\b", r"@\[\s*csimp",
]


def allowed_imports(task):
    lib = re.escape(task.lib)
    return re.compile(rf"^({lib}\.Spec|{lib}\.Lemmas|Init(\..+)?|Std(\..+)?)$")


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


# Monotonic deadline for every Lean run in this process (set by agents from their budget).
DEADLINE = None
TIMEOUT_MARK = "error: run stopped at the time limit"
_local = threading.local()


def deadline():
    """The earlier of the process deadline and the calling thread's `time_limit`, if any."""
    ds = [d for d in (DEADLINE, getattr(_local, "deadline", None)) if d is not None]
    return min(ds) if ds else None


@contextlib.contextmanager
def time_limit(seconds):
    """Deadline for every Lean run made by the calling thread (one API request), nested
    limits keep the earlier one."""
    prev = getattr(_local, "deadline", None)
    end = time.monotonic() + seconds
    _local.deadline = end if prev is None else min(prev, end)
    try:
        yield
    finally:
        _local.deadline = prev


def run(cmd, timeout=900, on_timeout=None):
    t0 = time.monotonic()
    if deadline() is not None:
        timeout = min(timeout, deadline() - t0)
    rec = {"command": cmd if isinstance(cmd, list) else [cmd]}
    if timeout <= 0:
        return {**rec, "exit_code": 124, "elapsed_ms": 0, "stdout_sha256": sha256_bytes(b""),
                "stderr_sha256": sha256_bytes(b""), "output_tail": TIMEOUT_MARK}
    # Own process group, so a timeout stops every descendant (lake, lean, the docker client).
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, errors="replace",
                         start_new_session=True)
    try:
        stdout, stderr = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        if on_timeout:
            on_timeout()
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = p.communicate()
        out = stdout + stderr
        return {**rec, "exit_code": 124, "elapsed_ms": int((time.monotonic() - t0) * 1000),
                "stdout_sha256": sha256_bytes(stdout.encode()), "stderr_sha256": sha256_bytes(stderr.encode()),
                "output_tail": out[-3000:] + "\n" + TIMEOUT_MARK}
    return {
        **rec,
        "exit_code": p.returncode,
        "elapsed_ms": int((time.monotonic() - t0) * 1000),
        "stdout_sha256": sha256_bytes(stdout.encode()),
        "stderr_sha256": sha256_bytes(stderr.encode()),
        "output_tail": (stdout + stderr)[-4000:],
    }


def load_workspace(arg: str) -> pathlib.Path:
    p = pathlib.Path(arg).resolve()
    if p.is_dir():
        return p
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-ws-"))
    (ws / "candidate").mkdir()
    shutil.copy(p, ws / "candidate" / "Solution.lean")
    return ws


def tree_check(ws: pathlib.Path, locked: dict, task) -> dict:
    """Any protected file present in the workspace must be byte-identical to the lock."""
    problems = []
    for rel, digest in locked["files"].items():
        f = ws / rel
        if f.exists() and sha256_bytes(f.read_bytes()) != digest:
            problems.append(f"protected file modified: {rel}")
    lock_digest = sha256_bytes(json.dumps(locked["files"], sort_keys=True).encode())
    if lock_digest != locked["manifest_sha256"]:
        problems.append("spec/locked.json is internally inconsistent")
    if sorted(locked["files"]) != sorted(task.protected()):
        problems.append("spec/locked.json does not cover exactly the protected files")
    for rel in locked["files"]:
        if not (task.root / rel).is_file():
            problems.append(f"repository protected file missing: {rel}")
        elif sha256_bytes((task.root / rel).read_bytes()) != locked["files"][rel]:
            problems.append(f"repository protected file differs from lock: {rel}")
    return {"passed": not problems, "problems": problems}


def candidate_files(ws: pathlib.Path):
    files = []
    for g in CANDIDATE_GLOBS:
        files += sorted(ws.glob(g))
    return files


def impl_scan(files, task) -> dict:
    problems = []
    for f in files:
        text = f.read_text()
        code = re.sub(r"/-.*?-/", "", text, flags=re.S)   # strip block comments
        code = re.sub(r"--[^\n]*", "", code)              # strip line comments
        for pat in FORBIDDEN:
            for m in re.finditer(pat, code):
                line = code[: m.start()].count("\n") + 1
                problems.append(f"{f.name}:{line}: forbidden construct `{m.group(0)}`")
        for m in re.finditer(r"^\s*import\s+(\S+)", code, flags=re.M):
            if not allowed_imports(task).match(m.group(1)):
                problems.append(f"{f.name}: import not allowed: {m.group(1)}")
    return {"passed": not problems, "problems": problems}


def fresh_project(ws: pathlib.Path, files, task) -> pathlib.Path:
    """Locked project files from the repository + the candidate files, nothing else."""
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-judge-"))
    for rel in taskmod.PROJECT_FILES:
        src = task.root / rel
        if src.is_dir():
            shutil.copytree(src, d / rel)
        else:
            shutil.copy(src, d / rel)
    for f in files:
        dst = d / f.relative_to(ws)
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(f, dst)
    return d


SLOTS = int(os.environ.get("PF_CONTAINER_SLOTS", "2"))
SLOT_DIR = pathlib.Path(tempfile.gettempdir()) / "proofforge-slots"


@contextlib.contextmanager
def container_slot():
    """Bound concurrent Lean containers across all processes on this host. A caller whose
    deadline passes while waiting gets None and no slot; its run then stops at once."""
    SLOT_DIR.mkdir(exist_ok=True)
    while True:
        if deadline() is not None and time.monotonic() >= deadline():
            yield None
            return
        for i in range(SLOTS):
            f = open(SLOT_DIR / f"slot{i}", "w")
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError:
                f.close()
                continue
            try:
                yield i
            finally:
                fcntl.flock(f, fcntl.LOCK_UN)
                f.close()
            return
        time.sleep(0.2)


IN_IMAGE = os.environ.get("PF_IN_IMAGE") == "1"


def image_id():
    """Content digest of the judge image (recorded in every Passport)."""
    if IN_IMAGE:
        return os.environ.get("PF_IMAGE_ID", "unknown")
    r = subprocess.run(["docker", "image", "inspect", IMAGE, "--format", "{{.Id}}"],
                       capture_output=True, text=True)
    return r.stdout.strip() or "unknown"


def in_container(project: pathlib.Path, script: str, timeout=900):
    """Run `script` in the pinned Lean image with `project` as the working directory. Inside
    the image itself (PF_IN_IMAGE=1, as in the verify image and on Linux hosts) it runs
    directly; Comparator's bubblewrap sandbox applies in both cases."""
    if IN_IMAGE:
        with container_slot():
            return run(["bash", "-lc", f"cd {shlex.quote(str(project))} && {script}"], timeout=timeout)
    name = f"pf-{os.getpid()}-{time.monotonic_ns()}"
    cmd = [
        "docker", "run", "--rm", "--name", name, "--network", "none",
        # bubblewrap (Comparator's sandbox) needs user namespaces inside the container.
        "--security-opt", "seccomp=unconfined", "--security-opt", "apparmor=unconfined",
        "--security-opt", "systempaths=unconfined", "--cap-add", "SYS_ADMIN",
        "--memory", "4g", "--pids-limit", "512",
        "-v", f"{project}:/work", "-w", "/work", IMAGE, "bash", "-lc", script,
    ]
    with container_slot():
        return run(cmd, timeout=timeout,
                   on_timeout=lambda: subprocess.run(["docker", "kill", name], capture_output=True))


def parse_axioms(output: str, task) -> dict:
    """Map each required theorem to the axioms `#print axioms` reports for it."""
    out = {}
    for t in task.theorems:
        m = re.search(rf"'{re.escape(task.ns)}\.{re.escape(t)}' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                      output)
        out[t] = None if not m else sorted(x.strip() for x in (m.group(2) or "").replace("\n", " ").split(",") if x.strip())
    return out


def judge(arg: str, scan: bool = True, task=None) -> dict:
    t0 = time.monotonic()
    task = task or taskmod.load()
    locked = task.locked()
    ws = load_workspace(arg)
    files = candidate_files(ws)
    result = {
        "schema_version": 1,
        "task": task.id,
        "candidate": str(arg),
        "manifest_sha256": locked["manifest_sha256"],
        "solution_tree_sha256": sha256_bytes(
            b"".join(sha256_bytes(f.read_bytes()).encode() for f in files)),
        "checks": {},
    }
    c = result["checks"]
    c["tree"] = tree_check(ws, locked, task)
    if not files:
        c["tree"]["passed"] = False
        c["tree"]["problems"].append("no candidate/Solution.lean")
    c["impl_scan"] = impl_scan(files, task) if scan else {"passed": True, "problems": [], "skipped": True}

    gate_ok = c["tree"]["passed"] and c["impl_scan"]["passed"]
    if gate_ok:
        project = fresh_project(ws, files, task)
        c["comparator"] = in_container(
            project, "lake comparator --paranoid --config spec/comparator.json")
        if c["comparator"]["exit_code"] == 0:
            c["leanchecker"] = in_container(
                project, "lake build Solution >/dev/null && lake env leanchecker Solution")
            if c["leanchecker"]["exit_code"] == 0:
                (project / "Audit.lean").write_text("import Solution\n" + "".join(
                    f"#print axioms {task.ns}.{t}\n" for t in task.theorems))
                c["axioms"] = in_container(project, "lake env lean Audit.lean")
                result["axioms_used"] = parse_axioms(c["axioms"]["output_tail"], task)
        shutil.rmtree(project, ignore_errors=True)

    accepted = (gate_ok and c.get("comparator", {}).get("exit_code") == 0
                and c.get("leanchecker", {}).get("exit_code") == 0)
    # Proof acceptance only; VERIFIED additionally needs the binary check (harness/passport.py).
    status = "ACCEPTED" if accepted else "REJECTED"
    result["requirements"] = {rid: status for rid, _ in task.requirements}
    result["accepted"] = accepted
    result["elapsed_ms"] = int((time.monotonic() - t0) * 1000)
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("candidate")
    ap.add_argument("--task")
    ap.add_argument("--json")
    a = ap.parse_args()
    r = judge(a.candidate, task=taskmod.load(a.task))
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(r, indent=2) + "\n")
    verdict = "ACCEPTED" if r["accepted"] else "REJECTED"
    reasons = r["checks"]["tree"]["problems"] + r["checks"]["impl_scan"]["problems"]
    if "comparator" in r["checks"] and r["checks"]["comparator"]["exit_code"] != 0:
        reasons.append(f"comparator exit {r['checks']['comparator']['exit_code']}")
    if "leanchecker" in r["checks"] and r["checks"]["leanchecker"]["exit_code"] != 0:
        reasons.append(f"leanchecker exit {r['checks']['leanchecker']['exit_code']}")
    print(f"{verdict}  {a.candidate}  ({r['elapsed_ms']} ms)" + (f"  {'; '.join(reasons)}" if reasons else ""))
    sys.exit(0 if r["accepted"] else 1)
