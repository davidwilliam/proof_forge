#!/usr/bin/env python3
"""ProofForge judge: decide statuses for one candidate workspace.

Pipeline:
  1. tree check       protected files in the workspace match spec/locked.json
  2. impl scan        candidate source has no code overrides or meta-programming
  3. fresh container  locked project + candidate files only, never built before
  4. comparator       `lake comparator` with bubblewrap (mandatory for VERIFIED)
  5. leanchecker      kernel replay of the solution module
  6. (optional) binary build + property tests are run by binary_check.py

Usage: judge.py <workspace-dir | candidate.lean> [--json out.json]
A bare .lean file is treated as a workspace containing only candidate/Solution.lean.
Statuses come only from exit codes recorded here; nothing a model writes is trusted.
"""
import argparse, hashlib, json, pathlib, re, shutil, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
IMAGE = "proofforge-lean:4.35.0"
CANDIDATE_GLOBS = ["candidate/Solution.lean", "candidate/Lib/**/*.lean"]
REQS = [
    ("REQ-VALID-SUCCEEDS", "Payout.req_valid_succeeds"),
    ("REQ-INVALID-NOOP", "Payout.req_invalid_noop"),
    ("REQ-FAIR-SHARES", "Payout.req_fair_shares"),
    ("REQ-EFFECTS", "Payout.req_effects"),
    ("REQ-CONSERVATION", "Payout.req_conservation"),
    ("REQ-NONNEGATIVE", "Payout.req_nonnegative"),
    ("REQ-AUTHORIZATION", "Payout.req_authorization"),
    ("REQ-IDEMPOTENCY", "Payout.req_idempotency"),
]
# Constructs that can make compiled code differ from what the kernel checked, or that
# run arbitrary code during elaboration. Defense in depth; Comparator is the authority.
FORBIDDEN = [
    r"implemented_by", r"\bextern\b", r"\bunsafe\b", r"@\[\s*export", r"\bmacro\b",
    r"\belab\b", r"\bsyntax\b", r"\binitialize\b", r"\bbuiltin_initialize\b",
    r"#eval", r"\brun_cmd\b", r"\brun_elab\b", r"\brun_meta\b", r"\bnative_decide\b",
    r"\bset_option\b", r"\bopaque\b", r"\baxiom\b", r"@\[\s*csimp",
]
ALLOWED_IMPORTS = re.compile(r"^(Payout\.Spec|Payout\.Lemmas|Init(\..+)?|Std(\..+)?)$")


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def run(cmd, timeout=900):
    t0 = time.monotonic()
    p = subprocess.run(cmd, capture_output=True, text=True, errors="replace", timeout=timeout)
    return {
        "command": cmd if isinstance(cmd, list) else [cmd],
        "exit_code": p.returncode,
        "elapsed_ms": int((time.monotonic() - t0) * 1000),
        "stdout_sha256": sha256_bytes(p.stdout.encode()),
        "stderr_sha256": sha256_bytes(p.stderr.encode()),
        "output_tail": (p.stdout + p.stderr)[-4000:],
    }


def load_workspace(arg: str) -> pathlib.Path:
    p = pathlib.Path(arg).resolve()
    if p.is_dir():
        return p
    ws = pathlib.Path(tempfile.mkdtemp(prefix="pf-ws-"))
    (ws / "candidate").mkdir()
    shutil.copy(p, ws / "candidate" / "Solution.lean")
    return ws


def tree_check(ws: pathlib.Path, locked: dict) -> dict:
    """Any protected file present in the workspace must be byte-identical to the lock."""
    problems = []
    for rel, digest in locked["files"].items():
        f = ws / rel
        if f.exists() and sha256_bytes(f.read_bytes()) != digest:
            problems.append(f"protected file modified: {rel}")
    lock_digest = sha256_bytes(json.dumps(locked["files"], sort_keys=True).encode())
    if lock_digest != locked["manifest_sha256"]:
        problems.append("spec/locked.json is internally inconsistent")
    for rel in locked["files"]:
        if sha256_bytes((FORMAL / rel).read_bytes()) != locked["files"][rel]:
            problems.append(f"repository protected file differs from lock: {rel}")
    return {"passed": not problems, "problems": problems}


def candidate_files(ws: pathlib.Path):
    files = []
    for g in CANDIDATE_GLOBS:
        files += sorted(ws.glob(g))
    return files


def impl_scan(files) -> dict:
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
            if not ALLOWED_IMPORTS.match(m.group(1)):
                problems.append(f"{f.name}: import not allowed: {m.group(1)}")
    return {"passed": not problems, "problems": problems}


def fresh_project(ws: pathlib.Path, files) -> pathlib.Path:
    """Locked project files from the repository + the candidate files, nothing else."""
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-judge-"))
    for rel in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "spec", "app"]:
        src = FORMAL / rel
        if src.is_dir():
            shutil.copytree(src, d / rel)
        else:
            shutil.copy(src, d / rel)
    for f in files:
        dst = d / f.relative_to(ws)
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(f, dst)
    return d


def in_container(project: pathlib.Path, script: str, timeout=900):
    cmd = [
        "docker", "run", "--rm", "--network", "none",
        # bubblewrap (Comparator's sandbox) needs user namespaces inside the container.
        "--security-opt", "seccomp=unconfined", "--security-opt", "apparmor=unconfined",
        "--security-opt", "systempaths=unconfined", "--cap-add", "SYS_ADMIN",
        "--memory", "4g", "--pids-limit", "512",
        "-v", f"{project}:/work", "-w", "/work", IMAGE, "bash", "-lc", script,
    ]
    return run(cmd, timeout=timeout)


def judge(arg: str, scan: bool = True) -> dict:
    t0 = time.monotonic()
    locked = json.loads((FORMAL / "spec" / "locked.json").read_text())
    ws = load_workspace(arg)
    files = candidate_files(ws)
    result = {
        "schema_version": 1,
        "candidate": str(arg),
        "manifest_sha256": locked["manifest_sha256"],
        "solution_tree_sha256": sha256_bytes(
            b"".join(sha256_bytes(f.read_bytes()).encode() for f in files)),
        "checks": {},
    }
    c = result["checks"]
    c["tree"] = tree_check(ws, locked)
    if not files:
        c["tree"]["passed"] = False
        c["tree"]["problems"].append("no candidate/Solution.lean")
    c["impl_scan"] = impl_scan(files) if scan else {"passed": True, "problems": [], "skipped": True}

    gate_ok = c["tree"]["passed"] and c["impl_scan"]["passed"]
    if gate_ok:
        project = fresh_project(ws, files)
        c["comparator"] = in_container(
            project, "lake comparator --config spec/comparator.json")
        if c["comparator"]["exit_code"] == 0:
            c["leanchecker"] = in_container(
                project, "lake build Solution >/dev/null && lake env leanchecker Solution")
        shutil.rmtree(project, ignore_errors=True)

    accepted = (gate_ok and c.get("comparator", {}).get("exit_code") == 0
                and c.get("leanchecker", {}).get("exit_code") == 0)
    status = "VERIFIED" if accepted else "REJECTED"
    result["requirements"] = {rid: status for rid, _ in REQS}
    result["accepted"] = accepted
    result["elapsed_ms"] = int((time.monotonic() - t0) * 1000)
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("candidate")
    ap.add_argument("--json")
    a = ap.parse_args()
    r = judge(a.candidate)
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
