#!/usr/bin/env python3
"""Muse Code on a ProofForge task: headless runs in an isolated copy, in two arms with equal caps.

Arms
  alone       Muse Code with the task files (the locked Lean project, the buggy candidate and the
              issue report) and Lean: the MCP server in its `lean` profile gives one tool,
              `lean_build`, which returns Lean's own output. No judge, no tests, no library.
  proofforge  Muse Code with ProofForge: the MCP server in its `proofforge` profile (lean_build,
              show_task, try_snippet, check_candidate, verify_passport, search_library,
              list_tasks), the skill `.agents/skills/proofforge`, the workspace AGENTS.md and the
              ProofForgeFin library vendored into the workspace.
Both arms get the same prompt (the arm-specific lines name the tools and, for proofforge, the
library import), the same model, effort, caps and Muse Code flags. Muse Code's shell sandbox
cannot reach Docker, so in both arms Lean runs only through the MCP server.

Isolation
  - the workspace is a fresh temporary copy of the task's project files, the start candidate and
    ISSUE.md, in its own git repository; reference solutions, attacks, witnesses, README and
    results are never copied;
  - Muse Code runs with its own HOME and XDG_CONFIG_HOME (settings.json holds only the MCP
    server, telemetry off), `--no-foreign-personal-context`, `--disable-web-tools`,
    `--disable-request-user-input`, `--trust-workspace` (loads the workspace's AGENTS.md and skill),
    `--disable-approval` with the sandbox on and `--sandbox-network restricted`;
  - the MCP server runs with `--blind`: `show_task` omits the README, which describes the fixes.

Cost and caps (integrations/muse/meter.py)
  Muse Code's model calls go through a local metering proxy (`--base-url`). Each call is reserved
  at its worst case and settled to the usage reported in its `response.completed` event, priced
  with agents/budget.py at standard list prices; the Contributor-tier charge is tracked
  separately. Each call's output allowance is at most 32,000 tokens, as for A0, A1 and A2. A call
  that cannot fit the dollars left is refused and the run stops once the calls in flight have
  settled (at most 300 s; a call cut off stays charged at its worst case). The wall cap
  covers everything: model calls, Lean through the MCP server, the runner's checks between
  sessions. Muse Code's own end-of-run `run.usage` (which omits its helper agents' calls) is
  recorded for comparison.

Sessions
  `muse exec` ends when the agent ends its turn. While the caps allow and the judge has not
  accepted the candidate, the runner continues the same session (`--session-id`) with a neutral
  message holding what ordinary checking gives (the Lean errors, or the theorems that still use
  `sorry`, or the judge's rejection), the same for both arms, as in A0 (agents/baseline.py).

Result
  The candidate on disk when the run stops is the run's result (`final.lean`). It is judged
  outside the budget by `bin/proofforge check` (identical for both arms); a VERIFIED Passport is
  reproduced with `bin/proofforge verify`.

Usage: muse_code.py --task T --arm alone|proofforge [--model muse-spark-1.3-contributor]
                    [--effort medium] [--budget-usd 10] [--budget-wall 14400] [--out DIR]
                    [--prompt-file FILE] [--max-sessions 12] [--max-model-steps 400]
"""
import argparse, json, os, pathlib, re, shutil, signal, subprocess, sys, tempfile, threading, time, uuid

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse")]
import meter as metermod  # noqa: E402
import proofforge_mcp  # noqa: E402
import fin_lib, judge, task as taskmod  # noqa: E402
from meta_client import api_key  # noqa: E402

MUSE = pathlib.Path(os.environ.get("MUSE_BIN") or shutil.which("muse") or pathlib.Path.home() / ".local/bin/muse")
FORBIDDEN_TEXT = ("sorry, axiom, opaque, implemented_by, extern, unsafe, @[export], @[csimp], macro, elab, syntax, "
                  "initialize, #eval, run_cmd, native_decide, set_option")
SETTLE_S = 300
ARM_TOOLS = {
    "alone": "lean_build (Lean's output for `lake build Solution`, or `lake env lean <file>` for any .lean file here)",
    "proofforge": "the proofforge tools (lean_build, show_task, try_snippet, check_candidate, verify_passport, "
                  "search_library, list_tasks) and the proofforge skill",
}


def muse_version():
    r = subprocess.run([str(MUSE), "--version"], capture_output=True, text=True, env={**os.environ, "MUSE_NO_AUTO_UPDATE": "1"})
    return r.stdout.strip()


# ------------------------------------------------------------------------------------------------
# Workspace

def make_workspace(task, arm, start=None):
    ws = pathlib.Path(tempfile.mkdtemp(prefix=f"pf-muse-{arm}-"))
    for rel in taskmod.PROJECT_FILES:
        src = task.root / rel
        (shutil.copytree if src.is_dir() else shutil.copy)(src, ws / rel)
    (ws / "candidate").mkdir()
    shutil.copy(start or task.start, ws / "candidate/Solution.lean")
    (ws / "ISSUE.md").write_text(f"# Issue report: {task.id}\n\n{task.issue}\n")
    (ws / ".proofforge").mkdir()
    (ws / ".proofforge/task.json").write_text(json.dumps({"task": task.id}) + "\n")
    (ws / ".gitignore").write_text(".lake/\n.proofforge/\n")
    if arm == "proofforge":
        shutil.copy(ROOT / "integrations/muse/workspace/AGENTS.md", ws / "AGENTS.md")
        (ws / ".agents/skills").mkdir(parents=True)
        shutil.copytree(ROOT / ".agents/skills/proofforge", ws / ".agents/skills/proofforge")
        fin_lib.vendor(ws, force=True)
    git = ["git", "-c", "user.name=proofforge-runner", "-c", "user.email=runner@proofforge.invalid", "-c", "commit.gpgsign=false"]
    subprocess.run(["git", "init", "-q", "-b", "main", str(ws)], check=True)
    subprocess.run(git + ["-C", str(ws), "add", "-A"], check=True)
    subprocess.run(git + ["-C", str(ws), "commit", "-q", "-m", f"{task.id}: task workspace"], check=True)
    return ws


def prompt_for(task, arm):
    defs = ", ".join(f"`{task.ns}.{d}`" for d in task.definitions)
    lemmas = ", {}.Lemmas".format(task.lib) if (task.root / task.spec_dir / "Lemmas.lean").exists() else ""
    imports = f"{task.lib}.Spec{lemmas}, Init.*, Std.*" + (", ProofForgeFin.* (vendored in this workspace)" if arm == "proofforge" else "")
    return f"""This directory is a Lean 4 (v4.35.0, core library only, no Mathlib) project with a locked specification.

Issue report (also in ISSUE.md): {task.issue}

Your job:
1. Fix {defs} in candidate/Solution.lean so it satisfies the locked requirements in {task.spec_dir}/Spec.lean.
2. Prove all {len(task.theorems)} theorems of {task.spec_dir}/Challenge.lean in candidate/Solution.lean, with exactly the same names and statements, and no `sorry`.

Rules (enforced by an independent judge; violations are rejected):
- Change only candidate/Solution.lean. Every other file is locked and checked byte for byte.
- candidate/Solution.lean must define {defs} and the {len(task.theorems)} theorems in `namespace {task.ns}`.
- Allowed imports: {imports}.
- Forbidden: {FORBIDDEN_TEXT}.
- Weakening or restating a theorem differently is rejected. Changing behavior to avoid hard inputs cannot satisfy requirements that demand success on valid inputs.

Lean is not installed in the shell. Run Lean through the MCP tools: {ARM_TOOLS[arm]}.
Work only inside this directory. Keep going until the file compiles and every required theorem is proved without `sorry`.
"""


def settings_for(arm, ws, task, mcp_log, real_home):
    server = {"transport": "stdio", "command": sys.executable,
              "args": [str(ROOT / "integrations/muse/proofforge_mcp.py"), "--workspace", str(ws), "--task", task.id,
                       "--profile", "lean" if arm == "alone" else "proofforge", "--blind", "--log", str(mcp_log)],
              "env": {"HOME": str(real_home), "DOCKER_CONFIG": str(real_home / ".docker"),
                      "PF_CONTAINER_SLOTS": os.environ.get("PF_CONTAINER_SLOTS", "2")},
              "mode": "required"}
    return {"schema_version": 1, "telemetry": {"enabled": False}, "mcp_servers": {"proofforge": server}}


# ------------------------------------------------------------------------------------------------
# Ordinary checking between sessions (what A0 gets)

def ordinary_feedback(server, task, ws):
    """(accepted, message): compile; then sorry status; then the judge, as agents/baseline.audit."""
    r = server.lean("lake build Solution 2>&1 | tail -c 60000")
    text = proofforge_mcp.clean_lean(r["output_tail"])
    if judge.TIMEOUT_MARK in text:
        return False, None
    if "error:" in text:
        return False, "candidate/Solution.lean does not compile. Lean output:\n" + text[-6000:]
    status = server.theorem_status(task)
    scan = judge.impl_scan([ws / "candidate/Solution.lean"], task)
    open_ = [t for t, v in status.items() if v != "PROVED"]
    if open_ or scan["problems"]:
        msg = "candidate/Solution.lean compiles."
        if open_:
            msg += " These required theorems are not proved yet: " + ", ".join(f"{t} ({status[t].lower()})" for t in open_) + "."
        if scan["problems"]:
            msg += " Rule violations:\n" + "\n".join(scan["problems"])
        return False, msg
    j = judge.judge(str(ws / "candidate/Solution.lean"), task=task)
    if j["accepted"]:
        return True, "accepted"
    reasons = j["checks"]["tree"]["problems"] + j["checks"]["impl_scan"]["problems"]
    cmp_ = j["checks"].get("comparator", {}).get("output_tail", "")
    return False, ("The file compiles with no sorry, but the judge rejected it: " + "; ".join(reasons) + "\n"
                   + "\n".join(l for l in cmp_.splitlines() if "error" in l.lower())[-3000:])


# ------------------------------------------------------------------------------------------------
# One Muse Code session

class Session:
    def __init__(self, a, task, ws, out, meter, port, env, sid):
        self.a, self.task, self.ws, self.out, self.meter, self.port, self.env, self.sid = a, task, ws, out, meter, port, env, sid
        self.snap_hash = None
        self.snaps = 0

    def snapshot(self):
        f = self.ws / "candidate/Solution.lean"
        try:
            text = f.read_text()
        except OSError:
            return
        h = hash(text)
        if h != self.snap_hash:
            self.snap_hash = h
            self.snaps += 1
            (self.out / f"candidate_v{self.snaps:03d}.lean").write_text(text)   # not tracked (.gitignore)

    def run(self, prompt, n):
        pfile = self.out / f"prompt-{n:02d}.txt"
        pfile.write_text(prompt)
        cmd = [str(MUSE), "exec", "--json", "--prompt-file", str(pfile), "--session-id", self.sid,
               "--model", self.a.model, "--reasoning-effort", self.a.effort,
               "--base-url", f"http://127.0.0.1:{self.port}/v1",
               "--no-foreign-personal-context", "--disable-web-tools", "--disable-request-user-input",
               "--trust-workspace", "--disable-approval", "--sandbox-network", "restricted",
               "--max-model-steps", str(self.a.max_model_steps)]
        events = (self.out / "events.jsonl").open("a")
        errf = (self.out / "muse-stderr.txt").open("a")
        errf.write(f"--- session part {n} ---\n")
        errf.flush()
        p = subprocess.Popen(cmd, cwd=self.ws, env=self.env, stdout=subprocess.PIPE, stderr=errf, text=True,
                             start_new_session=True)
        info = {"part": n, "terminal": None, "run_usage": None, "exit": None, "killed": None}

        def reader():
            for line in p.stdout:
                events.write(line)
                events.flush()
                try:
                    e = json.loads(line)
                except ValueError:
                    continue
                pt = e.get("payload_type", "")
                if pt == "run.usage":
                    info["run_usage"] = e["payload"]
                elif pt.startswith("run.terminal"):
                    info["terminal"] = {k: e["payload"].get(k) for k in ("terminal", "reason")}
                    info["final_text"] = (e["payload"].get("text") or "")[:2000]
        th = threading.Thread(target=reader, daemon=True)
        th.start()
        settle_from = None
        while p.poll() is None:
            time.sleep(2)
            self.snapshot()
            if self.meter.budget.elapsed() >= self.a.budget_wall:
                info["killed"] = "wall"        # the deadline is hard: calls in flight stay at worst case
            elif self.meter.stopped:
                # Dollar stop: no new call is admitted; the calls already sent finish and settle at
                # their reported usage (at most SETTLE_S), then Muse Code is stopped.
                settle_from = settle_from or time.monotonic()
                if self.meter.in_flight() == 0 or time.monotonic() - settle_from > SETTLE_S:
                    info["killed"] = "usd"
            if info["killed"]:
                self.kill(p)
                break
        p.wait()
        th.join(timeout=30)
        events.close()
        errf.close()
        self.snapshot()
        info["exit"] = p.returncode
        return info

    @staticmethod
    def kill(p):
        for sig, wait in ((signal.SIGTERM, 20), (signal.SIGKILL, 10)):
            try:
                os.killpg(p.pid, sig)
            except ProcessLookupError:
                return
            try:
                p.wait(timeout=wait)
                return
            except subprocess.TimeoutExpired:
                continue


# ------------------------------------------------------------------------------------------------

def sanitize(path, replacements):
    """Replace machine paths in a run record with placeholders before it is committed."""
    if not path.is_file():
        return
    text = path.read_text(errors="replace")
    for old, new in replacements:
        text = text.replace(old, new)
    path.write_text(text)


def official_check(task, out):
    """`bin/proofforge check` on final.lean (identical for both arms) and, when VERIFIED,
    `bin/proofforge verify`. Outside the budget."""
    final = out / "final.lean"
    r = subprocess.run([sys.executable, "bin/proofforge", "check", "--task", task.id, "--candidate",
                        str(final.relative_to(ROOT)), "--out", str((out / "passport.json").relative_to(ROOT))],
                       capture_output=True, text=True, cwd=ROOT)
    (out / "check.txt").write_text(r.stdout + r.stderr)
    p = json.loads((out / "passport.json").read_text()) if (out / "passport.json").is_file() else None
    if p and p["status"] == "VERIFIED":
        v = subprocess.run([sys.executable, "bin/proofforge", "verify", str((out / "passport.json").relative_to(ROOT)),
                            "--candidate", str(final.relative_to(ROOT))], capture_output=True, text=True, cwd=ROOT)
        (out / "verify.txt").write_text(v.stdout + v.stderr)
    return p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", required=True)
    ap.add_argument("--arm", choices=["alone", "proofforge"], required=True)
    ap.add_argument("--model", default="muse-spark-1.3-contributor")
    ap.add_argument("--effort", default="medium")
    ap.add_argument("--budget-usd", type=float, default=10.0)
    ap.add_argument("--budget-wall", type=float, default=14400.0)
    ap.add_argument("--max-sessions", type=int, default=12,
                    help="session parts (the first prompt plus continuations) before the run stops")
    ap.add_argument("--max-model-steps", type=int, default=400, help="Muse Code's own step cap per session part")
    ap.add_argument("--prompt-file", help="a different first prompt (the demonstration)")
    ap.add_argument("--start", help="a different start candidate")
    ap.add_argument("--no-continue", action="store_true", help="one session part only")
    ap.add_argument("--no-check", action="store_true", help="skip the official check of the final candidate")
    ap.add_argument("--out")
    a = ap.parse_args()

    task = taskmod.load(a.task)
    out = pathlib.Path(a.out or ROOT / "runs" / f"muse-{time.strftime('%Y%m%d-%H%M%S')}-{task.id}-{a.arm}").resolve()
    out.mkdir(parents=True, exist_ok=True)
    real_home = pathlib.Path.home()
    ws = make_workspace(task, a.arm, a.start)
    home = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-home-"))
    (home / ".config/muse").mkdir(parents=True)
    (home / ".config/muse/settings.json").write_text(json.dumps(settings_for(a.arm, ws, task, out / "mcp-calls.jsonl", real_home), indent=2))
    env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config"),
           "TMPDIR": os.environ.get("TMPDIR", "/tmp"), "LANG": os.environ.get("LANG", "en_US.UTF-8"),
           "MUSE_NO_AUTO_UPDATE": "1", "META_API_KEY": api_key()}
    version = muse_version()
    meter = metermod.Meter(out, usd_cap=a.budget_usd, wall_cap=a.budget_wall)
    port = meter.start()
    server = proofforge_mcp.Server(ws, task.id, "lean")
    judge.DEADLINE = meter.budget.deadline()   # the runner's own Lean runs stop at the wall cap too
    config = {"task": task.id, "arm": a.arm, "model": a.model, "effort": a.effort, "budget_usd": a.budget_usd,
              "budget_wall_s": a.budget_wall, "max_sessions": a.max_sessions, "max_model_steps": a.max_model_steps,
              "muse_code": version, "muse_flags": ["exec", "--json", "--no-foreign-personal-context", "--disable-web-tools",
                                                    "--disable-request-user-input", "--trust-workspace", "--disable-approval",
                                                    "--sandbox-network restricted", f"--max-model-steps {a.max_model_steps}",
                                                    f"--model {a.model}", f"--reasoning-effort {a.effort}", "--base-url <meter>",
                                                    "--session-id <run session>"],
              "mcp_profile": "lean" if a.arm == "alone" else "proofforge", "library_vendored": a.arm == "proofforge",
              "library_source_tree_sha256": fin_lib.tree_sha256() if a.arm == "proofforge" else None,
              "git_commit": subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=ROOT).stdout.strip(),
              "started": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    (out / "config.json").write_text(json.dumps(config, indent=2) + "\n")
    print(f"[muse-code] {task.id} arm={a.arm} {version} workspace={ws} out={out}", flush=True)

    sid = str(uuid.uuid4())
    sess = Session(a, task, ws, out, meter, port, env, sid)
    prompt = pathlib.Path(a.prompt_file).read_text() if a.prompt_file else prompt_for(task, a.arm)
    parts, stop, accepted, idle = [], None, False, 0
    for n in range(1, a.max_sessions + 1):
        calls_before = meter.calls
        info = sess.run(prompt, n)
        info["model_calls"] = meter.calls - calls_before
        info["elapsed_s"] = round(meter.budget.elapsed(), 1)
        parts.append(info)
        print(f"[muse-code] part {n}: exit {info['exit']} terminal {info['terminal']} calls {info['model_calls']} "
              f"list ${meter.budget.usd_list:.2f} {info['elapsed_s']} s", flush=True)
        if info["killed"]:
            stop = info["killed"]
            break
        if a.no_continue:
            stop = "single_session"
            break
        if info["model_calls"] == 0 and info["exit"] not in (0, None):
            stop = "muse_error"    # Muse Code failed before any model call (see muse-stderr.txt)
            break
        idle = idle + 1 if info["model_calls"] == 0 else 0
        if idle >= 2:
            stop = "no_model_calls"
            break
        ok, feedback = ordinary_feedback(server, task, ws)
        if meter.budget.elapsed() >= a.budget_wall:
            stop = "wall"
            break
        if ok:
            accepted, stop = True, "accepted"
            break
        if meter.stopped:
            stop = "usd"
            break
        prompt = ("Your session ended, but the task is not finished. " + (feedback or "") +
                  "\nContinue from the current candidate/Solution.lean until the file compiles and every required theorem is proved.")
    else:
        stop = "max_sessions"
    meter_summary = meter.summary()
    meter.stop()
    judge.DEADLINE = None   # the final status and the official check are outside the budget
    sess.snapshot()
    shutil.copy(ws / "candidate/Solution.lean", out / "final.lean")
    elapsed = round(meter.budget.elapsed(), 1)

    # Muse Code's own usage records, summed over the session parts (main agent only).
    reported = {"input_tokens": 0, "cached_tokens": 0, "output_tokens": 0, "reasoning_tokens": 0, "calls": 0}
    for pinfo in parts:
        for m in (pinfo.get("run_usage") or {}).get("models", []):
            for k in reported:
                reported[k] += m.get(k, 0)
    main_steps = (meter_summary["by_role"].get("main") or {}).get("calls", 0)
    status = server.theorem_status(task) if "error:" not in proofforge_mcp.clean_lean(
        server.lean("lake build Solution 2>&1 | tail -c 20000", timeout=900)["output_tail"]) else {}
    summary = {**config, "stop": stop if stop != "accepted" else None, "ended_by": stop, "accepted_in_run": accepted,
               "elapsed_s": elapsed, "session_parts": parts, "model_calls": meter_summary["calls"],
               "main_agent_calls": main_steps, "meter": meter_summary, "muse_reported_usage": reported,
               "snapshots": sess.snaps, "final_theorem_status": status,
               "requirements_proved_in_run": sum(v == "PROVED" for v in status.values())}
    if not a.no_check:
        p = official_check(task, out)
        if p:
            summary["passport"] = {"status": p["status"], "passport_sha256": p["passport_sha256"],
                                   "requirements": {q["id"]: q["status"] for q in p["requirements"]},
                                   "verified": sum(q["status"] == "VERIFIED" for q in p["requirements"])}
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    shutil.copy(ws / "candidate/Solution.lean", out / "final.lean")
    reps = [(str(ws.resolve()), "<workspace>"), (str(ws), "<workspace>"), (str(home), "<muse-home>"),
            (str(ROOT), "<proofforge>"), (str(real_home), "~")]
    for name in ("events.jsonl", "muse-stderr.txt", "mcp-calls.jsonl", "calls.jsonl", "summary.json", "config.json"):
        sanitize(out / name, reps)
    print(json.dumps({k: summary[k] for k in ("task", "arm", "ended_by", "elapsed_s", "model_calls")} |
                     {"usd_list": meter_summary["usd_list"], "usd_actual": meter_summary["usd_actual"],
                      "passport": summary.get("passport", {}).get("status")}), flush=True)
    shutil.rmtree(home, ignore_errors=True)
    if os.environ.get("PF_KEEP_WORKSPACE") != "1":
        shutil.rmtree(ws, ignore_errors=True)


if __name__ == "__main__":
    main()
