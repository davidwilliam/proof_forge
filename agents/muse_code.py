#!/usr/bin/env python3
"""Muse Code on a ProofForge task: headless runs in an isolated copy, in arms with equal caps.

Arms
  alone            Muse Code with the task files (the locked Lean project, the buggy candidate and
                   the issue report) and Lean: the MCP server in its `lean` profile gives one tool,
                   `lean_build`, which returns Lean's own output. No judge, no tests, no library.
  proofforge       Muse Code with ProofForge as measured in results/muse-code-1: the MCP server in
                   its `proofforge` profile (lean_build, show_task, try_snippet, check_candidate,
                   verify_passport, search_library, list_tasks), the skill
                   `.agents/skills/proofforge`, the workspace AGENTS.md and the ProofForgeFin
                   library vendored into the workspace.
  proofforge-full  Muse Code with everything ProofForge offers: the `full` profile adds the
                   harness's proof tools (goal_at and check_snippet_fast on a persistent Lean
                   session, try_tactics with the tactic portfolio, refute_statement on concrete
                   values, search_library with the goal-aware ranking, and prior_attempts with the
                   attempt ledger when the run resumes); same skill, AGENTS.md and library.
All arms get the same prompt (the arm-specific lines name the tools and, with ProofForge, the
library import), the same model, effort, caps and Muse Code flags. Muse Code's shell sandbox
cannot reach Docker, so in every arm Lean runs only through the MCP server.

Resuming (`--resume-from DIR[,DIR...]`, run directories of earlier runs on the same task and
locked spec, refused otherwise as in agents/ledger.py)
  Every arm starts from a prior run's final file, as agents/baseline.py starts from a prior
  candidate: each prior `final.lean` is compiled by Lean in this run (inside the wall cap) and the
  one that compiles with the most required theorems proved is the start (the first one when none
  compiles). The prompt says that the file comes from a previous attempt. `alone` and
  `proofforge` get nothing else. `proofforge-full` also gets `prior_attempts`: the prior runs'
  attempt ledgers, their proved declarations re-checked by Lean against the current file, their
  best compiling versions and their failure notes.

Attempt ledger
  Every run writes `ledger.json` (agents/ledger.py) into its run directory: the declarations of
  every candidate version Lean compiled in a tool call or in the runner's checks, the final file,
  the best compiling version, and failure notes for the goals left open, built from the
  ProofForge tool calls (snippets per goal, tactics tried, statements refuted) and the runner's
  feedback.

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
  at its worst case (its input tokens bounded by the request's bytes, or, for a request that
  extends an earlier one of the same conversation, by that request's reported prompt tokens plus
  the bytes of the new items; the same rule for every arm) and settled to the usage reported in
  its `response.completed` event, priced
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
  `sorry`, or the judge's rejection), the same in `alone` and `proofforge`, as in A0
  (agents/baseline.py). In `proofforge-full` the message also gives the run's progress
  (progress_prompt): Lean's first errors rather than the end of its output, the required theorems
  the file proves, whether the session changed the file, and the best compiling version of the run
  when it proves more; a file that does not compile is saved as `.proofforge/unfinished-NN.lean`
  and the best compiling version, when there is one, takes its place.

Result
  The candidate on disk when the run stops is the run's result (`final.lean`), except in
  `proofforge-full`: there the result is the compiling version of the run with the most required
  theorems proved by Lean, the latest on a tie, when the file on disk does not compile or proves
  fewer (a run stopped by a cap is often in the middle of an edit); the file on disk is then kept
  as `final-on-disk.lean` and summary.json records the choice (`final_choice`). The versions
  considered are those Lean compiled in a tool call or in the runner's checks; the choice is made
  after the caps, as the theorem status of the final file is. The result is judged
  outside the budget by `bin/proofforge check` (identical for every arm); a VERIFIED Passport is
  reproduced with `bin/proofforge verify`. summary.json records the tools Muse Code called and how
  often (`tool_calls`: every tool from the transcript, and the ProofForge tools from the MCP log
  with errors and seconds), and, when the final file does not compile, the newest compiling
  version with its theorem status (`last_compiling`).

Usage: muse_code.py --task T --arm alone|proofforge|proofforge-full [--model muse-spark-1.3-contributor]
                    [--effort medium] [--budget-usd 10] [--budget-wall 14400] [--out DIR]
                    [--resume-from DIR[,DIR...]] [--prompt-file FILE] [--max-sessions 12]
                    [--max-model-steps 400]
"""
import argparse, collections, json, os, pathlib, re, shutil, signal, subprocess, sys, tempfile, threading, time, uuid

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse")]
import meter as metermod  # noqa: E402
import proofforge_mcp  # noqa: E402
import fin_lib, judge, task as taskmod  # noqa: E402
import ledger  # noqa: E402
from meta_client import api_key  # noqa: E402

MUSE = pathlib.Path(os.environ.get("MUSE_BIN") or shutil.which("muse") or pathlib.Path.home() / ".local/bin/muse")
FORBIDDEN_TEXT = ("sorry, axiom, opaque, implemented_by, extern, unsafe, @[export], @[csimp], macro, elab, syntax, "
                  "initialize, #eval, run_cmd, native_decide, set_option")
SETTLE_S = 300
MCP_TOOL_TIMEOUT_S = 3600   # Muse Code's per-server `tool_timeout_sec`; the run's wall cap still applies
ARMS = ("alone", "proofforge", "proofforge-full")
PROFILE = {"alone": "lean", "proofforge": "proofforge", "proofforge-full": "full"}
ARM_TOOLS = {
    "alone": "lean_build (Lean's output for `lake build Solution`, or `lake env lean <file>` for any .lean file here)",
    "proofforge": "the proofforge tools (lean_build, show_task, try_snippet, check_candidate, verify_passport, "
                  "search_library, list_tasks) and the proofforge skill",
    "proofforge-full": "the proofforge tools (lean_build, show_task, goal_at, check_snippet_fast, try_snippet, "
                       "try_tactics, refute_statement, search_library, check_candidate, verify_passport, "
                       "list_tasks{prior}) and the proofforge skill",
}
RESUMED_LINE = ("This run resumes a previous attempt: candidate/Solution.lean is the final file of that attempt, "
                "not the original buggy candidate.")
# Arms whose result is the best compiling version of the run (most required theorems proved, then
# latest) rather than the file on disk when the run stops; `alone` and `proofforge` keep the file
# on disk, as measured in results/muse-code-1 and results/hard-task-1.
KEEP_BEST = ("proofforge-full",)
BEST_CANDIDATES = 3     # compiling versions, ranked by their text, that Lean checks for the best one


def with_proofforge(arm):
    return arm != "alone"


def arm_tools(arm, resumed=False):
    return ARM_TOOLS[arm].replace("{prior}", ", prior_attempts" if resumed else "")


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
    if with_proofforge(arm):
        shutil.copy(ROOT / "integrations/muse/workspace/AGENTS.md", ws / "AGENTS.md")
        (ws / ".agents/skills").mkdir(parents=True)
        shutil.copytree(ROOT / ".agents/skills/proofforge", ws / ".agents/skills/proofforge")
        fin_lib.vendor(ws, force=True)
    git = ["git", "-c", "user.name=proofforge-runner", "-c", "user.email=runner@proofforge.invalid", "-c", "commit.gpgsign=false"]
    subprocess.run(["git", "init", "-q", "-b", "main", str(ws)], check=True)
    subprocess.run(git + ["-C", str(ws), "add", "-A"], check=True)
    subprocess.run(git + ["-C", str(ws), "commit", "-q", "-m", f"{task.id}: task workspace"], check=True)
    return ws


def prompt_for(task, arm, resumed=False):
    defs = ", ".join(f"`{task.ns}.{d}`" for d in task.definitions)
    lemmas = ", {}.Lemmas".format(task.lib) if (task.root / task.spec_dir / "Lemmas.lean").exists() else ""
    imports = f"{task.lib}.Spec{lemmas}, Init.*, Std.*" + (", ProofForgeFin.* (vendored in this workspace)" if with_proofforge(arm) else "")
    resume = f"\n{RESUMED_LINE}\n" if resumed else ""
    return f"""This directory is a Lean 4 (v4.35.0, core library only, no Mathlib) project with a locked specification.

Issue report (also in ISSUE.md): {task.issue}
{resume}
Your job:
1. Fix {defs} in candidate/Solution.lean so it satisfies the locked requirements in {task.spec_dir}/Spec.lean.
2. Prove all {len(task.theorems)} theorems of {task.spec_dir}/Challenge.lean in candidate/Solution.lean, with exactly the same names and statements, and no `sorry`.

Rules (enforced by an independent judge; violations are rejected):
- Change only candidate/Solution.lean. Every other file is locked and checked byte for byte.
- candidate/Solution.lean must define {defs} and the {len(task.theorems)} theorems in `namespace {task.ns}`.
- Allowed imports: {imports}.
- Forbidden: {FORBIDDEN_TEXT}.
- Weakening or restating a theorem differently is rejected. Changing behavior to avoid hard inputs cannot satisfy requirements that demand success on valid inputs.

Lean is not installed in the shell. Run Lean through the MCP tools: {arm_tools(arm, resumed)}.
Work only inside this directory. Keep going until the file compiles and every required theorem is proved without `sorry`.
"""


def settings_for(arm, ws, task, mcp_log, real_home, record_dir=None, resume_from=()):
    args = [str(ROOT / "integrations/muse/proofforge_mcp.py"), "--workspace", str(ws), "--task", task.id,
            "--profile", PROFILE[arm], "--blind", "--log", str(mcp_log)]
    if record_dir:
        args += ["--record-dir", str(record_dir)]
    if resume_from and PROFILE[arm] == "full":     # only the full toolset reads the prior attempts' ledgers
        args += ["--resume-from", ",".join(str(x) for x in resume_from)]
    env = {"HOME": str(real_home), "DOCKER_CONFIG": str(real_home / ".docker"),
           "PF_CONTAINER_SLOTS": os.environ.get("PF_CONTAINER_SLOTS", "2")}
    for k in ("TMPDIR", "PF_FIN_CACHE", "PF_LSP_IDLE", "LEAN_NUM_THREADS"):   # the slot directory and library cache
        if os.environ.get(k):
            env[k] = os.environ[k]
    server = {"transport": "stdio", "command": sys.executable, "args": args, "env": env,
              "mode": "required",
              # A full check or a Passport reproduction takes minutes; past Muse Code's default MCP
              # tool timeout the call fails and the server's connection is closed for the session.
              "tool_timeout_sec": MCP_TOOL_TIMEOUT_S}
    return {"schema_version": 1, "telemetry": {"enabled": False}, "mcp_servers": {"proofforge": server}}


# ------------------------------------------------------------------------------------------------
# Ordinary checking between sessions (what A0 gets)

INFRA = re.compile(r"Cannot connect to the Docker daemon|Error response from daemon|context canceled|^docker: ", re.M)


def unavailable(r):
    """A Lean run that produced no verdict: stopped at its time limit or failed in Docker itself."""
    out = r.get("output_tail") or ""
    return judge.TIMEOUT_MARK in out or r.get("exit_code") in (125, 126, 127) or bool(INFRA.search(out))


def ordinary_feedback(server, task, ws, record=None):
    """(accepted, message): compile; then sorry status; then the judge, as agents/baseline.audit.
    The message is None when Lean or the judge gave no verdict (a time limit or a Docker failure),
    so that an infrastructure failure is never reported to the agent as a rejection. `record`, a
    dict, receives Lean's whole output when the file does not compile (`lean`) and the theorem
    status when it does (`status`)."""
    record = {} if record is None else record
    r = server.lean("lake build Solution 2>&1 | tail -c 60000")
    if unavailable(r):
        return False, None
    text = proofforge_mcp.clean_lean(r["output_tail"])
    if "error:" in text:
        record["lean"] = text
        return False, "candidate/Solution.lean does not compile. Lean output:\n" + text[-6000:]
    status = server.theorem_status(task)
    record["status"] = status
    scan = judge.impl_scan([ws / "candidate/Solution.lean"], task)
    if all(v == "MISSING" for v in status.values()) and not any("required theorem missing" in p for p in scan["problems"]):
        return False, None      # the axiom audit produced no output
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
    runs = [c for c in j["checks"].values() if isinstance(c, dict) and "exit_code" in c]
    cmp_ = j["checks"].get("comparator", {}).get("output_tail", "")
    errors = [l for l in cmp_.splitlines() if "error" in l.lower()]
    if not reasons and (not errors or any(unavailable(c) for c in runs)):
        return False, None
    return False, ("The file compiles with no sorry, but the judge rejected it: " + "; ".join(reasons) + "\n"
                   + "\n".join(errors)[-3000:])


CONTINUE = "Your session ended, but the task is not finished. "
CONTINUE_END = "\nContinue from the current candidate/Solution.lean until the file compiles and every required theorem is proved."


def first_errors(lean, limit=3, lines=30, chars=4000):
    """Lean's first `limit` errors, each cut to `lines` lines: the message with its position, which
    the last characters of a long output (the end of one goal state) can leave out."""
    blocks = [b for sev, b in proofforge_mcp.lean_blocks(lean)
              if sev == "error" and not re.match(r"^error: build failed", b[0])]
    if not blocks:
        return lean[-chars:]
    text = "\n".join("\n".join(b[:lines] + (["  [...]"] if len(b) > lines else [])) for b in blocks[:limit])
    if len(blocks) > limit:
        text += f"\n({len(blocks) - limit} more errors)"
    return text[:chars]


def proved_names(task, status):
    return [t for t in task.theorems if status.get(t) == "PROVED"]


def describe(task, status):
    proved = proved_names(task, status)
    open_ = [f"{t} ({(status.get(t) or 'missing').lower()})" for t in task.theorems if status.get(t) != "PROVED"]
    return (f"it proves {len(proved)} of {len(task.theorems)} required theorems" + (": " + ", ".join(proved) if proved else "")
            + ("; not proved yet: " + ", ".join(open_) if open_ else ""))


def progress_prompt(server, task, ws, n, feedback, record, start_text, versions):
    """The continuation message of a KEEP_BEST arm after session part n: what ordinary checking
    gives (`feedback`, `record` from ordinary_feedback), with Lean's first errors in place of the
    end of its output, and the progress of the run: whether the session changed the file, the
    required theorems the file proves, and the best compiling version of the run (best_version)
    when it proves more. When the file does not compile and a compiling version exists, the file is
    saved as .proofforge/unfinished-NN.lean and that version takes its place. The best version is
    also kept as the MCP server's .proofforge/best.lean. A judge's rejection is passed on as is."""
    path = ws / "candidate/Solution.lean"
    text = path.read_text()
    msg = CONTINUE + ("The session made no change to candidate/Solution.lean. " if text == start_text else "")
    broken, status = "lean" in record, record.get("status") or {}
    proved = len(proved_names(task, status))
    if not broken and (not status or proved == len(task.theorems)):
        return msg + feedback + CONTINUE_END
    pick, top = None, rank_versions(task, versions)[:1]
    if top and (broken or text_proved(task, versions[top[0]]) > proved):
        try:
            pick = best_version(server, task, ws, versions)
        except RuntimeError:
            pick = None
    if broken:
        errors = first_errors(record["lean"]) + proofforge_mcp.tactic_hints(record["lean"], {"candidate/Solution.lean": text})
        if pick is None:
            return msg + "candidate/Solution.lean does not compile. Lean's first errors:\n" + errors + CONTINUE_END
        saved = f".proofforge/unfinished-{n:02d}.lean"
        (ws / ".proofforge").mkdir(exist_ok=True)
        (ws / saved).write_text(text)
        path.write_text(pick[0])
        proofforge_mcp.save_best(ws, pick[0], proved_names(task, pick[1]))
        return (msg + "candidate/Solution.lean did not compile. Lean's first errors:\n" + errors + "\n"
                f"That file is saved as {saved}, and candidate/Solution.lean is now the best compiling version of this "
                f"run; {describe(task, pick[1])}. Continue from it, or copy the saved file back and fix its errors."
                + CONTINUE_END)
    msg += f"candidate/Solution.lean compiles; {describe(task, status)}."
    if "Rule violations:" in feedback:
        msg += " Rule violations:" + feedback.split("Rule violations:", 1)[1]
    if pick and len(proved_names(task, pick[1])) > proved:
        proofforge_mcp.save_best(ws, pick[0], proved_names(task, pick[1]))
        msg += (f"\nAn earlier compiling version of this run, saved as {proofforge_mcp.BEST}, proves more; "
                f"{describe(task, pick[1])}.")
    return msg + CONTINUE_END


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
        self.proc = p
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


# ------------------------------------------------------------------------------------------------
# Resuming, tool counts and the attempt ledger

def compiles(server, timeout=900):
    """(compiles, theorem status) of the workspace candidate; RuntimeError when Lean gives no verdict."""
    r = server.lean("lake build Solution 2>&1 | tail -c 20000", timeout=timeout)
    if unavailable(r):
        raise RuntimeError("Lean gave no verdict (time limit or Docker failure)")
    if r["exit_code"] != 0 or "error:" in proofforge_mcp.clean_lean(r["output_tail"]):
        return False, {}
    return True, server.theorem_status(server.task())


def resume_base(server, task, ws, priors):
    """The start of a resumed run: the prior runs' final files, each compiled by Lean here; the one
    that compiles with the most required theorems proved (first on a tie), else the first. The
    workspace candidate becomes it and the workspace commits it. Returns its record."""
    cands, seen = [], set()
    for led in priors:
        text = (led.get("final") or {}).get("text")
        if text and text not in seen:
            seen.add(text)
            cands.append((led["run_dir"], text))
    best, tried = None, []
    for run_dir, text in cands:
        (ws / "candidate/Solution.lean").write_text(text)
        ok, status = compiles(server)
        rec = {"run_dir": run_dir, "compiles": ok, "proved": sum(v == "PROVED" for v in status.values()),
               "proved_required": sorted(t for t, v in status.items() if v == "PROVED")}
        tried.append(rec)
        if ok and (best is None or not best[0]["compiles"] or rec["proved"] > best[0]["proved"]):
            best = (rec, text)
        elif best is None:
            best = (rec, text)
    rec, text = best
    (ws / "candidate/Solution.lean").write_text(text)
    git = ["git", "-c", "user.name=proofforge-runner", "-c", "user.email=runner@proofforge.invalid", "-c", "commit.gpgsign=false"]
    subprocess.run(git + ["-C", str(ws), "commit", "-q", "--allow-empty", "-am", "resume: final file of a previous attempt"], check=True)
    return {**rec, "candidates": tried}


def jsonl(path):
    out = []
    if path.is_file():
        for line in path.read_text(errors="replace").splitlines():
            try:
                out.append(json.loads(line))
            except ValueError:
                pass
    return out


def tool_counts(out):
    """Which tools Muse Code called and how often: every tool proposed in the transcript
    (`task.lifecycle.proposed` with a `tool.` task kind; MCP tools appear as mcp__proofforge__NAME)
    and, from the MCP log, each ProofForge tool's calls, errors and seconds."""
    muse = collections.Counter()
    for e in jsonl(out / "events.jsonl"):
        if e.get("payload_type") == "task.lifecycle.proposed":
            kind = ((e.get("payload") or {}).get("event") or {}).get("task_kind") or ""
            if kind.startswith("tool."):
                muse[kind[len("tool."):]] += 1
    pf = {}
    for r in jsonl(out / "mcp-calls.jsonl"):
        t = pf.setdefault(r.get("tool"), {"calls": 0, "errors": 0, "seconds": 0.0})
        t["calls"] += 1
        t["errors"] += int(bool(r.get("error")))
        t["seconds"] = round(t["seconds"] + (r.get("seconds") or 0.0), 1)
    return {"muse_code": dict(sorted(muse.items(), key=lambda x: (-x[1], x[0]))),
            "proofforge": dict(sorted(pf.items(), key=lambda x: (-x[1]["calls"], x[0])))}


DECL_NAME = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s:({\[]+)", re.M)


def ledger_events(mcp_log, feedback):
    """Ledger events (agents/ledger.goal_notes) from the ProofForge tool calls of a run: snippets
    per theorem they state, goal_at states, portfolio tactics that did not close a goal, statements
    refuted; and the runner's feedback between sessions as whole-run audits."""
    ev = []
    for r in jsonl(mcp_log):
        tool, args = r.get("tool"), r.get("args") or {}
        if tool in ("try_snippet", "check_snippet_fast"):
            m = DECL_NAME.search(args.get("code") or "")
            if m:
                ev.append({"kind": "tool", "label": f"muse:{m.group(1).split('.')[-1]}", "name": "try_snippet",
                           "args": {"code": args.get("code")}, "result": r.get("result") or ""})
        elif tool == "goal_at" and args.get("name"):
            ev.append({"kind": "tool", "label": f"muse:{str(args['name']).split('.')[-1]}", "name": "goal_at",
                       "args": args, "result": r.get("result") or ""})
        elif tool == "try_tactics" and r.get("portfolio") and not r["portfolio"].get("closed_by"):
            p = r["portfolio"]
            ev.append({"kind": "portfolio", "closed": {}, "results": {p["goal"]: {k: None for k in p.get("tried") or []}}})
        elif tool == "refute_statement" and (r.get("refute") or {}).get("status") == "false" and r["refute"].get("name"):
            ev.append({"kind": "refute", "ok": True, "name": r["refute"]["name"]})
    ev += [{"kind": "audit", "feedback": f} for f in feedback if f]
    return ev


def compiled_sources(record_dir, extra=()):
    """The candidate versions Lean compiled without errors, oldest first (by the time each was
    found to compile), de-duplicated: the MCP server's records and `extra`, (epoch seconds, text)."""
    srcs = [(p.stat().st_mtime, p.read_text()) for p in pathlib.Path(record_dir).glob("compiled-*.lean")] if record_dir else []
    srcs += [x for x in extra if x and x[1]]
    return list(dict.fromkeys(text for _, text in sorted(srcs, key=lambda x: x[0])))


def text_proved(task, text):
    """The required theorems a compiling version proves in its text: no `sorry` in the theorem or in
    a candidate declaration it uses (ledger.proved_in)."""
    return sum(1 for n in ledger.proved_in(text, task.ns) if n in task.theorems)


def rank_versions(task, versions):
    """Indices of `versions` (oldest first), best first: by text_proved, the latest first on a tie."""
    return sorted(range(len(versions)), key=lambda i: (text_proved(task, versions[i]), i), reverse=True)


def best_version(server, task, ws, versions, limit=BEST_CANDIDATES):
    """The compiling version with the most required theorems proved by Lean (`#print axioms`), the
    latest on a tie, among the `limit` best of `versions` by their text: (text, theorem status), or
    None when none of them compiles. The workspace candidate is left as it was. RuntimeError when
    Lean gives no verdict."""
    path = ws / "candidate/Solution.lean"
    current, best = path.read_text(), None
    try:
        for i in rank_versions(task, versions)[:limit]:
            path.write_text(versions[i])
            ok, status = compiles(server)
            n = sum(v == "PROVED" for v in status.values())
            if ok and (best is None or (n, i) > best[:2]):
                best = (n, i, status)
    finally:
        path.write_text(current)
    return None if best is None else (versions[best[1]], best[2])


def choose_final(server, task, ws, out, versions, disk_text, disk_ok, disk_status):
    """The result of a KEEP_BEST arm: the best compiling version of the run (best_version) when the
    file on disk does not compile or proves fewer required theorems; the file on disk otherwise, and
    when Lean gives no verdict. The chosen text becomes the workspace candidate; a replaced file on
    disk is kept as final-on-disk.lean. Returns (text, compiles, theorem status, record)."""
    def proved(status):
        return sorted(t for t, v in status.items() if v == "PROVED")
    rec = {"from": "file on disk", "on_disk": {"compiles": disk_ok, "proved": len(proved(disk_status))}}
    try:
        pick = best_version(server, task, ws, versions)
    except RuntimeError as e:
        return disk_text, disk_ok, disk_status, {**rec, "error": str(e)}
    if pick is None or (disk_ok and len(proved(pick[1])) <= len(proved(disk_status))):
        return disk_text, disk_ok, disk_status, rec
    (out / "final-on-disk.lean").write_text(disk_text)
    (ws / "candidate/Solution.lean").write_text(pick[0])
    return pick[0], True, pick[1], {**rec, "from": "best compiling version", "proved": proved(pick[1])}


def write_ledger(task, out, arm, summary, sources, events, final_text, final_status, last_compiling=None):
    """ledger.json of a Muse Code run (agents/ledger.py's format), from its compiling versions."""
    extra = {"mode": "muse-code", "model": summary.get("model"),
             "budget": {"usd_list": (summary.get("meter") or {}).get("usd_list"), "elapsed_s": summary.get("elapsed_s")},
             "resumed_from": summary.get("resumed_from") or []}
    led = ledger.build(task, out, sources, events, final_text, final_status, arm, extra)
    if last_compiling and len(last_compiling["proved_required"]) > len(led["best_candidate"]["proved_required"]):
        led["best_candidate"] = {"version": "last compiling", "proved_required": last_compiling["proved_required"],
                                 "text": last_compiling["text"]}
    (out / ledger.NAME).write_text(json.dumps(led, indent=1))
    return led


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", required=True)
    ap.add_argument("--arm", choices=list(ARMS), required=True)
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
    ap.add_argument("--resume-from", help="comma-separated run directories (or ledger.json files) of prior runs on the "
                                          "same task and locked spec: start from their final file (the one that "
                                          "compiles with the most required theorems proved); proofforge-full also "
                                          "gets prior_attempts")
    a = ap.parse_args()

    task = taskmod.load(a.task)
    priors, prior_record = [], []
    if a.resume_from:
        if a.start:
            ap.error("--resume-from and --start both choose the start candidate")
        priors, prior_record = ledger.load_many([x.strip() for x in a.resume_from.split(",")], task)
        for r in prior_record:
            print(f"[resume] {r['path']}: " + ("used" if r["used"] else f"refused ({r['refused']})"), flush=True)
        if not priors:
            ap.error("--resume-from: no usable prior run: " + "; ".join(f"{r['path']}: {r['refused']}" for r in prior_record))
    # Absolute: the MCP server runs in the workspace, where a path relative to this checkout means nothing.
    resume_dirs = [str(pathlib.Path(r["path"]).resolve()) for r in prior_record if r["used"]]
    out = pathlib.Path(a.out or ROOT / "runs" / f"muse-{time.strftime('%Y%m%d-%H%M%S')}-{task.id}-{a.arm}").resolve()
    out.mkdir(parents=True, exist_ok=True)
    real_home = pathlib.Path.home()
    ws = make_workspace(task, a.arm, a.start)
    home = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-home-"))
    record_dir = pathlib.Path(tempfile.mkdtemp(prefix="pf-muse-compiled-"))   # candidate versions Lean compiled
    (home / ".config/muse").mkdir(parents=True)
    (home / ".config/muse/settings.json").write_text(json.dumps(
        settings_for(a.arm, ws, task, out / "mcp-calls.jsonl", real_home, record_dir, resume_dirs), indent=2))
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
              "mcp_profile": PROFILE[a.arm], "library_vendored": with_proofforge(a.arm),
              "library_source_tree_sha256": fin_lib.tree_sha256() if with_proofforge(a.arm) else None,
              "resumed_from": resume_dirs,
              "git_commit": subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=ROOT).stdout.strip(),
              "started": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    (out / "config.json").write_text(json.dumps(config, indent=2) + "\n")
    print(f"[muse-code] {task.id} arm={a.arm} {version} workspace={ws} out={out}", flush=True)

    runner_compiled, feedback_log = [], []
    if priors:   # inside the wall cap, as the A0 and repair agents resume inside their budgets
        try:
            base = resume_base(server, task, ws, priors)
        except RuntimeError as e:
            sys.exit(f"[resume] {e}")
        config["resume"] = {"ledgers": prior_record, "base": base, "seconds": round(meter.budget.elapsed(), 1)}
        (out / "config.json").write_text(json.dumps(config, indent=2) + "\n")
        if base["compiles"]:
            runner_compiled.append((time.time(), (ws / "candidate/Solution.lean").read_text()))
        print(f"[resume] start from {pathlib.Path(base['run_dir']).name}: compiles {base['compiles']}, "
              f"{base['proved']} required theorems proved", flush=True)

    sid = str(uuid.uuid4())
    sess = Session(a, task, ws, out, meter, port, env, sid)

    def interrupted(signum, frame):   # stop Muse Code (and through it the MCP server) with the runner
        if getattr(sess, "proc", None) and sess.proc.poll() is None:
            Session.kill(sess.proc)
        sys.exit(128 + signum)
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    prompt = pathlib.Path(a.prompt_file).read_text() if a.prompt_file else prompt_for(task, a.arm, resumed=bool(priors))
    parts, stop, accepted, idle = [], None, False, 0
    for n in range(1, a.max_sessions + 1):
        calls_before = meter.calls
        start_text = (ws / "candidate/Solution.lean").read_text()
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
        checked = (ws / "candidate/Solution.lean").read_text()
        record = {}
        ok, feedback = ordinary_feedback(server, task, ws, record)
        if not ok and feedback is None and meter.budget.elapsed() < a.budget_wall - 120:
            time.sleep(60)              # no verdict: try once more before deciding anything
            record = {}
            ok, feedback = ordinary_feedback(server, task, ws, record)
        if ok or (feedback and not feedback.startswith("candidate/Solution.lean does not compile")):
            runner_compiled.append((time.time(), checked))
        feedback_log.append(feedback)
        if meter.budget.elapsed() >= a.budget_wall:
            stop = "wall"
            break
        if ok:
            accepted, stop = True, "accepted"
            break
        if meter.stopped:
            stop = "usd"
            break
        if feedback is None:
            stop = "judge_unavailable"    # Lean or the judge gave no verdict twice; nothing is sent to the agent
            break
        if a.arm in KEEP_BEST:
            prompt = progress_prompt(server, task, ws, n, feedback, record, start_text,
                                     compiled_sources(record_dir, runner_compiled))
        else:
            prompt = CONTINUE + (feedback or "") + CONTINUE_END
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
    summary = {**config, "stop": stop if stop != "accepted" else None, "ended_by": stop, "accepted_in_run": accepted,
               "elapsed_s": elapsed, "session_parts": parts, "model_calls": meter_summary["calls"],
               "main_agent_calls": main_steps, "meter": meter_summary, "muse_reported_usage": reported,
               "snapshots": sess.snaps, "tool_calls": tool_counts(out)}
    # The run's record is written before any further Lean work, so a failure there cannot lose it.
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    final_text = (ws / "candidate/Solution.lean").read_text()
    try:
        final_ok, status = compiles(server)
        srcs = compiled_sources(record_dir, runner_compiled + ([(time.time(), final_text)] if final_ok else []))
        if a.arm in KEEP_BEST and not accepted:
            final_text, final_ok, status, summary["final_choice"] = choose_final(server, task, ws, out, srcs, final_text,
                                                                                final_ok, status)
        summary.update(final_theorem_status=status, requirements_proved_in_run=sum(v == "PROVED" for v in status.values()))
        last = None
        older = [x for x in srcs if x != final_text]
        if not final_ok and older:
            # The newest version Lean compiled during the run, and its theorem status (outside the budget).
            (ws / "candidate/Solution.lean").write_text(older[-1])
            ok, st = compiles(server)
            (ws / "candidate/Solution.lean").write_text(final_text)
            if ok:
                last = {"proved_required": sorted(t for t, v in st.items() if v == "PROVED"), "text": older[-1]}
                summary["last_compiling"] = {"theorem_status": st, "proved": len(last["proved_required"]),
                                             "of_compiled_versions": len(srcs)}
        try:
            led = write_ledger(task, out, a.arm, summary, srcs, ledger_events(out / "mcp-calls.jsonl", feedback_log),
                               final_text, status, last)
            summary["ledger"] = {"proved": len(led["proved"]), "open_goals": [g["name"] for g in led["open_goals"]],
                                 "compiled_versions": len(srcs)}
        except Exception as e:   # the summary and final candidate stand without it
            summary["ledger_error"] = f"{type(e).__name__}: {e}"[:500]
        if not a.no_check:
            p = official_check(task, out)
            if p:
                summary["passport"] = {"status": p["status"], "passport_sha256": p["passport_sha256"],
                                       "requirements": {q["id"]: q["status"] for q in p["requirements"]},
                                       "verified": sum(q["status"] == "VERIFIED" for q in p["requirements"])}
    except Exception as e:   # recorded; the final candidate can be checked again with bin/proofforge check
        summary["final_check_error"] = f"{type(e).__name__}: {e}"[:500]
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    shutil.copy(ws / "candidate/Solution.lean", out / "final.lean")
    reps = [(str(ws.resolve()), "<workspace>"), (str(ws), "<workspace>"), (str(home), "<muse-home>"),
            (str(ROOT), "<proofforge>"), (str(real_home), "~")]
    for name in ("events.jsonl", "muse-stderr.txt", "mcp-calls.jsonl", "calls.jsonl", "summary.json", "config.json",
                 "ledger.json"):
        sanitize(out / name, reps)
    print(json.dumps({k: summary[k] for k in ("task", "arm", "ended_by", "elapsed_s", "model_calls")} |
                     {"usd_list": meter_summary["usd_list"], "usd_actual": meter_summary["usd_actual"],
                      "passport": summary.get("passport", {}).get("status")}), flush=True)
    shutil.rmtree(home, ignore_errors=True)
    shutil.rmtree(record_dir, ignore_errors=True)
    if os.environ.get("PF_KEEP_WORKSPACE") != "1":
        shutil.rmtree(ws, ignore_errors=True)


if __name__ == "__main__":
    main()
