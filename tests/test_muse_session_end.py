"""Sessions that end on responses cut at their output allowance (agents/muse_code.py). No model
calls.

In hard-task-1 every session that ended with no text (19 session parts, 6 of them in
proofforge-full on rw-oz-sqrt) ended right after model responses that reached their output
allowance of 32,000 tokens (`response.incomplete`), almost all of it reasoning; in proofforge-full
three in a row each time. Three of those six sessions made no edit, and each was continued with the
same list of eight `sorry` theorems.

  * response_end reads the last wire event of a model response from Muse Code's status events;
    over the committed events of hard-task-1, every session part that ended with no text ended on
    such responses, and the proofforge-full parts on three in a row;
  * a session part records its model responses, the cut ones and how many in a row ended it;
  * the continuation of a proofforge-full session that ended that way says so and asks for one
    step per response; a compiling file gets its first unproved required theorem as the next
    target, with its statement, and with the proof state from goal_at when its proof is a tactic
    block with `sorry`; the other arms' message is unchanged.
  * the skill and AGENTS.md of the ProofForge workspace ask for one step per response, since a
    response cut at the output limit is lost; the alone workspace has neither.

With Lean (the pinned image, one container at a time; skipped with --quick): goal_state on a
required theorem of rate-limiters-bucket-b1 whose proof is a tactic block with `sorry`.

Run: python3 tests/test_muse_session_end.py [--quick]
"""
import gzip, json, os, pathlib, shutil, sys, tempfile, types
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "integrations" / "muse"), str(ROOT / "tests")]
import muse_code  # noqa: E402
import test_muse_keep_best as kb  # noqa: E402

TASK = kb.TASK
RUNS = ROOT / "results/hard-task-1/runs"


def status_event(end):
    """Muse Code's status event at the end of one model response (the shape of events.jsonl)."""
    return {"payload_type": "task.lifecycle.status", "payload": {"kind": "task_lifecycle", "event": {
        "kind": "status", "message": "completed meta model stream attempt 1/10", "details": {
            "phase": "stream_succeeded", "facets": [
                {"kind": "external_attempt", "system": "meta", "operation": "model.response", "attempt": 1},
                {"kind": "producer", "detail": {"kind": "provider", "provider": "meta", "stream": {
                    "bytes_read": 677722, "last_wire_event_type": end, "eof": False}}}]}}}}


def parts_of(path):
    """Per session part of a committed events.jsonl.gz: (responses' last wire events, terminal text)."""
    parts = []
    for line in gzip.open(path, "rt"):
        try:
            e = json.loads(line)
        except ValueError:
            continue
        if e.get("payload_type") == "turn.input.user":
            parts.append([[], None])
        elif parts and muse_code.response_end(e):
            parts[-1][0].append(muse_code.response_end(e))
        elif parts and e.get("payload_type", "").startswith("run.terminal"):
            parts[-1][1] = e["payload"].get("text") or ""
    return parts


def trailing_cut(ends):
    n = 0
    for x in reversed(ends):
        if x != "response.incomplete":
            break
        n += 1
    return n


def test_response_end_reads_the_last_wire_event():
    assert muse_code.response_end(status_event("response.incomplete")) == "response.incomplete"
    assert muse_code.response_end(status_event("response.completed")) == "response.completed"
    opening = status_event("x")
    opening["payload"]["event"]["details"]["facets"][1]["detail"].pop("stream")
    assert muse_code.response_end(opening) is None
    assert muse_code.response_end({"payload_type": "run.usage", "payload": {}}) is None
    assert muse_code.response_end({"payload_type": "task.lifecycle.status", "payload": {"event": {}}}) is None


def test_silent_session_ends_in_hard_task_1_follow_cut_responses():
    silent, full = 0, {}
    for run in sorted(RUNS.glob("*/*")):
        for i, (ends, text) in enumerate(parts_of(run / "events.jsonl.gz"), 1):
            if text == "":
                silent += 1
                assert trailing_cut(ends) >= 1, (run.name, i, ends[-5:])
            if run.name.startswith("proofforge-full") and run.parent.name == "rw-oz-sqrt":
                full[(run.name, i)] = (trailing_cut(ends), text)
    assert silent == 19, silent
    assert [k for k, (n, text) in sorted(full.items()) if text == ""] == [
        ("proofforge-full-2", 1), ("proofforge-full-2", 2), ("proofforge-full-3", 1), ("proofforge-full-3", 2),
        ("proofforge-full-3", 3), ("proofforge-full-5", 1)]
    assert all(n == 3 for n, text in full.values() if text == ""), full
    assert full[("proofforge-full-3", 4)][0] == 0 and full[("proofforge-full-2", 3)][1] is None


FAKE_MUSE = """#!{python}
import sys
sys.stdout.write(open({events!r}).read())
"""


def test_a_session_part_records_cut_responses():
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-session-end-"))
    try:
        ends = ["response.completed", "response.incomplete", "response.completed", "response.failed",
                "response.incomplete", "response.incomplete", "response.incomplete"]
        lines = [status_event(e) for e in ends] + [
            {"payload_type": "run.terminal.completed", "payload": {"terminal": "completed", "text": "", "reason": None}}]
        (d / "events.jsonl").write_text("".join(json.dumps(x) + "\n" for x in lines))
        fake = d / "muse"
        fake.write_text(FAKE_MUSE.format(python=sys.executable, events=str(d / "events.jsonl")))
        fake.chmod(0o755)
        a = types.SimpleNamespace(model="m", effort="medium", max_model_steps=10, budget_wall=600)
        meter = types.SimpleNamespace(budget=types.SimpleNamespace(elapsed=lambda: 0.0), stopped=False,
                                      in_flight=lambda: 0)
        (d / "ws/candidate").mkdir(parents=True)
        (d / "ws/candidate/Solution.lean").write_text("x")
        (d / "out").mkdir()
        with patch.object(muse_code, "MUSE", fake):
            sess = muse_code.Session(a, TASK, d / "ws", d / "out", meter, 1, dict(os.environ), "sid")
            info = sess.run("prompt", 1)
        assert info["exit"] == 0 and info["terminal"] == {"terminal": "completed", "reason": None}, info
        assert (info["responses"], info["incomplete"], info["cut_off"]) == (7, 4, 3), info
        assert (d / "out/events.jsonl").read_text() == (d / "events.jsonl").read_text()
    finally:
        shutil.rmtree(d)


# Continuation messages

def continue_after(ws, text, cut_off, start_text="changed", versions=()):
    (ws / "candidate/Solution.lean").write_text(text)
    lean = kb.ScriptedLean(ws)
    record = {}
    ok, feedback = muse_code.ordinary_feedback(lean, TASK, ws, record)
    assert not ok and feedback
    return muse_code.progress_prompt(lean, TASK, ws, 2, feedback, record, start_text, list(versions), cut_off=cut_off)


def test_a_cut_session_hears_why_and_gets_the_first_open_requirement():
    th, n = TASK.theorems, len(TASK.theorems)
    ws, out = kb.dirs()
    try:
        text = kb.candidate(th[:2])
        with patch.object(muse_code, "goal_state", side_effect=AssertionError("no tactic proof, no goal_at")):
            msg = continue_after(ws, text, 3, start_text=text)
        assert msg.startswith(muse_code.CONTINUE + "The session made no change to candidate/Solution.lean. "
                              "The session ended after 3 responses in a row reached the output limit of a response "
                              "(32,000 tokens, reasoning included) before a tool call or an edit"), msg
        assert "Take one step per response" in msg and msg.endswith(muse_code.CONTINUE_END), msg
        assert f"candidate/Solution.lean compiles; it proves 2 of {n} required theorems" in msg, msg
        assert f"Next target: `{th[2]}`, the first required theorem not proved yet:\n```lean\ntheorem {th[2]} : P_{th[2]} sqrt\n```" in msg, msg
        assert f"Run try_tactics on `{th[2]}` first" in msg, msg
        one = continue_after(ws, text, 1)
        assert "after 1 response in a row" in one and "what it worked out is lost" in one, one
        plain = continue_after(ws, text, 0)
        assert "output limit" not in plain and "made no change" not in plain and f"Next target: `{th[2]}`" in plain, plain
        assert len(msg) < 3000, len(msg)
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_a_started_tactic_proof_gets_its_proof_state():
    th = TASK.theorems
    ws, out = kb.dirs()
    try:
        text = kb.candidate(th[:1]).replace(f"theorem {th[1]} : P_{th[1]} sqrt := sorry",
                                            f"theorem {th[1]} : P_{th[1]} sqrt := by\n  intro a\n  sorry")
        calls = []

        def goal_state(ws_, task, name):
            calls.append(name)
            return "`req` line 3: sorry\na : Nat\n⊢ P a"
        with patch.object(muse_code, "goal_state", goal_state):
            msg = continue_after(ws, text, 3)
        assert calls == [th[1]], calls
        assert f"Next target: `{th[1]}`" in msg and "goal_at on it:\n`req` line 3: sorry\na : Nat\n⊢ P a" in msg, msg
        assert "Run try_tactics" not in msg, msg
        with patch.object(muse_code, "goal_state", lambda *a: None):     # no state from Lean: the hint instead
            msg = continue_after(ws, text, 0)
        assert f"Run try_tactics on `{th[1]}` first" in msg, msg
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_a_missing_requirement_is_named_with_its_locked_statement():
    th = TASK.theorems
    ws, out = kb.dirs()
    try:
        text = kb.candidate(th[:1]).replace(f"theorem {th[1]} : P_{th[1]} sqrt := sorry\n", "")
        (ws / "candidate/Solution.lean").write_text(text)
        target = muse_code.next_target(TASK, ws, text, {th[0]: "PROVED", th[1]: "MISSING"})
        import passport
        assert f"```lean\ntheorem {th[1]} : {passport.statement(TASK, th[1])}\n```" in target, target
        assert muse_code.next_target(TASK, ws, text, {t: "PROVED" for t in th}) == ""
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_a_broken_file_and_the_other_arms_get_no_target():
    th = TASK.theorems
    ws, out = kb.dirs()
    try:
        msg = continue_after(ws, kb.candidate(th[:1], broken=True), 3)
        assert "output limit" in msg and "Lean's first errors" in msg and "Next target" not in msg, msg
        assert muse_code.KEEP_BEST == ("proofforge-full",)
        assert muse_code.CONTINUE + "F" + muse_code.CONTINUE_END == (
            "Your session ended, but the task is not finished. F\nContinue from the current candidate/Solution.lean "
            "until the file compiles and every required theorem is proved.")
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


# Guidance

def test_workspace_guidance_asks_for_one_step_per_response():
    alone = muse_code.make_workspace(TASK, "alone")
    full = muse_code.make_workspace(TASK, "proofforge-full")
    try:
        skill = (full / ".agents/skills/proofforge/SKILL.md").read_text()
        agents = (full / "AGENTS.md").read_text()
        for text in (skill, agents):
            assert "reasoning included" in text and "32,000" in text and "`have` steps ending in `sorry`" in text
        assert "one step per response" in agents.lower() and "Work out the next step only" in skill
        assert not (alone / ".agents").exists() and not (alone / "AGENTS.md").exists()
    finally:
        shutil.rmtree(alone)
        shutil.rmtree(full)


# With Lean

def test_goal_state_with_lean():
    import test_topdown as td
    bucket = td.BUCKET
    start = td.FIXED_BUCKET.replace("theorem req_valid_succeeds       : ValidSucceeds step := sorry",
                                    "theorem req_valid_succeeds       : ValidSucceeds step := by\n  unfold ValidSucceeds\n  sorry")
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-session-end-start-"))
    (d / "Solution.lean").write_text(start)
    ws = muse_code.make_workspace(bucket, "proofforge-full", d / "Solution.lean")
    try:
        target = muse_code.next_target(bucket, ws, start, {t: "SORRY" for t in bucket.theorems})
        assert "Next target: `req_valid_succeeds`" in target and "goal_at on it:\n" in target, target
        assert "⊢" in target and "Run try_tactics" not in target, target
    finally:
        shutil.rmtree(ws, ignore_errors=True)
        shutil.rmtree(d, ignore_errors=True)


LEAN_TESTS = {"test_goal_state_with_lean"}

if __name__ == "__main__":
    quick = "--quick" in sys.argv
    for name, fn in list(globals().items()):
        if not name.startswith("test_"):
            continue
        if name in LEAN_TESTS and (quick or not __import__("test_topdown").have_lean()):
            print(f"skip  {name}")
            continue
        fn()
        print(f"ok  {name}")
