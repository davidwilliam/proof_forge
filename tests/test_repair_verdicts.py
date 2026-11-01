"""Lean feedback of the repair agent (agents/repair.py, arm A1): snippet verdicts from Lean's whole
output, linter-only warnings, build digests, banking notes, the whole-file phase that keeps a file
as the model wrote it, and the guarantee that the whole-file phase always gets the rest of the
budget. No model calls (the model client and the HTTP layer are never reached).

The fixture tests/fixtures/repair_verdicts/workflow_b1_snippets.json holds three try_snippet calls
recorded in results/e1-test-open-1/permissions-workflow-b1/A1 (the code, the result the run
returned) with Lean's complete output when each is compiled after that run's final candidate:
two proofs Lean accepted with linter warnings, which the run did not bank, and one proof with five
errors that the run reported as compiling, because only the last 4000 characters of Lean's output
were read.

Without Lean: the verdicts on the recorded outputs, the verdict rules, the build digest, the
removal of exploration commands from banked chunks, the banking notes, the whole-file phase's
verbatim saves (on the A0 file of queues-ring-b2 that the reordering breaks) and the phase order
of orchestrate().
With Lean (the pinned image, one container at a time): the recorded snippets replayed through
Session.try_snippet on the recorded candidate, and the A0 file of queues-ring-b2 compiled as written
and as reordered.

Run: python3 tests/test_repair_verdicts.py [--quick] [name ...]   (--quick skips the Lean runs)
"""
import argparse, json, os, pathlib, re, shutil, subprocess, sys, tempfile
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness")]
import budget, judge, repair, task as taskmod  # noqa: E402

FIXTURE = json.loads((ROOT / "tests/fixtures/repair_verdicts/workflow_b1_snippets.json").read_text())
WORKFLOW = taskmod.load("permissions-workflow-b1")
RING = taskmod.load("queues-ring-b2")
RECORDED = ROOT / "results/e1-test-open-1"


def case(label, recorded):
    return next(c for c in FIXTURE["cases"] if c["label"] == label and c["recorded"] == recorded)


def old_verdict(output, offset):
    """The rule the recorded run applied: messages located in the snippet, from the last 4000
    characters of the output (judge.run keeps that much), clean when none is an error or a warning."""
    msgs, cur = [], None
    for l in repair.Session._clean(output[-4000:]).splitlines():
        m = re.match(r"^Scratch\.lean:(\d+):(\d+): (error|warning)", l)
        if m:
            cur = int(m.group(1)) - offset >= 0
        if cur:
            msgs.append(l)
    return not any(re.search(r": (error|warning)", m) for m in msgs)


def bare_session(task, cls=repair.Session):
    """A session without a workspace, for the text-only methods."""
    s = cls.__new__(cls)
    s.task, s.ns, s.theorems, s.end = task, task.ns, task.theorems, f"end {task.ns}"
    s.boundary = (r"(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |instance |abbrev "
                  rf"|structure |inductive |open |{re.escape(s.end)})")
    return s


def session(task, start=None):
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-verdicts-"))
    return repair.Session(task, "muse-spark-1.3-contributor", start or task.start, out, budget.Budget(None, None))


def close(s):
    shutil.rmtree(s.ws, ignore_errors=True)
    shutil.rmtree(s.out, ignore_errors=True)


def forward_uses(src):
    """Declarations that use a declaration placed after them in `src`."""
    decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(?:theorem|lemma|def|instance|abbrev)\s+([^\s:({\[]+)", re.M)
    found = [(m.start(), m.group(1)) for m in decl.finditer(src)]
    bad = []
    for i, (p, n) in enumerate(found):
        body = src[p:found[i + 1][0] if i + 1 < len(found) else len(src)]
        bad += [f"{n} uses {o}" for q, o in found if q > p and o != n and re.search(rf"(?<![\w.']){re.escape(o)}(?![\w'])", body)]
    return bad


# Without Lean

def test_recorded_false_clean_is_not_clean():
    c = case("pass1:req_effects", "clean")
    assert c["recorded_result"].startswith("snippet compiles with no errors or warnings")
    assert c["exit"] == 1 and len(re.findall(r"(?m)^Scratch\.lean:\d+:\d+: error", c["output"])) == 5
    assert old_verdict(c["output"], c["offset"])          # what the run concluded from the tail
    clean, msgs = repair.scratch_verdict(c["output"], c["offset"], c["exit"])
    assert not clean
    text = repair.join_messages(msgs)
    assert "snippet:10:9: error: unknown tactic" in text and text.count(": error") == 5, text[:800]


def test_recorded_linter_only_proofs_are_clean():
    for c in [x for x in FIXTURE["cases"] if x["recorded"] == "warn-only"]:
        assert not old_verdict(c["output"], c["offset"])   # refused by the run for a linter warning
        clean, msgs = repair.scratch_verdict(c["output"], c["offset"], c["exit"])
        assert clean and c["exit"] == 0, msgs
        assert msgs and all("warning" in m for m in msgs)   # the warnings are still shown
        assert "unused" in "\n".join(msgs)


def test_verdict_rules():
    head = "Scratch.lean:{}:2: {}: {}\n"
    lint = head.format(12, "warning", "unused variable `h`") + "\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n"
    sorry = head.format(13, "warning", "declaration uses `sorry`")
    dep = head.format(12, "warning", "`Nat.foo` has been deprecated: use `Nat.bar`") + "\nHint: Replace the deprecated name\n"
    before = head.format(3, "error", "unknown identifier `x`")
    big = head.format(14, "error", "unsolved goals") + "⊢ " + "a ∧ " * 3000 + "True\n"
    assert repair.scratch_verdict(lint, 10, 0) == (True, ["snippet:2:2: warning: unused variable `h`"])
    assert not repair.scratch_verdict(lint + sorry, 10, 0)[0]
    clean, msgs = repair.scratch_verdict(dep, 10, 0)
    assert clean and msgs == []                            # a deprecation is left out whole
    assert repair.scratch_verdict(before + lint, 10, 1)[0]   # errors before the snippet are not its own
    assert not repair.scratch_verdict(lint, 10, None)[0]     # no exit status: nothing is established
    clean, msgs = repair.scratch_verdict("", 10, 1)
    assert not clean and "without reporting an error" in msgs[0]
    clean, msgs = repair.scratch_verdict(big + big.replace(":14:", ":20:") + sorry, 10, 1)
    assert not clean and len(msgs) == 3 and all(len(m) < repair.MESSAGE_CHARS + 40 for m in msgs)
    text = repair.join_messages(msgs, limit=2000)
    assert "snippet:4:2: error" in text and "2 more message(s): snippet:10:2: error" in text, text[-300:]


def test_build_digest_keeps_every_error_location():
    goal = "⊢ " + "x = x ∧ " * 900 + "True\n"
    out = ("✖ [3/4] Building Solution (554ms)\ntrace: .> lean candidate/Solution.lean\n"
           + "".join(f"warning: candidate/Solution.lean:{n}:4: declaration uses `sorry`\n" for n in (5, 9))
           + "".join(f"error: candidate/Solution.lean:{n}:8: unsolved goals\ncase pos\n{goal}" for n in (40, 80, 120, 160))
           + "Some required targets logged failures:\n- Solution\nerror: build failed\n")
    assert len(out) > 25000 and "candidate/Solution.lean:40" not in out[-4000:]   # the plain tail had one goal
    d = repair.build_digest(out, 1)
    assert len(d) <= repair.BUILD_CHARS and d.endswith("error: build failed"), d[-200:]
    assert "error: candidate/Solution.lean:40:8: unsolved goals" in d and "message shortened" in d
    assert all(f"candidate/Solution.lean:{n}:8" in d for n in (40, 80, 120, 160)), d
    ok = "⚠ [3/4] Built Solution (513ms)\nwarning: candidate/Solution.lean:5:4: declaration uses `sorry`\n"
    assert "error:" not in repair.build_digest(ok, 0)
    assert "error:" in repair.build_digest("uncaught exception: out of memory\n", 137)


def test_banked_chunks_drop_exploration_commands():
    text = ("theorem a : 1 = 1 := rfl\n#check a\n#print axioms a\nexample : 2 = 2 := by\n  rfl\n\n"
            "-- kept\ntheorem b : True := by\n  trivial")
    assert repair.strip_explorations(text) == "theorem a : 1 = 1 := rfl\n-- kept\ntheorem b : True := by\n  trivial"
    assert repair.strip_explorations("theorem c : True := by\n  trivial") == "theorem c : True := by\n  trivial"


def test_bank_says_what_it_did_not_bank():
    s = session(WORKFLOW)
    try:
        src = s._source()
        proof = "theorem req_valid_succeeds : ValidSucceeds step := by\n  intro s r h\n  exact absurd h h"
        helper = "theorem my_helper : True := by\n  trivial"
        with patch.object(repair.Session, "_scratch", lambda self, code, hoist=(): (True, [], 1)), \
                patch.object(repair.Session, "compile", lambda self, tail=9000: {"output_tail": "error: candidate/Solution.lean:30:2: unsolved goals\nerror: build failed", "elapsed_ms": 1}):
            out = s.try_snippet(helper + "\n\n" + proof)
        assert "banked into" not in out, out
        assert "`req_valid_succeeds` was not banked: with it candidate/Solution.lean does not compile" in out, out
        assert "`my_helper` was not banked" in out and "unsolved goals" in out, out
        assert s._source() == s._normalize(src)                     # every edit reverted
        s._save(src.replace("theorem req_authorization        : Authorized step := sorry",
                            "theorem req_authorization : Authorized step := by\n  intro s r h\n  exact absurd h h"), "test")
        with patch.object(repair.Session, "_scratch", lambda self, code, hoist=(): (True, [], 1)):
            out = s.try_snippet("theorem req_authorization : Authorized step := by\n  exact fun _ _ h => absurd h h")
        assert "`req_authorization` already has a proof in candidate/Solution.lean, which was kept" in out, out
    finally:
        close(s)


def test_whole_file_phase_keeps_the_file_as_written():
    a0 = (RECORDED / "queues-ring-b2/A0/final.lean").read_text()   # accepted by the judge for A0
    s = bare_session(RING)
    assert not forward_uses(a0)
    moved = s._normalize(a0)
    assert any("step_contents_fifo_aux uses req_enqueue_contents" in b for b in forward_uses(moved))
    s.verbatim = True
    assert s._normalize(a0) == a0
    import baseline
    assert baseline.FileSession.full_messages is False and repair.Session.full_messages is True


def test_whole_file_phase_runs_verbatim_whenever_not_accepted():
    """The e1-dev-1 defect (a session that ends with budget left) cannot come back: phase 3 runs
    when phase 0 fails and when phases 1 and 2 end without acceptance; it saves verbatim."""
    seen = []

    def fake_run(s, a, state="", library_text="", resume_text=""):
        seen.append((s.verbatim, a.max_turns, state))
    for phase0_ok in (False, True):
        s = session(WORKFLOW)
        try:
            s.run_tests = lambda: '{"status": "FAIL"}'
            a = argparse.Namespace(model="m", effort="medium", phase0_turns=1)
            middle = lambda *_: seen.append("middle")   # noqa: E731
            with patch.object(repair, "dialog", lambda *x, **k: (phase0_ok, [])), \
                    patch("baseline.run", fake_run):
                repair.orchestrate(s, a, middle=middle)
            assert s.verbatim is False
        finally:
            close(s)
    assert seen == [(True, 200, "current, partly repaired"), "middle", (True, 200, "current, partly repaired")], seen


# With Lean

def test_recorded_snippets_replayed_on_the_recorded_candidate():
    s = session(WORKFLOW, RECORDED / "permissions-workflow-b1/A1/final.lean")
    try:
        before = s._source()
        out = s.try_snippet(case("pass1:req_effects", "clean")["code"])
        assert out.startswith("snippet:") and "error" in out and s._source() == before, out[:500]
        out = s.try_snippet(case("pass1:req_invalid_noop", "warn-only")["code"])
        assert out.startswith("snippet compiles with no errors (linter warnings only)"), out[:500]
        assert "banked into candidate/Solution.lean: req_invalid_noop" in out, out
        assert s.check_status(["req_invalid_noop"]) == {"req_invalid_noop": "PROVED"}
    finally:
        close(s)


def test_whole_file_attempt_compiles_as_written():
    a0 = RECORDED / "queues-ring-b2/A0/final.lean"
    s = session(RING)
    try:
        s._save(a0.read_text(), "reordered")
        r = s.compile()
        assert "error:" in r["output_tail"] and "req_enqueue_contents" in r["output_tail"], r["output_tail"][-600:]
        s.verbatim = True
        s._save(a0.read_text(), "attempt")
        assert s._source() == a0.read_text()
        assert "error:" not in s.compile()["output_tail"]
    finally:
        close(s)


LEAN = {"test_recorded_snippets_replayed_on_the_recorded_candidate", "test_whole_file_attempt_compiles_as_written"}


def have_lean():
    if judge.IN_IMAGE:
        return True
    return subprocess.run(["docker", "image", "inspect", judge.IMAGE], capture_output=True).returncode == 0


if __name__ == "__main__":
    from test_topdown import limit_lean_threads
    limit_lean_threads(int(os.environ.get("LEAN_NUM_THREADS", "4")))
    quick = "--quick" in sys.argv
    only = [x for x in sys.argv[1:] if not x.startswith("--")]
    lean = have_lean()
    for name, fn in list(globals().items()):
        if not name.startswith("test_") or not callable(fn) or (only and name not in only):
            continue
        if name in LEAN and (quick or not lean):
            print(f"skip {name}")
            continue
        fn()
        print(f"ok  {name}")
