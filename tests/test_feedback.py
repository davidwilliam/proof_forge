"""Attempt ledger, --resume-from and the tactic portfolio, with scripted model clients; no model API
calls (the HTTP layer is replaced by a function that fails the test, as in tests/test_topdown.py).

Without Lean: the ledger's proved set and dependencies, failure notes from events, refusal of a
ledger for another spec, the prompt text of failure notes, the portfolio's parsing of Lean's JSON
messages, and the optional `resumed_from` field of a Passport.
With Lean (the pinned image, one container at a time):
  * the portfolio closes an easy goal with zero model calls, banking it like a clean snippet;
  * a goal no tactic closes is left to the model;
  * the per-tactic heartbeat limit and the batch's wall allowance stop the attempts;
  * repair.py --resume-from re-checks every carried declaration with Lean, drops a broken one and
    its dependent, refuses a ledger for another spec, works the open goal first with the prior
    failure notes in its prompt, and the judge accepts in the session;
  * baseline.py --resume-from starts from the prior candidate with the most requirements proved
    and gives the model the failure summary.

Run: python3 tests/test_feedback.py [--quick] [name ...]   (--quick skips the Lean runs)
"""
import json, os, pathlib, re, shutil, sys, tempfile, time
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "tests")]
import budget, judge, ledger, meta_client, passport, portfolio, repair  # noqa: E402
import test_topdown as td  # noqa: E402
from test_topdown import BUCKET, SPARK, Script, say, tool_call, turns, no_http, events  # noqa: E402

SPEC = ledger.spec_sha256(BUCKET)

# A prior attempt on the bucket: the definition fixed, three helpers and six required theorems
# proved, `req_capacity` left open, and two declarations whose proofs Lean does not accept (as a
# tampered ledger would hold them; nothing in a ledger is trusted).
PRIOR = """import TokenBucket.Spec

namespace TokenBucket

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem td0_step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
  simp [step, h]

theorem td0_step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by
  simp [step, h]

theorem td0_adm_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : Admissible s r := by
  by_cases hv : Admissible s r
  · exact hv
  · rw [td0_step_of_not hv] at h; cases h

theorem td0_broken (n : Nat) : n + 1 = n + 2 := by omega

theorem td0_uses_broken (n : Nat) : n + 1 = n + 2 := td0_broken n
""" + ("theorem req_valid_succeeds" + td.SKELETON_BUCKET.split("theorem req_valid_succeeds", 1)[1]).replace(
    "theorem req_capacity : CapacityBound step := by\n  intro s r _\n  exact td0_capacity_step s r\n",
    "theorem req_capacity : CapacityBound step := sorry\n") + "\nend TokenBucket\n"

CLEAN = (PRIOR.replace("theorem td0_broken (n : Nat) : n + 1 = n + 2 := by omega\n\n", "")
         .replace("theorem td0_uses_broken (n : Nat) : n + 1 = n + 2 := td0_broken n\n", ""))

MARK = "theorem prior_attempt_marker"
PRIOR_EVENTS = [
    {"kind": "turn", "label": "pass1:req_capacity", "turn": 0, "model": SPARK, "text": "Try a direct proof.",
     "usage": {"prompt_tokens": 100000, "completion_tokens": 2000}},
    {"kind": "tool", "label": "pass1:req_capacity", "name": "try_snippet",
     "args": {"code": f"{MARK} : CapacityBound step := by\n  intro s r h; simp [step]"},
     "result": "snippet:2:2: error: unsolved goals\ns : State\n⊢ (step s r).2.tokens ≤ (step s r).2.capacity"},
    {"kind": "turn", "label": "pass1:req_capacity", "turn": 1, "model": SPARK, "text": "The bound needs the hypothesis.",
     "usage": {"prompt_tokens": 120000, "completion_tokens": 1500}},
]

CAPACITY_PROOF = """theorem td1_capacity_step (s : State) (r : Request) (hs : s.tokens ≤ s.capacity) :
    (step s r).2.tokens ≤ (step s r).2.capacity := by
  by_cases hv : Admissible s r
  · rw [td0_step_of_adm hv]
    show refilled s r.time - r.cost ≤ s.capacity
    have : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    omega
  · rw [td0_step_of_not hv]; exact hs

theorem req_capacity : CapacityBound step := by
  intro s r hs
  exact td1_capacity_step s r hs"""


def prior_ledger(src=PRIOR, spec=SPEC, status=None, evs=PRIOR_EVENTS, name="prior"):
    """A ledger written by ledger.build, as repair.finish writes one, in its own run directory."""
    d = pathlib.Path(tempfile.mkdtemp(prefix=f"pf-ledger-{name}-"))
    status = status or {t: ("SORRY" if t == "req_capacity" else "PROVED") for t in BUCKET.theorems}
    led = ledger.build(BUCKET, d, [src], evs, src, status, "A1", {"mode": "orchestrated", "model": SPARK}, spec=spec)
    (d / ledger.NAME).write_text(json.dumps(led))
    return d, led


# Without Lean

def test_ledger_records_proved_declarations_with_dependencies():
    _, led = prior_ledger()
    by = {r["name"]: r for r in led["proved"]}
    assert {"td0_step_of_adm", "td0_step_of_not", "td0_adm_of_ok", "req_valid_succeeds", "step"} <= set(by), sorted(by)
    assert "req_capacity" not in by                              # open
    assert {"step", "td0_step_of_not"} <= set(by["td0_adm_of_ok"]["deps"]), by["td0_adm_of_ok"]["deps"]
    assert {"td0_step_of_adm", "td0_adm_of_ok", "step"} <= set(by["req_allow_iff_sufficient"]["deps"])
    assert by["step"]["required_definition"] and by["req_valid_succeeds"]["required_theorem"]
    assert all(r["task"] == BUCKET.id and r["spec_sha256"] == SPEC for r in led["proved"])
    # A declaration that mentions an open one is not proved.
    src = PRIOR.replace("theorem td0_broken", "theorem td0_open (n : Nat) : n = n := by sorry\n\ntheorem td0_broken") \
        .replace("td0_broken n", "td0_open n ▸ td0_broken n")
    proved = ledger.proved_in(src, BUCKET.ns)
    assert "td0_open" not in proved and "td0_uses_broken" not in proved and "td0_broken" in proved
    goals = {g["name"]: g for g in led["open_goals"]}
    g = goals["req_capacity"]
    assert g["required"] and g["turns"] == 2 and g["dialogs"] == 1 and g["usd_list"] > 0
    assert MARK in g["tried"][0]["code"] and "unsolved goals" in g["tried"][0]["lean"] and "unsolved goals" in g["last_lean"]
    assert led["best_candidate"]["proved_required"] == sorted(t for t in BUCKET.theorems if t != "req_capacity")


def test_failure_notes_reach_the_prompt_text():
    _, led = prior_ledger()
    notes = ledger.notes_by_goal([led])
    text = ledger.prompt_notes(notes, "req_capacity")
    assert text.startswith("Previous attempts at this goal failed") and "Do not repeat" in text
    assert MARK in text and "2 turn(s)" in text and "unsolved goals" in text
    assert ledger.prompt_notes(notes, "req_effects") == ""
    whole = ledger.summary_text([led])
    assert "req_capacity" in whole and MARK in whole


def test_ledger_for_another_spec_or_task_is_refused():
    d_bad, _ = prior_ledger(spec="0" * 64, name="badspec")
    d_good, _ = prior_ledger()
    used, record = ledger.load_many([str(d_bad), str(d_good), "/nonexistent/run"], BUCKET)
    assert len(used) == 1 and used[0]["spec_sha256"] == SPEC
    assert record[0]["used"] is False and "spec hash" in record[0]["refused"]
    assert record[1]["used"] is True and record[2]["used"] is False
    _, why = ledger.load(d_good, td.COMPOUND)
    assert "task" in why
    # repair.py and baseline.py stop before any Lean or model work when no ledger is usable.
    for mod, argv in ((repair, ["repair.py"]), (__import__("baseline"), ["baseline.py"])):
        with patch.object(sys, "argv", argv + ["--task", BUCKET.id, "--resume-from", str(d_bad)]), \
                patch.object(repair, "chat", no_http), patch.object(meta_client, "_attempt", no_http):
            try:
                mod.main()
                raise AssertionError("a run started from a ledger for another spec")
            except SystemExit as e:
                assert e.code == 2
    for d in (d_bad, d_good):
        shutil.rmtree(d, ignore_errors=True)


def test_portfolio_parses_lean_messages():
    goals = [{"name": "g", "head": "theorem g (n : Nat) : n = n", "open_in": "", "rest": " (n : Nat) : n = n"}]
    s = td.session(BUCKET)
    try:
        text, att = portfolio.batch_text(s, goals, portfolio.PORTFOLIO[:2] + portfolio.PORTFOLIO[-2:], 1000)
        assert [a["key"] for a in att] == ["exact?", "try?", "grind", "omega"]   # searches first
        lines = text.split("\n")
        for a in att:
            assert lines[a["lines"][0] - 1].startswith("set_option maxHeartbeats 1000 in")
            assert lines[a["lines"][0]].startswith(f"theorem {a['copy']} (n : Nat)")
        ex, tr, gr, om = att
        msgs = [
            {"severity": "information", "pos": {"line": ex["lines"][0] + 2}, "data": "Try this:\n  [apply] exact rfl"},
            {"severity": "information", "pos": {"line": tr["lines"][0] + 2},
             "data": f"Try these:\n  [apply] exact {portfolio.PREFIX}0_0 n\n  [apply] grind"},
            {"severity": "error", "pos": {"line": gr["lines"][0] + 2},
             "data": "(deterministic) timeout at `whnf`, maximum number of heartbeats (1000) has been reached"},
            {"severity": "information", "pos": {"line": gr["lines"][0] + 1},
             "data": f"[Elab.async] [0.250000] ✅️ elaborating proof of TokenBucket.{gr['copy']}"},
        ] + [{"severity": "information", "pos": {"line": 999}, "data": f"'TokenBucket.{a['copy']}' depends on axioms: [propext]"}
             for a in att[:3]] + [
            {"severity": "information", "pos": {"line": 999}, "data": f"'TokenBucket.{om['copy']}' depends on axioms: [sorryAx]"}]
        res = portfolio.parse("\n".join(json.dumps(m) for m in msgs) + "\nnot json\n", att, "TokenBucket")
        assert res[ex["copy"]]["ok"] and res[ex["copy"]]["suggest"] == ["exact rfl"]
        assert res[tr["copy"]]["suggest"] == [f"exact {portfolio.PREFIX}0_0 n", "grind"]
        assert not res[gr["copy"]]["ok"] and res[gr["copy"]]["limit"] and res[gr["copy"]]["ms"] == 250
        assert not res[om["copy"]]["ok"]                                   # depends on sorry
        assert portfolio.bank_text(goals[0], "exact?", {"suggest": ["exact rfl"]}) == "theorem g (n : Nat) : n = n := by\n  exact rfl"
        assert portfolio.split_proof("theorem t (s : S) : f { s with a := 1 } = 2 := by simp")[0] == \
            "theorem t (s : S) : f { s with a := 1 } = 2"
        assert portfolio.forbidden("theorem t : 1 = 1 := by native_decide")
    finally:
        td.close(s)


def test_passport_names_prior_runs_only_when_resumed():
    j = {"accepted": False, "checks": {"tree": {"passed": True, "problems": []}, "impl_scan": {"passed": True, "problems": []}},
         "solution_tree_sha256": "0" * 64, "elapsed_ms": 1}
    b = {"status": "BUILD_FAILED"}
    cand = BUCKET.start
    with patch.object(judge, "image_id", lambda: "img"), patch.object(judge, "image_platform", lambda: "linux/arm64"):
        plain = passport.build(BUCKET, str(cand), j, b, provenance={"task": BUCKET.id})
        resumed = passport.build(BUCKET, str(cand), j, b, provenance={"task": BUCKET.id, "resumed_from": ["/runs/a", "/runs/b"]})
    assert "resumed_from" not in plain and resumed["resumed_from"] == ["/runs/a", "/runs/b"]
    assert resumed["passport_sha256"] == passport.content_hash(resumed)


# With Lean

def opts(**kw):
    a = repair.parser().parse_args([])
    a.variants = 0   # these tests cover the portfolio; tests/test_lean_feedback.py covers the variants
    for k, v in kw.items():
        setattr(a, k, v)
    return a


def with_goals(extra):
    """The fixed bucket start with extra declarations before the namespace end."""
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-feedback-start-"))
    (d / "Solution.lean").write_text(td.FIXED_BUCKET.replace("end TokenBucket", extra.strip() + "\n\nend TokenBucket"))
    return d / "Solution.lean"


EASY = "theorem easy_succ_le (n m : Nat) (h : n < m) : n + 1 ≤ m := by\n  sorry"
HARD = "theorem hard_capacity (s : State) (r : Request) :\n    (step s r).2.tokens ≤ (step s r).2.capacity := by\n  sorry"


def test_portfolio_closes_an_easy_goal_with_zero_model_calls():
    s = td.session(BUCKET, start=with_goals(EASY))
    script = Script([])   # any model call fails the test
    try:
        with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http):
            ok = repair.prove_target(s, opts(), "system", "spec", "easy_succ_le", 3, "d0")
        assert ok and script.calls == []
        assert repair.own_sorry_free(s, "easy_succ_le")
        text = repair.decl_text(s, "easy_succ_le")
        assert text.startswith("theorem easy_succ_le (n m : Nat) (h : n < m) : n + 1 ≤ m := by\n  grind"), text
        ev = [e for e in s.events if e["kind"] == "portfolio"]
        assert ev[0]["closed"] == {"easy_succ_le": "grind"} and ev[0]["results"]["easy_succ_le"]["grind"][0] == 1
        assert any(e["kind"] == "portfolio_bank" and e["banked"] for e in s.events)
        assert any(e["kind"] == "obligation" and e.get("by") == "portfolio" for e in s.events)
        assert "error:" not in s.compile()["output_tail"]
        print(f"   portfolio batch {ev[0]['ms']} ms, {ev[0]['attempts']} attempts")
    finally:
        td.close(s)


def test_portfolio_leaves_a_hard_goal_to_the_model():
    s = td.session(BUCKET, start=with_goals(HARD))
    script = Script([(r":d0:hard_capacity:turn\d+$", turns([say("It is false for an over-full level.")]))])
    try:
        with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http):
            ok = repair.prove_target(s, opts(), "system", "spec", "hard_capacity", 1, "d0")
        assert not ok and [p for _, p, _ in script.calls] == [f"repair:{BUCKET.id}:d0:hard_capacity:turn0"]
        ev = [e for e in s.events if e["kind"] == "portfolio"]
        assert ev and ev[0]["closed"] == {} and set(ev[0]["results"]["hard_capacity"]) >= {"grind", "omega", "exact?", "try?"}
        # The same goal in the same file is not tried again.
        with patch.object(repair, "chat", script):
            assert portfolio.close_goals(s, opts(), ["hard_capacity"]) == {}
        assert len([e for e in s.events if e["kind"] == "portfolio"]) == 1
    finally:
        td.close(s)


def test_portfolio_respects_the_time_limit():
    s = td.session(BUCKET, start=with_goals(EASY))
    try:
        # The heartbeat limit stops each tactic: with one thousand heartbeats grind cannot finish.
        g = portfolio.goal_of(s, "easy_succ_le")
        res, info = portfolio.run_batch(s, [g], entries=[e for e in portfolio.PORTFOLIO if e[0] in ("grind", "decide")],
                                        heartbeats=1)
        assert not info["stopped"] and not any(r["ok"] for r in res["easy_succ_le"].values()), res
        assert res["easy_succ_le"]["grind"]["limit"], res
        # The wall allowance stops the batch: nothing closes and nothing is banked.
        with patch.object(portfolio, "BASE_SECONDS", 0):
            t0 = time.monotonic()
            closed = portfolio.close_goals(s, opts(portfolio_seconds=0.05), ["easy_succ_le"])
            took = time.monotonic() - t0
        ev = [e for e in s.events if e["kind"] == "portfolio"][-1]
        assert closed == {} and ev["stopped"] and took < 30, (closed, ev, took)
        assert ev["retried"]   # stopped once with the searches, then once more without them
        assert not repair.own_sorry_free(s, "easy_succ_le")
        # The run's deadline stops it too: past the deadline nothing is tried.
        s.budget = budget.Budget(None, 0.001)
        time.sleep(0.01)
        s.portfolio_seen = set()
        assert portfolio.close_goals(s, opts(), ["easy_succ_le"]) == {}
    finally:
        judge.DEADLINE = None
        td.close(s)


def test_resume_carries_rechecked_declarations_and_works_open_goals_first():
    d_prior, led = prior_ledger()
    d_bad, _ = prior_ledger(spec="f" * 64, name="badspec")
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-feedback-resume-"))
    seen = {}

    def resume_dialog(purpose, messages):
        seen.setdefault("user", messages[1]["content"])
        return say("Use a capacity invariant this time.", tool_call("try_snippet", code=CAPACITY_PROOF))
    script = Script([(r":resume:req_capacity:turn\d+$", resume_dialog)])
    passing = '{"status": "PASS", "violations": {}, "examples": []}'
    td.run_main(["--task", BUCKET.id, "--loop", "orchestrated", "--model", SPARK, "--planner", "none",
                 "--start", str(td.fixed_start()), "--resume-from", f"{d_bad},{d_prior}", "--portfolio", "off",
                 "--goal-tool", "off", "--refute", "off", "--variants", "0",
                 "--obligation-turns", "2", "--budget-usd", "5", "--out", str(out)], script,
                [patch.object(repair.Session, "run_tests", lambda self: passing)])
    summary = json.loads((out / "summary.json").read_text())
    ev = events(out)
    rec = summary["resume"]
    assert summary["resumed_from"] == [str(d_prior.resolve())], summary["resumed_from"]
    assert rec["ledgers"][0]["used"] is False and "spec hash" in rec["ledgers"][0]["refused"]
    carried = set(rec["carried"])
    assert {"td0_step_of_adm", "td0_step_of_not", "td0_adm_of_ok", "req_valid_succeeds", "req_effects"} <= carried, carried
    dropped = {d["name"]: d["reason"] for d in rec["dropped"]}
    assert dropped["td0_broken"].startswith("Lean error") and "td0_broken" not in carried, dropped
    assert dropped["td0_uses_broken"] == "depends on a dropped declaration" and "td0_uses_broken" not in carried
    assert any(e["kind"] == "resume_carry" for e in ev)
    # The open goal is worked first, with the prior failure notes in its prompt.
    first_dialog = next(e for e in ev if e["kind"] == "turn")
    assert first_dialog["label"] == "resume:req_capacity", first_dialog
    assert "Previous attempts at this goal failed" in seen["user"] and MARK in seen["user"] and "Do not repeat" in seen["user"]
    assert summary["accepted_in_session"] is True and set(summary["final_status"].values()) == {"PROVED"}
    assert [p for _, p, _ in script.calls] == [f"repair:{BUCKET.id}:resume:req_capacity:turn0"]
    final = (out / "final.lean").read_text()
    assert "td0_broken" not in final and "td1_capacity_step" in final
    # The new run's ledger names where it came from and holds the carried work.
    new = json.loads((out / "ledger.json").read_text())
    assert new["resumed_from"] == [str(d_prior.resolve())] and new["open_goals"] == []
    assert {"td0_step_of_adm", "td1_capacity_step", "req_capacity"} <= {r["name"] for r in new["proved"]}
    print(f"   resume: {summary['versions']} versions, {summary['budget']['elapsed_s']} s")
    for d in (d_prior, d_bad, out):
        shutil.rmtree(d, ignore_errors=True)


def test_baseline_resume_starts_from_the_best_prior_candidate():
    import baseline
    # Three prior attempts: nothing proved; six proved but the file does not compile (a broken
    # lemma); six proved in a compiling file. The last one is the base.
    d_none, _ = prior_ledger(src=td.FIXED_BUCKET, status={t: "SORRY" for t in BUCKET.theorems}, evs=[], name="none")
    d_broken, _ = prior_ledger(name="broken")
    d_best, _ = prior_ledger(src=CLEAN, name="clean")
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-feedback-a0-"))
    seen = []

    def reply(purpose, messages):
        seen.append(messages[1]["content"])
        return say("```lean\n" + CLEAN.replace("theorem req_capacity : CapacityBound step := sorry\n", CAPACITY_PROOF + "\n")
                   + "```")
    script = Script([(r"^baseline:", reply)])
    with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http), \
            patch.object(repair.Session, "pause", lambda self, seconds: None), \
            patch.object(repair.Session, "check", lambda self: "NOT ACCEPTED (judge not run in this test)"), \
            patch.object(sys, "argv", ["baseline.py", "--task", BUCKET.id, "--model", SPARK, "--budget-usd", "5", "--max-turns", "1",
                                       "--resume-from", f"{d_none},{d_broken},{d_best}", "--out", str(out)]):
        baseline.main()
    summary = json.loads((out / "summary.json").read_text())
    base = summary["resume"]["base"]
    assert base["run_dir"] == str(d_best.resolve()) and base["proved"] == 6, base
    assert summary["resumed_from"] == [str(d.resolve()) for d in (d_none, d_broken, d_best)]
    assert len(seen) == 1 and summary["budget"]["by_model"][SPARK]["calls"] == 1
    first = seen[0]
    assert "from a previous attempt, 6 of 7 required theorems proved" in first
    assert "theorem td0_step_of_adm" in first and "Previous attempts on this task ended as follows" in first
    assert MARK in first
    ev = events(out)
    tried = [e for e in ev if e["kind"] == "resume_base"]
    assert len(tried) == 3 and "ERROR" in tried[1]["status"].values() and tried[0]["proved"] == 0, tried
    assert any(e["kind"] == "audit" and not e["errors"] and e["status"]["req_capacity"] == "PROVED" for e in ev)
    assert (out / "ledger.json").exists()
    for d in (d_none, d_broken, d_best, out):
        shutil.rmtree(d, ignore_errors=True)


LEAN = {"test_portfolio_closes_an_easy_goal_with_zero_model_calls",
        "test_portfolio_leaves_a_hard_goal_to_the_model",
        "test_portfolio_respects_the_time_limit",
        "test_resume_carries_rechecked_declarations_and_works_open_goals_first",
        "test_baseline_resume_starts_from_the_best_prior_candidate"}


if __name__ == "__main__":
    td.limit_lean_threads(int(os.environ.get("LEAN_NUM_THREADS", "4")))
    quick = "--quick" in sys.argv
    only = [x for x in sys.argv[1:] if not x.startswith("--")]
    lean = td.have_lean()
    for name, fn in list(globals().items()):
        if not name.startswith("test_") or (only and name not in only):
            continue
        if name in LEAN and (quick or not lean):
            print(f"skip {name}")
            continue
        fn()
        print(f"ok  {name}")
