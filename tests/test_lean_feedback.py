"""The goal tool (persistent Lean session), refutation of new helpers on concrete values and
parallel short variants, with scripted model clients; no model API calls (the HTTP layer is
replaced by a function that fails the test, as in tests/test_topdown.py).

Without Lean: LSP positions and message formatting, the probe text and the parsing of its output,
the task generator's JSON values, the variant framings, the budget under concurrent callers (the
dollar cap holds with requests in flight at once), the CLI defaults and that A0 has none of it.
With Lean (the pinned image; at most two containers at a time through the host's slots):
  * goal_at shows the hypotheses and goal at each `sorry`, and before and after a line; a snippet
    with an error or a `sorry` is answered by the persistent session with the state at its
    `sorry`, a clean one is still compiled and banked; a model dialog uses goal_at;
  * the sampler finds a kernel-checked counterexample for a false helper and none for true ones;
    prove_target spends no turn on a false helper; replace_declaration refuses a false helper; a
    planner decomposition with a false lemma is refused and the planner asked again; a skeleton
    with a false helper is rejected with the counterexample;
  * variants: after a failed first dialog two variants run at once, the first that Lean accepts is
    installed, the other is stopped and every request of both is charged to the run's budget; with
    `--variants 0` nothing runs.

Run: python3 tests/test_lean_feedback.py [--quick] [name ...]   (--quick skips the Lean runs)
"""
import json, os, pathlib, sys, threading, time
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "tests")]
import budget, leanserver, meta_client, refute, repair, variants  # noqa: E402
import test_topdown as td  # noqa: E402
from test_topdown import BUCKET, SPARK, WONDER, Script, say, tool_call, turns, no_http  # noqa: E402


def opts(**kw):
    a = repair.parser().parse_args([])
    a.portfolio = "off"
    for k, v in kw.items():
        setattr(a, k, v)
    return a


def with_goals(extra):
    d = pathlib.Path(__import__("tempfile").mkdtemp(prefix="pf-leanfb-start-"))
    (d / "Solution.lean").write_text(td.FIXED_BUCKET.replace("end TokenBucket", extra.strip() + "\n\nend TokenBucket"))
    return d / "Solution.lean"


def session(extra="", goal_tool=False, refute_on=False, cap=None):
    s = td.session(BUCKET, start=with_goals(extra) if extra else td.fixed_start(), cap=cap)
    s.goal_tool = goal_tool
    s.refute_samples = refute.SAMPLES if refute_on else 0
    return s


def close(s):
    leanserver.close(s)
    variants.join(s, timeout=60)
    td.close(s)


# Without Lean

def test_positions_and_messages():
    text = "theorem a : 1 ≤ 2 := by\n  sorry\n-- 𝔸x\n"
    assert leanserver.position(text, text.index("sorry")) == {"line": 1, "character": 2}
    off = text.index("x")
    assert leanserver.position(text, off) == {"line": 2, "character": 5}   # 𝔸 is two UTF-16 units
    assert leanserver.codepoint_col("-- 𝔸x", 5) == 4
    diags = [{"range": {"start": {"line": 3, "character": 2}}, "severity": 1, "message": "unsolved goals\n⊢ False"},
             {"range": {"start": {"line": 4, "character": 0}}, "severity": 2, "message": "declaration uses `sorry`"},
             {"range": {"start": {"line": 4, "character": 0}}, "severity": 2,
              "message": "unused variable `h`\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`"},
             {"range": {"start": {"line": 4, "character": 0}}, "severity": 2,
              "message": "`Nat.foo` has been deprecated: use `Nat.bar` instead"},
             {"range": {"start": {"line": 0, "character": 0}}, "severity": 1, "message": "error before the snippet"}]
    doc = "a\nb\nc\n  x\ny\n"
    msgs, errors, warnings, topdown_warnings = leanserver._messages(diags, doc, 3, "snippet")
    # As Session._scratch decides: outside the top-down loop the `sorry` and the linter warning count
    # (the linter's first line is shown) and the deprecation does not; in it, all but the linter's.
    assert (errors, warnings, topdown_warnings) == (1, 2, 2), (errors, warnings, topdown_warnings)
    assert msgs[0].startswith("snippet:1:2: error: unsolved goals") and msgs[1].startswith("snippet:2:0: warning")
    assert len(msgs) == 3 and not any("deprecated" in m for m in msgs)   # left out whole
    assert leanserver._render([]) .startswith("no goals") and "goal 2 of 2" in leanserver._render(["a", "b"])


def test_probe_text_and_parse():
    text = refute.probe_text(["TokenBucket.td0_x", "TokenBucket.foo'"], samples=7, heartbeats=99)
    assert "[`TokenBucket.td0_x, `TokenBucket.foo'] do" in text and "7).run'" in text and "99 * 1000" in text
    assert "NAMES" not in text and "SAMPLES" not in text and "HEARTBEATS" not in text
    out = ("noise\nPFREFUTE N.a\tfalse\t3\t4\tn := 1, m := 5\nPFREFUTE N.b\tsurvived\t64\t2\n"
           "PFREFUTE N.c\tunsupported\tnot decidable\nPFREFUTE N.d\tunconfirmed\t64\t0\tx := 2\n")
    r = refute.parse(out)
    assert r["N.a"] == {"status": "false", "instance": 3, "tried": 4, "counterexample": "n := 1, m := 5"}
    assert r["N.b"]["status"] == "survived" and r["N.b"]["undecided"] == 2
    assert r["N.c"]["reason"] == "not decidable" and r["N.d"]["counterexample"] == "x := 2"
    assert "FALSE" in refute.feedback({"a": "n := 1"}, {"a": "theorem a : False"})


def test_generator_values_come_from_the_oracle():
    vals = refute.gen_values(BUCKET)
    states = [v for v in vals if isinstance(v, dict) and set(v) == {"capacity", "rate", "tokens", "last"}]
    reqs = [v for v in vals if isinstance(v, dict) and set(v) == {"time", "cost"}]
    assert len(states) > 10 and len(reqs) > 10 and states[0] == BUCKET.oracle.FLAGSHIP["state"]
    assert refute.gen_values(BUCKET) == vals   # fixed seed


def test_variant_framings():
    class S:
        library = False
    assert [f[0] for f in variants.framings(S, 3)] == ["retry", "decompose", "cases"]
    S.library = True
    assert [f[0] for f in variants.framings(S, 3)] == ["retry", "decompose", "library"]
    assert variants.settings(opts(variants=0))[0] == 0 and variants.settings(opts())[0] == variants.DEFAULT_K


def test_budget_cap_holds_with_concurrent_requests():
    """Four threads call the model at once; every request is charged its worst case before it is
    sent, so the dollars charged never exceed the cap, and the refused ones raise BudgetExceeded."""
    s = td.session(BUCKET, cap=0.2)
    peak, seen = [0.0], []
    gate = threading.Barrier(4)

    def slow_chat(model, messages, purpose, **kw):
        peak[0] = max(peak[0], s.budget.usd_list)
        time.sleep(0.3)
        return {"choices": [{"message": {"content": "ok"}}], "usage": {"prompt_tokens": 1000, "completion_tokens": 100}}

    def worker():
        gate.wait()
        for _ in range(6):
            try:
                s.call(SPARK, [{"role": "user", "content": "x" * 20000}], "test", max_tokens=8000)
                seen.append("ok")
            except budget.BudgetExceeded:
                seen.append("stop")
                return
    try:
        with patch.object(repair, "chat", slow_chat):
            th = [threading.Thread(target=worker) for _ in range(4)]
            for t in th:
                t.start()
            for t in th:
                t.join()
        assert peak[0] <= 0.2 + 1e-9 and s.budget.usd_list <= 0.2 + 1e-9, (peak, s.budget.usd_list)
        assert "stop" in seen and s.budget.reserved_open == 0
    finally:
        td.close(s)


def test_defaults_and_a0():
    a = repair.parser().parse_args([])
    assert (a.goal_tool, a.refute, a.variants, a.variant_turns) == ("on", "on", 0, 2)   # variants off (6662568)
    s = td.session(BUCKET)
    try:
        repair.configure(s, a)
        assert s.goal_tool and s.refute_samples == refute.SAMPLES and s.variants_k == 0
        f = repair.features_summary(s, a)
        assert set(f) == {"portfolio", "goal_tool", "refute", "variants"} and f["variants"]["k"] == 0
        assert f["portfolio"]["batches"] == 0 and f["goal_tool"]["enabled"] and f["refute"]["enabled"]
        repair.configure(s, repair.parser().parse_args(["--goal-tool", "off", "--refute", "off", "--variants", "0"]))
        assert not s.goal_tool and not s.refute_samples and s.variants_k == 0
        repair.configure(s, repair.parser().parse_args(["--variants", "2"]))
        assert s.variants_k == 2
    finally:
        td.close(s)
    # A0: the baseline session class has every feature off and its options have none of them.
    import baseline
    assert not baseline.FileSession.goal_tool and not baseline.FileSession.refute_samples
    assert not baseline.FileSession.variants_k


# With Lean

GOAL = """theorem gt_step (n m : Nat) (h : n < m) : n + 1 ≤ m := by
  have h2 : n + 1 ≤ m := by
    sorry
  exact h2"""


def test_goal_at_and_fast_snippet_check():
    s = session(GOAL, goal_tool=True)
    try:
        t0 = time.monotonic()
        out = leanserver.goal_at(s, "gt_step")
        first = time.monotonic() - t0
        assert "h : n < m" in out and "⊢ n + 1 ≤ m" in out and "line 3" in out, out
        t0 = time.monotonic()
        out = leanserver.goal_at(s, "gt_step", line=4)
        assert "before this line" in out and "h2 : n + 1 ≤ m" in out and "no goals" in out, out
        again = time.monotonic() - t0
        # A snippet with an error: answered by the session, with the state at its sorry.
        t0 = time.monotonic()
        res = s.try_snippet("theorem gt_aux (a b : Nat) (h : a < b) : a + 2 ≤ b + 1 := by\n"
                            "  have : a + 1 ≤ b := by sorry\n  exact Nat.le_refl _")
        fast = time.monotonic() - t0
        assert "snippet:3" in res and "error" in res and "Proof state at each `sorry`" in res and "⊢ a + 1 ≤ b" in res, res
        assert any(e["kind"] == "fast_check" and not e["ok"] for e in s.events)
        assert not (s.ws / "Scratch.lean").exists()                    # nothing was compiled
        # A clean snippet is compiled and banked as before.
        t0 = time.monotonic()
        res = s.try_snippet("theorem gt_aux2 (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega")
        slow = time.monotonic() - t0
        assert "banked" in res and "gt_aux2" in res, res
        assert repair.own_sorry_free(s, "gt_aux2")
        st = leanserver.summary(s)
        assert st["starts"] == 1 and st["fast_rejected"] == 1 and st["fast_clean"] == 1 and st["goal_at_calls"] == 2, st
        print(f"   goal_at first {first:.1f} s (server start and full elaboration), then {again:.2f} s; "
              f"failing snippet {fast:.2f} s; clean snippet (server, compile, bank) {slow:.1f} s")
    finally:
        close(s)


def test_dialog_uses_goal_at():
    s = session(GOAL, goal_tool=True)
    seen = []

    def step(purpose, messages):
        k = int(purpose.rsplit("turn", 1)[1])
        if k == 0:
            return say("Look at the goal first.", tool_call("goal_at", name="gt_step"))
        seen.append(messages[-1]["content"])
        return say("", tool_call("try_snippet", code="theorem gt_step (n m : Nat) (h : n < m) : n + 1 ≤ m := by omega"))
    script = Script([(r":d0:gt_step:turn\d+$", step)])
    s.targets.add("gt_step")   # a helper the bank may replace while it is sorry, as planner and skeleton helpers are
    try:
        with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http):
            ok = repair.prove_target(s, opts(variants=0), "system", "spec", "gt_step", 3, "d0")
        assert ok and len(script.calls) == 2 and "goal_at" in script.calls[0][2]
        assert "⊢ n + 1 ≤ m" in seen[0], seen
    finally:
        close(s)


FALSE_HELPER = "theorem td9_sub_add (n m : Nat) : n - m + m = n := by\n  sorry"
TRUE_HELPER = "theorem td9_add_sub (n m : Nat) : n + m - m = n := by\n  sorry"
CAP = ("theorem td9_cap (s : State) (r : Request) :\n"
       "    (step s r).2.tokens ≤ (step s r).2.capacity := by\n  sorry")
CAP_OK = ("theorem td9_cap_ok (s : State) (r : Request) (hs : s.tokens ≤ s.capacity) :\n"
          "    (step s r).2.tokens ≤ (step s r).2.capacity := by\n  sorry")
# `s'` is fixed by the step equation (a refill can raise the level), and a predicate without a
# Decidable instance is unfolded.
STEP_FALSE = ("theorem td9_ok_tokens (s s' : State) (r : Request) (h : step s r = (.ok, s')) :\n"
              "    s'.tokens ≤ s.tokens := by\n  sorry")
STEP_TRUE = ("theorem td9_ok_last (s s' : State) (r : Request) (h : step s r = (.ok, s')) :\n"
             "    s'.last = r.time := by\n  sorry")
WITHIN = ("def td9Within (s : State) : Prop := s.tokens ≤ s.capacity\n\n"
          "theorem td9_within (s : State) (r : Request) (h : td9Within s) : td9Within (step s r).2 := by\n  sorry\n\n"
          "theorem td9_within_bad (s : State) (r : Request) : td9Within (step s r).2 := by\n  sorry")


def test_sampler_refutes_false_helpers_only():
    s = session("\n\n".join([FALSE_HELPER, TRUE_HELPER, CAP, CAP_OK, STEP_FALSE, STEP_TRUE, WITHIN]), refute_on=True)
    names = ["td9_sub_add", "td9_add_sub", "td9_cap", "td9_cap_ok", "td9_ok_tokens", "td9_ok_last", "td9_within",
             "td9_within_bad"]
    try:
        t0 = time.monotonic()
        false = refute.check(s, names, "test")
        took = time.monotonic() - t0
        assert set(false) == {"td9_sub_add", "td9_cap", "td9_ok_tokens", "td9_within_bad"}, false
        assert "n := " in false["td9_sub_add"] and "tokens :=" in false["td9_cap"], false
        assert "s' := " in false["td9_ok_tokens"], false
        ev = [e for e in s.events if e["kind"] == "refute_sample"][-1]
        for n in ("td9_add_sub", "td9_cap_ok", "td9_ok_last", "td9_within"):
            assert ev["results"][n]["status"] == "survived", ev["results"]
        print(f"   sampler: {len(names)} statements in {took:.1f} s; {false}")
        # Cached: the same statements in the same context are not sampled again.
        n = len([e for e in s.events if e["kind"] == "refute_sample"])
        assert refute.check(s, ["td9_sub_add", "td9_add_sub"], "again") == {"td9_sub_add": false["td9_sub_add"]}
        assert len([e for e in s.events if e["kind"] == "refute_sample"]) == n
    finally:
        close(s)


def test_false_helper_gets_no_turns_and_replace_declaration_refuses_it():
    s = session(FALSE_HELPER, refute_on=True)
    script = Script([])   # any model call fails the test
    try:
        with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http):
            ok = repair.prove_target(s, opts(), "system", "spec", "td9_sub_add", 3, "d1")
        assert not ok and script.calls == [] and "td9_sub_add" in s.refuted
        assert s.refuted["td9_sub_add"]["counterexample"]
        assert any(e["kind"] == "obligation" and e.get("by") == "refuted" for e in s.events)
        fb = repair.restructure_feedback(s, {"refuted": ["td9_sub_add"]})
        assert "FALSE" in fb and "Counterexample" in fb
        before = s._source()
        res = s.replace_declaration("td9_mul", "theorem td9_mul (n : Nat) : n * 2 = n + 1 := by\n  sorry")
        assert res.startswith("REVERTED: `td9_mul` is false") and "n := " in res, res
        assert "td9_mul" not in s._source() and s._source().strip() == s._normalize(before).strip()
        res = s.replace_declaration("td9_ok", "theorem td9_ok (n : Nat) : n * 2 = n + n := by\n  sorry")
        assert res.startswith("inserted declaration td9_ok"), res
    finally:
        close(s)


def test_planner_lemma_refused_before_any_turn():
    s = session("theorem td9_target (n m : Nat) (h : m ≤ n) : n - m + m = n := by\n  sorry", refute_on=True)
    replies = [
        td.lean_block("Cancel the subtraction.", "theorem plan0_cancel (n m : Nat) : n - m + m = n := by sorry"),
        td.lean_block("Cancel under the hypothesis.",
                      "theorem plan0_cancel (n m : Nat) (h : m ≤ n) : n - m + m = n := by sorry"),
    ]
    script = Script([(r"^plan:", lambda p, m: say(replies[min(len(script.calls), len(replies)) - 1]))])
    try:
        with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http):
            lemmas, _ = repair.plan(s, opts(planner=WONDER), "spec", "td9_target", 0)
        # A statement whose compile fails is reverted and asked again (one more planner call); the
        # intermittent lake build read of a partially written file can cause that here.
        reverts = sum(1 for e in s.events if e["kind"] == "write" and e["why"].startswith("revert plan"))
        assert lemmas == ["plan0_cancel"] and len(script.calls) == 2 + reverts, \
            [(e["kind"], e.get("why") or e.get("results")) for e in s.events]
        ev = [e for e in s.events if e["kind"] == "plan_refuted"]
        assert ev and "plan0_cancel" in ev[0]["false"]
        assert "(h : m ≤ n)" in repair.decl_text(s, "plan0_cancel")
    finally:
        close(s)


def test_skeleton_with_a_false_helper_is_rejected():
    s = session(refute_on=True)
    try:
        ctx = {"round": 0, "status": s.check_status(), "pending": list(BUCKET.theorems), "tries": 0,
               "accepted": None, "source": "planner"}
        ok, msg = repair.accept_skeleton(s, td.SKELETON_BUCKET, ctx)
        assert not ok and "`td0_capacity_step` is false" in msg and "counterexample" in msg, msg
        assert "td0_capacity_step" not in s._source()
    finally:
        close(s)


VGOAL = "theorem vgoal (n m : Nat) (h : n < m) : n + 1 ≤ m := by\n  sorry"


def test_variants_first_accepted_wins_and_every_request_is_charged():
    s = session(VGOAL, cap=5)
    release = threading.Event()

    def first(purpose, messages):
        return say("I could not find it.")

    def retry(purpose, messages):
        return say("", tool_call("try_snippet", code="theorem vgoal (n m : Nat) (h : n < m) : n + 1 ≤ m := by omega"))

    def decompose(purpose, messages):
        release.wait(30)     # still in flight when the other variant wins
        time.sleep(1)
        return say("Helper first.", tool_call("try_snippet", code="theorem vg_h (n : Nat) : n ≤ n + 1 := by omega"))
    script = Script([(r":d0:vgoal:turn\d+$", first), (r":v0-retry:vgoal:turn\d+$", retry),
                     (r":v1-decompose:vgoal:turn\d+$", decompose)])
    s.targets.add("vgoal")
    try:
        with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http):
            t0 = time.monotonic()
            ok = repair.prove_target(s, opts(variants=2, variant_turns=3), "system", "spec", "vgoal", 1, "d0")
            took = time.monotonic() - t0
            release.set()
            variants.join(s, timeout=120)
        assert ok and repair.own_sorry_free(s, "vgoal"), s._source()
        purposes = [p for _, p, _ in script.calls]
        assert purposes[0].endswith(":d0:vgoal:turn0")
        assert any(":v0-retry:" in p for p in purposes) and any(":v1-decompose:" in p for p in purposes)
        res = [e for e in s.events if e["kind"] == "variants_result"][0]
        assert res["ok"] and res["winner"] == "retry"
        ends = {e["framing"]: e for e in s.events if e["kind"] == "variant_end"}
        assert ends["retry"]["won"] and not ends["decompose"]["ok"]
        assert ends["decompose"]["turns"] == 1               # its one request was answered and charged
        # Every model request (the first dialog and both variants) is charged to the one budget.
        calls = s.budget.by_model[SPARK]["calls"]
        assert calls == len(script.calls) == 3, (calls, purposes)
        assert abs(s.budget.usd_list - 3 * budget.list_cost(SPARK, td.USAGE)) < 1e-9
        assert s.budget.reserved_open == 0
        assert "vg_h" not in s._source()                     # the loser's work is not installed
        assert any(e["kind"] == "obligation" and e.get("by") == "variant" for e in s.events)
        st = variants.summary(s, opts(variants=2, variant_turns=3))
        assert st["goals"] == 1 and st["won"] == 1 and st["turns"] == 2, st
        print(f"   variants: winner installed after {took:.1f} s; {calls} requests charged")
    finally:
        close(s)


def test_no_variants_when_off():
    s = session(VGOAL)
    script = Script([(r":d0:vgoal:turn\d+$", turns([say("No.")]))])
    try:
        with patch.object(repair, "chat", script), patch.object(meta_client, "_attempt", no_http):
            ok = repair.prove_target(s, opts(variants=0), "system", "spec", "vgoal", 1, "d0")
        assert not ok and len(script.calls) == 1
        assert not any(e["kind"].startswith("variant") for e in s.events)
    finally:
        close(s)


LEAN = {"test_goal_at_and_fast_snippet_check", "test_dialog_uses_goal_at", "test_sampler_refutes_false_helpers_only",
        "test_false_helper_gets_no_turns_and_replace_declaration_refuses_it",
        "test_planner_lemma_refused_before_any_turn", "test_skeleton_with_a_false_helper_is_rejected",
        "test_variants_first_accepted_wins_and_every_request_is_charged", "test_no_variants_when_off"}


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
