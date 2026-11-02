"""Where the repair agent (agents/repair.py, arm A1) spends its dollars: the changes made after
results/e1-test-open-2 (results/e1-open-diagnosis-2/README.md). No model calls.

Fixtures in tests/fixtures/repair_e1open2/, extracted from the recorded A1 runs of e1-test-open-2:
- portfolio_grants_b4.json: the candidate of permissions-grants-b4 at version 3, the portfolio batch
  that closed req_no_self_grant and req_others_unchanged on it, and the four texts the run tried to
  bank, none of which compiled (the continuation lines of a multi-line tactic were indented twice).
- spend_trajectories.json: for eleven A1 runs, every dialog turn of phases 1 and 2 in order, with
  the list dollars spent before it, the required theorems open before it and its own list dollars.
- phase0_definitions.json: for permissions-acl-b2, -acl-b3, -grants-b3 and -grants-b4, A1's file
  after phase 0 and A0's final file.

Without Lean: the banked proof is the proof the batch checked, for every portfolio entry; the
whole-file reserve on the recorded trajectories (it stops the per-requirement phases of
permissions-acl-b3 and permissions-grants-b4, which spent $2.69 and $2.64 there, and of no run that
verified); dialog() makes no model call once the reserve is reached and the whole-file phase is
never stopped by it; A0's first request is byte for byte the one of the code that ran
e1-test-open-2; the phase-0 request carries the note on the definition's form (both modes) and the
per-requirement requests do not; the whole-file phase's first request ends with the note that the
definition may be rewritten.
With Lean (the pinned image): the recorded closure banks on the recorded candidate and `#print
axioms` shows the requirement proved; the recorded text does not compile. On permissions-acl-b3 the
portfolio proves both validity requirements on A0's definitions and neither on A1's phase-0 file.

Run: python3 tests/test_repair_spend.py [--quick] [name ...]   (--quick skips the Lean runs)
"""
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess, sys, tempfile
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "tests")]
import budget, judge, portfolio, repair, task as taskmod  # noqa: E402

FIX = ROOT / "tests/fixtures/repair_e1open2"
PORT = json.loads((FIX / "portfolio_grants_b4.json").read_text())
GRANTS = taskmod.load(PORT["task"])
TRAJ = json.loads((FIX / "spend_trajectories.json").read_text())["runs"]
DEFS = json.loads((FIX / "phase0_definitions.json").read_text())["runs"]


def bare_session(task):
    s = repair.Session.__new__(repair.Session)
    s.task, s.ns, s.theorems, s.end = task, task.ns, task.theorems, f"end {task.ns}"
    s.boundary = (r"(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |instance |abbrev "
                  rf"|structure |inductive |open |{re.escape(s.end)})")
    s.library, s.lib_index = False, None
    return s


def session(task, source):
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-spend-"))
    (out / "start.lean").write_text(source)
    return repair.Session(task, "m", out / "start.lean", out, budget.Budget(None, None))


def close(s):
    shutil.rmtree(s.ws, ignore_errors=True)
    shutil.rmtree(s.out, ignore_errors=True)


# Without Lean

def test_banked_proof_is_the_proof_the_batch_checked():
    s = bare_session(GRANTS)
    s._source = lambda: PORT["source"]
    goal = portfolio.goal_of(s, "req_no_self_grant", PORT["source"])
    assert goal and goal["unfold"] == ["NoSelfGrant", "step"], goal
    text, attempts = portfolio.batch_text(s, [goal], portfolio.PORTFOLIO, 1000, PORT["source"])
    lines = text.split("\n")
    for a in attempts:
        key = a["key"]
        if key in portfolio.SEARCH:
            continue
        first, last = a["lines"]                                  # 1-based: set_option ... blank line
        assert lines[first].startswith(f"theorem {a['copy']}") and lines[first].endswith(":= by")
        checked = "\n".join(lines[first + 1:last - 1])           # the proof lines after `:= by`
        banked = portfolio.bank_text(goal, key, {"suggest": []})
        assert banked.split(" := by\n", 1)[1] == checked, (key, banked, checked)
        body = banked.split(" := by\n", 1)[1].split("\n")
        assert all(l.startswith("  ") and not l.startswith("   ") for l in body if l.strip()), (key, body)


def test_recorded_texts_were_indented_twice():
    """The four texts the recorded run tried to bank: each multi-line proof had its continuation
    lines at four spaces, which Lean parses as part of the first tactic's line, then as a new
    command; the current text of the same entries keeps every line at two."""
    s = bare_session(GRANTS)
    for r in PORT["recorded"]:
        assert not r["banked"]
        assert re.search(r"\n    \S", r["text"]), r["text"]
        goal = portfolio.goal_of(s, r["name"], PORT["source"])
        new = portfolio.bank_text(goal, r["tactic"], {"suggest": []})
        assert new != r["text"] and not re.search(r"\n    \S", new), new
        assert new.replace("\n  ", "\n") == r["text"].replace("\n    ", "\n").replace("\n  ", "\n"), (new, r["text"])
    assert set(PORT["batch_closed"]["req_no_self_grant"]) >= {"unfold_grind", "grind_defs"}


def first_stop(run, frac):
    """(dollars spent, requirements open) at the first recorded turn the reserve would not have made."""
    for usd, n_open, _ in run["turns"]:
        if usd >= repair.reserve_limit(run["cap"], frac, n_open, run["n"]):
            return usd, n_open
    return None


def test_reserve_on_the_recorded_spend():
    assert repair.WHOLE_FILE_RESERVE == 0.5
    assert repair.reserve_limit(3.0, 0.5, 9, 9) == 1.5 and repair.reserve_limit(3.0, 0.5, 0, 9) == 3.0
    stops = {tid: first_stop(run, repair.WHOLE_FILE_RESERVE) for tid, run in TRAJ.items()}
    # The two runs that never got a working whole-file phase: stopped with most of the budget left.
    usd, n_open = stops["permissions-acl-b3"]
    assert 1.8 < usd < 1.9 and n_open == 7, stops["permissions-acl-b3"]   # $2.69 spent there, no phase 3
    usd, n_open = stops["permissions-grants-b4"]
    assert 2.0 < usd < 2.1 and n_open == 5, stops["permissions-grants-b4"]  # $2.64 spent there
    # Every recorded run that verified keeps its per-requirement phases whole.
    for tid, run in TRAJ.items():
        if run["completed"]:
            assert stops[tid] is None, (tid, stops[tid])
    # Off means the recorded behavior.
    assert all(first_stop(run, 0.0) is None or first_stop(run, 0.0)[0] >= run["cap"] for run in TRAJ.values())


def reserve_session(cap, spent, src):
    s = bare_session(GRANTS)
    s.budget = budget.Budget(cap, None)
    s.budget.usd_list = spent
    s._source = lambda: src
    s.events = []
    s.log = lambda **kw: s.events.append(kw)
    return s


def test_dialog_makes_no_call_once_the_reserve_is_reached():
    src = PORT["source"]                                  # all 8 requirements open (sorry)
    calls = []

    def call(*a, **k):
        calls.append(a)
        return {"choices": [{"message": {"content": "", "tool_calls": []}}]}, {}
    for spent, reserve, expect_calls in ((1.49, 0.5, 1), (1.50, 0.5, 0), (2.99, 0.0, 1)):
        calls.clear()
        s = reserve_session(3.0, spent, src)
        s.reserve = reserve
        s.call = call
        ok, msgs = repair.dialog(s, "m", "medium", "sys", "user", {"try_snippet"}, 1, lambda: False, "pass1:x")
        assert len(calls) == expect_calls and not ok, (spent, reserve, calls)
        if not expect_calls:
            assert s.events[0]["phase"] == "reserve" and s.events[0]["open"] == 8 and s.events[0]["limit"] == 1.5
    # With four of eight proved the limit moves to $2.25.
    proved = src
    for name in ("req_valid_succeeds", "req_invalid_noop", "req_authorization", "req_no_self_grant"):
        proved = re.sub(rf"(theorem {name}\s*:[^\n]*?):= sorry", r"\1:= by trivial", proved)
    s = reserve_session(3.0, 2.2, proved)
    s.reserve = 0.5
    assert len(repair.open_required(s)) == 4 and not repair.reserve_reached(s)
    s.budget.usd_list = 2.25
    assert repair.reserve_reached(s) and s.reserve_hit["open"] == 4


def test_whole_file_phase_is_never_stopped_by_the_reserve():
    """orchestrate() sets the reserve for the per-requirement phases only: phase 3 runs with it
    off, whatever was spent."""
    seen = []
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-spend-"))
    (out / "start.lean").write_text(PORT["source"])
    s = repair.Session(GRANTS, "m", out / "start.lean", out, budget.Budget(3.0, None))
    try:
        s.run_tests = lambda: '{"status": "PASS"}'

        def middle(s, a, system, spec):
            assert s.reserve == 0.5
            s.budget.usd_list = 1.6
            seen.append(("middle", repair.reserve_reached(s)))

        def fake_run(s, a, state="", library_text="", resume_text="", note=""):
            seen.append(("whole-file", s.reserve, repair.reserve_reached(s)))
        a = argparse.Namespace(model="m", effort="medium", phase0_turns=1, whole_file_reserve=0.5)
        with patch("baseline.run", fake_run):
            repair.orchestrate(s, a, middle=middle)
        assert seen == [("middle", True), ("whole-file", 0.0, False)], seen
        assert repair.parser().parse_args([]).whole_file_reserve == 0.5
        assert repair.parser().parse_args(["--whole-file-reserve", "0"]).whole_file_reserve == 0.0
    finally:
        close(s)


# A0's first request (messages, model, purpose, options) on three tasks, computed with the code that
# ran e1-test-open-2 (commit 57d1ed5; agents/baseline.py and the parts of agents/repair.py it uses
# are unchanged since).
A0_FIRST_REQUEST = {
    "permissions-grants-b4": "a4f3073b759e2f10d49cd6fbc17fe3b294ca5dbcd75613406a45904dbc4e2609",
    "permissions-acl-b3": "519d81552e2ae9384a88555fc955ca68959ce99cc94a045d51ebab541c9b874c",
    "ledgers-reversal-b1": "44b158f724ca00e21b69f06971bca53c6bb93dd1906b2a301cd902b43e9ef4fe",
}


def test_a0_first_request_is_unchanged():
    import baseline

    class Stop(Exception):
        pass
    for tid, digest in A0_FIRST_REQUEST.items():
        t = taskmod.load(tid)
        out = pathlib.Path(tempfile.mkdtemp(prefix="pf-a0-"))
        s = baseline.FileSession(t, "meta-models/muse-spark-open-1026", t.start, out, budget.Budget(3.0, 3600))
        seen = {}

        def call(model, messages, purpose, **extra):
            seen["req"] = {"model": model, "messages": messages, "purpose": purpose, "extra": extra}
            raise Stop()
        s.call = call
        try:
            baseline.run(s, argparse.Namespace(model="meta-models/muse-spark-open-1026", effort="medium", max_turns=200))
        except Stop:
            pass
        finally:
            close(s)
        assert hashlib.sha256(json.dumps(seen["req"], sort_keys=True).encode()).hexdigest() == digest, tid


def test_phase0_request_asks_for_the_specification_terms():
    seen = []

    def fake_dialog(s, model, effort, system, user, tools, turns, done, label, stop=None):
        seen.append((label, user, system))
        return True, []
    for mode in ("repair", "implement"):
        seen.clear()
        out = pathlib.Path(tempfile.mkdtemp(prefix="pf-spend-"))
        (out / "start.lean").write_text(PORT["source"])
        s = repair.Session(GRANTS, "m", out / "start.lean", out, budget.Budget(None, None), mode=mode)
        try:
            s.run_tests = lambda: '{"status": "REFUTED"}'
            a = argparse.Namespace(model="m", effort="medium", phase0_turns=1, whole_file_reserve=0.0)
            with patch.object(repair, "dialog", fake_dialog), patch("baseline.run", lambda *x, **k: None):
                repair.orchestrate(s, a, middle=lambda *x: None)
        finally:
            close(s)
        (label, user, system), = seen
        assert label == "implement" and user.endswith(repair.SPEC_SHAPED), user[-300:]
        assert "Phase 1 of 2: " + ("implement" if mode == "implement" else "fix") in user
        assert repair.SPEC_SHAPED not in system
    for word in ("Grants", "Acl", "permissions", "ValidCommand", "ValidQuery"):
        assert word not in repair.SPEC_SHAPED, word


def test_whole_file_phase_says_the_definition_may_change():
    """Phase 3's first request ends with the note; the rest of it is A0's protocol on the current
    file. A0 itself passes no note (test_a0_first_request_is_unchanged)."""
    import baseline

    class Stop(Exception):
        pass
    seen = {}

    def call(model, messages, purpose, **extra):
        seen["messages"] = messages
        raise Stop()
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-spend-"))
    (out / "start.lean").write_text(PORT["source"])
    s = repair.Session(GRANTS, "m", out / "start.lean", out, budget.Budget(None, None))
    try:
        s.run_tests = lambda: '{"status": "PASS"}'
        s.call = call
        a = argparse.Namespace(model="m", effort="medium", phase0_turns=1, whole_file_reserve=0.0)
        try:
            repair.orchestrate(s, a, middle=lambda *x: None)
        except Stop:
            pass
    finally:
        close(s)
    system, user = seen["messages"][0]["content"], seen["messages"][1]["content"]
    note = repair.WHOLE_FILE_NOTE.format(defs="`Grants.step`")
    assert user.endswith("\n\n" + note) and "(current, partly repaired)" in user, user[-400:]
    assert system.startswith(repair.task_brief(GRANTS)) and note not in system
    assert "may rewrite it together with the proofs" in note and repair.SPEC_TERMS in note


def test_per_requirement_requests_carry_no_phase0_note():
    seen = []

    def fake_dialog(s, model, effort, system, user, tools, turns, done, label, stop=None):
        seen.append(user)
        return False, []
    out = pathlib.Path(tempfile.mkdtemp(prefix="pf-spend-"))
    (out / "start.lean").write_text(PORT["source"])
    s = repair.Session(GRANTS, "m", out / "start.lean", out, budget.Budget(None, None))
    try:
        a = argparse.Namespace(model="m", effort="medium", portfolio="off", variants=0, obligation_turns=1)
        with patch.object(repair, "dialog", fake_dialog), patch.object(s, "check_status", lambda names=None: {}):
            repair.prove_target(s, a, "sys", repair.spec_text(s), "req_effects", 1, "pass1")
    finally:
        close(s)
    assert seen and repair.SPEC_SHAPED not in seen[0] and "Do not change `step`" in seen[0]


# With Lean

def test_recorded_closure_banks_on_the_recorded_candidate():
    s = session(GRANTS, PORT["source"])
    try:
        rec = PORT["recorded"][0]
        assert rec["name"] == "req_no_self_grant" and rec["tactic"] == "unfold_grind"
        before = s._source()
        assert s.bank(rec["text"]) == [] and s._source().rstrip("\n") == repair.Session._normalize(s, before).rstrip("\n")
        goal = portfolio.goal_of(s, rec["name"])
        assert s.bank(portfolio.bank_text(goal, rec["tactic"], {"suggest": []})) == [rec["name"]]
        assert s.check_status([rec["name"]]) == {rec["name"]: "PROVED"}
    finally:
        close(s)


def test_validity_requirements_close_on_the_specification_terms():
    """permissions-acl-b3: A1's phase-0 definition guards on `s.users.contains r.user && r.user != 0`;
    A0's accepted one on the specification's `ValidQuery`. The portfolio (nothing banked) proves the
    two validity requirements on A0's definitions and neither on A1's file."""
    import ledger
    t = taskmod.load("permissions-acl-b3")
    rec = DEFS[t.id]
    ch = (t.root / t.spec_dir / "Challenge.lean").read_text()
    a0 = rec["a0_final"]
    for name, kind, text in ledger.declarations(a0, t.ns):
        if kind in ("theorem", "lemma"):
            a0 = a0.replace(text, "", 1)
    stmts = [re.search(rf"^theorem\s+{re.escape(n)}\b.*?:=\s*sorry", ch, re.S | re.M).group(0) for n in t.theorems]
    head, tail = a0.rsplit(f"end {t.ns}", 1)
    a0 = head.rstrip() + "\n\n" + "\n\n".join(stmts) + f"\n\nend {t.ns}" + tail
    assert "if _h : ValidQuery s r" in a0 and "ValidQuery" not in rec["a1_phase0"].split("def step")[1]
    closed = {}
    for label, text in (("a1", rec["a1_phase0"]), ("a0", a0)):
        s = session(t, text)
        try:
            assert "error:" not in s.compile()["output_tail"], label
            goals = [g for g in (portfolio.goal_of(s, n) for n in ("req_valid_answered", "req_invalid_noop")) if g]
            results, _ = portfolio.run_portfolio(s, goals)
            closed[label] = sorted(n for n, r in results.items() if any(v["ok"] for v in r.values()))
        finally:
            close(s)
    assert closed == {"a1": [], "a0": ["req_invalid_noop", "req_valid_answered"]}, closed


LEAN = {"test_recorded_closure_banks_on_the_recorded_candidate", "test_validity_requirements_close_on_the_specification_terms"}


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
