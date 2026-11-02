"""Where the repair agent (agents/repair.py, arm A1) spends its dollars: the changes made after
results/e1-test-open-2 (results/e1-open-diagnosis-2/README.md). No model calls.

Fixtures in tests/fixtures/repair_e1open2/, extracted from the recorded A1 runs of e1-test-open-2:
- portfolio_grants_b4.json: the candidate of permissions-grants-b4 at version 3, the portfolio batch
  that closed req_no_self_grant and req_others_unchanged on it, and the four texts the run tried to
  bank, none of which compiled (the continuation lines of a multi-line tactic were indented twice).

Without Lean: the banked proof is the proof the batch checked, for every portfolio entry.
With Lean (the pinned image): the recorded closure banks on the recorded candidate and `#print
axioms` shows the requirement proved; the recorded text does not compile.

Run: python3 tests/test_repair_spend.py [--quick] [name ...]   (--quick skips the Lean runs)
"""
import json, os, pathlib, re, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "tests")]
import budget, judge, portfolio, repair, task as taskmod  # noqa: E402

FIX = ROOT / "tests/fixtures/repair_e1open2"
PORT = json.loads((FIX / "portfolio_grants_b4.json").read_text())
GRANTS = taskmod.load(PORT["task"])


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


LEAN = {"test_recorded_closure_banks_on_the_recorded_candidate"}


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
