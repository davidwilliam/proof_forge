"""Failure mining and retrieval by goal shape (harness/mine.py, harness/fin_retrieval.py, the
goal-aware ranking of harness/fin_lib.py, `harvest.py run --unverified`); no model calls.

Without Lean: the task split is the one its rule gives and was fixed with the mining set apart
from every test-split family; goals read back from Lean's goal display; shape tags; conclusions
and shapes of statements and goals; the goal-aware ranking (on a small index); the unverified
sources of the salvage harvest come only from the mining set; the new library modules are
library code with a doc string on every theorem and mention no task; the usage prior names
library declarations; the recorded retrieval and held-out results are consistent with their
details.
With the built library (skipped without Docker and the pinned image, and by --quick): the
goal-aware ranking on the real index puts the lemma a goal needs first for sample goals.

Run: python3 tests/test_feedback_library.py [--quick]
"""
import hashlib, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "tests")]
import fin_lib, harvest, mine  # noqa: E402

OUT = ROOT / "results/feedback-library-1"
NEW_MODULES = ["ProofForgeFin/Sums.lean", "ProofForgeFin/Sums/Eqns.lean", "ProofForgeFin/Sums/Index.lean",
               "ProofForgeFin/Sums/Update.lean", "ProofForgeFin/Sums/Floor.lean", "ProofForgeFin/Accrual.lean",
               "ProofForgeFin/Tactic/LibDefs.lean"]


def test_split_follows_its_rule():
    sp = mine.load_split()
    fams = {t["family"] for t in sp["tasks"].values()}
    test_fams = {t["family"] for t in sp["tasks"].values() if t["split"] == "test"}
    assert set(sp["test_split_families"]) == test_fams
    rest = sorted(fams - test_fams)
    h = {f: hashlib.sha256((sp["salt"] + f).encode()).hexdigest() for f in rest}
    assert h == sp["family_hashes"]
    drawn = sorted(rest, key=lambda f: h[f])[:2]
    assert drawn == sp["drawn_families"]
    assert set(sp["held_out_families"]) == test_fams | set(drawn)
    assert set(sp["mining_families"]) == fams - set(sp["held_out_families"])
    for tid, t in sp["tasks"].items():
        assert t["set"] == ("held-out" if t["family"] in sp["held_out_families"] else "mining"), tid
        if t["split"] == "test":
            assert t["set"] == "held-out", tid


def test_goals_read_back_from_lean_display():
    g = "s : State\nr : Request\nhok : (step s r).fst = Outcome.ok\n⊢ (step s r).snd.accounts = s.accounts ∧\n    True"
    st = mine.goal_statement(g)
    assert st == " (s : State) (r : Request) (hok : (step s r).fst = Outcome.ok) :\n    (step s r).snd.accounts = s.accounts ∧ True", st
    assert mine.goal_statement("x✝ : Nat\n⊢ x✝ = x✝") is None          # inaccessible name
    assert mine.goal_statement("h : a = ⋯\n⊢ True") is None               # elided proof
    assert mine.goal_statement("n c : Int\n⊢ c + n * c = (n + 1) * c") == " (n c : Int) :\n    c + n * c = (n + 1) * c"


def test_shape_tags():
    def tags(c):
        return mine.shape_tags({"conclusion": c})
    assert "sum-after-update" in tags("sumOver l (fun a => if a = x then f a + d else f a) = sumOver l f + d")
    assert "division-bound" in tags("a / b * b ≤ a")
    assert "min-max" in tags("x.sent + min q (x.qty - x.sent) ≤ x.qty")
    assert tags("Conserves step") == ["other"]


def test_conclusion_and_shape_of_statements_and_goals():
    t = fin_lib.text_shape("theorem t (l : List Nat) (h : l.Nodup) : sumOver l (upd f k v) = sumOver l f - f k + v")
    assert (t["rel"], t["lhs"], t["rhs"]) == ("=", "sumOver", "+") and {"sumOver", "upd", "-"} <= t["consts"]
    t = fin_lib.text_shape("s : State\n⊢ (step s r).snd.balance a = s.balance a + ↑(shareOf r a)")
    assert (t["rel"], t["lhs"], t["rhs"]) == ("=", "balance", "+") and "↑" in t["consts"]
    t = fin_lib.text_shape("(a + b) / c ≤ a / c + b / c + 1")
    assert (t["rel"], t["lhs"], t["rhs"]) == ("≤", "/", "+")
    assert fin_lib.conclusion_text("∀ (x : Nat), x ∈ l → f x ≤ c") == "f x ≤ c"
    assert fin_lib.looks_like_goal("a / b * b ≤ a") and not fin_lib.looks_like_goal("ceiling division bounds")


def test_goal_aware_ranking_on_a_small_index():
    def thm(name, sig, concl, doc=""):
        return {"kind": "theorem", "name": name, "module": "M", "signature": f"{name} {sig}", "doc": doc,
                "concl": concl}
    entries = [
        thm("A.sumOver_upd", "(l : List α) : sumOver l (upd f k v) = sumOver l f - f k + v",
            {"rel": "Eq", "lhs": "Ledger.sumOver", "rhs": "HAdd.hAdd",
             "consts": ["Eq", "Ledger.sumOver", "Ledger.upd", "HAdd.hAdd", "HSub.hSub"]}, "sum after an update"),
        thm("A.sumOver_le", "(h : ∀ a ∈ l, f a ≤ g a) : sumOver l f ≤ sumOver l g",
            {"rel": "LE.le", "lhs": "Ledger.sumOver", "rhs": "Ledger.sumOver", "consts": ["LE.le", "Ledger.sumOver"]},
            "sum update monotone"),
        thm("A.div_mul_le", "(a b : Nat) : a / b * b ≤ a",
            {"rel": "LE.le", "lhs": "HMul.hMul", "rhs": "", "consts": ["LE.le", "HMul.hMul", "HDiv.hDiv"]}),
    ]
    idx = fin_lib.Index(entries, usage={"A.div_mul_le": 3})
    goal = "sumOver accounts (upd bal x v) = sumOver accounts bal - bal x + v"
    assert idx.search("sum update", limit=1, goal=goal)[0]["name"] == "A.sumOver_upd"
    assert idx.search("a / b * b ≤ a", limit=1)[0]["name"] == "A.div_mul_le"     # the query reads as a goal
    assert [e["name"] for e in idx.search("sum update", limit=3)] == \
        [e["name"] for _, e in sorted(((s, e) for s, e in idx.scored("sum update", limit=3)), key=lambda x: -x[0])]


def test_salvage_sources_come_from_the_mining_set():
    sp = mine.load_split()
    rec = json.loads((OUT / "salvage/harvest.json").read_text())
    for s in rec["sources"]:
        assert s["kind"] == "unverified"
        assert s["harvest"] == (sp["tasks"][s["task"]]["set"] == "mining")
    harvested = {s["id"] for s in rec["sources"] if s["harvest"]}
    for d in rec["decls"]:
        assert d["src"] in harvested
        if d.get("final_name"):
            assert d["final_name"].startswith("ProofForgeFin.Salvaged.")


def test_new_modules_are_library_code_and_mention_no_task():
    root = ROOT / "lib"
    mods = [m[:-len(".lean")].replace("/", ".") for m in NEW_MODULES]
    assert fin_lib.scan(mods)["passed"], fin_lib.scan(mods)
    sp = mine.load_split()
    # Task ids, protocol names and names of task definitions (family names such as `lending` or
    # `fixed-point` are ordinary words).
    words = set(sp["tasks"])
    words |= {"Compound", "Balancer", "Knight", "Euler", "Cetus", "Hundred", "Spliit", "moneyphp", "go-money",
              "natSum", "fairShare", "weightedShare", "shareOf", "indexOf?", "Payout", "Router"}
    for rel in NEW_MODULES:
        text = (root / rel).read_text()
        for w in words:
            assert not re.search(rf"(?<![\w-]){re.escape(w)}(?![\w-])", text), (rel, w)
        code = fin_lib.strip_comments(text)
        for m in re.finditer(r"^theorem (\S+)", text, re.M):
            before = text[:m.start()].rstrip()
            assert before.endswith("-/"), (rel, m.group(1))
        assert "sorry" not in code


def test_usage_prior_names_library_declarations():
    u = json.loads(fin_lib.USAGE.read_text())["uses"]
    assert u and all(n.startswith("ProofForgeFin.") and v > 0 for n, v in u.items())


def test_recorded_retrieval_is_consistent():
    f = OUT / "retrieval.json"
    if not f.is_file():
        print("   no retrieval.json yet")
        return
    rec = json.loads(f.read_text())
    ranks = json.loads((OUT / "retrieval-ranks.json").read_text())
    for name, r in rec["sets"].items():
        rows = ranks[name]
        assert r["pairs"] == len(rows)
        for which in ("old", "new"):
            for k in (1, 5, 10):
                got = round(sum(1 for x in rows if x[which] and x[which] <= k) / len(rows), 4) if rows else None
                assert got == r[f"{which}_recall@{k}"], (name, which, k)


def test_recorded_held_out_measurement_is_consistent():
    for f in ("open-held-out.json", "reprove-held-out.json"):
        p = OUT / f
        if not p.is_file():
            print(f"   no {f} yet")
            continue
        rec = json.loads(p.read_text())
        assert rec["set"] == "held-out"
        sp = mine.load_split()
        for c in rec["candidates"]:
            assert sp["tasks"][c["task"]]["set"] == "held-out", c["task"]
        obs = [o for c in rec["candidates"] for o in c.get("obligations", [])]
        s = rec["summary"]
        assert s["closed_base"] == sum(o.get("base") == "closed" for o in obs)
        assert s["closed_new"] == sum(o.get("new") == "closed" for o in obs)


def test_goal_aware_ranking_on_the_library_index():
    from test_fin_lib import skip_without_docker
    if skip_without_docker():
        return
    idx = fin_lib.Index.load()
    cases = [
        ("sumOver l (upd f k v) = sumOver l f - f k + v", "ProofForgeFin.Machine.sumOver_upd"),
        ("(l.set i x).sum = l.sum - l[i] + x", "ProofForgeFin.Sums.sum_set_int"),
        ("((List.range n).map (fun i => if i < m then 1 else 0)).sum = min m n", "ProofForgeFin.Sums.sum_range_indicator"),
    ]
    for goal, want in cases:
        got = [e["name"] for e in idx.search(goal, limit=3, goal=goal)]
        assert want in got, (goal, got)


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    tests = [(n, f) for n, f in sorted(globals().items()) if n.startswith("test_") and callable(f)]
    failed = 0
    for n, f in tests:
        if quick and n == "test_goal_aware_ranking_on_the_library_index":
            continue
        try:
            f()
            print(f"ok   {n}")
        except Exception as e:  # noqa: BLE001
            failed += 1
            print(f"FAIL {n}: {e!r}")
    sys.exit(1 if failed else 0)
