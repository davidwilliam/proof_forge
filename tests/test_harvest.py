"""Proof harvesting (harness/harvest.py): reading candidates, restating lemmas over library
definitions, the harvested modules and their provenance, the recorded counts, and Passports of
the library before the harvest; no model calls.

Without Lean: the reader of Lean files, the restatement, names and modules, the corrections the
final check applies, the obligation sites of the measurement, the sources and the provenance of
every harvested lemma (each doc string names a file whose hash and evidence match), the
consistency of results/harvest-1/harvest.json and measure.json, and the library version pinning
(the pre-harvest sources are found in git by their tree hash).
With Lean (skipped without Docker and the pinned image, and by --quick): a Passport issued
against the pre-harvest library for tests/fixtures/library/compound_lib.lean reproduces with
`bin/proofforge verify` from this checkout, which has the harvested library.

Run: python3 tests/test_harvest.py [--quick]
"""
import contextlib, io, json, pathlib, re, runpy, sys, tempfile, types

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "tests")]
import fin_lib, harvest  # noqa: E402

OUT = ROOT / "results/harvest-1"
HARVESTED = ROOT / "lib/ProofForgeFin/Harvested"

SAMPLE = '''import Pay.Spec
namespace Pay
open List

/-- Doc of a helper. -/
@[simp] theorem helper_one (l : List Nat) (n : Nat) :
    (l ++ [n]).length = l.length + 1 := by
  simp

theorem uses_let (a : Nat) : (let b := a; b + 0) = a := by
  simp
-- a comment with theorem fake : True := trivial
/- block comment
theorem fake2 : True := trivial
-/
open Nat in
theorem with_open (s : State) (x : Nat) : (s.accounts.contains x) = true ↔ x ∈ s.accounts := by
  simp [List.contains_eq_mem]

theorem req_main : Main step := sorry

def step (s : State) : State := s

end Pay
'''


def test_reader_finds_theorems_with_scope():
    p = harvest.parse(SAMPLE)
    names = [t["name"] for t in p["theorems"]]
    assert names == ["helper_one", "uses_let", "with_open", "req_main"], names
    h = p["theorems"][0]
    assert h["ns"] == "Pay" and h["opens"] == ["List"] and h["attrs"] == ["simp"]
    assert h["statement"].strip().startswith("(l : List Nat)") and h["proof"].strip() == "by\n  simp"
    assert p["theorems"][1]["statement"].strip() == "(a : Nat) : (let b := a; b + 0) = a"
    assert p["theorems"][2]["opens"] == ["List", "Nat"]
    assert "step" in p["defs"]


def test_restatement_over_library_definitions_and_structures():
    lib_defs, lib_thms = harvest.library_tables()
    assert lib_defs[harvest.norm_def("{α : Type v} (l : List α) (f : α → Int) : Int := "
                                     "l.foldr (fun a acc => f a + acc) 0")] == "ProofForgeFin.Ledger.sumOver"
    spec = harvest.parse('''namespace Pay
abbrev AccountId := Nat
/-- Sum. -/
def sumOver {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun a acc => f a + acc) 0
structure State where
  accounts : List AccountId
  balance  : AccountId → Int
theorem sumOver_append {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by sorry
end Pay
''')
    ctx = harvest.context_from(spec["defs"], spec["structures"], {t["name"] for t in spec["theorems"]},
                               lib_defs, lib_thms, "Pay")
    assert ctx["aliases"] == {"AccountId": "Nat"}
    assert ctx["defs"] == {"sumOver": "ProofForgeFin.Ledger.sumOver"}
    assert ctx["lemmas"] == {"sumOver_append": "ProofForgeFin.Ledger.sumOver_append"}
    assert ctx["structs"]["State"] == [("accounts", "List Nat"), ("balance", "Nat → Int")]
    th = {"statement": " (l : List AccountId) (f : AccountId → Int) : Pay.sumOver l f = sumOver l f",
          "proof": " by simp [sumOver_append]"}
    v = dict((x[0], x[1:]) for x in harvest.variants(th, ctx))
    assert v["v1"][0] == (" (l : List Nat) (f : Nat → Int) : ProofForgeFin.Ledger.sumOver l f = "
                          "ProofForgeFin.Ledger.sumOver l f")
    assert v["v1"][1] == " by simp [ProofForgeFin.Ledger.sumOver_append]"
    assert v["v0"][0] == th["statement"]
    th = {"statement": " (s : State) (x : Nat) : (s.accounts.contains x) = true ↔ x ∈ s.accounts",
          "proof": " by simp [List.contains_eq_mem]"}
    v = dict((x[0], x[1:]) for x in harvest.variants(th, ctx))
    assert v["v2"][0] == " (s_accounts : List Nat) (x : Nat) : (s_accounts.contains x) = true ↔ x ∈ s_accounts"
    # A binder used other than through a field stays: no v2.
    th = {"statement": " (s : State) : s = s", "proof": " rfl"}
    assert [x[0] for x in harvest.variants(th, ctx)] == ["v1"]


def test_names_topics_and_suggestions():
    assert harvest.clean_name("my_floor_bound2") == "floor_bound"
    assert harvest.clean_name("plan1_sumOver_range_const") == "sumOver_range_const"
    assert harvest.clean_name("tmp_const2") == "const"
    assert harvest.clean_name("State.foo'") == "State_foo"
    assert harvest.topic(" (a b : Nat) : a + b = b + a") == 0
    assert harvest.topic(" (l : List Nat) : l.length = l.length") == 1
    assert harvest.topic(" (l : List Nat) (f : Nat → Int) : ProofForgeFin.Ledger.sumOver l f = 0") == 2
    assert harvest.suggestion("Try this:\n  [apply] exact Nat.le_of_lt h") == "Nat.le_of_lt h"


def test_final_check_corrections():
    body = "theorem t (n : Nat) : n + 0 = n := by\n  simp [Nat.add_zero, foo]\n"
    m = {"data": "This simp argument is unused:\n  foo", "pos": {"line": 11, "column": 22},
         "endPos": {"line": 11, "column": 25}}
    assert harvest.fix_of(m, body, 10) == "theorem t (n : Nat) : n + 0 = n := by\n  simp [Nat.add_zero]\n"
    m = {"data": "This simp argument is unused:\n  Nat.add_zero", "pos": {"line": 11, "column": 8},
         "endPos": {"line": 11, "column": 20}}
    assert harvest.fix_of(m, body, 10) == "theorem t (n : Nat) : n + 0 = n := by\n  simp [foo]\n"
    one = "theorem t : True := by\n  simp [foo]\n"
    m = {"data": "This simp argument is unused:\n  foo", "pos": {"line": 2, "column": 8}, "endPos": {"line": 2, "column": 11}}
    assert harvest.fix_of(m, one, 1) == "theorem t : True := by\n  simp\n"
    dep = "theorem t : x := by rw [if_pos h]\n"
    m = {"data": "`if_pos` has been deprecated: Use `ite_eq_left` instead", "pos": {"line": 5, "column": 24},
         "endPos": {"line": 5, "column": 30}}
    assert harvest.fix_of(m, dep, 5) == "theorem t : x := by rw [ite_eq_left h]\n"
    m = {"data": "unused variable `h`", "pos": {"line": 5, "column": 0}, "endPos": {"line": 5, "column": 1}}
    assert harvest.fix_of(m, dep, 5) is None


def test_obligation_sites():
    text = '''theorem a : P := sorry
theorem b : Q := by
  intro x
  sorry
theorem c : R := by
  exact foo sorry
theorem d : S := by
  induction n with
  | zero => sorry
  | succ n ih => simp
theorem e : T := match h with
  | .inl _ => sorry
  | .inr _ => trivial
-- sorry in a comment
theorem f : U := by simp [show "sorry" = "sorry" from rfl]
'''
    sites = harvest.sorry_sites(text)
    assert len(sites) == 5, sites
    kinds = [harvest.site_kind(text, p) for p in sites]
    assert kinds == ["term", "tactic", "term", "tactic", "term"], kinds
    out, obs = harvest.battery_text(text, [])
    assert len(obs) == 5 and out.count("PFH_OPEN_") == 5 and "import ProofForgeFin" in out
    spans = harvest.theorem_spans(text)
    assert [s[0] for s in spans] == ["a", "b", "c", "d", "e", "f"]
    out, obs = harvest.battery_text(text, [spans[1]])
    assert obs[0]["kind"] == "failing theorem" and obs[0]["theorem"] == "b" and len(obs) == 5


def test_sources_are_bound_to_their_evidence():
    srcs, skipped = harvest.sources()
    assert not skipped, skipped
    assert len(srcs) >= 250
    for s in srcs:
        assert harvest.sha256_file(ROOT / s["file"]) == s["file_sha256"]
        assert s["harvest"] == (s["split"] in harvest.LIBRARY_SPLITS)
    assert {s["split"] for s in srcs if not s["harvest"]} == {"test"}
    assert any(s["kind"] == "passport" for s in srcs) and any(s["kind"] == "eval" for s in srcs)


def harvest_record():
    return json.loads((OUT / "harvest.json").read_text())


def test_harvested_modules_are_library_code():
    top = (ROOT / "lib/ProofForgeFin.lean").read_text()
    assert "import ProofForgeFin.Harvested\n" in top
    mods = fin_lib.closure(["ProofForgeFin.Harvested"])
    assert any(m.startswith("ProofForgeFin.Harvested.") for m in mods)
    assert fin_lib.scan(mods)["passed"], fin_lib.scan(mods)
    for f in HARVESTED.glob("*.lean"):
        code = fin_lib.strip_comments(f.read_text())
        assert "@[simp" not in code and "attribute" not in code and "set_option" not in code, f


def test_every_harvested_lemma_has_its_provenance():
    rec = harvest_record()
    srcs = {s["id"]: s for s in rec["sources"]}
    written = {r["final_name"]: r for r in rec["decls"] if r.get("final_name")}
    assert written
    seen = set()
    for f in sorted(HARVESTED.glob("*.lean")):
        text = f.read_text()
        for m in re.finditer(r"/-- Harvested from task `([^`]+)`: `([^`]+)` in `([^`]+)` \(file sha256 `([0-9a-f]{64})`; "
                             r"(?:Passport sha256 `([0-9a-f]{64})`|eval\.json sha256 `([0-9a-f]{64})`)(.*?)-/\s*\n"
                             r"theorem (\S+)", text, re.S):
            task, name, file, fsha, psha, esha, _, thm = m.groups()
            full = f"{harvest.NAMESPACE}.{thm}"
            assert full in written, full
            r = written[full]
            assert (r["task"], r["name"], r["file"]) == (task, name, file)
            assert harvest.sha256_file(ROOT / file) == fsha
            s = srcs[r["src"]]
            assert s["split"] in harvest.LIBRARY_SPLITS
            if psha:
                assert s["passport_sha256"] == psha
                if s["kind"] == "passport":
                    assert json.loads((ROOT / s["evidence"]).read_text())["passport_sha256"] == psha
            else:
                assert harvest.sha256_file(ROOT / s["evidence"]) == esha
                e = json.loads((ROOT / s["evidence"]).read_text())
                assert e["judge"] == "ACCEPT" and e["binary"] == "PASS" and e["final_sha256"] == fsha
            seen.add(full)
    assert seen == set(written), set(written) - seen
    n = sum(len(re.findall(r"^theorem ", f.read_text(), re.M)) for f in HARVESTED.glob("*.lean"))
    assert n == len(written)


def test_recorded_counts_are_consistent():
    rec = harvest_record()
    c = rec["counts"]
    d = rec["decls"]
    assert c["helper_theorems"] == len(d) == c["task_specific"] + c["general_statements"]
    assert c["general_checked"] + c["general_proof_rejected"] == c["general_statements"]
    assert sum(c["by_verdict"].values()) == c["distinct_statements"]
    assert c["written"]["accepted"] == c["by_verdict"].get("accepted", 0)
    assert c["written"]["accepted"] + c["written"]["support"] == sum("final_name" in r for r in d)
    for r in d:
        if r.get("verdict") == "accepted":
            assert r.get("final_name"), r
        if r["class"] == "task-specific":
            assert "final_name" not in r
    assert rec["base_library_sha256"] != rec["library_sha256"] == fin_lib.tree_sha256()


def test_measurement_record_is_consistent():
    f = OUT / "measure.json"
    if not f.is_file():
        print("   no measure.json yet")
        return
    m = json.loads(f.read_text())
    u = m["unresolved"]
    obs = [o for c in u["candidates_detail"] for o in c.get("obligations", [])]
    assert u["obligations"] == len(obs)
    assert u["closed_before"] == sum(o.get("base") == "closed" for o in obs)
    assert u["closed_after"] == sum(o.get("harvest") == "closed" for o in obs)
    for name, r in m["reprove"].items():
        rows = r["rows"]
        assert r["lemmas"] == len(rows)
        assert r["closed_before"] == sum(bool(x["base"]) for x in rows)
        assert r["closed_after"] == sum(bool(x["harvest"]) and not x["circular"] for x in rows)
    assert m["library_after_sha256"] == fin_lib.tree_sha256()
    assert m["library_before_sha256"] == harvest_record()["base_library_sha256"]


def test_pre_harvest_library_is_found_by_its_tree_hash():
    base = harvest_record()["base_library_sha256"]
    assert fin_lib.tree_sha256() != base
    commit = fin_lib.find_commit(base)
    assert commit and fin_lib.tree_sha256_at(commit) == base
    root = fin_lib.materialize(commit, base)
    assert root and fin_lib.tree_sha256(root) == base
    assert not (root / "ProofForgeFin/Harvested.lean").exists()
    assert fin_lib.tree_sha256(harvest.base_root()) == base
    # A Passport record of that version, with and without the commit, resolves to its sources.
    for rec in ({"vendored": True, "source_tree_sha256": base, "git_commit": commit},
                {"vendored": True, "source_tree_sha256": base, "git_commit": None}):
        r, c, note = fin_lib.root_for(rec)
        assert r and fin_lib.tree_sha256(r) == base and c == commit and "using the library sources" in note
    assert fin_lib.root_for({"vendored": True, "source_tree_sha256": fin_lib.tree_sha256()})[0] is None
    assert fin_lib.root_for({"vendored": False})[0] is None
    r, c, note = fin_lib.root_for({"vendored": True, "source_tree_sha256": "0" * 64, "git_commit": None})
    assert r is None and "no commit provides it" in note


def test_passport_of_the_pre_harvest_library_reproduces():
    from test_fin_lib import skip_without_docker
    if skip_without_docker():
        return
    import passport, task as taskmod
    cli = runpy.run_path(str(ROOT / "bin/proofforge"))
    fixture = ROOT / "tests/fixtures/library/compound_lib.lean"
    t = taskmod.load("rw-compound-comp")
    base = harvest_record()["base_library_sha256"]
    root = fin_lib.materialize(fin_lib.find_commit(base), base)
    with harvest.limited():
        with fin_lib.using(root):
            p = passport.run(fixture, t, cases=300)
        assert p["status"] == "VERIFIED", p["proof_check"]
        assert p["library"]["source_tree_sha256"] == base and p["library"]["vendored"]
        d = pathlib.Path(tempfile.mkdtemp(prefix="pf-harvest-pp-"))
        (d / "passport.json").write_text(json.dumps(p, indent=2) + "\n")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = cli["cmd_verify"](types.SimpleNamespace(passport=str(d / "passport.json"), candidate=str(fixture),
                                                         strict_image=False))
    text = out.getvalue()
    print(text)
    assert rc == 0 and text.rstrip().endswith("reproduced"), text
    assert "using the library sources of commit" in text
    assert "same       library source tree" in text


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    lean = {"test_passport_of_the_pre_harvest_library_reproduces"}
    for name, fn in list(globals().items()):
        if name.startswith("test_") and not (quick and name in lean):
            fn()
            print(f"ok  {name}")
