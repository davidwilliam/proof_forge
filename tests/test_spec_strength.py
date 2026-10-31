"""Specification strength gate (harness/spec_strength.py).

Deterministic and without Docker or model calls: tokenizer, proof stripping, every mutation
operator, mutant selection, classification (with the container steps replaced by stubs), report
hashing and verification, the Passport record, the CLI listing, and the committed reports under
results/spec-strength-1.
"""
import copy, json, pathlib, subprocess, sys, tempfile, types
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "harness"))
import judge, spec_strength as ss, task as taskmod  # noqa: E402

RESULTS = ROOT / "results" / "spec-strength-1"
FAKE = types.SimpleNamespace(definitions=["step"], id="fake-task")

SRC = """import Demo.Spec
/-!
# Demo
-/

namespace Demo

/-- helper used by step -/
def adjust (bal : Nat → Int) (a : Nat) (amt : Int) : Nat → Int :=
  fun b => if b = a then bal b + amt else bal b

def unused (x : Nat) : Nat := x + 1

instance instDec (s : State) : Decidable (Valid s) := by
  unfold Valid <;> infer_instance

def step : Impl := fun s r =>
  if 0 < r.amount && r.source != r.target then
    let debited := adjust s.balance r.source (-(r.amount : Int))
    (.ok, { s with balance := adjust debited r.target r.amount, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem step_ok (s : State) (r : Request) :
    let t := step s r
    t.1 = .ok ∨ t.1 = .rejected := by
  unfold step
  split <;> simp

theorem by_cases_thm : ∀ n : Nat, n + 0 = n
  | 0 => rfl
  | n + 1 => rfl

end Demo
"""


def descs(text=SRC, task=FAKE, names=()):
    return [(s.op, s.desc) for s in ss.sites(text, task, names)]


def test_tokenizer_keeps_tactic_combinator_and_projections_whole():
    toks = [t.text for t in ss.tokenize("cases op <;> simp -- note\n(s.acct u).e /- c -/ x")]
    assert "<;>" in toks and "<" not in toks
    assert "-- note" in toks and "/- c -/" in toks
    code = [t for t in ss.tokenize("(s.acct u).e + x") if t.kind != "comment"]
    assert ss._projection_at(code, 4) and ss._atom_after(code, 0) == (0, 5)


def test_strip_proofs_replaces_only_proof_bodies():
    out = ss.strip_proofs(SRC)
    assert "unfold step" not in out and "| 0 => rfl" not in out
    assert "    let t := step s r\n    t.1 = .ok ∨ t.1 = .rejected := sorry" in out
    assert "theorem by_cases_thm : ∀ n : Nat, n + 0 = n\n  := sorry" in out
    # definitions and instances are kept byte for byte, including the tactic block of the instance
    for d in ss.declarations(SRC):
        if d.kind in ("def", "instance"):
            assert SRC[d.start:d.end].rstrip() in out


def test_strip_proofs_keeps_every_code_declaration_of_real_references():
    for tid in ("payout-flagship", "rw-cetus-shlw", "rw-compound-comp", "transfers-overdraft-b1"):
        t = taskmod.load(tid)
        src = ss.reference_file(t).read_text()
        out = ss.strip_proofs(src)
        before = [src[d.start:d.end].rstrip() for d in ss.declarations(src) if d.kind in ss.CODE_KW | {"structure"}]
        after = [out[d.start:d.end].rstrip() for d in ss.declarations(out) if d.kind in ss.CODE_KW | {"structure"}]
        assert before == after
        proofs = [d for d in ss.declarations(out) if d.kind in ss.PROOF_KW]
        assert proofs and all(out[d.start:d.end].rstrip().endswith(":= sorry") for d in proofs)


def test_only_reachable_code_is_mutated_and_proofs_never():
    sites = ss.sites(ss.strip_proofs(SRC), FAKE)
    assert {s.decl for s in sites} == {"adjust", "step"}     # not `unused`, not the theorems
    assert not any("infer_instance" in s.desc or "<;>" in s.desc for s in sites)


def test_operators():
    d = descs(ss.strip_proofs(SRC))
    expect = [
        ("boundary", "`<` replaced by `≤`"),
        ("equality", "`=` replaced by `≠`"),
        ("equality", "`!=` replaced by `==`"),
        ("arith", "`+` replaced by `-`"),
        ("arith", "unary minus dropped"),
        ("logic", "`&&` replaced by `||`"),
        ("drop-conjunct", "conjunct `0 < r.amount` replaced by `true`"),
        ("drop-conjunct", "conjunct `r.source != r.target` replaced by `true`"),
        ("guard", "condition `0 < r.amount && r.source != r.target` replaced by `true`"),
        ("guard", "condition `0 < r.amount && r.source != r.target` replaced by `false`"),
        ("guard", "condition `b = a` replaced by `false`"),
        ("field", "field read `r.source` replaced by `r.target`"),
        ("field", "field read `r.amount` replaced by `r.txId`"),
        ("field", "update of field `balance` dropped"),
        ("field", "update of field `applied` dropped"),
        ("swap", "arguments `debited` and `r.target` of `adjust` swapped"),
        ("swap", "operands of `<` swapped"),
        ("constant", "constant `0` replaced by `1`"),
    ]
    for e in expect:
        assert e in d, e


def test_rounding_and_constant_operators():
    src = ("import X.Spec\nnamespace X\n"
           "def mulDown (a b : Nat) : Nat := a * b / ONE\n"
           "def mulUp (a b : Nat) : Nat := (a * b + ONE - 1) / ONE\n"
           "def divUp (a b : Nat) : Nat := (a * ONE - 1) / b + 1\n"
           "def step (a : Nat) : Nat := min (mulDown a 1000) (mulUp a 3) + divUp a 7\nend X\n")
    d = descs(src)
    assert ("rounding", "floor division `/` replaced by ceiling division") in d
    assert ("rounding", "`mulDown` replaced by `mulUp`") in d and ("rounding", "`mulUp` replaced by `mulDown`") in d
    assert ("rounding", "ceiling division idiom `(a + b - 1) / b` replaced by floor division") in d
    assert ("rounding", "ceiling division idiom `(a - 1) / b + 1` replaced by floor division") in d
    assert ("swap", "`min` replaced by `max`") in d
    assert {("constant", f"constant `1000` replaced by `{v}`") for v in (1001, 999, 10000, 100)} <= set(d)
    ceil = next(s for s in ss.sites(src, FAKE) if s.helper)
    out = ss.apply(src, ceil)
    assert "infixl:70 \" ⌈/⌉ \" => PfCeilDiv.cdiv" in out and out.index("PfCeilDiv") > out.index("import X.Spec")


def test_projection_swap_and_atoms_with_projections():
    src = "namespace E\ndef step (s : St) (u x : Nat) : Nat := min x (s.acct u).d + (s.acct u).e\nend E\n"
    d = descs(src)
    assert ("field", "projection `.d` replaced by `.e`") in d and ("field", "projection `.e` replaced by `.d`") in d
    assert ("swap", "arguments `x` and `(s.acct u).d` of `min` swapped") in d


def test_application_does_not_continue_on_a_less_indented_line():
    src = ("namespace P\ndef step (r : R) : Nat :=\n  let n := r.xs.length\n"
           "  f (r.a / n) (r.a % n)\nend P\n")
    d = descs(src)
    assert ("swap", "arguments `(r.a / n)` and `(r.a % n)` of `f` swapped") in d
    assert not any("of `r.xs.length`" in x for _, x in d)


def test_mutants_are_deterministic_and_distinct():
    t = taskmod.load("transfers-overdraft-b1")
    a, b = ss.mutants(t), ss.mutants(t)
    assert [m["source_sha256"] for m in a["mutants"]] == [m["source_sha256"] for m in b["mutants"]]
    hashes = [m["source_sha256"] for m in a["mutants"]]
    assert len(set(hashes)) == len(hashes) and a["stripped_sha256"] not in hashes
    assert [m["id"] for m in a["mutants"]] == [f"M{i:03d}" for i in range(1, len(hashes) + 1)]
    assert all(m["diff"].startswith("--- a/Solution.lean") for m in a["mutants"])
    assert any(m["description"] == "conjunct `s.auth r.requester r.source` replaced by `true`" for m in a["mutants"])


def test_selection_is_stratified_and_deterministic():
    t = taskmod.load("rw-euler-donate")
    full = ss.mutants(t)
    a, b = ss.mutants(t, 30), ss.mutants(t, 30)
    assert a["generated"] == full["generated"] and len(a["mutants"]) == 30
    assert [m["source_sha256"] for m in a["mutants"]] == [m["source_sha256"] for m in b["mutants"]]
    ops = {m["operator"] for m in full["mutants"]}
    assert {m["operator"] for m in a["mutants"]} == ops      # every operator represented


def test_cetus_boundary_mutant_is_generated():
    ms = ss.mutants(taskmod.load("rw-cetus-shlw"))["mutants"]
    m = next(m for m in ms if m["description"] == "`≥` replaced by `>`")
    assert "-  if n ≥ mask then (0, true) else (n <<< 64, false)" in m["diff"]
    assert "+  if n > mask then (0, true) else (n <<< 64, false)" in m["diff"]


def test_first_difference():
    cases = [json.dumps({"x": i}) for i in range(3)]
    ref = ['{"y": 0}', '{"y": 1}', '{"y": 2}']
    assert ss.first_difference(cases, ref, ref) == (0, None)
    n, f = ss.first_difference(cases, ['{"y": 0}', '{"y": 5}', '{"y": 2}'], ref)
    assert n == 1 and f == {"case": 1, "input": {"x": 1}, "output": {"y": 5}, "reference_output": {"y": 1}}
    assert ss.first_difference(cases, ['{ "y" : 0 }', '{"y":1}', '{"y": 2}'], ref)[0] == 0


def _stub_run(task, verdicts):
    """run_task with the container steps replaced: `verdicts` maps a mutant id to
    (binary sha, standard result, standard outputs, extended result, extended outputs)."""
    gen = ss.mutants(task)
    ids = [m["id"] for m in gen["mutants"]]
    cases = [json.dumps({"k": i}) for i in range(4)]
    ref_outs = ['{"o": 0}'] * 4
    builds = {"REF": {"exit_code": 0, "binary_sha256": "ref"}}
    for i in ids:
        v = verdicts.get(i)
        builds[i] = {"exit_code": 1, "error": "error: type mismatch"} if v is None else {"exit_code": 0, "binary_sha256": v[0]}
    state = {"current": "REF", "round": 0}

    def install(project, task, mid):
        state["current"], state["round"] = mid, 0

    def tests(project, task, n, seed):
        state["round"] += 1
        if state["current"] == "REF":
            return {"status": "PASS", "cases": 4, "violations": {}}, cases, ref_outs
        v = verdicts[state["current"]]
        res, outs = (v[1], v[2]) if state["round"] == 1 else (v[3], v[4])
        return res, cases, outs

    tmp = pathlib.Path(tempfile.mkdtemp())
    with patch.object(ss, "build_all", lambda project, task, ms, log: builds), \
         patch.object(ss, "install_binary", install), patch.object(ss, "run_tests", tests), \
         patch.object(judge, "fresh_project", lambda ws, files, task: tmp), \
         patch.object(judge, "image_id", lambda: "sha256:test"), patch.object(judge, "image_platform", lambda: "linux/test"):
        return ss.run_task(task, counterexamples=False, log=lambda *a: None), ids


PASS = {"status": "PASS", "cases": 4, "violations": {}}


def refuted(rid):
    return {"status": "REFUTED", "cases": 4, "violations": {rid: 2},
            "witnesses": [{"requirement": rid, "message": "m", "input": {}, "output": {}}]}


def test_classification():
    t = taskmod.load("transfers-overdraft-b1")
    same = ['{"o": 0}'] * 4
    diff = ['{"o": 0}', '{"o": 1}', '{"o": 0}', '{"o": 0}']
    gen_ids = [m["id"] for m in ss.mutants(t)["mutants"]]
    v = {gen_ids[0]: ("ref", None, None, None, None),                       # identical executable
         gen_ids[1]: ("b1", refuted("REQ-LIMIT"), diff, None, None),         # killed
         gen_ids[2]: ("b2", PASS, same, refuted("REQ-EFFECTS"), diff),       # killed by extended cases
         gen_ids[3]: ("b3", PASS, same, PASS, same),                         # survived, same outputs
         gen_ids[4]: ("b4", PASS, diff, PASS, same)}                         # survived, differs
    rep, ids = _stub_run(t, v)
    st = {m["id"]: m["status"] for m in rep["mutants"]}
    assert st[ids[0]] == "equivalent" and st[ids[1]] == "killed" and st[ids[2]] == "killed_extended"
    assert st[ids[3]] == "survived_same" and st[ids[4]] == "survived_differs"
    assert all(st[i] == "not_compiled" for i in ids[5:])
    m4 = next(m for m in rep["mutants"] if m["id"] == ids[4])
    assert m4["first_difference"]["case"] == 1 and m4["differing_cases"] == 1
    s = rep["summary"]
    assert (s["compiled"], s["equivalent"], s["killed"], s["survived"], s["kill_ratio"]) == (5, 1, 2, 2, "2 of 4")
    vac = {v["requirement"]: v for v in rep["vacuity"]}
    assert vac["REQ-LIMIT"]["violated_by"] == 1 and vac["REQ-LIMIT"]["not_trivially_true"] == "tested"
    assert vac["REQ-CONSERVATION"]["not_trivially_true"] == "not shown"
    assert rep["report_sha256"] == ss.content_hash(rep) and ss.verify_report(rep) == []
    md = ss.markdown(rep)
    assert "## Survivors" in md and f"### {ids[4]}: survived, behaviour differs" in md


def test_verify_report_detects_changes():
    t = taskmod.load("transfers-overdraft-b1")
    rep, ids = _stub_run(t, {})
    assert ss.verify_report(rep) == []
    bad = copy.deepcopy(rep)
    bad["mutants"][0]["status"] = "killed"
    assert "report content hash differs" in ss.verify_report(bad)
    bad["report_sha256"] = ss.content_hash(bad)
    assert "summary does not match the mutant records" in ss.verify_report(bad)
    bad = copy.deepcopy(rep)
    bad["mutants"][0]["diff"] = bad["mutants"][1]["diff"]
    bad["report_sha256"] = ss.content_hash(bad)
    assert f"mutant {ids[0]} is not regenerated" in ss.verify_report(bad)
    bad = copy.deepcopy(rep)
    bad["locked"]["manifest_sha256"] = "0" * 64
    bad["report_sha256"] = ss.content_hash(bad)
    assert "locked manifest differs from the task in this checkout" in ss.verify_report(bad)


def test_passport_record():
    t = taskmod.load("transfers-overdraft-b1")
    rep, _ = _stub_run(t, {})
    rec = ss.passport_record(rep)
    assert rec["report_sha256"] == rep["report_sha256"]
    assert rec["locked_manifest_sha256"] == t.locked()["manifest_sha256"]
    passport = {"locked": {"manifest_sha256": t.locked()["manifest_sha256"]}, "spec_strength": rec}
    assert ss.verify_passport_record(passport, rep) == []
    assert ss.verify_passport_record({"locked": passport["locked"]}, rep) == []     # the field is optional
    other = copy.deepcopy(passport)
    other["spec_strength"]["mutants"]["killed"] += 1
    assert "spec_strength record does not match the report" in ss.verify_passport_record(other, rep)
    other = copy.deepcopy(passport)
    other["locked"]["manifest_sha256"] = "1" * 64
    assert "spec_strength record is for another locked manifest" in ss.verify_passport_record(other, rep)


def test_cli_lists_mutants():
    out = subprocess.run([sys.executable, str(ROOT / "bin/proofforge"), "spec-strength", "--task", "rw-cetus-shlw",
                          "--list"], capture_output=True, text=True, check=True).stdout
    assert out.startswith("rw-cetus-shlw: ") and "M001" in out


def test_committed_reports_verify():
    reports = sorted(RESULTS.glob("*/report.json")) if RESULTS.is_dir() else []
    for f in reports:
        rep = json.loads(f.read_text())
        assert ss.verify_report(rep) == [], f
