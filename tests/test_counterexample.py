"""Counterexample stage (harness/counterexample.py).

The generation, Passport and verify tests make no Docker calls. The kernel tests run Lean in
the pinned image and are skipped without it: they check accepted refutations, and that a false
instance and a weakened statement are rejected.
"""
import contextlib, copy, io, json, pathlib, runpy, subprocess, sys, tempfile, types
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "harness"))
import binary_check, counterexample as cx, judge, passport, task as taskmod  # noqa: E402

cli = runpy.run_path(str(ROOT / "bin/proofforge"))
CETUS = ROOT / "results/cetus-1/passports/original-port.json"
CETUS_CANDIDATE = ROOT / "realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean"


def cetus_witnesses():
    p = json.loads(CETUS.read_text())
    return {r["id"]: r["witness"] for r in p["requirements"] if r["witness"]}


def test_statement_and_challenge_come_from_the_locked_challenge():
    t = taskmod.load("rw-cetus-shlw")
    locked = (t.root / t.spec_dir / "Challenge.lean").read_text()
    assert cx.locked_statement(t, "req_shlw_exact") == "ShlwExact checkedShlw"
    ch = cx.challenge_source(t, "req_shlw_exact", "ShlwExact checkedShlw")
    assert ch.startswith(locked.rstrip("\n"))
    assert "theorem cex_req_shlw_exact : ¬ (ShlwExact checkedShlw) := sorry" in ch
    # the locked holes and theorems are kept unchanged
    assert "def checkedShlw : Shlw := sorry" in ch and "theorem req_shlw_exact" in ch


def test_adapter_lookup_prefers_the_task_then_the_id_then_the_base():
    assert cx.adapter_path(taskmod.load("rw-cetus-shlw")) == ROOT / "counterexamples/rw-cetus-shlw.py"
    assert cx.adapter_path(taskmod.load("queues-ring-b3")) == ROOT / "counterexamples/queues-ring.py"
    assert cx.adapter_path(taskmod.load("payout-flagship")) == ROOT / "counterexamples/payout-flagship.py"
    assert cx.adapter_path(taskmod.load("payouts-flagship-b2")) == ROOT / "counterexamples/payouts-flagship.py"
    assert cx.adapter_path(taskmod.load("queues-prio-b1")) is None
    assert cx.base_id("rate-limiters-bucket-b5") == "rate-limiters-bucket" and cx.base_id("rw-cetus-shlw") == "rw-cetus-shlw"
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp)
        (root / "counterexample.py").write_text("def instance(task, requirement, case, out, origin=None):\n    return None\n")
        assert cx.adapter_path(types.SimpleNamespace(root=root, id="queues-ring-b1")) == root / "counterexample.py"


def test_generated_refutation_instantiates_the_requirement_at_the_witness():
    t = taskmod.load("rw-cetus-shlw")
    w = cetus_witnesses()
    it = cx.generate(t, w["REQ-DELTA-A-COVERS"])
    assert it["statement"] == "¬ (DeltaACovers checkedShlw)" and it["theorem"] == "ClmmMath.cex_req_delta_a_covers"
    src = it["lean_source"]
    assert src.startswith("import Solution\n") and "theorem cex_req_delta_a_covers : ¬ (DeltaACovers checkedShlw) := by" in src
    assert "(60257519765924248467716150) (60863087478126617965993239) (10365647984364446732462244378333008) _ " in src
    assert "native_decide" not in src and "axiom" not in src.split("-/", 1)[1]
    it = cx.generate(t, w["REQ-SHLW-EXACT"])
    assert "have hx := h (6277101735386683105903941386108044688699448269690241981769)" in it["lean_source"]


def test_unsafe_adapter_output_and_missing_adapters_are_reasons_not_refutations():
    t = taskmod.load("rw-cetus-shlw")
    w = cetus_witnesses()["REQ-SHLW-EXACT"]
    bad = types.SimpleNamespace(instance=lambda *a, **k: {"preamble": "axiom cheat : False", "args": ["0"]})
    with patch.object(cx, "adapter", return_value=(bad, ROOT / "counterexamples/rw-cetus-shlw.py")):
        it = cx.generate(t, w)
    assert "lean_source" not in it and "forbidden construct" in it["reason"]
    boom = types.SimpleNamespace(instance=lambda *a, **k: 1 / 0)
    with patch.object(cx, "adapter", return_value=(boom, ROOT / "counterexamples/rw-cetus-shlw.py")):
        assert cx.generate(t, w)["reason"].startswith("adapter error: ZeroDivisionError")
    skip = types.SimpleNamespace(instance=lambda *a, **k: {"unsupported": "a frame condition"})
    with patch.object(cx, "adapter", return_value=(skip, ROOT / "counterexamples/rw-cetus-shlw.py")):
        assert cx.generate(t, w)["reason"] == "not handled by the adapter: a frame condition"
    q = taskmod.load("queues-prio-b1")
    it = cx.generate(q, {"requirement": "REQ-FIFO-TIES", "input": {}, "output": {}})
    assert it["reason"] == "the task has no counterexample adapter" and it["statement"] == "¬ (FifoTies step)"
    items = cx.check_items(q, CETUS_CANDIDATE, [it])
    assert items[0]["kernel_checked"] is False


def test_spec_propositions_are_found_for_unfolding():
    props = cx.prop_defs(taskmod.load("rw-euler-donate"))
    assert {"Healthy", "Allowed", "EffectOn", "Checked", "NoBadDebt"} <= set(props)
    assert "genesis" not in props and "runAll" not in props
    assert "Legacy.WellFormed" in cx.prop_defs(taskmod.load("rw-compound-comp"))


def test_every_refuted_requirement_keeps_a_witness_and_follow_ups_keep_their_origin():
    oracle = types.SimpleNamespace(
        gen_case=lambda rng: {"i": rng.randrange(1000)},
        check=lambda c, o: [] if c.get("again") else [(f"REQ-{c['i'] % 9}", "bad")],
        followup=lambda c, o: ({"again": True, "i": c["i"]}, "REQ-IDEM") if c["i"] % 2 else None)
    t = types.SimpleNamespace(oracle=oracle, exe="x")

    def fake_run(project, exe, cases, name):
        return [{"echo": c} for c in cases]
    oracle.check = lambda c, o: [("REQ-IDEM", "resubmitted")] if c.get("again") else [(f"REQ-{c['i'] % 9}", "bad")]
    with patch.object(binary_check, "run_cases", fake_run):
        r = binary_check.property_tests(None, t, 400, 0, {})
    have = {w["requirement"] for w in r["witnesses"]}
    assert have == set(r["violations"]) and len(have) == 10
    first_six = {w["requirement"] for w in r["witnesses"][:6]}
    assert len(r["witnesses"]) == 6 + len(have - first_six)
    idem = next(w for w in r["witnesses"] if w["requirement"] == "REQ-IDEM")
    assert idem["origin"]["input"]["i"] == idem["input"]["i"] and "again" not in idem["origin"]["input"]
    assert all("origin" not in w for w in r["witnesses"] if w["requirement"] != "REQ-IDEM")


def judged(task, status="REFUTED"):
    j = {"accepted": False, "elapsed_ms": 0, "solution_tree_sha256": "src",
         "checks": {"tree": {"passed": True, "problems": []}, "impl_scan": {"passed": True, "problems": []}}}
    b = {"status": status, "cases": 2001, "followup_cases": 0, "seed": 0, "violations": {"REQ-SHLW-EXACT": 1},
         "binary_sha256": "e" * 64, "witnesses": [cetus_witnesses()["REQ-SHLW-EXACT"]]}
    return j, b


RECORD = {"requirement": "REQ-SHLW-EXACT", "refutes": "ClmmMath.req_shlw_exact",
          "theorem": "ClmmMath.cex_req_shlw_exact", "statement": "¬ (ShlwExact checkedShlw)",
          "kernel_checked": True, "kernels": ["Lean default"], "axioms": [], "lean_source": "import Solution\n",
          "lean_file_sha256": cx.sha256_text("import Solution\n"), "challenge_sha256": "c" * 64}


def build_passport(cx_records):
    t = taskmod.load("rw-cetus-shlw")
    j, b = judged(t)
    with patch.object(passport.judge, "image_id", return_value="img"), \
            patch.object(passport.judge, "image_platform", return_value="linux/arm64"):
        return passport.build(t, CETUS_CANDIDATE, j, b, counterexamples=cx_records)


def test_passport_field_is_optional_and_hashed():
    plain = build_passport(None)
    assert "counterexamples" not in plain
    withcx = build_passport([dict(RECORD)])
    assert withcx["counterexamples"][0]["kernel_checked"] is True
    assert withcx["passport_sha256"] == passport.content_hash(withcx) != plain["passport_sha256"]
    assert "Counterexamples checked by the kernel" in passport.markdown(withcx)
    assert "ClmmMath.cex_req_shlw_exact : ¬ (ShlwExact checkedShlw)" in passport.markdown(withcx)


def test_committed_passports_still_hash_and_carry_no_counterexamples():
    for path in sorted((ROOT / "results").rglob("*.json")):
        if "counterexamples-1" in path.parts:
            continue
        try:
            p = json.loads(path.read_text())
        except ValueError:
            continue
        if isinstance(p, dict) and "passport_sha256" in p and "requirements" in p:
            assert p["passport_sha256"] == passport.content_hash(p), path
            assert "counterexamples" not in p, path


def verify(issued, rechecked, again=None):
    with tempfile.TemporaryDirectory() as tmp:
        dest = pathlib.Path(tmp) / "passport.json"
        dest.write_text(json.dumps(issued))
        out = io.StringIO()
        with patch.object(passport, "run", return_value=rechecked), \
                patch.object(cli["cexmod"], "recheck", return_value=again or []) as rc, \
                contextlib.redirect_stdout(out):
            code = cli["cmd_verify"](types.SimpleNamespace(passport=str(dest), candidate=str(CETUS_CANDIDATE)))
        return code, out.getvalue(), rc


def test_verify_rechecks_recorded_refutations_only_when_present():
    plain = build_passport(None)
    code, out, rc = verify(plain, copy.deepcopy(plain))
    assert code == 0 and not rc.called
    issued = build_passport([dict(RECORD)])
    same = {k: RECORD[k] for k in ("requirement", "statement", "challenge_sha256", "kernel_checked", "kernels", "axioms")}
    code, out, rc = verify(issued, copy.deepcopy(plain), [same])
    assert code == 0 and rc.called and "same       REQ-SHLW-EXACT counterexample kernel check" in out
    code, out, _ = verify(issued, copy.deepcopy(plain), [{**same, "kernel_checked": False}])
    assert code == 1 and "DIFFERENT  REQ-SHLW-EXACT counterexample kernel check" in out
    tampered = copy.deepcopy(issued)
    tampered["counterexamples"][0]["lean_source"] = "import Solution\n-- changed\n"
    tampered["passport_sha256"] = passport.content_hash(tampered)
    code, out, _ = verify(tampered, copy.deepcopy(plain), [same])
    assert code == 1 and "DIFFERENT  REQ-SHLW-EXACT counterexample source" in out


def test_check_runs_the_stage_unless_disabled():
    t = taskmod.load("rw-cetus-shlw")
    calls = []

    def fake_run(cand, task, cases=2000, seed=0, counterexample=False, **kw):
        calls.append(counterexample)
        return build_passport(None)
    with tempfile.TemporaryDirectory() as tmp, patch.object(passport, "run", fake_run), \
            contextlib.redirect_stdout(io.StringIO()):
        base = dict(task=t.id, candidate=str(CETUS_CANDIDATE), cases=2000, seed=0, out=str(pathlib.Path(tmp) / "p.json"), comment=None)
        cli["cmd_check"](types.SimpleNamespace(**base))
        cli["cmd_check"](types.SimpleNamespace(**base, no_counterexample=True))
    assert calls == [True, False]


# Kernel tests (Docker and the pinned image).

def docker_ready():
    try:
        return subprocess.run(["docker", "image", "inspect", judge.IMAGE], capture_output=True, timeout=30).returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def skip_without_docker():
    if docker_ready():
        return False
    try:
        import pytest
        pytest.skip("Docker or the pinned Lean image is not available")
    except ImportError:
        print("skip: Docker or the pinned Lean image is not available")
    return True


def test_kernel_accepts_the_cetus_refutations_and_rejects_false_ones():
    if skip_without_docker():
        return
    t = taskmod.load("rw-cetus-shlw")
    w = cetus_witnesses()
    good = [cx.generate(t, w["REQ-SHLW-EXACT"]), cx.generate(t, w["REQ-DELTA-A-COVERS"])]
    # n = 1 is shifted exactly by the original port: this instance does not refute REQ-SHLW-EXACT.
    false = cx.generate(t, {**w["REQ-SHLW-EXACT"], "input": {"op": "shlw", "n": 1}})
    # A source that proves a weaker statement under the counterexample's name.
    weak = {k: good[0][k] for k in ("requirement", "refutes", "theorem", "statement")}
    weak["lean_source"] = good[0]["lean_source"].replace(
        ": ¬ (ShlwExact checkedShlw) := by", ": ¬ (ShlwExact checkedShlw) ∨ True := by\n  exact Or.inr trivial\n  all_goals")
    items = cx.check_items(t, CETUS_CANDIDATE, good + [false, weak])
    assert [it["kernel_checked"] for it in items] == [True, True, False, False], [it.get("reason") for it in items]
    assert len(items[0]["kernels"]) == 6 and items[0]["axioms"] == [] and items[1]["axioms"] == ["propext"]
    assert items[2]["reason"].startswith("refutation does not build")
    assert items[3]["reason"].startswith("Comparator rejected") or items[3]["reason"].startswith("refutation does not build")
    again = cx.recheck(t, CETUS_CANDIDATE, [items[0]])
    assert again[0]["kernel_checked"] and again[0]["lean_file_sha256"] == items[0]["lean_file_sha256"]
    assert again[0]["challenge_sha256"] == items[0]["challenge_sha256"]


def test_kernel_refutes_idempotency_from_the_follow_up_origin():
    if skip_without_docker():
        return
    t = taskmod.load("transfers-overdraft-b3")
    case = {"state": {"balances": [[1, 100], [2, 0]], "limits": [[1, 0], [2, 0]], "auth": [[1, 1]], "applied": []},
            "request": {"txId": 4, "requester": 1, "source": 1, "target": 2, "amount": 30}}
    after = {"balances": [[1, 70], [2, 30]], "limits": [[1, 0], [2, 0]], "auth": [[1, 1]], "applied": []}
    w = {"requirement": "REQ-IDEMPOTENCY", "message": "follow-up case: resubmission succeeded",
         "input": {"state": after, "request": case["request"]}, "output": {},
         "origin": {"input": case, "output": {"outcome": "ok", "state": after}}}
    it = cx.generate(t, w)
    assert "congrArg" in it["lean_source"] and it["origin"]["input"] == case
    items = cx.check_items(t, t.start, [it])
    assert items[0]["kernel_checked"], items[0].get("reason")


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print(f"ok  {name}")
