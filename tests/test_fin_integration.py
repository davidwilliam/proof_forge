"""ProofForgeFin in the judge, the Passport, verify and the repair agent's retrieval; no model calls.

Lean runs in the pinned image through the judge's container slots, one at a time:
  * the judge accepts a candidate for rw-compound-comp that imports ProofForgeFin
    (tests/fixtures/library/compound_lib.lean: the reference implementation and per-call proofs,
    the three sequence bounds from the library argument of the Compound demonstration), with
    Comparator's six kernels, leanchecker and only the permitted axioms;
  * its Passport binds the library version, and `bin/proofforge verify` reproduces it and reports
    a changed library record (source tree, imports, or a Passport without a library record);
  * committed Passports issued before the library was integrated still reproduce.
Without Lean: importing ProofForgeFinDemo and candidate metaprograms are rejected even with
`import ProofForgeFin`; the library scan; fresh projects without a library import are unchanged;
retrieval over the generated index; the library flag of agents/repair.py (A0 unchanged).

Run: python3 tests/test_fin_integration.py [--quick]   (--quick skips the Lean runs)
"""
import contextlib, copy, io, json, pathlib, re, runpy, shutil, sys, tempfile, types

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "agents")]
import fin_lib, judge, passport, task as taskmod  # noqa: E402

cli = runpy.run_path(str(ROOT / "bin/proofforge"))
COMPOUND = taskmod.load("rw-compound-comp")
FIXTURE = ROOT / "tests/fixtures/library/compound_lib.lean"
KERNELS = ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"]
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}
OLD = [  # committed Passports issued before the library integration, with their candidates
    ("results/cetus-1/repair-A1-1/passport.json", "results/cetus-1/repair-A1-1/final.lean"),
    ("results/knight-1/A2-2/passport.json", "results/knight-1/A2-2/final.lean"),
    ("results/balancer-1/repair-A2-1/passport.json", "results/balancer-1/repair-A2-1/final.lean"),
    ("results/compound-1/passports/reference.json", "realworld/tasks/rw-compound-comp/reference/SolutionA.lean"),
    ("results/counterexamples-1/cetus-original-port/passport.json",
     "realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean"),
]
_state = {}


def candidate(source):
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-fin-test-"))
    f = d / "Solution.lean"
    f.write_text(source)
    return f


def verify(path, cand, strict=False):
    """Run `bin/proofforge verify`; returns (exit code, output)."""
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = cli["cmd_verify"](types.SimpleNamespace(passport=str(path), candidate=str(cand), strict_image=strict))
    return rc, out.getvalue()


def write_passport(p):
    p = copy.deepcopy(p)
    p["passport_sha256"] = passport.content_hash(p)
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-fin-pp-"))
    (d / "passport.json").write_text(json.dumps(p, indent=2) + "\n")
    return d / "passport.json"


# ---------------------------------------------------------------------------------------------
# Without Lean

def test_package_excludes_the_demonstrations_and_audit():
    files = fin_lib.source_files()
    assert "lakefile.toml" in files and "ProofForgeFin.lean" in files
    assert any(f.startswith("ProofForgeFin/Tactic/") for f in files)
    assert not any(f.startswith("ProofForgeFinDemo") or f == "Audit.lean" for f in files)


def test_demo_import_is_rejected():
    src = FIXTURE.read_text().replace("import ProofForgeFin.DeFi\n", "import ProofForgeFin.DeFi\nimport ProofForgeFinDemo.DeFi.Compound\n", 1)
    j = judge.judge(str(candidate(src)), task=COMPOUND)
    assert not j["accepted"]
    assert "Solution.lean: import not allowed: ProofForgeFinDemo.DeFi.Compound" in j["checks"]["impl_scan"]["problems"]
    assert "comparator" not in j["checks"]   # rejected before any Lean run
    for mod in ("ProofForgeFinDemo", "ProofForgeFinDemo.DeFi.Compound", "Lean", "Lean.Elab.Command"):
        assert not judge.allowed_imports(COMPOUND).match(mod), mod
    for mod in ("ProofForgeFin", "ProofForgeFin.DeFi.Rewards", "ProofForgeFin.Tactic"):
        assert judge.allowed_imports(COMPOUND).match(mod), mod


METAPROGRAMS = {
    "elab": 'elab "my_tac" : tactic => pure ()',
    "macro": 'macro "my_tac" : tactic => `(tactic| rfl)',
    "elab_rules": 'syntax "my_tac" : tactic\nelab_rules : tactic | `(tactic| my_tac) => pure ()',
    "macro_rules": 'macro_rules | `(tactic| trivial) => `(tactic| rfl)',
    "run_tac": "theorem t : True := by run_tac pure ()",
    "by_elab": "def x : Nat := by_elab pure (Lean.mkNatLit 1)",
    "simproc": "simproc myProc (Nat.succ _) := fun _ => pure .continue",
    "register_simp_attr": "register_simp_attr my_simps",
    "tactic attribute": "open Lean Elab Tactic in\n@[tactic Lean.Parser.Tactic.done] def myDone : Tactic := fun _ => pure ()",
    "command_elab attribute": "open Lean Elab Command in\n@[command_elab Lean.Parser.Command.check] def myCheck : CommandElab := fun _ => pure ()",
    "initialize": "initialize pure ()",
    "declare_syntax_cat": "declare_syntax_cat mycat",
}


def test_candidate_metaprograms_are_rejected_with_the_library_imported():
    base = FIXTURE.read_text()
    for name, code in METAPROGRAMS.items():
        src = base.replace("\nend CompRewards\n", f"\n{code}\n\nend CompRewards\n")
        j = judge.judge(str(candidate(src)), task=COMPOUND)
        assert not j["accepted"], name
        assert j["checks"]["impl_scan"]["problems"], name
        assert "comparator" not in j["checks"], name
        assert j["library"]["imported"] == ["ProofForgeFin.DeFi"], name


def test_library_scan_rejects_hazards_in_library_code():
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp) / "lib"
        shutil.copytree(ROOT / "lib", root, ignore=shutil.ignore_patterns(".lake"))
        assert fin_lib.scan(fin_lib.closure(["ProofForgeFin"], root), root)["passed"]
        f = root / "ProofForgeFin/Rounding.lean"
        f.write_text(f.read_text() + "\n@[implemented_by id] def evil (n : Nat) : Nat := n + 1\n"
                     "theorem t2 : 2 + 2 = 4 := by native_decide\n")
        r = fin_lib.scan(fin_lib.closure(["ProofForgeFin.Shares"], root), root)
        assert not r["passed"]
        assert any("implemented_by" in p for p in r["problems"]) and any("native_decide" in p for p in r["problems"])
        assert fin_lib.tree_sha256(root) != fin_lib.tree_sha256()


def test_a_library_build_stopped_by_the_time_limit_is_a_timeout_not_a_rejection():
    from unittest.mock import patch
    import binary_check

    def stopped(*_a, **_k):
        raise RuntimeError("ProofForgeFin build failed (exit 124):\n" + judge.TIMEOUT_MARK)
    with patch.object(fin_lib, "ensure_built", stopped):
        j = judge.judge(str(FIXTURE), task=COMPOUND)
        b = binary_check.check_binary(str(FIXTURE), n_cases=5, task=COMPOUND)
    assert not j["accepted"] and j["checks"]["comparator"]["exit_code"] == 124
    assert b["status"] == "TIMEOUT"
    b["seed"] = 0
    p = passport.build(COMPOUND, str(FIXTURE), j, b)
    assert p["status"] == "UNRESOLVED"
    assert any("time limit" in r for r in p["proof_check"]["reasons"]), p["proof_check"]["reasons"]


def test_fresh_project_without_a_library_import_is_unchanged():
    ref = COMPOUND.root / "reference/SolutionA.lean"
    ws = judge.load_workspace(str(ref))
    d = judge.fresh_project(ws, judge.candidate_files(ws), COMPOUND)
    try:
        assert not (d / ".lake").exists()
        for rel in ("lakefile.toml", "lake-manifest.json"):
            assert (d / rel).read_bytes() == (COMPOUND.root / rel).read_bytes(), rel
    finally:
        shutil.rmtree(d, ignore_errors=True)
    rec = fin_lib.record(judge.candidate_files(ws))
    assert rec["vendored"] is False and rec["imported"] == []


def test_retrieval_finds_relevant_lemmas():
    idx = fin_lib.Index.load()
    kinds = {e["kind"] for e in idx.entries}
    assert {"theorem", "def", "module", "tactic", "simp_set"} <= kinds, kinds
    tactics = {e["name"] for e in idx.entries if e["kind"] == "tactic"}
    assert {"struct_simp", "step_cases", "run_induction", "fin_simp", "div_norm", "round_bound",
            "generalize_divs"} <= tactics, tactics

    def top(query, k):
        return [e["name"] for e in idx.search(query, limit=k)]
    cases = [
        ("ceiling division bounds", 5, "ProofForgeFin.ceilDiv_spec"),
        ("invariant preserved by every operation holds after any sequence of operations", 3,
         "ProofForgeFin.Seq.run_invariant"),
        ("share value never falls redeem rounded down", 8, "ProofForgeFin.Shares.redeem_value"),
        ("transfer between two accounts conserves the total sum", 6, "ProofForgeFin.Ledger.sumOver_transfer"),
        ("scaled potential bound accumulated emission", 6, "ProofForgeFin.Seq.run_bound_via_potential"),
        ("induction over a sequence of operations tactic", 6, "run_induction"),
        ("ProofForgeFin.mulDown_spec", 1, "ProofForgeFin.mulDown_spec"),
    ]
    for q, k, want in cases:
        got = top(q, k)
        assert want in got, (q, want, got)


def test_obligation_hints_for_compound():
    import repair
    s = types.SimpleNamespace(task=COMPOUND, lib_index=fin_lib.Index.load(), library=True)
    q = repair.obligation_query(s, "theorem req_rewards_bounded : RewardsBounded comptroller")
    assert len(q.splitlines()) > 1   # the doc string of RewardsBounded is part of the query
    hits = [e["name"] for e in s.lib_index.search(q, limit=14)]
    assert "ProofForgeFin.Seq.run_bound_via_potential" in hits, hits


def test_repair_library_flag_and_a0_unchanged():
    import baseline, repair
    t = COMPOUND
    names = [x["function"]["name"] for x in repair.tools_for(t)]
    assert "search_library" not in names and "add_import" not in names
    assert {"search_library", "add_import"} <= {x["function"]["name"] for x in repair.tools_for(t, True)}
    # A0's system prompt: the shared brief and its protocol, no library section.
    off = types.SimpleNamespace(task=t, mode="repair", library=False, lib_index=None)
    assert repair.system_prompt(off) == repair.task_brief(t) + repair.WORKFLOW
    assert "ProofForgeFin" not in repair.task_brief(t) + baseline.PROTOCOL
    on = types.SimpleNamespace(task=t, mode="repair", library=True, lib_index=fin_lib.Index.load())
    text = repair.system_prompt(on)
    assert "import ProofForgeFin" in text and "ProofForgeFinDemo is not importable" in text
    for tac in ("struct_simp", "step_cases", "run_induction", "fin_simp", "div_norm", "round_bound", "generalize_divs"):
        assert re.search(rf"^- `{tac}` \(", text, re.M), tac
    src = (ROOT / "agents/repair.py").read_text()
    assert re.search(r'add_argument\("--library", default="on", choices=\["on", "off"\]', src)
    assert '"library": library_summary(s)' in src
    assert "--library" not in (ROOT / "agents/baseline.py").read_text()


def test_e1_arms_record_the_library_flag():
    sys.path.insert(0, str(ROOT / "eval"))
    import e1
    assert e1.arm_command("A0", "on")[-1].endswith("baseline.py")
    assert e1.arm_command("A1", "off")[-2:] == ["--library", "off"]
    assert e1.arm_command("A2", "on")[-2:] == ["--library", "on"]
    from unittest.mock import patch
    a = types.SimpleNamespace(model="m", budget_usd=3, budget_wall=60, parallel=1, batch_usd=None, library="off")
    with patch.object(e1.judge, "image_id", return_value="test-image"):
        off = e1.frozen_config(a, [], ["A0", "A1"])
        a.library = "on"
        on = e1.frozen_config(a, [], ["A0", "A1"])
    assert off["library"]["arms"] == [] and on["library"]["arms"] == ["A1"]
    assert on["library"]["source_tree_sha256"] == fin_lib.tree_sha256()
    assert off["config_sha256"] != on["config_sha256"]


# ---------------------------------------------------------------------------------------------
# Lean runs

def compound_passport():
    if "passport" not in _state:
        p = passport.run(FIXTURE, COMPOUND, cases=300)
        _state["passport"] = p
    return _state["passport"]


def test_judge_accepts_a_library_importing_solution():
    p = compound_passport()
    assert p["status"] == "VERIFIED", p["proof_check"]
    assert p["proof_check"]["accepted"]
    assert p["checks"]["comparator_kernels"] == KERNELS, p["checks"]["comparator_kernels"]
    assert p["checks"]["leanchecker"]["exit_code"] == 0
    for r in p["requirements"]:
        assert r["axioms_used"] is not None and set(r["axioms_used"]) <= PERMITTED, r
    assert p["checks"]["library_scan"]["passed"]


def test_passport_binds_the_library_version():
    p = compound_passport()
    lib = p["library"]
    assert lib["vendored"] and lib["imported"] == ["ProofForgeFin.DeFi"]
    assert lib["source_tree_sha256"] == fin_lib.tree_sha256()
    assert lib["built_with"]["judge_image"] == judge.image_id() == p["toolchain"]["judge_image"]
    assert lib["built_with"]["lean"] == p["toolchain"]["lean"]
    assert passport.LIBRARY_TRUST in p["trust_assumptions"]
    # A candidate that imports nothing from the library: the record says so.
    rec = fin_lib.record([COMPOUND.root / "reference/SolutionA.lean"])
    assert rec == {"package": "proofforge-fin", "library": "ProofForgeFin",
                   "source_tree_sha256": fin_lib.tree_sha256(), "imported": [], "vendored": False}


def test_verify_checks_the_library_record():
    p = compound_passport()
    rc, out = verify(write_passport(p), FIXTURE)
    assert rc == 0 and out.rstrip().endswith("reproduced"), out
    assert "same       library source tree" in out and "same       library imports" in out
    # Another library version without a commit that provides it: a difference.
    q = copy.deepcopy(p)
    q["library"]["source_tree_sha256"] = "0" * 64
    q["library"]["git_commit"] = None
    rc, out = verify(write_passport(q), FIXTURE)
    assert rc == 1 and "DIFFERENT  library source tree" in out, out
    # A Passport without a library record (as before the integration) for a library-importing
    # candidate: a difference.
    q = copy.deepcopy(p)
    del q["library"]
    rc, out = verify(write_passport(q), FIXTURE)
    assert rc == 1 and "DIFFERENT  library vendored" in out, out


def test_old_passports_reproduce():
    for pp, cand in OLD:
        old = json.loads((ROOT / pp).read_text())
        assert "library" not in old, pp
        rc, out = verify(ROOT / pp, ROOT / cand)
        assert rc == 0, (pp, out[-1500:])
        assert "same       library vendored: False" in out, pp
        print(f"   reproduced {pp}")


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    lean = {"test_judge_accepts_a_library_importing_solution", "test_passport_binds_the_library_version",
            "test_verify_checks_the_library_record", "test_old_passports_reproduce"}
    for name, fn in list(globals().items()):
        if name.startswith("test_") and not (quick and name in lean):
            fn()
            print(f"ok  {name}")
