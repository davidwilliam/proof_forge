"""ProofForgeFin through every kernel the judge uses (harness/fin_kernels.py); no model calls.

SLOW. The Lean test builds the library and its demonstrations in the pinned image, exports every
declaration they make and runs the export through `lake comparator --paranoid` (Lean default and
paranoid, lean4lean, nanoda, con-leche, con-ron) as the judge does, then `leanchecker` over every
module; one container at a time through the judge's container slots. A library declaration that
a kernel rejects would make the judge reject every candidate that depends on it, so the test
requires that every kernel accept every declaration. It is skipped without Docker and the pinned
image.

Without Lean: the parsing of Comparator's report, the attribution of a rejection to a declaration,
the closure over dependents, and the files the checker builds.

Run: .venv/bin/python tests/test_fin_kernels.py [--quick]   (--quick skips the Lean run)
"""
import pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "harness"), str(ROOT / "tests")]
import fin_kernels  # noqa: E402

KERNELS = ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"]

# Comparator's report of a run in which con-leche and con-ron were stopped (abridged).
REPORT = """Running Lean paranoid kernel on solution
Lean paranoid kernel accepts the solution
Running lean4lean kernel on solution
checked 2210 declarations
lean4lean kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running con-leche kernel on solution
con-leche kernel rejected the solution
Running con-ron kernel on solution
con-ron: declined: definition with safety 'partial' (--verified)
con-ron kernel rejected the solution
Running Lean default kernel on solution
error: con-leche exited with 137
Lean default kernel accepts the solution
"""
# con-leche run directly with one worker on the same export (the last lines).
DIRECT = """exit=1
con-leche: check failed at fold position 1849 t=5.0s (check 4.2s)
con-leche: internal error: fuel exhausted: whnfCore [at theorem ProofForgeFinDemo.DeFi.Compound.psi_moves, fold position 1849] (--verified) t=5.0s
"""


def test_comparator_report_is_parsed_per_kernel():
    v = fin_kernels.kernel_verdicts(REPORT)
    assert list(v) == KERNELS
    assert {k for k, x in v.items() if not x["accepted"]} == {"con-leche", "con-ron"}
    assert v["lean4lean"]["output"] == "checked 2210 declarations"
    assert "declined: definition with safety 'partial'" in v["con-ron"]["output"]
    assert v["con-leche"]["output"] == ""   # the kernel was stopped and named nothing
    assert set(fin_kernels.KERNELS) == set(KERNELS)


def test_rejection_is_attributed_to_the_declaration_the_kernel_names():
    decls = {"ProofForgeFinDemo.DeFi.Compound.psi_moves": {}, "ProofForgeFinDemo.DeFi.Compound.Psi": {}}
    assert fin_kernels.named_declarations(DIRECT, decls) == ["ProofForgeFinDemo.DeFi.Compound.psi_moves"]
    assert fin_kernels.named_declarations("con-leche kernel rejected the solution", decls) == []
    assert set(fin_kernels.DIRECT) == {"con-leche", "con-ron"}


def test_dependents_are_closed_under_use():
    decls = {n: {"name": n, "uses": u} for n, u in
             {"a": [], "b": ["a"], "c": ["b"], "d": [], "e": ["d", "c"]}.items()}
    assert fin_kernels.dependents(decls, {"b"}) == {"b", "c", "e"}
    assert fin_kernels.dependents(decls, {"d"}) == {"d", "e"}


def test_checker_builds_the_library_and_every_demonstration():
    files = fin_kernels.staged_files()
    assert "ProofForgeFin.lean" in files and "ProofForgeFinDemo.lean" in files and "Audit.lean" in files
    assert "ProofForgeFinDemo/DeFi/Compound.lean" in files
    assert any(f.startswith("ProofForgeFin/Tactic/") for f in files)
    assert not any(f.startswith("docs/") or f.endswith(".md") for f in files)
    assert len(fin_kernels.tree_sha256()) == 64


def test_every_declaration_passes_every_judge_kernel():
    from test_fin_lib import skip_without_docker
    if skip_without_docker():
        return
    rep = fin_kernels.check()
    print(fin_kernels.summary(rep))
    assert not rep["failures"], fin_kernels.summary(rep)
    assert not rep["unattributed"], rep["unattributed"]
    last = rep["rounds"][-1]
    assert len(rep["rounds"]) == 1 and last["exit_code"] == 0, rep["rounds"]
    assert list(last["kernels"]) == KERNELS and all(last["kernels"].values()), last
    assert last["exported"] == rep["safe_exported"] > 5000 and rep["theorems"] > 3000, rep["safe_exported"]
    unsafe = rep.get("unsafe")
    if unsafe:
        assert unsafe["passed"], unsafe
        for k in ("Lean default", "Lean paranoid", "lean4lean"):
            assert unsafe["kernels"][k] == "accepts", (k, unsafe["kernels"][k])
    lc = rep["leanchecker"]
    assert lc["exit_code"] == 0 and not lc["failed"] and lc["modules"] >= 70, lc
    assert rep["passed"]


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    lean = {"test_every_declaration_passes_every_judge_kernel"}
    for name, fn in list(globals().items()):
        if name.startswith("test_") and not (quick and name in lean):
            fn()
            print(f"ok  {name}")
