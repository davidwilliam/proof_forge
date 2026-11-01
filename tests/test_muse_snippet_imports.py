"""check_snippet_fast in the `full` profile imports the library modules a snippet needs
(integrations/muse/session_tools.library_modules). No model calls.

Without Lean: the modules found for the snippets of results/hard-task-1 that failed on a library
name the candidate did not import (`ProofForgeFin.Evm.log2_spec` under `open ProofForgeFin.Evm in`,
`toNat_ushiftRight` under `open ProofForgeFin in`), none for a module the candidate already imports
(directly or through another module), none for core names, and none when the library is off.

With Lean (the pinned image; one container, the persistent Lean server; skipped with --quick):
the first of those snippets, sent to the server, is checked with the module imported, and the
result names the import the candidate needs.

Run: python3 tests/test_muse_snippet_imports.py [--quick]
"""
import pathlib, shutil, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "integrations" / "muse"), str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "tests")]
import session_tools as st, proofforge_mcp as pm, muse_code, fin_lib  # noqa: E402
import task as taskmod  # noqa: E402

TASK = taskmod.load("rw-oz-sqrt")
START = TASK.start.read_text()

LOG2 = """open ProofForgeFin.Sqrt
open ProofForgeFin.Evm in
theorem _x0le (n : Nat) (hn : 0 < n) : 2 ^ (Nat.log2 n / 2) * 2 ^ (Nat.log2 n / 2) ≤ n := by
  have h1 := @ProofForgeFin.Evm.log2_spec
  sorry"""

USHR = """open ProofForgeFin in
theorem init_val (a : U256) : (log2 a >>> 1).toNat = (log2 a).toNat / 2 := by
  rw [toNat_ushiftRight]
  sorry"""


class Lib:
    library = True
    lib_index = fin_lib.Index.load()
    _lib_names = None


def test_modules_for_library_names_the_candidate_does_not_import():
    s = Lib()
    assert st.library_modules(s, LOG2, START) == ["ProofForgeFin.Evm.Bits", "ProofForgeFin.Sqrt"]
    assert st.library_modules(s, USHR, START) == ["ProofForgeFin.Word"]
    imported = START.replace("import OzSqrt.Lemmas", "import OzSqrt.Lemmas\nimport ProofForgeFin.Sqrt\nimport ProofForgeFin.Evm.Bits")
    assert st.library_modules(s, LOG2, imported) == []
    whole = START.replace("import OzSqrt.Lemmas", "import OzSqrt.Lemmas\nimport ProofForgeFin")
    assert st.library_modules(s, LOG2 + "\n" + USHR, whole) == []        # through the root module
    core = "theorem t (a b : Nat) (h : a < b) : a + 1 ≤ b := by\n  have := Nat.sqrt_le a\n  omega"
    assert st.library_modules(s, core, START) == []
    s.library = False
    assert st.library_modules(s, LOG2, START) == []


def test_check_snippet_fast_imports_them_with_lean():
    ws = muse_code.make_workspace(TASK, "proofforge-full")
    s = pm.Server(ws, TASK.id, "full")
    try:
        out = s.call("check_snippet_fast", {"code": LOG2})
        assert "unknown namespace" not in out and "Unknown identifier" not in out, out
        assert "Imported for this check: `import ProofForgeFin.Evm.Bits`, `import ProofForgeFin.Sqrt`" in out, out
        assert "candidate/Solution.lean needs the same import" in out and (ws / "candidate/Solution.lean").read_text() == START
    finally:
        s.cleanup()
        shutil.rmtree(ws, ignore_errors=True)


LEAN_TESTS = {"test_check_snippet_fast_imports_them_with_lean"}

if __name__ == "__main__":
    import test_topdown as td
    quick = "--quick" in sys.argv
    for name, fn in list(globals().items()):
        if not name.startswith("test_"):
            continue
        if name in LEAN_TESTS and (quick or not td.have_lean()):
            print(f"skip  {name}")
            continue
        fn()
        print(f"ok  {name}")
