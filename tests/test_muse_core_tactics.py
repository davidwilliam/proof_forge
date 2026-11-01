"""Hints for Mathlib tactics in the `full` profile and the proofforge-full continuation message
(integrations/muse/proofforge_mcp.tactic_hints). No model calls.

Without Lean: the hint for the two final candidates of results/hard-task-1 that the judge rejected
for an unknown tactic (`by_contra` in proofforge-full-1, `set` in proofforge-full-4), from the
judge's own output; hints at a snippet position; no hint for a tactic that is not a Mathlib one;
the hint in lean_build, try_snippet and check_snippet_fast of the `full` profile, in the
continuation message of proofforge-full, and not in the `lean` and `proofforge` profiles; the
skill's note.

With Lean (the pinned image, one container; skipped with --quick): every Mathlib tactic named is
unknown to Lean core, and the core replacements the hints name elaborate.

Run: python3 tests/test_muse_core_tactics.py [--quick]
"""
import pathlib, shutil, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "integrations" / "muse"), str(ROOT / "agents"), str(ROOT / "harness"), str(ROOT / "tests")]
import proofforge_mcp as pm, muse_code  # noqa: E402
import test_muse_keep_best as kb  # noqa: E402

RUNS = ROOT / "results/hard-task-1/runs/rw-oz-sqrt"


def test_hints_for_the_judge_rejections_of_hard_task_1():
    for run, tactic in (("proofforge-full-1", "by_contra"), ("proofforge-full-4", "set")):
        fin = (RUNS / run / "final.lean").read_text()
        out = pm.tactic_hints((RUNS / run / "check.txt").read_text(), {"candidate/Solution.lean": fin})
        assert out == f"\nHint: `{tactic}` is a Mathlib tactic; Lean core has no Mathlib. Use {pm.CORE_TACTICS[tactic]}.", out


def test_hints_at_a_snippet_position_and_only_for_mathlib_tactics():
    code = "theorem r (a b : Nat) : a * b = b * a := by ring\n\ntheorem s (x : Nat) : True := by\n  interval_cases x\n  foo_bar"
    out = f"snippet:1:{code.index('ring') + 1}: error: unknown tactic\nsnippet:4:3: error: unknown tactic\nsnippet:5:3: error: unknown tactic"
    hints = pm.tactic_hints(out, {"snippet": code})
    assert "`ring` is a Mathlib tactic" in hints and "`interval_cases` is a Mathlib tactic" in hints, hints
    assert "foo_bar" not in hints and hints.count("Hint:") == 2
    assert pm.tactic_hints(out + "\n" + out, {"snippet": code}).count("Hint:") == 2      # once each
    assert pm.tactic_hints("snippet:9:3: error: unknown tactic", {"snippet": code}) == ""


def test_hints_in_the_full_profile_and_the_continuation_only():
    th = kb.TASK.theorems
    ws, out = kb.dirs()
    try:
        bad = kb.candidate(th[:1], broken=True, extra="theorem t (p : Prop) : p := by\n  by_contra h")
        ln = bad.splitlines().index("  by_contra h") + 1
        err = f"error: candidate/Solution.lean:{ln}:3: unknown tactic"
        (ws / "candidate/Solution.lean").write_text(bad)
        r = kb.Scripted(ws, "full", err).lean_build()
        assert "`by_contra` is a Mathlib tactic" in r and "Classical.byContradiction" in r, r
        for profile in ("lean", "proofforge"):
            assert "Hint:" not in kb.Scripted(ws, profile, err).lean_build()
        msg, _ = kb.continue_after(ws, bad, [kb.candidate(th[:1])], error=err)
        assert "`by_contra` is a Mathlib tactic" in msg and "unfinished-02.lean" in msg, msg
    finally:
        shutil.rmtree(ws)
        shutil.rmtree(out)


def test_skill_names_the_core_replacements():
    skill = (ROOT / ".agents/skills/proofforge/SKILL.md").read_text()
    for tactic in ("by_contra", "set", "ring", "linarith", "interval_cases", "push_neg"):
        assert f"`{tactic}`" in skill, tactic
    assert "Classical.byContradiction" in skill and "generalize hx : e = x" in skill


PROBE = """
example (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by grind
example (p : Prop) (h : ¬¬p) : p := by
  apply Classical.byContradiction
  intro hn
  exact h hn
example (x : Nat) (h : x + 1 = 3) : x * 2 = 4 := by
  generalize hy : x + 1 = y at h
  omega
example (a : Nat) (h : ¬ a < 2) : 2 ≤ a := by
  simp only [Nat.not_lt] at h
  exact h
example (a : Nat) (h : a < 2) : a * a < 4 := by
  rcases Nat.lt_or_ge a 1 with h1 | h1
  · have : a = 0 := by omega
    subst this; decide
  · have : a = 1 := by omega
    subst this; decide
example (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b ^ 3 := Nat.mul_pos ha (Nat.pow_pos hb)
example (p : Nat → Prop) (h : ¬ ∀ x, p x) : ∃ x, ¬ p x := Classical.not_forall.mp h
example : (12 : Nat) * 3 = 36 := by decide
example (x : Nat) : ∃ y, y = x := ⟨x, rfl⟩
example (a b c d : Nat) (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d := Nat.mul_le_mul h1 h2
"""


def test_mathlib_tactics_are_unknown_and_the_replacements_elaborate_with_lean():
    t = kb.TASK
    ws = muse_code.make_workspace(t, "alone")
    try:
        s = pm.Server(ws, t.id, "lean")
        (ws / "Probe.lean").write_text(PROBE)
        out = s.lean_build("Probe.lean")
        assert "exit code 0" in out and "error" not in out, out
        names = sorted(pm.CORE_TACTICS)
        (ws / "Mathlib.lean").write_text("".join(f"example : True := by\n  {n}\n" for n in names))
        out = s.lean_build("Mathlib.lean")
        unknown = {int(l.split(":")[1]) for l in out.splitlines() if l.endswith("unknown tactic")}
        assert unknown == {2 * i + 2 for i in range(len(names))}, out
    finally:
        shutil.rmtree(ws, ignore_errors=True)


LEAN_TESTS = {"test_mathlib_tactics_are_unknown_and_the_replacements_elaborate_with_lean"}

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
