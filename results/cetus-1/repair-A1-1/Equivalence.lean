import ClmmMath.Spec
/-!
The accepted Muse repair (`final.lean`) and the port of `checked_shlw` after pull request 7
(`realworld/tasks/rw-cetus-shlw/reference/SolutionA.lean`) return the same value and flag on
every 256-bit input. Both definitions are copied verbatim under new names.
-/
open ClmmMath

def museShlw : Shlw := fun n =>
  if n.toNat * 2 ^ 64 < 2 ^ 256 then (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false) else (0, true)

def pr7Shlw : Shlw := fun n =>
  let mask : BitVec 256 := (1 : BitVec 256) <<< 192
  if n ≥ mask then (0, true) else (n <<< 64, false)

theorem muse_eq_pr7 : ∀ n : BitVec 256, museShlw n = pr7Shlw n := by
  intro n
  have hm : ((1 : BitVec 256) <<< 192).toNat = 2 ^ 192 := by decide
  unfold museShlw pr7Shlw
  by_cases h : n.toNat < 2 ^ 192
  · have h1 : n.toNat * 2 ^ 64 < 2 ^ 256 := by omega
    have h2 : ¬ n ≥ (1 : BitVec 256) <<< 192 := by
      intro c; have := BitVec.le_def.mp c; omega
    simp only [h1, h2, ite_true, ite_false]
    refine Prod.ext (BitVec.eq_of_toNat_eq ?_) rfl
    rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · have h1 : ¬ n.toNat * 2 ^ 64 < 2 ^ 256 := by omega
    have h2 : n ≥ (1 : BitVec 256) <<< 192 := BitVec.le_def.mpr (by omega)
    simp only [h1, h2, ite_true, ite_false]

#print axioms muse_eq_pr7
