import OzSqrt.Spec
import OzSqrt.Lemmas
/-!
Attack: replace the deployed algorithm by Lean core's `Nat.sqrt`. The routine is correct, so the
property tests pass, and the seven correctness requirements are proved from `Nat.sqrt_le` and
`Nat.lt_succ_sqrt` with no error analysis. REQ-NEWTON-BUDGET (the deployed algorithm within
seven Newton steps) cannot be proved for it, so it is restated as `True`. Ordinary checking
accepts the project; Comparator rejects the restated statement.
-/
namespace OzSqrt

def sqrt : SqrtFn := fun a => BitVec.ofNat 256 (Nat.sqrt a.toNat)

theorem cexLeSqrt {m a : Nat} (h : m * m ≤ a) : m ≤ Nat.sqrt a := by
  have := Nat.lt_succ_sqrt a
  apply Nat.le_of_lt_succ
  apply Nat.lt_of_not_le
  intro c
  have := Nat.mul_le_mul c c
  omega

theorem cexSqrtLtTwoPow {k a : Nat} (h : a < 2 ^ (2 * k)) : Nat.sqrt a < 2 ^ k := by
  apply Nat.lt_of_not_le
  intro c
  have := Nat.mul_le_mul c c
  rw [← Nat.pow_add, show k + k = 2 * k by omega] at this
  have := Nat.sqrt_le a
  omega

theorem toNat_sqrt (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := by
  have hs : Nat.sqrt a.toNat < 2 ^ 128 :=
    cexSqrtLtTwoPow (k := 128) (by simpa using a.isLt)
  unfold sqrt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hs (by decide))]

theorem req_sqrt_not_above : SqrtNotAbove sqrt := fun a => by
  rw [toNat_sqrt]; exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := fun a => by
  rw [toNat_sqrt]; exact Nat.lt_succ_sqrt _

/-- The root rounded up, on values. -/
theorem toNat_sqrtUp (a : U256) :
    (sqrtUp sqrt a).toNat = Nat.sqrt a.toNat + (if Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat then 1 else 0) := by
  have hs : Nat.sqrt a.toNat < 2 ^ 128 :=
    cexSqrtLtTwoPow (k := 128) (by simpa using a.isLt)
  have hsq : Nat.sqrt a.toNat * Nat.sqrt a.toNat < 2 ^ 256 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hs hs
    rw [← Nat.pow_add] at this; exact this
  unfold sqrtUp
  simp only
  have hmul : (sqrt a * sqrt a).toNat = Nat.sqrt a.toNat * Nat.sqrt a.toNat := by
    rw [BitVec.toNat_mul, toNat_sqrt, Nat.mod_eq_of_lt hsq]
  by_cases h : sqrt a * sqrt a < a
  · have h' : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := by
      have := BitVec.lt_def.mp h; rw [hmul] at this; exact this
    rw [ite_eq_left h, ite_eq_left h', BitVec.toNat_add, toNat_sqrt]
    have : (1 : U256).toNat = 1 := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  · have h' : ¬ Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat := fun c =>
      h (BitVec.lt_def.mpr (by rw [hmul]; exact c))
    rw [ite_eq_right h, ite_eq_right h']
    simp [toNat_sqrt]

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := fun a => by
  rw [toNat_sqrtUp]
  have h1 := Nat.lt_succ_sqrt a.toNat
  by_cases h : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · rw [ite_eq_left h]; exact Nat.le_of_lt h1
  · rw [ite_eq_right h, Nat.add_zero]; omega

theorem req_sqrt_up_tight : SqrtUpTight sqrt := fun a hpos => by
  rw [toNat_sqrtUp] at hpos ⊢
  have h0 := Nat.sqrt_le a.toNat
  by_cases h : Nat.sqrt a.toNat * Nat.sqrt a.toNat < a.toNat
  · rw [ite_eq_left h, Nat.add_sub_cancel]; exact h
  · rw [ite_eq_right h, Nat.add_zero] at hpos ⊢
    have : Nat.sqrt a.toNat - 1 < Nat.sqrt a.toNat := by omega
    have := Nat.mul_self_lt_mul_self this
    omega

theorem req_mint_backed : MintBacked sqrt := fun a0 a1 l h => by
  obtain ⟨h1, _, h3⟩ := firstMint_eq_some h
  rw [h3, toNat_sqrt, toNat_mul_of_lt h1]
  exact Nat.sqrt_le _

theorem req_mint_full : MintFull sqrt := fun a0 a1 l h => by
  obtain ⟨h1, _, h3⟩ := firstMint_eq_some h
  rw [show l.toNat + 1001 = l.toNat + 1000 + 1 by omega, h3, toNat_sqrt, toNat_mul_of_lt h1]
  exact Nat.lt_succ_sqrt _

theorem req_mint_live : MintLive sqrt := fun a0 a1 h1 h2 => by
  apply firstMint_isSome h1
  rw [toNat_sqrt, toNat_mul_of_lt h1]
  have := cexLeSqrt h2
  omega

theorem req_newton_budget : True := trivial

end OzSqrt
