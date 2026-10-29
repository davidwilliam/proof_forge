import ClmmMath.Spec
import ClmmMath.Lemmas
/-!
# Reference solution B (build team; hidden from agents)

An independent rewrite: the shift is exact exactly when the top 64 bits of `n` are zero, so it
tests `n >> 192 == 0` instead of comparing with a mask, and it computes the shifted value from
the natural number `n * 2^64`.
-/

namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  if n >>> 192 = 0 then (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false) else (0, true)

theorem top_zero_iff (n : BitVec 256) : n >>> 192 = 0 ↔ n.toNat < 2 ^ 192 := by
  rw [BitVec.toNat_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have : (0 : BitVec 256).toNat = 0 := rfl
  rw [this]
  constructor
  · intro h
    have := Nat.lt_of_div_eq_zero (by decide) h
    exact this
  · intro h
    exact Nat.div_eq_of_lt h

theorem flag_false_iff (n : BitVec 256) : (checkedShlw n).2 = false ↔ n.toNat < 2 ^ 192 := by
  unfold checkedShlw
  by_cases h : n >>> 192 = 0
  · simp only [h, ite_true]
    simpa using (top_zero_iff n).mp h
  · simp only [h, ite_false]
    have := mt (top_zero_iff n).mpr h
    constructor
    · intro e; exact absurd e (by decide)
    · intro e; exact absurd e this

theorem value_of_flag (n : BitVec 256) (h : (checkedShlw n).2 = false) :
    (checkedShlw n).1.toNat = n.toNat * 2 ^ 64 := by
  have hlt := (flag_false_iff n).mp h
  unfold checkedShlw
  simp only [(top_zero_iff n).mpr hlt, ite_true]
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem req_shlw_exact : ShlwExact checkedShlw := value_of_flag

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n h
  exact (flag_false_iff n).mpr (by omega)

/-- With no overflow, the numerator is the exact numerator. -/
theorem numerator_exact (sp0 sp1 liquidity : BitVec 128)
    (h : (checkedShlw (fullMul liquidity (absDiff sp0 sp1))).2 = false) :
    (checkedShlw (fullMul liquidity (absDiff sp0 sp1))).1.toNat = exactNumerator sp0 sp1 liquidity := by
  rw [value_of_flag _ h, toNat_fullMul, toNat_absDiff]
  rfl

theorem exact_zero (sp0 sp1 liquidity : BitVec 128)
    (h : priceDiff sp0 sp1 = 0 ∨ liquidity.toNat = 0) : exactNumerator sp0 sp1 liquidity = 0 := by
  unfold exactNumerator
  rcases h with h | h <;> simp [h]

theorem req_delta_a_covers : DeltaACovers checkedShlw := by
  intro sp0 sp1 liquidity amount h
  rcases getDeltaA_cases _ _ _ _ _ _ h with ⟨hz, rfl⟩ | ⟨_, _, hf, q, hq, _, ha⟩
  · rw [exact_zero _ _ _ hz]; exact Nat.zero_le _
  · have := (divRound_up _ _ _ hq).1
    rw [numerator_exact _ _ _ hf, toNat_fullMul] at this
    rw [ha]
    exact this

theorem req_delta_a_tight : DeltaATight checkedShlw := by
  intro sp0 sp1 liquidity amount h hpos
  rcases getDeltaA_cases _ _ _ _ _ _ h with ⟨_, rfl⟩ | ⟨_, _, hf, q, hq, _, ha⟩
  · exact absurd hpos (by decide)
  · have := (divRound_up _ _ _ hq).2 (ha ▸ hpos)
    rw [numerator_exact _ _ _ hf, toNat_fullMul] at this
    rw [ha]
    exact this

theorem req_delta_a_floor : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liquidity amount h
  rcases getDeltaA_cases _ _ _ _ _ _ h with ⟨hz, rfl⟩ | ⟨_, _, hf, q, hq, _, ha⟩
  · simp
  · have := divRound_down _ _ _ hq
    rw [numerator_exact _ _ _ hf, toNat_fullMul] at this
    rw [ha]
    exact this

end ClmmMath
