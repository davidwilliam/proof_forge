import ClmmMath.Spec
import ClmmMath.Lemmas
/-!
# Reference solution A (build team; hidden from agents)

Port of `checked_shlw` after pull request 7 of CetusProtocol/integer-mate (merge commit
06660f704c4ac1d443ab62346a46b5b60d49df33, `sui/sources/math_u256.move` lines 18 to 25):

```
public fun checked_shlw(n: u256): (u256, bool) {
    let mask = 1 << 192;
    if (n >= mask) {
        (0, true)
    } else {
        ((n << 64), false)
    }
}
```
-/

namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  let mask : BitVec 256 := (1 : BitVec 256) <<< 192
  if n ≥ mask then (0, true) else (n <<< 64, false)

theorem mask_toNat : ((1 : BitVec 256) <<< 192).toNat = 2 ^ 192 := by decide

theorem flag_false_iff (n : BitVec 256) : (checkedShlw n).2 = false ↔ n.toNat < 2 ^ 192 := by
  unfold checkedShlw
  by_cases h : n ≥ (1 : BitVec 256) <<< 192
  · have h' : 2 ^ 192 ≤ n.toNat := mask_toNat ▸ (BitVec.le_def.mp h)
    simp only [h, ite_true]
    constructor
    · intro e; exact absurd e (by decide)
    · intro e; omega
  · have h' : n.toNat < 2 ^ 192 := by
      have := mt BitVec.le_def.mpr h
      rw [mask_toNat] at this
      omega
    simp only [h, ite_false]
    simpa using h'

theorem value_of_flag (n : BitVec 256) (h : (checkedShlw n).2 = false) :
    (checkedShlw n).1.toNat = n.toNat * 2 ^ 64 := by
  have hlt := (flag_false_iff n).mp h
  unfold checkedShlw
  have hc : ¬ n ≥ (1 : BitVec 256) <<< 192 := by
    intro hc
    have := BitVec.le_def.mp hc
    rw [mask_toNat] at this
    omega
  simp only [hc, ite_false]
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
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
