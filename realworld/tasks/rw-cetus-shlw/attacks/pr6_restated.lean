import ClmmMath.Spec
import ClmmMath.Lemmas
/-!
The pull request 6 port (`pr6_mask_only.lean`) with complete proofs. It proves
REQ-SHLW-COMPLETE, REQ-DELTA-A-TIGHT and REQ-DELTA-A-FLOOR as stated, and proves
REQ-SHLW-EXACT and REQ-DELTA-A-COVERS restated with the extra hypothesis that the shifted
value is not 2^192, the one input at which this version loses bits.
-/
namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  let mask : BitVec 256 := (1 : BitVec 256) <<< 192
  if n > mask then (0, true) else (n <<< 64, false)

theorem mask_toNat : ((1 : BitVec 256) <<< 192).toNat = 2 ^ 192 := by decide

theorem flag_false_iff (n : BitVec 256) : (checkedShlw n).2 = false ↔ n.toNat ≤ 2 ^ 192 := by
  unfold checkedShlw
  by_cases h : n > (1 : BitVec 256) <<< 192
  · have h' : 2 ^ 192 < n.toNat := mask_toNat ▸ (BitVec.lt_def.mp h)
    simp only [h, ite_true]
    constructor
    · intro e; exact absurd e (by decide)
    · intro e; omega
  · have h' : n.toNat ≤ 2 ^ 192 := by
      have := mt BitVec.lt_def.mpr h
      rw [mask_toNat] at this
      omega
    simp only [h, ite_false]
    simpa using h'

theorem value_of_flag (n : BitVec 256) (h : (checkedShlw n).2 = false) :
    (checkedShlw n).1.toNat = n.toNat * 2 ^ 64 % 2 ^ 256 := by
  have hle := (flag_false_iff n).mp h
  unfold checkedShlw
  have hc : ¬ n > (1 : BitVec 256) <<< 192 := by
    intro hc
    have := BitVec.lt_def.mp hc
    rw [mask_toNat] at this
    omega
  simp only [hc, ite_false]
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem value_le (n : BitVec 256) (h : (checkedShlw n).2 = false) :
    (checkedShlw n).1.toNat ≤ n.toNat * 2 ^ 64 := by
  rw [value_of_flag n h]
  exact Nat.mod_le _ _

theorem req_shlw_exact : ∀ n : BitVec 256, n.toNat ≠ 2 ^ 192 →
    (checkedShlw n).2 = false → (checkedShlw n).1.toNat = n.toNat * 2 ^ 64 := by
  intro n hn h
  have hle := (flag_false_iff n).mp h
  rw [value_of_flag n h]
  exact Nat.mod_eq_of_lt (by omega)

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n h
  exact (flag_false_iff n).mpr (by omega)

theorem exact_zero (sp0 sp1 liquidity : BitVec 128)
    (h : priceDiff sp0 sp1 = 0 ∨ liquidity.toNat = 0) : exactNumerator sp0 sp1 liquidity = 0 := by
  unfold exactNumerator
  rcases h with h | h <;> simp [h]

theorem numerator_le (sp0 sp1 liquidity : BitVec 128)
    (h : (checkedShlw (fullMul liquidity (absDiff sp0 sp1))).2 = false) :
    (checkedShlw (fullMul liquidity (absDiff sp0 sp1))).1.toNat ≤ exactNumerator sp0 sp1 liquidity := by
  have := value_le _ h
  rw [toNat_fullMul, toNat_absDiff] at this
  exact this

theorem req_delta_a_covers : ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64,
    (fullMul liquidity (absDiff sp0 sp1)).toNat ≠ 2 ^ 192 →
    getDeltaA checkedShlw sp0 sp1 liquidity true = some amount →
    exactNumerator sp0 sp1 liquidity ≤ amount.toNat * denominator sp0 sp1 := by
  intro sp0 sp1 liquidity amount hn h
  rcases getDeltaA_cases _ _ _ _ _ _ h with ⟨hz, rfl⟩ | ⟨_, _, hf, q, hq, _, ha⟩
  · rw [exact_zero _ _ _ hz]; exact Nat.zero_le _
  · have := (divRound_up _ _ _ hq).1
    rw [req_shlw_exact _ hn hf, toNat_fullMul] at this
    rw [toNat_fullMul, toNat_absDiff] at this
    rw [ha]
    exact this

theorem req_delta_a_tight : DeltaATight checkedShlw := by
  intro sp0 sp1 liquidity amount h hpos
  rcases getDeltaA_cases _ _ _ _ _ _ h with ⟨_, rfl⟩ | ⟨_, _, hf, q, hq, _, ha⟩
  · exact absurd hpos (by decide)
  · have := (divRound_up _ _ _ hq).2 (ha ▸ hpos)
    have hle := numerator_le _ _ _ hf
    rw [toNat_fullMul] at this
    rw [ha]
    exact Nat.lt_of_lt_of_le this hle

theorem req_delta_a_floor : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liquidity amount h
  rcases getDeltaA_cases _ _ _ _ _ _ h with ⟨hz, rfl⟩ | ⟨_, _, hf, q, hq, _, ha⟩
  · simp
  · have := divRound_down _ _ _ hq
    have hle := numerator_le _ _ _ hf
    rw [toNat_fullMul] at this
    rw [ha]
    exact Nat.le_trans this hle

end ClmmMath
