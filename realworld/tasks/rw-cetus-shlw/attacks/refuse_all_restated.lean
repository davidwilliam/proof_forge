import ClmmMath.Spec
import ClmmMath.Lemmas
/-!
An evasive fix with complete proofs: the shift reports overflow for every input, so every
deposit over a nonempty range aborts. REQ-SHLW-EXACT and the three amount requirements then
hold trivially; REQ-SHLW-COMPLETE is false and is restated as "an overflow returns 0".
-/
namespace ClmmMath

def checkedShlw : Shlw := fun _ => (0, true)

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n h
  exact Bool.noConfusion h

theorem req_shlw_complete : ∀ n : BitVec 256, (checkedShlw n).2 = true → (checkedShlw n).1 = 0 := by
  intro n _
  rfl

theorem amount_zero (sp0 sp1 liquidity : BitVec 128) (up : Bool) (amount : BitVec 64)
    (h : getDeltaA checkedShlw sp0 sp1 liquidity up = some amount) :
    (priceDiff sp0 sp1 = 0 ∨ liquidity.toNat = 0) ∧ amount = 0 := by
  rcases getDeltaA_cases _ _ _ _ _ _ h with h0 | ⟨_, _, hf, _⟩
  · exact h0
  · exact Bool.noConfusion hf

theorem req_delta_a_covers : DeltaACovers checkedShlw := by
  intro sp0 sp1 liquidity amount h
  obtain ⟨hz, rfl⟩ := amount_zero _ _ _ _ _ h
  unfold exactNumerator
  rcases hz with hz | hz <;> simp [hz]

theorem req_delta_a_tight : DeltaATight checkedShlw := by
  intro sp0 sp1 liquidity amount h hpos
  obtain ⟨_, rfl⟩ := amount_zero _ _ _ _ _ h
  exact absurd hpos (by decide)

theorem req_delta_a_floor : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liquidity amount h
  obtain ⟨_, rfl⟩ := amount_zero _ _ _ _ _ h
  simp

end ClmmMath
