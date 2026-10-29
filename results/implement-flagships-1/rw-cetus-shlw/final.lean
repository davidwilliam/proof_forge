import ClmmMath.Spec
import ClmmMath.Lemmas

namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  if n.toNat * 2 ^ 64 < 2 ^ 256 then (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false)
  else (0, true)

theorem req_shlw_complete   : ShlwComplete checkedShlw := by
  intro n hn
  unfold checkedShlw
  simp only [hn, ite_true]

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n hflag
  unfold checkedShlw at hflag ⊢
  by_cases h : n.toNat * 2 ^ 64 < 2 ^ 256
  · simp only [h, ite_true] at hflag ⊢
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h
  · simp only [h, ite_false] at hflag ⊢
    simp at hflag

theorem req_delta_a_floor   : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq false amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hq, hfit, ham⟩
  · simp [exactNumerator, denominator]
  · have hdown := divRound_down _ _ _ hq
    have hex := req_shlw_exact (fullMul liq (absDiff sp0 sp1)) hflag
    have hfull_liq : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * (absDiff sp0 sp1).toNat := toNat_fullMul _ _
    have habs : (absDiff sp0 sp1).toNat = priceDiff sp0 sp1 := toNat_absDiff _ _
    have hfull_sp : (fullMul sp0 sp1).toNat = sp0.toNat * sp1.toNat := toNat_fullMul _ _
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat = exactNumerator sp0 sp1 liq := by
      unfold exactNumerator
      rw [hex, hfull_liq, habs]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator
      rw [hfull_sp]
    rw [← ham, hden, hnum] at hdown
    exact hdown

theorem req_delta_a_tight   : DeltaATight checkedShlw := by
  intro sp0 sp1 liq amount h hpos
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hq, hfit, ham⟩
  · simp at hpos
  · have hup := divRound_up _ _ _ hq
    have hex := req_shlw_exact (fullMul liq (absDiff sp0 sp1)) hflag
    have hfull_liq : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * (absDiff sp0 sp1).toNat := toNat_fullMul _ _
    have habs : (absDiff sp0 sp1).toNat = priceDiff sp0 sp1 := toNat_absDiff _ _
    have hfull_sp : (fullMul sp0 sp1).toNat = sp0.toNat * sp1.toNat := toNat_fullMul _ _
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat = exactNumerator sp0 sp1 liq := by
      unfold exactNumerator
      rw [hex, hfull_liq, habs, Nat.mul_assoc]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator
      exact hfull_sp
    have hqpos : 0 < q.toNat := by rw [← ham]; exact hpos
    have ht := hup.2 hqpos
    calc (amount.toNat - 1) * denominator sp0 sp1
        = (q.toNat - 1) * (fullMul sp0 sp1).toNat := by rw [ham, hden]
      _ < (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat := ht
      _ = exactNumerator sp0 sp1 liq := hnum

theorem req_delta_a_covers  : DeltaACovers checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hq, hfit, ham⟩
  · unfold exactNumerator denominator priceDiff at *
    rcases hz with hz | hz
    · rw [hz]; simp
    · rw [hz]; simp
  · have hup := divRound_up _ _ _ hq
    have hex := req_shlw_exact (fullMul liq (absDiff sp0 sp1)) hflag
    have hfull_liq : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * (absDiff sp0 sp1).toNat := toNat_fullMul _ _
    have habs : (absDiff sp0 sp1).toNat = priceDiff sp0 sp1 := toNat_absDiff _ _
    have hfull_sp : (fullMul sp0 sp1).toNat = sp0.toNat * sp1.toNat := toNat_fullMul _ _
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat = exactNumerator sp0 sp1 liq := by
      unfold exactNumerator
      rw [hex, hfull_liq, habs, Nat.mul_assoc]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator
      exact hfull_sp
    calc exactNumerator sp0 sp1 liq = (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat := hnum.symm
      _ ≤ q.toNat * (fullMul sp0 sp1).toNat := hup.1
      _ = amount.toNat * denominator sp0 sp1 := by rw [ham, hden]

end ClmmMath
