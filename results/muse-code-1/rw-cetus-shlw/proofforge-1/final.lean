import ClmmMath.Spec
import ClmmMath.Lemmas

namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  (BitVec.ofNat 256 (n.toNat * 2 ^ 64), decide (2 ^ 256 ≤ n.toNat * 2 ^ 64))

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n hflag
  unfold checkedShlw at hflag ⊢
  simp only at hflag ⊢
  have hneg : ¬ (2 ^ 256 ≤ n.toNat * 2 ^ 64) := of_decide_eq_false hflag
  have hlt : n.toNat * 2 ^ 64 < 2 ^ 256 := Nat.lt_of_not_ge hneg
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n h
  unfold checkedShlw
  simp only
  exact decide_eq_false (Nat.not_le.mpr h)

theorem req_delta_a_covers : DeltaACovers checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hdiv, hfit, hamt⟩
  · unfold exactNumerator denominator
    rcases hz with hz | hz
    · rw [hz]; simp
    · rw [hz]; simp
  · have hex := req_shlw_exact _ hflag
    have hfull : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator; rw [toNat_fullMul]
    have hup := (divRound_up _ _ _ hdiv).1
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = liq.toNat * priceDiff sp0 sp1 * 2 ^ 64 := by
      rw [hex, hfull]
    unfold exactNumerator denominator
    rw [hamt]
    rw [hden] at hup
    rw [hnum] at hup
    exact hup

theorem req_delta_a_tight : DeltaATight checkedShlw := by
  intro sp0 sp1 liq amount h hpos
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, heq⟩ | ⟨hd, hl, hflag, q, hdiv, hfit, hamt⟩
  · simp [heq] at hpos
  · have hex := req_shlw_exact _ hflag
    have hfull : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator; rw [toNat_fullMul]
    have hup := (divRound_up _ _ _ hdiv).2
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = liq.toNat * priceDiff sp0 sp1 * 2 ^ 64 := by
      rw [hex, hfull]
    have hqpos : 0 < q.toNat := by rw [← hamt]; exact hpos
    have hlt := hup hqpos
    rw [hden, hnum] at hlt
    unfold exactNumerator
    rw [hamt]
    exact hlt

theorem req_delta_a_floor : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq false amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hdiv, hfit, hamt⟩
  · unfold exactNumerator denominator; simp
  · have hex := req_shlw_exact _ hflag
    have hfull : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator; rw [toNat_fullMul]
    have hdown := divRound_down _ _ _ hdiv
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = liq.toNat * priceDiff sp0 sp1 * 2 ^ 64 := by
      rw [hex, hfull]
    unfold exactNumerator denominator
    rw [hamt]
    rw [hden] at hdown
    rw [hnum] at hdown
    exact hdown

end ClmmMath
