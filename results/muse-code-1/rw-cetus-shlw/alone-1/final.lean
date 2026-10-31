import ClmmMath.Spec
import ClmmMath.Lemmas

namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  if n.toNat * 2 ^ 64 < 2 ^ 256 then
    (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false)
  else
    (0, true)

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n hf
  by_cases hc : n.toNat * 2 ^ 64 < 2 ^ 256
  · have hval : (checkedShlw n).1 = BitVec.ofNat 256 (n.toNat * 2 ^ 64) := by
      unfold checkedShlw
      simp only [hc, ite_true]
    show (checkedShlw n).1.toNat = n.toNat * 2 ^ 64
    rw [hval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  · have h2 : (checkedShlw n).2 = true := by
      unfold checkedShlw
      simp only [hc, ite_false]
    rw [h2] at hf
    contradiction

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n hn
  unfold checkedShlw
  simp only [hn, ite_true]

theorem req_delta_a_covers : DeltaACovers checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hqdiv, hqfit, ham⟩
  · rcases hz with hz | hz
    · have hz0 : exactNumerator sp0 sp1 liq = 0 := by
        simp [exactNumerator, hz]
      rw [hz0]
      simp
    · have hz0 : exactNumerator sp0 sp1 liq = 0 := by
        simp [exactNumerator, hz]
      rw [hz0]
      simp
  · have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        exactNumerator sp0 sp1 liq := by
      have e := req_shlw_exact _ hflag
      rw [toNat_fullMul, toNat_absDiff] at e
      simp [exactNumerator, e]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      simp [denominator, toNat_fullMul]
    have hup := (divRound_up _ _ _ hqdiv).1
    rw [hnum, hden] at hup
    rw [ham]
    exact hup

theorem req_delta_a_tight : DeltaATight checkedShlw := by
  intro sp0 sp1 liq amount h hpos
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hqdiv, hqfit, ham⟩
  · simp at hpos
  · have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        exactNumerator sp0 sp1 liq := by
      have e := req_shlw_exact _ hflag
      rw [toNat_fullMul, toNat_absDiff] at e
      simp [exactNumerator, e]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      simp [denominator, toNat_fullMul]
    have hup := (divRound_up _ _ _ hqdiv).2
    have hqpos : 0 < q.toNat := by omega
    have hlt := hup hqpos
    rw [hnum, hden] at hlt
    rw [ham]
    exact hlt

theorem req_delta_a_floor : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq false amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hqdiv, hqfit, ham⟩
  · have hz0 : exactNumerator sp0 sp1 liq = 0 := by
      rcases hz with hz | hz
      · simp [exactNumerator, hz]
      · simp [exactNumerator, hz]
    rw [hz0]
    simp
  · have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        exactNumerator sp0 sp1 liq := by
      have e := req_shlw_exact _ hflag
      rw [toNat_fullMul, toNat_absDiff] at e
      simp [exactNumerator, e]
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      simp [denominator, toNat_fullMul]
    have hdown := divRound_down _ _ _ hqdiv
    rw [hnum, hden] at hdown
    rw [ham]
    exact hdown

end ClmmMath
