import ClmmMath.Spec
import ClmmMath.Lemmas

namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  if n.toNat < 2 ^ 192 then (n * (18446744073709551616 : BitVec 256), false) else (0, true)

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n hflag
  have hC : ((18446744073709551616 : BitVec 256).toNat = 2 ^ 64) := rfl
  by_cases hc : n.toNat < 2 ^ 192
  · have hEq : checkedShlw n = (n * (18446744073709551616 : BitVec 256), false) := by
      unfold checkedShlw
      exact if_pos hc
    have h1 : (checkedShlw n).1.toNat = ((n * (18446744073709551616 : BitVec 256)).toNat) := by
      rw [hEq]
    rw [h1, BitVec.toNat_mul, hC]
    have hpow : (2 : Nat) ^ 192 * 2 ^ 64 = 2 ^ 256 := by
      rw [← Nat.pow_add]
    have hlt1 : n.toNat * 2 ^ 64 < 2 ^ 192 * 2 ^ 64 := by
      omega
    rw [hpow] at hlt1
    rw [Nat.mod_eq_of_lt hlt1]
  · have hEq : checkedShlw n = ((0 : BitVec 256), true) := by
      unfold checkedShlw
      exact if_neg hc
    have hf : (checkedShlw n).2 = true := by rw [hEq]
    rw [hf] at hflag
    cases hflag

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n hlt
  have hpow : (2 : Nat) ^ 192 * 2 ^ 64 = 2 ^ 256 := by
    rw [← Nat.pow_add]
  have hc : n.toNat < 2 ^ 192 := by
    omega
  have hEq : checkedShlw n = (n * (18446744073709551616 : BitVec 256), false) := by
    unfold checkedShlw
    exact if_pos hc
  have hf : (checkedShlw n).2 = false := by rw [hEq]
  exact hf

theorem req_delta_a_covers : DeltaACovers checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, heq⟩ | ⟨hd, hl, hno, q, hdiv, hfit, ham⟩
  · have hex0 : exactNumerator sp0 sp1 liq = 0 := by
      unfold exactNumerator
      rcases hz with hz | hz
      · rw [hz]
        simp
      · rw [hz]
        simp
    rw [hex0]
    exact Nat.zero_le _
  · have hfull : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hex : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        (fullMul liq (absDiff sp0 sp1)).toNat * 2 ^ 64 :=
      req_shlw_exact _ hno
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        exactNumerator sp0 sp1 liq := by
      unfold exactNumerator
      rw [← hfull]
      exact hex
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator
      rw [toNat_fullMul]
    have hup := (divRound_up _ _ _ hdiv).1
    rw [hnum, hden, ← ham] at hup
    exact hup

theorem req_delta_a_tight : DeltaATight checkedShlw := by
  intro sp0 sp1 liq amount h hpos
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, heq⟩ | ⟨hd, hl, hno, q, hdiv, hfit, ham⟩
  · have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [heq, h0] at hpos
    cases Nat.lt_irrefl 0 hpos
  · have hfull : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hex : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        (fullMul liq (absDiff sp0 sp1)).toNat * 2 ^ 64 :=
      req_shlw_exact _ hno
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        exactNumerator sp0 sp1 liq := by
      unfold exactNumerator
      rw [← hfull]
      exact hex
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator
      rw [toNat_fullMul]
    have hpair := divRound_up _ _ _ hdiv
    have hpos_q : 0 < q.toNat := by
      rw [← ham]
      exact hpos
    have hlt := hpair.2 hpos_q
    rw [hnum, hden, ← ham] at hlt
    exact hlt

theorem req_delta_a_floor : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq false amount h
  rcases hc with ⟨hz, heq⟩ | ⟨hd, hl, hno, q, hdiv, hfit, ham⟩
  · have hex0 : exactNumerator sp0 sp1 liq = 0 := by
      unfold exactNumerator
      rcases hz with hz | hz
      · rw [hz]
        simp
      · rw [hz]
        simp
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [heq, h0, hex0]
    simp
  · have hfull : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hex : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        (fullMul liq (absDiff sp0 sp1)).toNat * 2 ^ 64 :=
      req_shlw_exact _ hno
    have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat =
        exactNumerator sp0 sp1 liq := by
      unfold exactNumerator
      rw [← hfull]
      exact hex
    have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      unfold denominator
      rw [toNat_fullMul]
    have hdown := divRound_down _ _ _ hdiv
    rw [hnum, hden, ← ham] at hdown
    exact hdown

end ClmmMath
