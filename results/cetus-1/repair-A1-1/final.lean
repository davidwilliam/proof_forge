import ClmmMath.Spec
import ClmmMath.Lemmas
namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  if n.toNat * 2 ^ 64 < 2 ^ 256 then (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false) else (0, true)

theorem dummy_foo : True := trivial

theorem dummy_baz : True := by
  have h := @BitVec.toNat_ofNat
  trivial

theorem req_shlw_exact_try3 : ShlwExact checkedShlw := by
  intro n h
  by_cases hc : n.toNat * 2 ^ 64 < 2 ^ 256
  · have hpair : checkedShlw n = (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false) := by
      simp only [checkedShlw, hc, ite_true]
    rw [hpair]
    have hto : (BitVec.ofNat 256 (n.toNat * 2 ^ 64)).toNat
        = n.toNat * 2 ^ 64 % 2 ^ 256 := BitVec.toNat_ofNat _ _
    rw [hto, Nat.mod_eq_of_lt hc]
  · have hpair : checkedShlw n = ((0 : BitVec 256), true) := by
      simp only [checkedShlw, hc, ite_false]
    rw [hpair] at h
    simp at h

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n h
  simp only [checkedShlw, h, ite_true]

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n h
  by_cases hc : n.toNat * 2 ^ 64 < 2 ^ 256
  · have hpair : checkedShlw n = (BitVec.ofNat 256 (n.toNat * 2 ^ 64), false) := by
      simp only [checkedShlw, hc, ite_true]
    rw [hpair]
    have hto : (BitVec.ofNat 256 (n.toNat * 2 ^ 64)).toNat
        = n.toNat * 2 ^ 64 % 2 ^ 256 := BitVec.toNat_ofNat _ _
    rw [hto, Nat.mod_eq_of_lt hc]
  · have hpair : checkedShlw n = ((0 : BitVec 256), true) := by
      simp only [checkedShlw, hc, ite_false]
    rw [hpair] at h
    simp at h

theorem req_delta_a_floor   : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq false amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hq, hfit, ham⟩
  · simp
  · have hex : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = (fullMul liq (absDiff sp0 sp1)).toNat * 2 ^ 64 :=
      req_shlw_exact _ hflag
    have hfull_liq : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hfull_sp : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      rw [toNat_fullMul]; rfl
    have hdown := divRound_down _ _ _ hq
    rw [hex, hfull_liq] at hdown
    rw [hfull_sp] at hdown
    rw [ham]
    exact hdown

theorem req_delta_a_tight   : DeltaATight checkedShlw := by
  intro sp0 sp1 liq amount h hpos
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hq, hfit, ham⟩
  · simp at hpos
  · have hex : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = (fullMul liq (absDiff sp0 sp1)).toNat * 2 ^ 64 :=
      req_shlw_exact _ hflag
    have hfull_liq : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hfull_sp : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      rw [toNat_fullMul]; rfl
    have hexact_eq : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = exactNumerator sp0 sp1 liq := by
      rw [hex, hfull_liq]; rfl
    have hup := (divRound_up _ _ _ hq).2
    have hqpos : 0 < q.toNat := by omega
    have hlt := hup hqpos
    rw [hexact_eq, hfull_sp] at hlt
    rw [ham]
    exact hlt

theorem req_delta_a_covers  : DeltaACovers checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  rcases hc with ⟨hz, rfl⟩ | ⟨hd, hl, hflag, q, hq, hfit, ham⟩
  · rcases hz with h0 | h0
    · have he : exactNumerator sp0 sp1 liq = 0 := by
        simp [exactNumerator, h0]
      simp [he]
    · have he : exactNumerator sp0 sp1 liq = 0 := by
        simp [exactNumerator, h0]
      simp [he]
  · have hex : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = (fullMul liq (absDiff sp0 sp1)).toNat * 2 ^ 64 :=
      req_shlw_exact _ hflag
    have hfull_liq : (fullMul liq (absDiff sp0 sp1)).toNat = liq.toNat * priceDiff sp0 sp1 := by
      rw [toNat_fullMul, toNat_absDiff]
    have hfull_sp : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
      rw [toNat_fullMul]; rfl
    have hexact_eq : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat
        = exactNumerator sp0 sp1 liq := by
      rw [hex, hfull_liq]; rfl
    have hup := (divRound_up _ _ _ hq).1
    rw [hexact_eq, hfull_sp] at hup
    rw [ham]
    exact hup

end ClmmMath
