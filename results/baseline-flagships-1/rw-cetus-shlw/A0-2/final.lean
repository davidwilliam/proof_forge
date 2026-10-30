import ClmmMath.Spec
import ClmmMath.Lemmas

namespace ClmmMath

def checkedShlw : Shlw := fun n =>
  if n.toNat * 2 ^ 64 < 2 ^ 256 then (n * 18446744073709551616, false) else (0, true)

theorem req_shlw_exact : ShlwExact checkedShlw := by
  intro n hflag
  by_cases hc : n.toNat * 2 ^ 64 < 2 ^ 256
  · have heq : checkedShlw n = (n * 18446744073709551616, false) := by
      unfold checkedShlw
      simp [hc]
    have hval : (checkedShlw n).1.toNat = (n * 18446744073709551616).toNat := by
      rw [heq]
    rw [hval]
    rw [BitVec.toNat_mul]
    have hC : (18446744073709551616 : BitVec 256).toNat = 2 ^ 64 := by decide
    rw [hC]
    exact Nat.mod_eq_of_lt hc
  · have heq : checkedShlw n = ((0 : BitVec 256), true) := by
      unfold checkedShlw
      simp [hc]
    rw [heq] at hflag
    cases hflag

theorem req_shlw_complete : ShlwComplete checkedShlw := by
  intro n h
  have heq : checkedShlw n = (n * 18446744073709551616, false) := by
    unfold checkedShlw
    simp [h]
  rw [heq]

theorem req_delta_a_covers : DeltaACovers checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  cases hc with
  | inl hleft =>
    cases hleft with
    | intro hz ham0 =>
      subst ham0
      cases hz with
      | inl hz0 =>
        have hex0 : exactNumerator sp0 sp1 liq = 0 := by
          unfold exactNumerator
          rw [hz0, Nat.mul_zero, Nat.zero_mul]
        have h0 : (0 : BitVec 64).toNat * denominator sp0 sp1 = 0 := by
          have h00 : (0 : BitVec 64).toNat = 0 := by decide
          rw [h00, Nat.zero_mul]
        rw [hex0, h0]
        exact Nat.le_refl 0
      | inr hz1 =>
        have hex0 : exactNumerator sp0 sp1 liq = 0 := by
          unfold exactNumerator
          rw [hz1, Nat.zero_mul, Nat.zero_mul]
        have h0 : (0 : BitVec 64).toNat * denominator sp0 sp1 = 0 := by
          have h00 : (0 : BitVec 64).toNat = 0 := by decide
          rw [h00, Nat.zero_mul]
        rw [hex0, h0]
        exact Nat.le_refl 0
  | inr hright =>
    cases hright with
    | intro hd h1 =>
      cases h1 with
      | intro hl h2 =>
        cases h2 with
        | intro hflag h3 =>
          cases h3 with
          | intro q hq =>
            cases hq with
            | intro hdiv h4 =>
              cases h4 with
              | intro hfit ham =>
                have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat = exactNumerator sp0 sp1 liq := by
                  unfold exactNumerator
                  rw [req_shlw_exact _ hflag, toNat_fullMul, toNat_absDiff]
                have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
                  unfold denominator
                  rw [toNat_fullMul]
                have hup := divRound_up _ _ _ hdiv
                cases hup with
                | intro hle _ =>
                  rw [hnum, hden, ←ham] at hle
                  exact hle

theorem req_delta_a_tight : DeltaATight checkedShlw := by
  intro sp0 sp1 liq amount h hpos
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq true amount h
  cases hc with
  | inl hleft =>
    cases hleft with
    | intro hz ham0 =>
      subst ham0
      have h00 : (0 : BitVec 64).toNat = 0 := by decide
      rw [h00] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
  | inr hright =>
    cases hright with
    | intro hd h1 =>
      cases h1 with
      | intro hl h2 =>
        cases h2 with
        | intro hflag h3 =>
          cases h3 with
          | intro q hq =>
            cases hq with
            | intro hdiv h4 =>
              cases h4 with
              | intro hfit ham =>
                have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat = exactNumerator sp0 sp1 liq := by
                  unfold exactNumerator
                  rw [req_shlw_exact _ hflag, toNat_fullMul, toNat_absDiff]
                have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
                  unfold denominator
                  rw [toNat_fullMul]
                have hup := divRound_up _ _ _ hdiv
                cases hup with
                | intro _ htight =>
                  have hqpos : 0 < q.toNat := by
                    rw [←ham]
                    exact hpos
                  have hlt := htight hqpos
                  rw [hden, hnum, ←ham] at hlt
                  exact hlt

theorem req_delta_a_floor : DeltaAFloor checkedShlw := by
  intro sp0 sp1 liq amount h
  have hc := getDeltaA_cases checkedShlw sp0 sp1 liq false amount h
  cases hc with
  | inl hleft =>
    cases hleft with
    | intro hz ham0 =>
      subst ham0
      cases hz with
      | inl hz0 =>
        have hex0 : exactNumerator sp0 sp1 liq = 0 := by
          unfold exactNumerator
          rw [hz0, Nat.mul_zero, Nat.zero_mul]
        have h00 : (0 : BitVec 64).toNat = 0 := by decide
        rw [h00, Nat.zero_mul, hex0]
        exact Nat.le_refl 0
      | inr hz1 =>
        have hex0 : exactNumerator sp0 sp1 liq = 0 := by
          unfold exactNumerator
          rw [hz1, Nat.zero_mul, Nat.zero_mul]
        have h00 : (0 : BitVec 64).toNat = 0 := by decide
        rw [h00, Nat.zero_mul, hex0]
        exact Nat.le_refl 0
  | inr hright =>
    cases hright with
    | intro hd h1 =>
      cases h1 with
      | intro hl h2 =>
        cases h2 with
        | intro hflag h3 =>
          cases h3 with
          | intro q hq =>
            cases hq with
            | intro hdiv h4 =>
              cases h4 with
              | intro hfit ham =>
                have hnum : (checkedShlw (fullMul liq (absDiff sp0 sp1))).1.toNat = exactNumerator sp0 sp1 liq := by
                  unfold exactNumerator
                  rw [req_shlw_exact _ hflag, toNat_fullMul, toNat_absDiff]
                have hden : (fullMul sp0 sp1).toNat = denominator sp0 sp1 := by
                  unfold denominator
                  rw [toNat_fullMul]
                have hle := divRound_down _ _ _ hdiv
                rw [hnum, hden, ←ham] at hle
                exact hle

end ClmmMath
