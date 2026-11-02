import OzSqrt.Spec
import OzSqrt.Lemmas

namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  show (newtonSqrt 7 a).toNat * (newtonSqrt 7 a).toNat ≤ a.toNat
  unfold newtonSqrt
  by_cases h0 : a = 0
  · subst h0
    simp
  · rw [if_neg h0]
    simp only []
    rw [toNat_min, BitVec.toNat_udiv]
    have h1 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := Nat.min_le_left _ _
    have h2 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := Nat.min_le_right _ _
    have h3 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat * (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) :=
      Nat.mul_le_mul h1 h2
    have h4 : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat * (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ a.toNat := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self a.toNat _
    omega

theorem floor_exists : ∀ A : Nat, ∃ s, s * s ≤ A ∧ A < (s + 1) * (s + 1) := by
  intro A
  induction A with
  | zero => exact ⟨0, Nat.le_refl 0, by decide⟩
  | succ n ih =>
    obtain ⟨s, h1, h2⟩ := ih
    by_cases h : n + 1 < (s + 1) * (s + 1)
    · exact ⟨s, by omega, h⟩
    · have hle : n + 1 ≤ (s + 1) * (s + 1) := Nat.succ_le_of_lt h2
      have hge : (s + 1) * (s + 1) ≤ n + 1 := Nat.le_of_not_gt h
      have heq : n + 1 = (s + 1) * (s + 1) := Nat.le_antisymm hle hge
      refine ⟨s + 1, by omega, ?_⟩
      have hlt : (s + 1) * (s + 1) < (s + 1 + 1) * (s + 1 + 1) :=
        Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega)
      omega

def natStart (A : Nat) : Nat := 2 ^ ((Nat.log2 A) / 2)

def natStep (A r : Nat) : Nat := (r + A / r) / 2

def natIter (A : Nat) : Nat → Nat
  | 0 => natStart A
  | n + 1 => natStep A (natIter A n)

theorem s_pos {A s : Nat} (hA : 0 < A) (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1)) :
    0 < s := by
  by_cases h : 0 < s
  · exact h
  · have hs0 : s = 0 := by omega
    subst hs0
    simp at h2
    omega

theorem x0_le_s {A s : Nat} (hx : natStart A * natStart A ≤ A)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1)) : natStart A ≤ s := by
  by_cases h : natStart A ≤ s
  · exact h
  · have hle : s + 1 ≤ natStart A := by omega
    have hge : (s + 1) * (s + 1) ≤ natStart A * natStart A :=
      Nat.mul_le_mul hle hle
    omega

theorem diff_sq_add {s D : Nat} (h : D ≤ s) :
    (s + D) * (s - D) + D * D = s * s := by
  have h1 : (s + D) * (s - D) = (s + D) * s - (s + D) * D := Nat.mul_sub _ _ _
  have h2 : (s + D) * s = s * s + D * s := Nat.add_mul _ _ _
  have h3 : (s + D) * D = s * D + D * D := Nat.add_mul _ _ _
  have hcomm : D * s = s * D := Nat.mul_comm _ _
  have hle1 : D * D ≤ s * s := Nat.mul_le_mul h h
  have hle2 : s * D + D * D ≤ s * s + s * D := by
    have := Nat.mul_le_mul (Nat.le_refl s) h
    omega
  omega

theorem step_from_below {s D0 x0 A t : Nat} (hD : D0 ≤ s) (hx0 : x0 + D0 = s)
    (hA : A = s * s + t) (hx0pos : 0 < x0) :
    natStep A x0 = s + ((D0 * D0 + t) / x0) / 2 := by
  have hsq : (s + D0) * (s - D0) + D0 * D0 = s * s := diff_sq_add hD
  have hx0eq : s - D0 = x0 := by omega
  have hAeq : A = (D0 * D0 + t) + x0 * (s + D0) := by
    have h1 : s * s = x0 * (s + D0) + D0 * D0 := by
      have h2 : (s + D0) * (s - D0) = x0 * (s + D0) := by
        rw [hx0eq, Nat.mul_comm]
      omega
    omega
  have hdiv : A / x0 = (D0 * D0 + t) / x0 + (s + D0) := by
    rw [hAeq, Nat.add_mul_div_left _ _ hx0pos]
  have hsum : x0 + A / x0 = 2 * s + (D0 * D0 + t) / x0 := by
    rw [hdiv]
    have hxs : x0 + (s + D0) = 2 * s := by omega
    omega
  unfold natStep
  have hcomm : (2 * s + (D0 * D0 + t) / x0) = ((D0 * D0 + t) / x0 + 2 * s) := by
    omega
  rw [hsum, hcomm, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  omega

theorem step_from_above {s D x A t : Nat} (hD : D ≤ s) (hx : x = s + D)
    (hA : A = s * s + t) (hxpos : 0 < x) (_hspos : 0 < s) :
    natStep A x = s + ((D * D + t) / (s + D)) / 2 := by
  have hsq : (s + D) * (s - D) + D * D = s * s := diff_sq_add hD
  have hAeq : A = (D * D + t) + x * (s - D) := by
    have h1 : s * s = x * (s - D) + D * D := by
      have h2 : (s + D) * (s - D) = x * (s - D) := by
        rw [hx, Nat.mul_comm]
      omega
    omega
  have hdiv : A / x = (D * D + t) / x + (s - D) := by
    rw [hAeq, Nat.add_mul_div_left _ _ hxpos]
  have hsum : x + A / x = 2 * s + (D * D + t) / x := by
    rw [hdiv]
    omega
  unfold natStep
  have hcomm : (2 * s + (D * D + t) / x) = ((D * D + t) / x + 2 * s) := by
    omega
  have hxrw : (D * D + t) / x = (D * D + t) / (s + D) := by rw [hx]
  rw [hsum, hcomm, hxrw, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  omega

theorem D1_le {s D0 x0 A t : Nat} (hD0 : D0 ≤ s / 2) (ht : t ≤ 2 * s)
    (hx0lo : s / 2 + 1 ≤ x0) (hx0pos : 0 < x0) (hspos : 0 < s)
    (hD0le : D0 ≤ s) :
    ((D0 * D0 + t) / x0) / 2 ≤ s / 4 + 1 := by
  have hPu : (s / 2) * (s / 2) ≤ 2 * ((s / 4) * (s / 2)) + s / 2 := by
    have e1 : s / 2 = 2 * (s / 4) + (s / 2 - 2 * (s / 4)) := by omega
    have h4 : s / 2 - 2 * (s / 4) ≤ 1 := by omega
    have h3 : (s / 2) * (s / 2 - 2 * (s / 4)) ≤ s / 2 := by
      calc (s / 2) * (s / 2 - 2 * (s / 4)) ≤ (s / 2) * 1 :=
            Nat.mul_le_mul_left _ h4
        _ = s / 2 := Nat.mul_one _
    have ePu : (s / 2) * (2 * (s / 4)) = 2 * ((s / 4) * (s / 2)) := by ac_rfl
    have hsplit : (s/2)*(2*(s/4)) + (s/2)*(s/2 - 2*(s/4)) = (s/2)*(s/2) := by
      rw [← Nat.mul_add, ← e1]
    have e2 : (s/2)*(s/2)
        = (s/2)*(2*(s/4)) + (s/2)*(s/2 - 2*(s/4)) := hsplit.symm
    rw [e2, ePu]
    exact Nat.add_le_add_left h3 _
  have hD0sq : D0 * D0 ≤ (s / 2) * (s / 2) := Nat.mul_le_mul hD0 hD0
  have hnum : D0 * D0 + t ≤ (s / 2) * (s / 2) + 2 * s :=
    Nat.add_le_add hD0sq ht
  have hexp2 : (2 * ((s / 4) + 1) + 1) * ((s / 2) + 1)
      = ((s / 4) * (s / 2)) * 2 + (s / 4) * 2 + (s / 2) * 3 + 3 := by
    have h3 : (3 : Nat) = 2 + 1 := rfl
    rw [h3]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    ac_rfl
  have hbound2 : (s / 2) * (s / 2) + 2 * s
      ≤ (2 * ((s / 4) + 1) + 1) * ((s / 2) + 1) + ((s / 2) + 1) - 1 := by
    rw [hexp2]
    clear hexp2
    have h1 : (s / 4) * 4 ≤ s := Nat.div_mul_le_self s 4
    have h2 : (s / 2) * 2 ≤ s := Nat.div_mul_le_self s 2
    omega
  have hVx : (2 * ((s / 4) + 1) + 1) * ((s / 2) + 1)
      ≤ (2 * ((s / 4) + 1) + 1) * x0 :=
    Nat.mul_le_mul_left _ hx0lo
  have hbound : (s / 2) * (s / 2) + 2 * s
      ≤ (2 * ((s / 4) + 1) + 1) * x0 + x0 - 1 := by omega
  have hdiv : ((s / 2) * (s / 2) + 2 * s) / x0 ≤ 2 * ((s / 4) + 1) + 1 :=
    (Nat.div_le_iff_le_mul hx0pos).mpr hbound
  have g1 : (D0 * D0 + t) / x0 ≤ ((s / 2) * (s / 2) + 2 * s) / x0 :=
    Nat.div_le_div_right hnum
  have g2 : ((D0 * D0 + t) / x0) / 2 ≤ (((s / 2) * (s / 2) + 2 * s) / x0) / 2 :=
    Nat.div_le_div_right g1
  have g3 : (((s / 2) * (s / 2) + 2 * s) / x0) / 2 ≤ s / 4 + 1 := by
    have hle : (((s / 2) * (s / 2) + 2 * s) / x0) / 2
        ≤ (2 * ((s / 4) + 1) + 1) / 2 :=
      Nat.div_le_div_right hdiv
    omega
  exact Nat.le_trans g2 g3

theorem two_s_le_add_div {s x A : Nat} (hx : 0 < x) (h1 : s * s ≤ A) :
    2 * s ≤ x + A / x := by
  by_cases h2s : 2 * s ≤ x
  · exact Nat.le_trans h2s (Nat.le_add_right _ _)
  · have hxlt : x < 2 * s := Nat.lt_of_not_ge h2s
    have hle : (2 * s - x) * x ≤ s * s := by
      by_cases hxle : x ≤ s
      · have hD : s - x ≤ s := by omega
        have heq : (s + (s - x)) * (s - (s - x)) + (s - x) * (s - x) = s * s :=
          diff_sq_add (by omega)
        have hxeq : x + (s - x) = s := by omega
        have h2eq : 2 * s - x = s + (s - x) := by omega
        have hmul : (2 * s - x) * x = (s + (s - x)) * (s - (s - x)) := by
          congr <;> omega
        rw [hmul]
        have hle : (s + (s - x)) * (s - (s - x)) ≤ s * s := by
          have heq2 : (s + (s - x)) * (s - (s - x)) + (s - x) * (s - x) = s * s :=
            diff_sq_add (by omega)
          omega
        exact hle
      · have hgt : s < x := Nat.lt_of_not_ge hxle
        have hD : x - s < s := by omega
        have hleD : x - s ≤ s := Nat.le_of_lt hD
        have heq : (s + (x - s)) * (s - (x - s)) + (x - s) * (x - s) = s * s :=
          diff_sq_add hleD
        have hxeq : s + (x - s) = x := by omega
        have h2eq : 2 * s - x = s - (x - s) := by omega
        have hmul : (2 * s - x) * x = (s - (x - s)) * (s + (x - s)) := by
          congr <;> omega
        rw [hmul]
        have hle : (s - (x - s)) * (s + (x - s)) ≤ s * s := by
          have heq2 : (s + (x - s)) * (s - (x - s)) + (x - s) * (x - s) = s * s :=
            diff_sq_add hleD
          have hcomm : (s - (x - s)) * (s + (x - s)) = (s + (x - s)) * (s - (x - s)) :=
            Nat.mul_comm _ _
          rw [hcomm]
          omega
        exact hle
    have hleA : (2 * s - x) * x ≤ A := Nat.le_trans hle h1
    have hdiv : 2 * s - x ≤ A / x := (Nat.le_div_iff_mul_le hx).mpr hleA
    omega

theorem s_lt_2x0 {A s : Nat} (hA : 0 < A)
    (h1 : s * s ≤ A) (h2 : A < (s + 1) * (s + 1)) :
    s < 2 * natStart A := by
  have hAne : A ≠ 0 := Nat.ne_of_gt hA
  have hlog := (Nat.log2_eq_iff hAne).mp rfl
  obtain ⟨hL1, hL2⟩ := hlog
  have hpow1 : (2:Nat) ^ (Nat.log2 A + 1) ≤ (2 * natStart A) * (2 * natStart A) := by
    unfold natStart
    have hexp : Nat.log2 A + 1 ≤ (Nat.log2 A) / 2 + 1 + (((Nat.log2 A) / 2 + 1)) := by omega
    have hle : (2:Nat) ^ (Nat.log2 A + 1) ≤ 2 ^ (((Nat.log2 A) / 2 + 1) + (((Nat.log2 A) / 2 + 1))) :=
      Nat.pow_le_pow_right (by omega) hexp
    have heq1 : (2:Nat) ^ (((Nat.log2 A) / 2 + 1) + (((Nat.log2 A) / 2 + 1)))
        = (2 ^ ((Nat.log2 A) / 2 + 1)) * (2 ^ ((Nat.log2 A) / 2 + 1)) := by
      rw [← Nat.pow_add]
    rw [heq1] at hle
    have heq2 : (2:Nat) * (2 ^ ((Nat.log2 A) / 2)) = 2 ^ ((Nat.log2 A) / 2 + 1) := by
      have hps : (2:Nat) ^ ((Nat.log2 A) / 2 + 1) = (2 ^ ((Nat.log2 A) / 2)) * 2 := by
        rw [Nat.pow_succ]
      omega
    have heq3 : (2 * (2 ^ ((Nat.log2 A) / 2))) * (2 * (2 ^ ((Nat.log2 A) / 2)))
        = (2 ^ ((Nat.log2 A) / 2 + 1)) * (2 ^ ((Nat.log2 A) / 2 + 1)) := by
      rw [← heq2]
    omega
  by_cases h : s < 2 * natStart A
  · exact h
  · have hle : 2 * natStart A ≤ s := Nat.le_of_not_gt h
    have hge : (2 * natStart A) * (2 * natStart A) ≤ s * s :=
      Nat.mul_le_mul hle hle
    omega

theorem natStart_pos {A : Nat} (hA : 0 < A) : 0 < natStart A := by
  unfold natStart
  exact Nat.two_pow_pos _

theorem natStart_sq_le {A : Nat} (hA : 0 < A) : natStart A * natStart A ≤ A := by
  have hAne : A ≠ 0 := Nat.ne_of_gt hA
  have hlog := (Nat.log2_eq_iff hAne).mp rfl
  obtain ⟨h1, _h2⟩ := hlog
  -- Actually Nat.log2_eq_iff gives 2^L ≤ A ∧ A < 2^(L+1) where L = log2 A? Need L = Nat.log2 A.
  -- h1 : 2 ^ (Nat.log2 A) ≤ A
  unfold natStart
  have hdiv : (Nat.log2 A) / 2 + ((Nat.log2 A) / 2) ≤ Nat.log2 A := by omega
  have hpow : (2:Nat) ^ ((Nat.log2 A) / 2 + ((Nat.log2 A) / 2)) ≤ 2 ^ (Nat.log2 A) :=
    Nat.pow_le_pow_right (by omega) hdiv
  have heq : (2 ^ ((Nat.log2 A) / 2)) * (2 ^ ((Nat.log2 A) / 2))
      = 2 ^ ((Nat.log2 A) / 2 + ((Nat.log2 A) / 2)) := by
    rw [← Nat.pow_add]
  rw [heq]
  exact Nat.le_trans hpow h1

theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry

theorem req_mint_backed : MintBacked sqrt := by
  intro a0 a1 l h
  have h' := firstMint_eq_some h
  obtain ⟨hprod, _hroot, hliq⟩ := h'
  have hNA := req_sqrt_not_above (a0 * a1)
  have hprod_eq : (a0 * a1).toNat = a0.toNat * a1.toNat :=
    toNat_mul_of_lt hprod
  have hNA' : (sqrt (a0 * a1)).toNat * (sqrt (a0 * a1)).toNat ≤ a0.toNat * a1.toNat := by
    rw [← hprod_eq]; exact hNA
  have heq : (l.toNat + 1000) * (l.toNat + 1000)
      = (sqrt (a0 * a1)).toNat * (sqrt (a0 * a1)).toNat := by
    rw [hliq]
  rw [heq]; exact hNA'

theorem req_mint_full : MintFull sqrt := by
  intro a0 a1 l h
  have h' := firstMint_eq_some h
  obtain ⟨hprod, _hroot, hliq⟩ := h'
  have hNB := req_sqrt_not_below (a0 * a1)
  have hprod_eq : (a0 * a1).toNat = a0.toNat * a1.toNat :=
    toNat_mul_of_lt hprod
  have hNB' : a0.toNat * a1.toNat < ((sqrt (a0 * a1)).toNat + 1) * ((sqrt (a0 * a1)).toNat + 1) := by
    rw [← hprod_eq]; exact hNB
  have hl : l.toNat + 1001 = (sqrt (a0 * a1)).toNat + 1 := by omega
  have heq : (l.toNat + 1001) * (l.toNat + 1001)
      = ((sqrt (a0 * a1)).toNat + 1) * ((sqrt (a0 * a1)).toNat + 1) := by
    rw [hl]
  rw [heq]; exact hNB'

theorem req_mint_live : MintLive sqrt := by
  intro a0 a1 hprod hbig
  have hNB := req_sqrt_not_below (a0 * a1)
  have hprod_eq : (a0 * a1).toNat = a0.toNat * a1.toNat :=
    toNat_mul_of_lt (by omega)
  have hNB' : (a0 * a1).toNat < ((sqrt (a0 * a1)).toNat + 1) * ((sqrt (a0 * a1)).toNat + 1) := hNB
  rw [hprod_eq] at hNB'
  have hroot : 1000 < (sqrt (a0 * a1)).toNat := by
    by_cases h : 1000 < (sqrt (a0 * a1)).toNat
    · exact h
    · have hc' : (sqrt (a0 * a1)).toNat ≤ 1000 := Nat.le_of_not_gt h
      have hle : ((sqrt (a0 * a1)).toNat + 1) * ((sqrt (a0 * a1)).toNat + 1) ≤ 1001 * 1001 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  have h1 : a0.toNat * a1.toNat < 2 ^ 256 := by omega
  exact firstMint_isSome h1 hroot

theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  intro a
  have hNA := req_sqrt_not_above a
  have hNB := req_sqrt_not_below a
  have hA : a.toNat < 2 ^ 256 := a.isLt
  have hprod_lt : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 :=
    Nat.lt_of_le_of_lt hNA hA
  have hBV : (sqrt a * sqrt a).toNat = (sqrt a).toNat * (sqrt a).toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hprod_lt]
  have hr_small : (sqrt a).toNat < 2 ^ 128 := by
    by_cases h : (sqrt a).toNat < 2 ^ 128
    · exact h
    · have hge : 2 ^ 128 ≤ (sqrt a).toNat := Nat.le_of_not_gt h
      have hge2 : (2:Nat) ^ 256 ≤ (sqrt a).toNat * (sqrt a).toNat := by
        have heq : (2:Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 := by
          rw [← Nat.pow_add]
        rw [heq]
        exact Nat.mul_le_mul hge hge
      omega
  have h10 : ((1 : U256)).toNat = 1 := by decide
  have h00 : ((0 : U256)).toNat = 0 := by decide
  by_cases h : sqrt a * sqrt a < a
  · have hNat : (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
      have := BitVec.lt_def.mp h
      rw [hBV] at this
      exact this
    have hUp_eq : (sqrtUp sqrt a).toNat = (sqrt a).toNat + 1 := by
      unfold sqrtUp
      simp only []
      rw [if_pos h, BitVec.toNat_add, h10, Nat.mod_eq_of_lt (by omega)]
    rw [hUp_eq]
    omega
  · have hNer : ¬ (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
      intro hc
      apply h
      rw [BitVec.lt_def, hBV]
      exact hc
    have heq : (sqrt a).toNat * (sqrt a).toNat = a.toNat := by omega
    have hUp_eq : (sqrtUp sqrt a).toNat = (sqrt a).toNat := by
      unfold sqrtUp
      simp only []
      rw [if_neg h, BitVec.toNat_add, h00, Nat.add_zero,
        Nat.mod_eq_of_lt (by omega : (sqrt a).toNat < 2 ^ 256)]
    rw [hUp_eq, heq]
    exact Nat.le_refl _

theorem req_sqrt_up_tight : SqrtUpTight sqrt := by
  intro a hpos
  have hNA := req_sqrt_not_above a
  have hA : a.toNat < 2 ^ 256 := a.isLt
  have hprod_lt : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 :=
    Nat.lt_of_le_of_lt hNA hA
  have hBV : (sqrt a * sqrt a).toNat = (sqrt a).toNat * (sqrt a).toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hprod_lt]
  have hr_small : (sqrt a).toNat < 2 ^ 128 := by
    by_cases h : (sqrt a).toNat < 2 ^ 128
    · exact h
    · have hge : 2 ^ 128 ≤ (sqrt a).toNat := Nat.le_of_not_gt h
      have hge2 : (2:Nat) ^ 256 ≤ (sqrt a).toNat * (sqrt a).toNat := by
        have heq : (2:Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 := by
          rw [← Nat.pow_add]
        rw [heq]
        exact Nat.mul_le_mul hge hge
      omega
  have h10 : ((1 : U256)).toNat = 1 := by decide
  have h00 : ((0 : U256)).toNat = 0 := by decide
  by_cases h : sqrt a * sqrt a < a
  · have hNat : (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
      have := BitVec.lt_def.mp h
      rw [hBV] at this
      exact this
    have hUp_eq : (sqrtUp sqrt a).toNat = (sqrt a).toNat + 1 := by
      unfold sqrtUp
      simp only []
      rw [if_pos h, BitVec.toNat_add, h10, Nat.mod_eq_of_lt (by omega)]
    rw [hUp_eq]
    have hsub : ((sqrt a).toNat + 1 - 1) = (sqrt a).toNat := by omega
    rw [hsub]
    exact hNat
  · have hUp_eq : (sqrtUp sqrt a).toNat = (sqrt a).toNat := by
      unfold sqrtUp
      simp only []
      rw [if_neg h, BitVec.toNat_add, h00, Nat.add_zero,
        Nat.mod_eq_of_lt (by omega : (sqrt a).toNat < 2 ^ 256)]
    have hNer : ¬ (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
      intro hc
      apply h
      rw [BitVec.lt_def, hBV]
      exact hc
    have heq : (sqrt a).toNat * (sqrt a).toNat = a.toNat := by omega
    have hrpos : 0 < (sqrt a).toNat := by omega
    have hlt : ((sqrt a).toNat - 1) * ((sqrt a).toNat - 1) < (sqrt a).toNat * (sqrt a).toNat := by
      have h1 : (sqrt a).toNat - 1 < (sqrt a).toNat := by omega
      have h2 : (sqrt a).toNat - 1 ≤ (sqrt a).toNat := by omega
      have h3 : 0 < (sqrt a).toNat := hrpos
      exact Nat.mul_lt_mul_of_lt_of_le h1 h2 h3
    rw [hUp_eq]
    omega

theorem req_newton_budget : NewtonBudget sqrt :=
  ⟨7, Nat.le_refl 7, fun _ => rfl⟩

end OzSqrt
