import OzSqrt.Spec
import OzSqrt.Lemmas
namespace OzSqrt

def sqrt : SqrtFn := fun a =>
  if a = 0 then 0
  else
    let result : U256 := (1 : U256) <<< (log2 a >>> 1)
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    min result (a / result)

theorem req_newton_budget : NewtonBudget sqrt := by
  unfold NewtonBudget
  exact ⟨7, Nat.le_refl 7, fun a => by simp only [sqrt, newtonSqrt, iterate, newtonStep]⟩

-- Nat Newton step
def ns (A r : Nat) : Nat := (r + A / r) / 2

-- square monotonicity
theorem sq_le_of_le {a b : Nat} (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

theorem lt_of_sq_lt {a b : Nat} (h : a * a < b * b) : a < b := by
  by_cases hc : a < b
  · exact hc
  · have hle : b ≤ a := by omega
    have := sq_le_of_le hle
    omega

theorem le_of_sq_le {a b : Nat} (h : a * a ≤ b * b) : a ≤ b := by
  by_cases hc : a ≤ b
  · exact hc
  · have hlt : b < a := by omega
    have h1 : b * b < a * a := by
      have h2 : b + 1 ≤ a := by omega
      have h3 : (b + 1) * (b + 1) ≤ a * a := sq_le_of_le h2
      have h4 : b * b < (b + 1) * (b + 1) := by
        have hb1 : b * b < b * b + (b + b + 1) := by omega
        have hexpand : (b + 1) * (b + 1) = b * b + (b + b + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
          ac_rfl
        omega
      omega
    omega

-- log2 bounds from library lemma
theorem log2_bounds {n : Nat} (h : 0 < n) : 2 ^ Nat.log2 n ≤ n ∧ n < 2 ^ (Nat.log2 n + 1) := by
  have := (Nat.log2_eq_iff (by omega : n ≠ 0)).mp rfl
  exact this

-- sqrt characterization helpers
theorem le_sqrt_of_sq_le {A r : Nat} (h : r * r ≤ A) : r ≤ Nat.sqrt A := by
  by_cases hc : r ≤ Nat.sqrt A
  · exact hc
  · have hlt : Nat.sqrt A < r := by omega
    have hle : Nat.sqrt A + 1 ≤ r := by omega
    have h1 : (Nat.sqrt A + 1) * (Nat.sqrt A + 1) ≤ r * r := sq_le_of_le hle
    have h2 : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := by
      have := Nat.lt_succ_sqrt A
      omega
    omega

theorem sqrt_lt_of_lt_succ_sq {A r : Nat} (h : A < (r + 1) * (r + 1)) (h2 : r * r ≤ A) : Nat.sqrt A = r := by
  have hle1 : r ≤ Nat.sqrt A := le_sqrt_of_sq_le h2
  have hle2 : Nat.sqrt A ≤ r := by
    by_cases hc : Nat.sqrt A ≤ r
    · exact hc
    · have hlt : r < Nat.sqrt A := by omega
      have hle : r + 1 ≤ Nat.sqrt A := by omega
      have h1 : (r + 1) * (r + 1) ≤ Nat.sqrt A * Nat.sqrt A := sq_le_of_le hle
      have h3 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
      omega
  omega

-- initial guess r0 = 2^(log2 A / 2)
def r0n (A : Nat) : Nat := 2 ^ (Nat.log2 A / 2)

theorem r0n_pos (A : Nat) : 0 < r0n A := by
  unfold r0n
  exact Nat.pow_pos (by decide)

theorem r0n_sq_le {A : Nat} (h : 0 < A) : r0n A * r0n A ≤ A := by
  unfold r0n
  have hb := log2_bounds h
  have hle : 2 * (Nat.log2 A / 2) ≤ Nat.log2 A := by
    have := Nat.div_add_mod (Nat.log2 A) 2
    omega
  have h1 : (2 ^ (Nat.log2 A / 2)) * (2 ^ (Nat.log2 A / 2)) = 2 ^ (2 * (Nat.log2 A / 2)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h1]
  have h2 : (2 : Nat) ^ (2 * (Nat.log2 A / 2)) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide) hle
  omega

theorem r0n_lt_two_mul {A : Nat} (h : 0 < A) : Nat.sqrt A < 2 * r0n A := by
  have hs2 := Nat.sqrt_le A
  have hlt := Nat.lt_succ_sqrt A
  have hr0 := r0n_sq_le h
  have hb := log2_bounds h
  have h4 : (2 * r0n A) * (2 * r0n A) = 4 * (r0n A * r0n A) := by
    ac_rfl
  have he : Nat.log2 A + 1 ≤ 2 * (Nat.log2 A / 2) + 2 := by
    have := Nat.div_add_mod (Nat.log2 A) 2
    omega
  have hpow : (2 : Nat) ^ (Nat.log2 A + 1) ≤ 2 ^ (2 * (Nat.log2 A / 2) + 2) :=
    Nat.pow_le_pow_right (by decide) he
  have hr0pow : r0n A * r0n A = 2 ^ (2 * (Nat.log2 A / 2)) := by
    unfold r0n
    rw [← Nat.pow_add]
    congr 1
    omega
  have h5 : A < 4 * (r0n A * r0n A) := by
    have h4eq : (4 : Nat) = 2 ^ 2 := by decide
    have h6 : (4 : Nat) * (r0n A * r0n A) = 2 ^ (2 * (Nat.log2 A / 2) + 2) := by
      rw [hr0pow, h4eq, ← Nat.pow_add]
      congr 1
      omega
    omega
  have h6 : Nat.sqrt A * Nat.sqrt A < (2 * r0n A) * (2 * r0n A) := by omega
  exact lt_of_sq_lt h6

theorem r0n_le_sqrt {A : Nat} (h : 0 < A) : r0n A ≤ Nat.sqrt A :=
  le_sqrt_of_sq_le (r0n_sq_le h)

-- Newton step stays above sqrt for any positive r
theorem ns_ge_sqrt {A r : Nat} (hr : 0 < r) : Nat.sqrt A ≤ ns A r := by
  unfold ns
  by_cases hA : A = 0
  · subst hA
    have h0 : Nat.sqrt 0 = 0 := by rfl
    simp [h0]
  · have hApos : 0 < A := by omega
    have hs2 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
    have h2s : 2 * Nat.sqrt A ≤ r + A / r := by
      have htot := Nat.le_total r (Nat.sqrt A)
      cases htot with
      | inl hle =>
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
        have hle_div : r + 2 * d ≤ A / r := by
          rw [Nat.le_div_iff_mul_le hr]
          have hexpand : (r + d) * (r + d) = (r + 2 * d) * r + d * d := by
            have h2d : 2 * d = d + d := by omega
            rw [h2d]
            simp only [Nat.add_mul, Nat.mul_add]
            ac_rfl
          have hsq : (r + d) * (r + d) ≤ A := by
            have := hs2
            rw [hd] at this
            exact this
          have hle1 : (r + 2 * d) * r ≤ (r + d) * (r + d) := by
            rw [hexpand]
            exact Nat.le_add_right _ _
          omega
        have heq : 2 * (r + d) = r + (r + 2 * d) := by omega
        have hgoal : 2 * (r + d) ≤ r + A / r := by omega
        rw [← hd] at hgoal
        have heq2 : 2 * Nat.sqrt A = 2 * (r + d) := by rw [hd]
        omega
      | inr hle =>
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        by_cases hds : Nat.sqrt A ≤ d
        · have h1 : 2 * Nat.sqrt A ≤ Nat.sqrt A + d := by omega
          have h2 : Nat.sqrt A + d ≤ Nat.sqrt A + d + A / (Nat.sqrt A + d) :=
            Nat.le_add_right _ _
          omega
        · have hlt : d < Nat.sqrt A := by omega
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
          have hs_eq : Nat.sqrt A = d + (k + 1) := by omega
          have hle_k : k + 1 ≤ A / (Nat.sqrt A + d) := by
            rw [Nat.le_div_iff_mul_le (by omega : 0 < Nat.sqrt A + d)]
            have hexpand : (d + (k + 1)) * (d + (k + 1))
                = (k + 1) * (d + (k + 1) + d) + d * d := by
              simp only [Nat.add_mul, Nat.mul_add]
              ac_rfl
            have hsq : (k + 1) * (Nat.sqrt A + d) ≤ Nat.sqrt A * Nat.sqrt A := by
              rw [hs_eq]
              have heq : (d + (k + 1)) * (d + (k + 1))
                  = (k + 1) * (d + (k + 1) + d) + d * d := hexpand
              have hle1 : (k + 1) * (d + (k + 1) + d)
                  ≤ (d + (k + 1)) * (d + (k + 1)) := by
                rw [heq]
                exact Nat.le_add_right _ _
              exact hle1
            have hss : Nat.sqrt A * Nat.sqrt A ≤ A := hs2
            have hle_trans : (k + 1) * (Nat.sqrt A + d) ≤ A :=
              Nat.le_trans hsq hss
            exact hle_trans
          omega
    have h2 : Nat.sqrt A * 2 ≤ r + A / r := by
      have hcomm : Nat.sqrt A * 2 = 2 * Nat.sqrt A := by rw [Nat.mul_comm]
      omega
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr h2

-- Quadratic upper bound: when r = s+d, Newton error shrinks
-- 2*(s+d)*(ns - s) ≤ d^2 + 2*s
theorem ns_upper {A d : Nat} :
    2 * (Nat.sqrt A + d) * (ns A (Nat.sqrt A + d) - Nat.sqrt A)
      ≤ d * d + 2 * Nat.sqrt A := by
  have hs2 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
  have hAlt : A ≤ Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A := by
    have hexpand : (Nat.sqrt A + 1) * (Nat.sqrt A + 1)
        = Nat.sqrt A * Nat.sqrt A + (2 * Nat.sqrt A + 1) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.two_mul]
      ac_rfl
    have hlt : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt A
    omega
  have h2ns_le : 2 * ns A (Nat.sqrt A + d) ≤ Nat.sqrt A + d + A / (Nat.sqrt A + d) := by
    unfold ns
    have hdiv : 2 * ((Nat.sqrt A + d + A / (Nat.sqrt A + d)) / 2)
        ≤ Nat.sqrt A + d + A / (Nat.sqrt A + d) := by
      have h0 := Nat.div_add_mod (Nat.sqrt A + d + A / (Nat.sqrt A + d)) 2
      omega
    have heq : ns A (Nat.sqrt A + d) = (Nat.sqrt A + d + A / (Nat.sqrt A + d)) / 2 := by
      rfl
    omega
  have hmul_le : (Nat.sqrt A + d) * (A / (Nat.sqrt A + d)) ≤ A :=
    Nat.mul_div_le A (Nat.sqrt A + d)
  have hmain : 2 * (Nat.sqrt A + d) * ns A (Nat.sqrt A + d)
      ≤ 2 * (Nat.sqrt A + d) * Nat.sqrt A + (d * d + 2 * Nat.sqrt A) := by
    have h1 : 2 * (Nat.sqrt A + d) * ns A (Nat.sqrt A + d)
        ≤ (Nat.sqrt A + d) * (Nat.sqrt A + d + A / (Nat.sqrt A + d)) := by
      have h2ns : 2 * ns A (Nat.sqrt A + d) ≤ Nat.sqrt A + d + A / (Nat.sqrt A + d) := h2ns_le
      have hmul : (Nat.sqrt A + d) * (2 * ns A (Nat.sqrt A + d))
          ≤ (Nat.sqrt A + d) * (Nat.sqrt A + d + A / (Nat.sqrt A + d)) :=
        Nat.mul_le_mul_left _ h2ns
      have heq1 : 2 * (Nat.sqrt A + d) * ns A (Nat.sqrt A + d)
          = (Nat.sqrt A + d) * (2 * ns A (Nat.sqrt A + d)) := by ac_rfl
      omega
    have h2 : (Nat.sqrt A + d) * (Nat.sqrt A + d + A / (Nat.sqrt A + d))
        = (Nat.sqrt A + d) * (Nat.sqrt A + d) + (Nat.sqrt A + d) * (A / (Nat.sqrt A + d)) := by
      rw [Nat.mul_add]
    have h3 : (Nat.sqrt A + d) * (Nat.sqrt A + d) + (Nat.sqrt A + d) * (A / (Nat.sqrt A + d))
        ≤ 2 * (Nat.sqrt A + d) * Nat.sqrt A + (d * d + 2 * Nat.sqrt A) := by
      have h_q_le : (Nat.sqrt A + d) * (A / (Nat.sqrt A + d))
          ≤ Nat.sqrt A * Nat.sqrt A + 2 * Nat.sqrt A :=
        Nat.le_trans hmul_le hAlt
      have hcomm_sd : Nat.sqrt A * d = d * Nat.sqrt A := Nat.mul_comm _ _
      simp only [Nat.add_mul, Nat.mul_add, Nat.two_mul] at h_q_le ⊢
      rw [hcomm_sd] at ⊢
      omega
    omega
  have heq_sub : 2 * (Nat.sqrt A + d) * (ns A (Nat.sqrt A + d) - Nat.sqrt A)
      = 2 * (Nat.sqrt A + d) * ns A (Nat.sqrt A + d)
        - 2 * (Nat.sqrt A + d) * Nat.sqrt A := by
    rw [Nat.mul_sub]
  have hmain_comm : 2 * (Nat.sqrt A + d) * Nat.sqrt A + (d * d + 2 * Nat.sqrt A)
      = (d * d + 2 * Nat.sqrt A) + 2 * (Nat.sqrt A + d) * Nat.sqrt A := by
    ac_rfl
  rw [hmain_comm] at hmain
  have hle_sub : 2 * (Nat.sqrt A + d) * ns A (Nat.sqrt A + d)
      - 2 * (Nat.sqrt A + d) * Nat.sqrt A ≤ d * d + 2 * Nat.sqrt A :=
    Nat.sub_le_of_le_add hmain
  rw [← heq_sub] at hle_sub
  exact hle_sub

-- Nat iteration of Newton steps
def niter (A : Nat) : Nat → Nat → Nat
  | 0, r => r
  | k + 1, r => niter A k (ns A r)

theorem niter_pos {A r : Nat} (hA : 0 < A) (hr : 0 < r) (k : Nat) : 0 < niter A k r := by
  induction k generalizing r with
  | zero => exact hr
  | succ k ih =>
    apply ih
    unfold ns
    by_cases hr1 : r = 1
    · subst hr1
      omega
    · have hr2 : 2 ≤ r := by omega
      generalize A / r = q
      omega

theorem niter_ge_sqrt {A r : Nat} (hr : 0 < r) (k : Nat) : Nat.sqrt A ≤ niter A (k + 1) r := by
  induction k generalizing r with
  | zero =>
    simp only [niter]
    exact ns_ge_sqrt hr
  | succ k ih =>
    simp only [niter]
    by_cases hA0 : A = 0
    · subst hA0
      have h0 : Nat.sqrt 0 = 0 := by rfl
      rw [h0]
      exact Nat.zero_le _
    · have hA : 0 < A := by omega
      have hpos : 0 < ns A r := niter_pos hA hr 1
      exact ih hpos

-- sqrt < 2^128 when A < 2^256
theorem sqrt_lt_128 {A : Nat} (hA : A < 2 ^ 256) : Nat.sqrt A < 2 ^ 128 := by
  have h1 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
  have h2 : (2 ^ 128) * (2 ^ 128) = 2 ^ 256 := by
    rw [← Nat.pow_add]
  have h3 : Nat.sqrt A * Nat.sqrt A < (2 ^ 128) * (2 ^ 128) := by omega
  exact lt_of_sq_lt h3

-- r0 ≤ 2^127 when A < 2^256
theorem r0n_le_127 {A : Nat} (hA : A < 2 ^ 256) : r0n A ≤ 2 ^ 127 := by
  unfold r0n
  by_cases hA0 : A = 0
  · subst hA0
    simp
  · have hpos : 0 < A := by omega
    have hb := log2_bounds hpos
    have he : Nat.log2 A ≤ 255 := by
      have h1 : 2 ^ Nat.log2 A ≤ A := hb.1
      have h2 : (2 : Nat) ^ 256 = 2 ^ 256 := by rfl
      have h3 : 2 ^ Nat.log2 A < 2 ^ 256 := by omega
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h3
      omega
    have he2 : Nat.log2 A / 2 ≤ 127 := by omega
    exact Nat.pow_le_pow_right (by decide) he2

-- sqrt toNat equals Nat.sqrt
theorem sqrt_toNat_eq (a : U256) : (sqrt a).toNat = Nat.sqrt a.toNat := sorry

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  unfold SqrtNotAbove
  intro a
  rw [sqrt_toNat_eq]
  exact Nat.sqrt_le _

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  unfold SqrtNotBelow
  intro a
  rw [sqrt_toNat_eq]
  exact Nat.lt_succ_sqrt _
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := by
  unfold SqrtUpCovers
  intro a
  -- s = sqrt, S = Nat.sqrt
  have hs_eq : (sqrt a).toNat = Nat.sqrt a.toNat := sqrt_toNat_eq a
  have hs2 : (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat := req_sqrt_not_above a
  have hlt : a.toNat < ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1) := req_sqrt_not_below a
  -- s*s < 2^256, so BitVec * has no wrap
  have hA256 : a.toNat < 2 ^ 256 := a.isLt
  have hss256 : (sqrt a).toNat * (sqrt a).toNat < 2 ^ 256 := by omega
  have hmul_toNat : ((sqrt a) * (sqrt a)).toNat = (sqrt a).toNat * (sqrt a).toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hss256]
  -- BitVec < corresponds to Nat <
  have hlt_iff : ((sqrt a) * (sqrt a) < a) = ((sqrt a).toNat * (sqrt a).toNat < a.toNat) := by
    have h1 : (((sqrt a) * (sqrt a)) < a) = ((((sqrt a) * (sqrt a)).toNat < a.toNat)) := by
      rw [BitVec.lt_def]
    rw [h1, hmul_toNat]
    rfl
  -- sqrtUp toNat = s + (if s*s < A then 1 else 0)
  have hUp_toNat : (sqrtUp sqrt a).toNat
      = (sqrt a).toNat + (if (sqrt a).toNat * (sqrt a).toNat < a.toNat then 1 else 0) := by
    unfold sqrtUp
    have h1 : (sqrt a + (if (sqrt a) * (sqrt a) < a then 1 else 0)).toNat
        = (sqrt a).toNat + (if (sqrt a) * (sqrt a) < a then (1 : U256) else 0).toNat := by
      have hbound : (sqrt a).toNat + (if (sqrt a) * (sqrt a) < a then (1 : U256) else 0).toNat < 2 ^ 256 := by
        have hs128 : (sqrt a).toNat < 2 ^ 128 := by
          rw [hs_eq]
          exact sqrt_lt_128 (by omega : a.toNat < 2 ^ 256)
        have hif : (if (sqrt a) * (sqrt a) < a then (1 : U256) else 0).toNat ≤ 1 := by
          by_cases hc : (sqrt a) * (sqrt a) < a
          · rw [if_pos hc]
            decide
          · rw [if_neg hc]
            simp
        omega
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hbound]
    have hif_toNat : (if (sqrt a) * (sqrt a) < a then (1 : U256) else 0).toNat
        = (if (sqrt a).toNat * (sqrt a).toNat < a.toNat then 1 else 0) := by
      by_cases hc : (sqrt a) * (sqrt a) < a
      · rw [if_pos hc]
        have hc' : (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
          have := BitVec.lt_def.mp hc
          rw [hmul_toNat] at this
          exact this
        rw [if_pos hc']
        decide
      · rw [if_neg hc]
        have hc' : ¬ (sqrt a).toNat * (sqrt a).toNat < a.toNat := by
          intro hlt'
          have : (sqrt a) * (sqrt a) < a := by
            have := BitVec.lt_def.mpr (by rw [hmul_toNat]; exact hlt')
            exact this
          exact hc this
        rw [if_neg hc']
        simp
    rw [h1, hif_toNat]
  -- now show A ≤ (s + (if ...))^2
  have hcases : (sqrt a).toNat * (sqrt a).toNat < a.toNat
      ∨ ¬ (sqrt a).toNat * (sqrt a).toNat < a.toNat := by omega
  cases hcases with
  | inl hlt_ss =>
    have hUp_eq : (sqrtUp sqrt a).toNat = (sqrt a).toNat + 1 := by
      rw [hUp_toNat, if_pos hlt_ss]
    rw [hUp_eq]
    have hle : a.toNat ≤ ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1) := by omega
    omega
  | inr hge =>
    have hUp_eq : (sqrtUp sqrt a).toNat = (sqrt a).toNat := by
      rw [hUp_toNat, if_neg hge]
      omega
    rw [hUp_eq]
    have heq : (sqrt a).toNat * (sqrt a).toNat = a.toNat := by omega
    omega
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry

end OzSqrt
