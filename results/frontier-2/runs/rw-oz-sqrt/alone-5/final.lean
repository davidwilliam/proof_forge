import OzSqrt.Spec
import OzSqrt.Lemmas

namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem req_newton_budget : NewtonBudget sqrt := ⟨7, Nat.le_refl 7, fun a => rfl⟩

/-! Nat-level Newton theory -/

def nstep (A x : Nat) : Nat := (x + A / x) / 2

def nseq (A : Nat) : Nat → Nat
  | 0 => 2 ^ (Nat.log2 A / 2)
  | n+1 => nstep A (nseq A n)

theorem le_sqrt_of_sq_le (x A : Nat) (h : x * x ≤ A) : x ≤ Nat.sqrt A := by
  by_cases hle : x ≤ Nat.sqrt A
  · exact hle
  · have hlt : Nat.sqrt A < x := Nat.lt_of_not_le hle
    have hsucc : Nat.sqrt A + 1 ≤ x := Nat.succ_le_of_lt hlt
    have hmul : (Nat.sqrt A + 1) * (Nat.sqrt A + 1) ≤ x * x :=
      Nat.mul_le_mul hsucc hsucc
    have hlt2 : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt A
    omega

theorem sqrt_lt_of_sq_lt (s x A : Nat) (hs : s = Nat.sqrt A) (h : A < x * x) : s < x := by
  subst hs
  by_cases hle : Nat.sqrt A < x
  · exact hle
  · have hle2 : x ≤ Nat.sqrt A := Nat.le_of_not_lt hle
    have h1 : x * x ≤ Nat.sqrt A * Nat.sqrt A := Nat.mul_le_mul hle2 hle2
    have h2 : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
    omega

theorem x0_sq_le (A : Nat) (hA : 0 < A) : (2 ^ (Nat.log2 A / 2)) ^ 2 ≤ A := by
  have hne : A ≠ 0 := by omega
  have hL := (Nat.log2_eq_iff hne).mp rfl
  obtain ⟨h1, h2⟩ := hL
  have hdiv : 2 * (Nat.log2 A / 2) ≤ Nat.log2 A := Nat.mul_div_le _ _
  have hpow : 2 ^ (2 * (Nat.log2 A / 2)) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide) hdiv
  have hpow2 : (2 ^ (Nat.log2 A / 2)) ^ 2 = 2 ^ (2 * (Nat.log2 A / 2)) := by
    rw [← Nat.pow_mul]
    have : 2 * (Nat.log2 A / 2) = (Nat.log2 A / 2) * 2 := by omega
    rw [this]
  rw [hpow2]
  omega

theorem x0_2sq_gt (A : Nat) (hA : 0 < A) : A < (2 * 2 ^ (Nat.log2 A / 2)) ^ 2 := by
  have hne : A ≠ 0 := by omega
  have hL := (Nat.log2_eq_iff hne).mp rfl
  obtain ⟨h1, h2⟩ := hL
  have hle : Nat.log2 A + 1 ≤ 2 * (Nat.log2 A / 2) + 2 := by omega
  have hpow2 : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ (2 * (Nat.log2 A / 2) + 2) :=
    Nat.pow_le_pow_right (by decide) hle
  have hexp : (2 * 2 ^ (Nat.log2 A / 2)) ^ 2 = 2 ^ (2 * (Nat.log2 A / 2) + 2) := by
    have h1 : 2 * 2 ^ (Nat.log2 A / 2) = 2 ^ (Nat.log2 A / 2 + 1) := by
      rw [Nat.pow_succ]
      omega
    rw [h1, ← Nat.pow_mul]
    have : (Nat.log2 A / 2 + 1) * 2 = 2 * (Nat.log2 A / 2) + 2 := by omega
    rw [this]
  omega

theorem sq_add_ge_2mul_aux1 (x d : Nat) :
    2 * (x + d) * x + d * d = x * x + (x + d) * (x + d) := by
  have h2 : (2 : Nat) * (x + d) = (x + d) + (x + d) := Nat.two_mul (x + d)
  rw [h2, Nat.add_mul]
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem sq_add_ge_2mul_aux2 (s d : Nat) :
    2 * s * (s + d) + d * d = s * s + (s + d) * (s + d) := by
  have h2 : (2 : Nat) * s * (s + d) = (s * (s + d) + s * (s + d)) := by
    rw [Nat.two_mul]
    rw [Nat.add_mul]
  rw [h2]
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem sq_add_ge_2mul (x s : Nat) : 2 * s * x ≤ x * x + s * s := by
  by_cases hle : x ≤ s
  · obtain ⟨d, rfl⟩ : ∃ d, s = x + d := ⟨s - x, by omega⟩
    have heq := sq_add_ge_2mul_aux1 x d
    omega
  · have hlt : s < x := Nat.lt_of_not_le hle
    obtain ⟨d, rfl⟩ : ∃ d, x = s + d := ⟨x - s, by omega⟩
    have heq := sq_add_ge_2mul_aux2 s d
    omega

theorem x0_pos (A : Nat) : 0 < 2 ^ (Nat.log2 A / 2) := Nat.two_pow_pos _

theorem x0_le_sqrt (A : Nat) (hA : 0 < A) : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A := by
  apply le_sqrt_of_sq_le
  rw [← Nat.pow_two]
  exact x0_sq_le A hA

theorem sqrt_lt_2x0 (A : Nat) (hA : 0 < A) : Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) := by
  apply sqrt_lt_of_sq_lt _ _ A rfl
  rw [← Nat.pow_two]
  exact x0_2sq_gt A hA

theorem nstep_pos (A x : Nat) (_hA : 0 < A) (hx : 0 < x) : 0 < nstep A x := by
  unfold nstep
  by_cases hx1 : x = 1
  · subst hx1
    have hdiv : A / 1 = A := Nat.div_one A
    rw [hdiv]
    have h2 : 2 ≤ 1 + A := by omega
    exact Nat.div_pos h2 (by decide)
  · have hx2 : 2 ≤ x := by omega
    have hle : x ≤ x + A / x := Nat.le_add_right x (A / x)
    have h2 : 2 ≤ x + A / x := Nat.le_trans hx2 hle
    exact Nat.div_pos h2 (by decide)

theorem expand_succ_mul (x q : Nat) : (x + q + 1) * x = x * x + q * x + x := by
  simp only [Nat.add_mul, Nat.one_mul]

theorem nstep_ge (A x : Nat) (_hA : 0 < A) (hx : 0 < x)
    (s : Nat) (hs : s = Nat.sqrt A) (_hspos : 0 < s) :
    s ≤ nstep A x := by
  unfold nstep
  have _hsle : s * s ≤ A := by rw [hs]; exact Nat.sqrt_le A
  have hle_add : x ≤ x + A / x := Nat.le_add_right x (A / x)
  have h2s : 2 * s ≤ x + A / x := by
    by_cases hge : 2 * s ≤ x
    · omega
    · have _hlt2 : x < 2 * s := Nat.lt_of_not_le hge
      by_cases hcon : x + A / x < 2 * s
      · have hle_succ : x + A / x + 1 ≤ 2 * s := Nat.succ_le_of_lt hcon
        have hr : A % x < x := Nat.mod_lt A hx
        have _heq : x * (A / x) + A % x = A := Nat.div_add_mod A x
        have hr1 : A % x + 1 ≤ x := Nat.succ_le_of_lt hr
        have hmul_le : (x + A / x + 1) * x ≤ (2 * s) * x :=
          Nat.mul_le_mul_right x hle_succ
        have hexp : (x + A / x + 1) * x = x * x + (A / x) * x + x := expand_succ_mul x (A / x)
        have _hcomm : (A / x) * x = x * (A / x) := Nat.mul_comm _ _
        have hsq := sq_add_ge_2mul x s
        omega
      · omega
  have h1 : s * 2 ≤ x + A / x := by omega
  have h2 : s * 2 / 2 ≤ (x + A / x) / 2 := Nat.div_le_div_right h1
  have h3 : s * 2 / 2 = s := by omega
  omega

theorem nstep_exact_le (A x s f d : Nat) (hxpos : 0 < x)
    (hs_eq : s * s + d = A)
    (hx_eq : x + f = s) :
    nstep A x = s + (f * f + d) / (2 * x) := by
  unfold nstep
  have hs_eq2 : s = x + f := by omega
  have hA_eq : A = x * (s + f) + (f * f + d) := by
    have h1 : s * s = x * (s + f) + f * f := by
      rw [hs_eq2]
      simp only [Nat.add_mul, Nat.mul_add]
      ac_rfl
    omega
  have hq_eq : A / x = (s + f) + (f * f + d) / x := by
    rw [hA_eq]
    exact Nat.mul_add_div hxpos _ _
  have hsum : x + A / x = 2 * s + (f * f + d) / x := by
    rw [hq_eq]
    omega
  have hdiv : (x + A / x) / 2 = s + ((f * f + d) / x) / 2 := by
    rw [hsum]
    have h1 : (2 * s + (f * f + d) / x) = ((f * f + d) / x + s * 2) := by omega
    rw [h1]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
    omega
  rw [hdiv]
  have hdiv2 : ((f * f + d) / x) / 2 = (f * f + d) / (2 * x) := by
    rw [Nat.div_div_eq_div_mul]
    have : x * 2 = 2 * x := Nat.mul_comm _ _
    rw [this]
  rw [hdiv2]

theorem nstep_exact_ge (A x s e d : Nat) (hxpos : 0 < x)
    (hs_eq : s * s + d = A)
    (hx_eq : s + e = x) (he_le : e ≤ s) :
    nstep A x = s + (e * e + d) / (2 * x) := by
  unfold nstep
  obtain ⟨t, ht_eq⟩ : ∃ t, s = t + e := ⟨s - e, by omega⟩
  have hx_eq2 : x = t + e + e := by omega
  have hA_eq : A = x * t + (e * e + d) := by
    have h1 : s * s = x * t + e * e := by
      rw [ht_eq, hx_eq2]
      simp only [Nat.add_mul, Nat.mul_add]
      ac_rfl
    omega
  have hq_eq : A / x = t + (e * e + d) / x := by
    rw [hA_eq]
    exact Nat.mul_add_div hxpos _ _
  have hsum : x + A / x = 2 * s + (e * e + d) / x := by
    rw [hq_eq]
    omega
  have hdiv : (x + A / x) / 2 = s + ((e * e + d) / x) / 2 := by
    rw [hsum]
    have h1 : (2 * s + (e * e + d) / x) = ((e * e + d) / x + s * 2) := by omega
    rw [h1]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
    omega
  rw [hdiv]
  have hdiv2 : ((e * e + d) / x) / 2 = (e * e + d) / (2 * x) := by
    rw [Nat.div_div_eq_div_mul]
    have : x * 2 = 2 * x := Nat.mul_comm _ _
    rw [this]
  rw [hdiv2]

theorem mul_div_le_mul_div (K a b : Nat) (hb : 0 < b) :
    K * (a / b) ≤ (K * a) / b := by
  have h1 : (a / b) * b ≤ a := Nat.div_mul_le_self a b
  have h2 : ((a / b) * K) * b ≤ a * K := by
    have h3 : ((a / b) * K) * b = ((a / b) * b) * K := by ac_rfl
    rw [h3]
    exact Nat.mul_le_mul_right K h1
  have h4 : K * (a / b) = (a / b) * K := Nat.mul_comm _ _
  have h5 : K * a = a * K := Nat.mul_comm _ _
  rw [h4, h5]
  exact (Nat.le_div_iff_mul_le hb).mpr h2

theorem sqrt_pos_of_pos (A : Nat) (hA : 0 < A) : 0 < Nat.sqrt A := by
  have hne : Nat.sqrt A ≠ 0 := by
    intro h0
    have hslt : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt A
    rw [h0] at hslt
    simp at hslt
    omega
  exact Nat.pos_iff_ne_zero.mpr hne

theorem d_le_2s (A s d : Nat) (hs_eq : s * s + d = A)
    (hs : s = Nat.sqrt A) : d ≤ 2 * s := by
  have hslt : A < (s + 1) * (s + 1) := by rw [hs]; exact Nat.lt_succ_sqrt A
  have hexp : (s + 1) * (s + 1) = s * s + (s + s + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    ac_rfl
  have h2s : s * 2 = s + s := Nat.mul_two s
  omega

theorem nseq1_le_2s (A : Nat) (hA : 0 < A) : nseq A 1 ≤ 2 * Nat.sqrt A := by
  have hx0_le : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A := x0_le_sqrt A hA
  have hs_lt : Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) := sqrt_lt_2x0 A hA
  have hx0_pos : 0 < 2 ^ (Nat.log2 A / 2) := x0_pos A
  have hslt : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := Nat.lt_succ_sqrt A
  have hspos : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA
  have h1lt : Nat.sqrt A + 1 ≤ 2 * 2 ^ (Nat.log2 A / 2) := by omega
  have hmul2 : (Nat.sqrt A + 1) * (Nat.sqrt A + 1)
      ≤ (2 * 2 ^ (Nat.log2 A / 2)) * (Nat.sqrt A + 1) :=
    Nat.mul_le_mul_right _ h1lt
  have hle2 : 2 * (Nat.sqrt A + 1) ≤ 3 * Nat.sqrt A + 2 := by omega
  have hmul3 : (2 * 2 ^ (Nat.log2 A / 2)) * (Nat.sqrt A + 1)
      ≤ (3 * Nat.sqrt A + 2) * 2 ^ (Nat.log2 A / 2) := by
    have hcomm1 : (2 * 2 ^ (Nat.log2 A / 2)) * (Nat.sqrt A + 1)
        = 2 ^ (Nat.log2 A / 2) * (2 * (Nat.sqrt A + 1)) := by ac_rfl
    have hcomm2 : (3 * Nat.sqrt A + 2) * 2 ^ (Nat.log2 A / 2)
        = 2 ^ (Nat.log2 A / 2) * (3 * Nat.sqrt A + 2) := by ac_rfl
    rw [hcomm1, hcomm2]
    exact Nat.mul_le_mul_left _ hle2
  have hltA : A < (3 * Nat.sqrt A + 2) * 2 ^ (Nat.log2 A / 2) := by omega
  have hdiv_lt : A / 2 ^ (Nat.log2 A / 2) < 3 * Nat.sqrt A + 2 :=
    (Nat.div_lt_iff_lt_mul hx0_pos).mpr hltA
  have hle_add : 2 ^ (Nat.log2 A / 2) + A / 2 ^ (Nat.log2 A / 2) < 4 * Nat.sqrt A + 2 := by omega
  have hlt_div : (2 ^ (Nat.log2 A / 2) + A / 2 ^ (Nat.log2 A / 2)) / 2 < 2 * Nat.sqrt A + 1 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)
  have hle_div : (2 ^ (Nat.log2 A / 2) + A / 2 ^ (Nat.log2 A / 2)) / 2 ≤ 2 * Nat.sqrt A :=
    Nat.le_of_lt_succ hlt_div
  exact hle_div

theorem nstep_le_2s (A x s : Nat) (hs : s = Nat.sqrt A) (hspos : 0 < s)
    (hx_ge : s ≤ x) (hx_le : x ≤ 2 * s) (hxpos : 0 < x) :
    nstep A x ≤ 2 * s := by
  unfold nstep
  have hslt : A < (s + 1) * (s + 1) := by rw [hs]; exact Nat.lt_succ_sqrt A
  have h1le : s + 1 ≤ 2 * s := by omega
  have hmul1 : (s + 1) * (s + 1) ≤ (s + 1) * (2 * s) := Nat.mul_le_mul_left _ h1le
  have hcomm1 : (s + 1) * (2 * s) = 2 * (s + 1) * s := by ac_rfl
  have hmul2 : 2 * (s + 1) * s ≤ 2 * (s + 1) * x := Nat.mul_le_mul_left _ hx_ge
  have hle1 : (s + 1) * (s + 1) ≤ 2 * (s + 1) * x := by omega
  have hexp : 2 * (s + 1) * x = (2 * s + 2) * x := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  have hle2 : (s + 1) * (s + 1) ≤ (2 * s + 2) * x := by omega
  have hltA : A < (2 * s + 2) * x := Nat.lt_of_lt_of_le hslt hle2
  have hdiv_lt : A / x < 2 * s + 2 := (Nat.div_lt_iff_lt_mul hxpos).mpr hltA
  have hle_add : x + A / x < 4 * s + 2 := by omega
  have hlt_div : (x + A / x) / 2 < 2 * s + 1 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by omega)
  exact Nat.le_of_lt_succ hlt_div

theorem nseq_pos (A : Nat) (hA : 0 < A) : ∀ n, 0 < nseq A n := by
  intro n
  induction n with
  | zero => exact x0_pos A
  | succ k ih => exact nstep_pos A (nseq A k) hA ih

theorem nseq_ge_s (A : Nat) (hA : 0 < A) : ∀ n, 0 < n → Nat.sqrt A ≤ nseq A n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    have hxpos : 0 < nseq A k := nseq_pos A hA k
    have hspos : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA
    exact nstep_ge A (nseq A k) hA hxpos (Nat.sqrt A) rfl hspos

theorem nseq_le_2s (A : Nat) (hA : 0 < A) : ∀ n, 0 < n → nseq A n ≤ 2 * Nat.sqrt A := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      exact nseq1_le_2s A hA
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hge : Nat.sqrt A ≤ nseq A k := nseq_ge_s A hA k hkpos
      have hle : nseq A k ≤ 2 * Nat.sqrt A := ih hkpos
      have hxpos : 0 < nseq A k := nseq_pos A hA k
      have hspos : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA
      have hs_eq : Nat.sqrt A = Nat.sqrt A := rfl
      exact nstep_le_2s A (nseq A k) (Nat.sqrt A) rfl hspos hge hle hxpos

theorem e1_bound (A : Nat) (hA : 0 < A) :
    4 * (nseq A 1 - Nat.sqrt A) ≤ Nat.sqrt A + 8 := by
  have hx0_le : 2 ^ (Nat.log2 A / 2) ≤ Nat.sqrt A := x0_le_sqrt A hA
  have hs_lt : Nat.sqrt A < 2 * 2 ^ (Nat.log2 A / 2) := sqrt_lt_2x0 A hA
  have hx0_pos : 0 < 2 ^ (Nat.log2 A / 2) := x0_pos A
  have hspos : 0 < Nat.sqrt A := sqrt_pos_of_pos A hA
  have hsle : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A
  have hs_eq : Nat.sqrt A * Nat.sqrt A + (A - Nat.sqrt A * Nat.sqrt A) = A :=
    Nat.add_sub_cancel' hsle
  have hd_le : A - Nat.sqrt A * Nat.sqrt A ≤ 2 * Nat.sqrt A := by
    have h := d_le_2s A (Nat.sqrt A) (A - Nat.sqrt A * Nat.sqrt A) hs_eq rfl
    exact h
  obtain ⟨f0, hf0_eq⟩ : ∃ f, 2 ^ (Nat.log2 A / 2) + f = Nat.sqrt A := ⟨Nat.sqrt A - 2 ^ (Nat.log2 A / 2), by omega⟩
  have hf0_lt : 2 * f0 < Nat.sqrt A := by omega
  have hx0_eq : nseq A 0 = 2 ^ (Nat.log2 A / 2) := rfl
  have h1_eq : nseq A 1 = nstep A (2 ^ (Nat.log2 A / 2)) := rfl
  have hge1 : Nat.sqrt A ≤ nseq A 1 := nseq_ge_s A hA 1 (by decide)
  have he1_eq : nseq A 1 - Nat.sqrt A = (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A)) / (2 * 2 ^ (Nat.log2 A / 2)) := by
    have hexact := nstep_exact_le A (2 ^ (Nat.log2 A / 2)) (Nat.sqrt A) f0 (A - Nat.sqrt A * Nat.sqrt A) hx0_pos hs_eq hf0_eq
    have hns : nstep A (2 ^ (Nat.log2 A / 2)) = Nat.sqrt A + (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A)) / (2 * 2 ^ (Nat.log2 A / 2)) := hexact
    have h1 : nseq A 1 = Nat.sqrt A + (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A)) / (2 * 2 ^ (Nat.log2 A / 2)) := by
      unfold nseq
      simp only
      exact hns
    omega
  have h4lt : (2 * f0) ^ 2 < Nat.sqrt A ^ 2 :=
    Nat.pow_lt_pow_left hf0_lt (by decide : 2 ≠ 0)
  have h4eq1 : (2 * f0) ^ 2 = 4 * (f0 * f0) := by
    rw [Nat.pow_two]
    have h4 : (4 : Nat) = 2 * 2 := rfl
    rw [h4]
    ac_rfl
  have h4eq2 : Nat.sqrt A ^ 2 = Nat.sqrt A * Nat.sqrt A := Nat.pow_two _
  have h4lt2 : 4 * (f0 * f0) < Nat.sqrt A * Nat.sqrt A := by omega
  have h4d_le : 4 * (A - Nat.sqrt A * Nat.sqrt A) ≤ 8 * Nat.sqrt A := by
    have h1 := Nat.mul_le_mul_left 4 hd_le
    have h2 : (4 : Nat) * (2 * Nat.sqrt A) = 8 * Nat.sqrt A := by ac_rfl
    omega
  have hsum_lt : 4 * (f0 * f0) + 4 * (A - Nat.sqrt A * Nat.sqrt A) < Nat.sqrt A * Nat.sqrt A + 8 * Nat.sqrt A := by omega
  have hmul_eq : 4 * (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A)) = 4 * (f0 * f0) + 4 * (A - Nat.sqrt A * Nat.sqrt A) := by
    simp only [Nat.mul_add]
  have hlt1 : 4 * (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A)) < Nat.sqrt A * Nat.sqrt A + 8 * Nat.sqrt A := by omega
  have hx0_2pos : 0 < 2 * 2 ^ (Nat.log2 A / 2) := by omega
  have hs1le : Nat.sqrt A + 1 ≤ 2 * 2 ^ (Nat.log2 A / 2) := by omega
  have hle_expand : Nat.sqrt A * Nat.sqrt A + 8 * Nat.sqrt A ≤ (Nat.sqrt A + 9) * (Nat.sqrt A + 1) := by
    have hexp : (Nat.sqrt A + 9) * (Nat.sqrt A + 1) = (Nat.sqrt A * Nat.sqrt A + 9 * Nat.sqrt A) + (Nat.sqrt A + 9) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have hle_mul : (Nat.sqrt A + 9) * (Nat.sqrt A + 1) ≤ (Nat.sqrt A + 9) * (2 * 2 ^ (Nat.log2 A / 2)) :=
    Nat.mul_le_mul_left _ hs1le
  have hlt2 : 4 * (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A)) < (Nat.sqrt A + 9) * (2 * 2 ^ (Nat.log2 A / 2)) := by omega
  have hdiv_lt : (4 * (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A))) / (2 * 2 ^ (Nat.log2 A / 2)) < Nat.sqrt A + 9 :=
    (Nat.div_lt_iff_lt_mul hx0_2pos).mpr hlt2
  have hle_div : (4 * (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A))) / (2 * 2 ^ (Nat.log2 A / 2)) ≤ Nat.sqrt A + 8 :=
    Nat.le_of_lt_succ hdiv_lt
  have hmul_le : 4 * ((f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A)) / (2 * 2 ^ (Nat.log2 A / 2))) ≤ (4 * (f0 * f0 + (A - Nat.sqrt A * Nat.sqrt A))) / (2 * 2 ^ (Nat.log2 A / 2)) :=
    mul_div_le_mul_div 4 _ _ hx0_2pos
  omega

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  by_cases h0 : a = 0
  · subst h0
    unfold sqrt newtonSqrt
    simp
  · have heq : newtonSqrt 7 a =
      min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
        (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) := by
      unfold newtonSqrt
      split
      next h => exact absurd h h0
      next h => rfl
    show (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat
    unfold sqrt
    rw [heq]
    have hmin : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))
      (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat =
      Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
        (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) := by
      rw [toNat_min, BitVec.toNat_udiv]
    rw [hmin]
    have h1 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
        (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤
        (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
      Nat.min_le_left _ _
    have h2 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
        (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤
        a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
      Nat.min_le_right _ _
    by_cases hr0 : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat = 0
    · rw [hr0] at h1 ⊢
      have hm0 : Nat.min 0 (a.toNat / 0) = 0 := Nat.le_zero.mp h1
      rw [hm0]
      simp
    · have hpos : 0 < (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
        Nat.pos_of_ne_zero hr0
      have hmul : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
          (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) *
          (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat ≤ a.toNat :=
        (Nat.le_div_iff_mul_le hpos).mp h2
      have hsq : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
          (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) *
          Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
          (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤
          Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat
          (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) *
          (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
        Nat.mul_le_mul_left _ h1
      omega

theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry

end OzSqrt
