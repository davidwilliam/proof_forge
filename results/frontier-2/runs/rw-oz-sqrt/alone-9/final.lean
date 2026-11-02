import OzSqrt.Spec
import OzSqrt.Lemmas
import Init.Data.Nat.Sqrt
import Init.Data.Nat.Lemmas

namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem sq_add_ge_aux (a d : Nat) :
    2 * a * (a + d) + d * d = a * a + (a + d) * (a + d) := by
  have h2a : 2 * a = a + a := by omega
  have e1 : 2 * a * (a + d) = (a + a) * (a + d) := by rw [h2a]
  have e2 : (a + a) * (a + d) = a * a + a * a + (a * d + a * d) := by
    rw [Nat.add_mul, Nat.mul_add]
    omega
  have e3 : (a + d) * (a + d) = a * a + (a * d + (a * d + d * d)) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm d a]
    omega
  omega

theorem sq_add_ge (a b : Nat) : 2 * a * b ≤ a * a + b * b := by
  by_cases h : a ≤ b
  · have hb : a + (b - a) = b := Nat.add_sub_cancel' h
    have key := sq_add_ge_aux a (b - a)
    rw [hb] at key
    omega
  · have h' : b ≤ a := by omega
    have hb : b + (a - b) = a := Nat.add_sub_cancel' h'
    have key := sq_add_ge_aux b (a - b)
    rw [hb] at key
    have hcomm : a * b = b * a := Nat.mul_comm _ _
    have e1 : 2 * a * b = 2 * (a * b) := Nat.mul_assoc _ _ _
    have e2 : 2 * b * a = 2 * (b * a) := Nat.mul_assoc _ _ _
    omega

theorem add_sq_div_ge (r s : Nat) (hr : 0 < r) : 2 * s ≤ r + s ^ 2 / r := by
  by_cases h2 : 2 * s ≤ r
  · exact Nat.le_trans h2 (Nat.le_add_right r _)
  · have hr2 : r < 2 * s := by omega
    have hadd : (2 * s - r) + r = 2 * s := by omega
    have hle : 2 * s - r ≤ s ^ 2 / r := by
      rw [Nat.le_div_iff_mul_le hr]
      have hsq := sq_add_ge s r
      have hss : s ^ 2 = s * s := by rw [Nat.pow_two]
      have hassoc1 : 2 * s * r = 2 * (s * r) := Nat.mul_assoc _ _ _
      have hmul : ((2 * s - r) + r) * r = 2 * s * r := by rw [hadd]
      have hdist : ((2 * s - r) + r) * r = (2 * s - r) * r + r * r := Nat.add_mul _ _ _
      omega
    have hle_add : (2 * s - r) + r ≤ s ^ 2 / r + r := Nat.add_le_add_right hle r
    rw [hadd] at hle_add
    have hcomm : s ^ 2 / r + r = r + s ^ 2 / r := Nat.add_comm _ _
    rw [hcomm] at hle_add
    exact hle_add

theorem newton_ge (A r s : Nat) (hr : 0 < r) (hsq : s * s ≤ A) :
    s ≤ (r + A / r) / 2 := by
  have hsq2 : s ^ 2 ≤ A := by rw [Nat.pow_two]; exact hsq
  have h1 : s ^ 2 / r ≤ A / r := Nat.div_le_div_right hsq2
  have h2 : 2 * s ≤ r + s ^ 2 / r := add_sq_div_ge r s hr
  have h3 : 2 * s ≤ r + A / r := by
    have hle : r + s ^ 2 / r ≤ r + A / r := Nat.add_le_add_left h1 r
    omega
  have h4 : s * 2 ≤ r + A / r := by omega
  have h5 : s ≤ (r + A / r) / 2 := by
    have hle : s * 2 ≤ r + A / r := h4
    have := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hle
    omega
  exact h5

theorem diff_sq_aux (d e : Nat) :
    d * (d + e + e) + e * e = (d + e) * (d + e) := by
  have e1 : d * (d + e + e) = d * d + (d * e + d * e) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have e2 : (d + e) * (d + e) = d * d + (d * e + (d * e + e * e)) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm e d]
    omega
  omega

theorem diff_sq (s e : Nat) (h : e ≤ s) :
    (s - e) * (s + e) + e * e = s * s := by
  have hd : s - e + e = s := Nat.sub_add_cancel h
  have key := diff_sq_aux (s - e) e
  have h1 : s - e + e + e = s + e := by omega
  have h2 : s - e + e = s := hd
  rw [h1, h2] at key
  exact key

theorem newton_upper_exact (s e t A r : Nat) (hs : 0 < s) (he : e ≤ s)
    (hr_eq : r = s + e) (hA : A = s * s + t) (hr0 : 0 < r) :
    (r + A / r) / 2 = s + ((e * e + t) / r) / 2 := by
  have hss : (s - e) * (s + e) + e * e = s * s := diff_sq s e he
  have hcomm : (s - e) * (s + e) = r * (s - e) := by
    rw [hr_eq, Nat.mul_comm]
  have hAeq : A = r * (s - e) + (e * e + t) := by
    rw [hA]
    have h1 : s * s = r * (s - e) + e * e := by
      rw [← hss, hcomm]
    omega
  have hdiv : A / r = (s - e) + (e * e + t) / r := by
    rw [hAeq]
    exact Nat.mul_add_div hr0 _ _
  have hsum : r + A / r = 2 * s + (e * e + t) / r := by
    rw [hdiv, hr_eq]
    have hadd : (s + e) + (s - e) = 2 * s := by omega
    omega
  rw [hsum]
  exact Nat.mul_add_div (by decide : 0 < 2) s ((e * e + t) / r)

def natR0 (A : Nat) : Nat := 2 ^ (Nat.log2 A / 2)

def natSeq (A : Nat) : Nat → Nat
  | 0 => natR0 A
  | n + 1 => ((natSeq A n + A / natSeq A n)) / 2

theorem natR0_pos (A : Nat) (hA : 0 < A) : 0 < natR0 A := by
  unfold natR0
  exact Nat.two_pow_pos _

theorem log2_lt_256 (A : Nat) (hA : A < 2 ^ 256) (hA0 : 0 < A) :
    Nat.log2 A < 256 := by
  have hne : A ≠ 0 := by omega
  have h1 : 2 ^ Nat.log2 A ≤ A := by
    have := (Nat.log2_eq_iff hne).mp rfl
    exact this.1
  by_cases h : Nat.log2 A < 256
  · exact h
  · have hle : 256 ≤ Nat.log2 A := by omega
    have hpow : 2 ^ 256 ≤ 2 ^ Nat.log2 A :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hle
    omega

theorem natR0_lt (A : Nat) (hA : A < 2 ^ 256) (hA0 : 0 < A) :
    natR0 A < 2 ^ 256 := by
  unfold natR0
  have hlog : Nat.log2 A / 2 < 256 := by
    have := log2_lt_256 A hA hA0
    omega
  have := Nat.pow_lt_pow_right (by decide : 1 < 2) hlog
  omega

theorem sqrt_le' (A : Nat) : Nat.sqrt A * Nat.sqrt A ≤ A := Nat.sqrt_le A

theorem sqrt_lt' (A : Nat) : A < (Nat.sqrt A + 1) * (Nat.sqrt A + 1) := by
  have h0 := Nat.lt_succ_sqrt A
  have h1 : Nat.sqrt A + 1 = (Nat.sqrt A).succ := by omega
  rw [← h1] at h0
  exact h0

theorem sq_succ_expand (s : Nat) :
    (s + 1) * (s + 1) = s * s + (2 * s + 1) := by
  have e1 : (s + 1) * (s + 1) = s * s + (s + (s + 1)) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  omega

theorem t_bound (A : Nat) : A - Nat.sqrt A * Nat.sqrt A ≤ 2 * Nat.sqrt A := by
  have h1 := sqrt_le' A
  have h2 := sqrt_lt' A
  have hex : (Nat.sqrt A + 1) * (Nat.sqrt A + 1)
      = Nat.sqrt A * Nat.sqrt A + (2 * Nat.sqrt A + 1) :=
    sq_succ_expand _
  omega

theorem pow_log2_le (A : Nat) (hA0 : 0 < A) : 2 ^ Nat.log2 A ≤ A := by
  have hne : A ≠ 0 := by omega
  have := (Nat.log2_eq_iff hne).mp rfl
  exact this.1

theorem lt_pow_succ_log2 (A : Nat) (hA0 : 0 < A) : A < 2 ^ (Nat.log2 A + 1) := by
  have hne : A ≠ 0 := by omega
  have := (Nat.log2_eq_iff hne).mp rfl
  exact this.2

theorem r0_sq_le (A : Nat) (hA0 : 0 < A) : natR0 A * natR0 A ≤ A := by
  unfold natR0
  have hdiv : 2 * (Nat.log2 A / 2) ≤ Nat.log2 A := by
    have hmod := Nat.div_add_mod (Nat.log2 A) 2
    omega
  have hpow1 : 2 ^ (2 * (Nat.log2 A / 2)) ≤ 2 ^ Nat.log2 A :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hdiv
  have hpow2 : 2 ^ Nat.log2 A ≤ A := pow_log2_le A hA0
  have hsq : (2 ^ (Nat.log2 A / 2)) * (2 ^ (Nat.log2 A / 2))
      = 2 ^ (2 * (Nat.log2 A / 2)) := by
    rw [← Nat.pow_add]
    have : Nat.log2 A / 2 + Nat.log2 A / 2 = 2 * (Nat.log2 A / 2) := by omega
    rw [this]
  omega

theorem r0_le_sqrt (A : Nat) (hA0 : 0 < A) : natR0 A ≤ Nat.sqrt A := by
  by_cases h : natR0 A ≤ Nat.sqrt A
  · exact h
  · have hle : Nat.sqrt A + 1 ≤ natR0 A := by omega
    have hsq1 := Nat.mul_le_mul hle hle
    have hsq2 := sqrt_lt' A
    have hr0 := r0_sq_le A hA0
    omega

theorem two_r0_sq_ge (A : Nat) (hA0 : 0 < A) :
    A < (2 * natR0 A) * (2 * natR0 A) := by
  have hlt := lt_pow_succ_log2 A hA0
  have hdiv : Nat.log2 A + 1 ≤ 2 * (Nat.log2 A / 2) + 2 := by omega
  have hpow : 2 ^ (Nat.log2 A + 1) ≤ 2 ^ (2 * (Nat.log2 A / 2) + 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hdiv
  have hexp : 2 ^ (2 * (Nat.log2 A / 2) + 2)
      = (2 * natR0 A) * (2 * natR0 A) := by
    unfold natR0
    have hrr : (2 * 2 ^ (Nat.log2 A / 2)) * (2 * 2 ^ (Nat.log2 A / 2))
        = (2 * 2) * (2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2)) := by ac_rfl
    have h22 : (2 * 2 : Nat) = 4 := by decide
    rw [h22] at hrr
    have hpp : 2 ^ (Nat.log2 A / 2) * 2 ^ (Nat.log2 A / 2)
        = 2 ^ (Nat.log2 A / 2 + Nat.log2 A / 2) := by rw [← Nat.pow_add]
    have hadd : Nat.log2 A / 2 + Nat.log2 A / 2 = 2 * (Nat.log2 A / 2) := by omega
    rw [hpp, hadd] at hrr
    have h4 : (4 : Nat) = 2 ^ 2 := by decide
    rw [h4] at hrr
    have hpow2 : (2 : Nat) ^ 2 * 2 ^ (2 * (Nat.log2 A / 2))
        = 2 ^ (2 + 2 * (Nat.log2 A / 2)) := by rw [← Nat.pow_add]
    have hcomm : 2 + 2 * (Nat.log2 A / 2) = 2 * (Nat.log2 A / 2) + 2 := by omega
    rw [hpow2, hcomm] at hrr
    omega
  omega

theorem s_lt_two_r0 (A : Nat) (hA0 : 0 < A) : Nat.sqrt A < 2 * natR0 A := by
  by_cases h : Nat.sqrt A < 2 * natR0 A
  · exact h
  · have hle : 2 * natR0 A ≤ Nat.sqrt A := by omega
    have hsq1 := Nat.mul_le_mul hle hle
    have hsq2 := two_r0_sq_ge A hA0
    have hsq3 := sqrt_le' A
    omega

theorem sq_lt_of_lt (a b : Nat) (h : a < b) : a * a < b * b := by
  have h1 : a + 1 ≤ b := Nat.succ_le_of_lt h
  have h2 : (a + 1) * (a + 1) ≤ b * b := Nat.mul_le_mul h1 h1
  have h3 : a * a < (a + 1) * (a + 1) := by
    have e : (a + 1) * (a + 1) = a * a + (2 * a + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    omega
  exact Nat.lt_of_lt_of_le h3 h2

theorem natSeq_pos (A : Nat) (hA0 : 0 < A) (n : Nat) : 0 < natSeq A n := by
  induction n with
  | zero => unfold natSeq natR0; exact Nat.two_pow_pos _
  | succ k ih =>
    show 0 < (natSeq A k + A / natSeq A k) / 2
    have h2le : 2 ≤ natSeq A k + A / natSeq A k := by
      by_cases h1 : natSeq A k = 1
      · have hAdiv : A / natSeq A k = A := by rw [h1, Nat.div_one]
        omega
      · have h2 : 2 ≤ natSeq A k := by omega
        have := Nat.le_add_right (natSeq A k) (A / natSeq A k)
        omega
    have hle : 2 / 2 ≤ (natSeq A k + A / natSeq A k) / 2 :=
      Nat.div_le_div_right h2le
    have heq : 2 / 2 = 1 := by decide
    omega

theorem natSeq_ge_sqrt_succ (A : Nat) (hA0 : 0 < A) (n : Nat) :
    Nat.sqrt A ≤ natSeq A (n + 1) := by
  induction n with
  | zero =>
    unfold natSeq
    exact newton_ge A (natR0 A) (Nat.sqrt A) (natR0_pos A hA0) (sqrt_le' A)
  | succ k ih =>
    show Nat.sqrt A ≤ (natSeq A (k + 1) + A / natSeq A (k + 1)) / 2
    exact newton_ge A (natSeq A (k + 1)) (Nat.sqrt A)
      (natSeq_pos A hA0 (k + 1)) (sqrt_le' A)

theorem natSeq_lt (A : Nat) (hA : A < 2 ^ 256) (hA0 : 0 < A) (n : Nat) :
    natSeq A n < 2 ^ 256 := by
  induction n with
  | zero => unfold natSeq; exact natR0_lt A hA hA0
  | succ k ih =>
    show ((natSeq A k + A / natSeq A k)) / 2 < 2 ^ 256
    have h1 : natSeq A k < 2 ^ 256 := ih
    have h2 : A / natSeq A k < 2 ^ 256 := by
      have := Nat.div_le_self A (natSeq A k)
      omega
    have h3 : natSeq A k + A / natSeq A k < 2 ^ 256 * 2 := by omega
    have h4 : (natSeq A k + A / natSeq A k) / 2 < 2 ^ 256 := by
      have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr h3
      have heq : 2 ^ 256 * 2 = 2 ^ 256 * 2 := rfl
      omega
    exact h4

def natErr (A : Nat) (n : Nat) : Nat := natSeq A (n + 1) - Nat.sqrt A

theorem natErr_eq (A : Nat) (hA0 : 0 < A) (n : Nat) :
    natSeq A (n + 1) = Nat.sqrt A + natErr A n := by
  unfold natErr
  have hge := natSeq_ge_sqrt_succ A hA0 n
  omega

theorem natSeq_pos_succ (A : Nat) (hA0 : 0 < A) (n : Nat) :
    0 < natSeq A (n + 1) := natSeq_pos A hA0 (n + 1)

theorem natErr_le_succ_aux (A e s r t : Nat) (hs : 0 < s) (he : e ≤ s)
    (hr_eq : r = s + e) (hA : A = s * s + t) (ht : t ≤ 2 * s) (hr0 : 0 < r) :
    (e * e + t) / (2 * r) ≤ s := by
  have he2 : e * e ≤ s * s := Nat.mul_le_mul he he
  have hle1 : e * e + t ≤ s * s + 2 * s := Nat.add_le_add he2 ht
  have hle2 : s * s + 2 * s = s * (s + 2) := by
    rw [Nat.mul_add, Nat.mul_comm 2 s]
  have hle3 : 2 * r = 2 * (s + e) := by rw [hr_eq]
  have h2s_le : 2 * s ≤ 2 * r := by
    have : s ≤ r := by omega
    exact Nat.mul_le_mul (Nat.le_refl 2) this
  have h2r_pos : 0 < 2 * r := by
    have : 0 < 2 := by decide
    have := Nat.mul_pos this hr0
    omega
  have h2s_pos : 0 < 2 * s := by
    have : (0 : Nat) < 2 := by decide
    have := Nat.mul_pos this hs
    omega
  have hdivA : (e * e + t) / (2 * r) ≤ (s * s + 2 * s) / (2 * r) :=
    Nat.div_le_div_right hle1
  have hdivB : (s * s + 2 * s) / (2 * r) ≤ (s * s + 2 * s) / (2 * s) := by
    apply Nat.div_le_div_left h2s_le h2s_pos
  have hdiv1 : (e * e + t) / (2 * r) ≤ (s * s + 2 * s) / (2 * s) :=
    Nat.le_trans hdivA hdivB
  have hnum : s * s + 2 * s = s * (s + 2) := by
    rw [Nat.mul_add, Nat.mul_comm s 2]
  have hden : 2 * s = s * 2 := Nat.mul_comm 2 s
  have heq : (s * s + 2 * s) / (2 * s) = (s + 2) / 2 := by
    rw [hnum, hden]
    exact Nat.mul_div_mul_left (s + 2) 2 hs
  have hfin : (s + 2) / 2 ≤ s := by omega
  omega

theorem natErr_le_succ (A : Nat) (hA0 : 0 < A) (hA2 : 2 ≤ Nat.sqrt A)
    (n : Nat) (he : natErr A n ≤ Nat.sqrt A) :
    natErr A (n + 1) ≤ Nat.sqrt A := by
  have hs : 0 < Nat.sqrt A := by omega
  have hr_eq : natSeq A (n + 1) = Nat.sqrt A + natErr A n :=
    natErr_eq A hA0 n
  have hr0 : 0 < natSeq A (n + 1) := natSeq_pos_succ A hA0 n
  have hsq : Nat.sqrt A * Nat.sqrt A ≤ A := sqrt_le' A
  have ht_le : A - Nat.sqrt A * Nat.sqrt A ≤ 2 * Nat.sqrt A := t_bound A
  have hAeq : A = Nat.sqrt A * Nat.sqrt A + (A - Nat.sqrt A * Nat.sqrt A) := by
    omega
  have hrr : natSeq A (n + 2)
      = (natSeq A (n + 1) + A / natSeq A (n + 1)) / 2 := rfl
  have hup := newton_upper_exact (Nat.sqrt A) (natErr A n)
    (A - Nat.sqrt A * Nat.sqrt A) A (natSeq A (n + 1)) hs he hr_eq hAeq hr0
  have hseq_eq : natSeq A (n + 2)
      = Nat.sqrt A + ((natErr A n * natErr A n
        + (A - Nat.sqrt A * Nat.sqrt A)) / natSeq A (n + 1)) / 2 := by
    rw [hrr, hup]
  have herr_eq : natErr A (n + 1)
      = ((natErr A n * natErr A n + (A - Nat.sqrt A * Nat.sqrt A))
        / natSeq A (n + 1)) / 2 := by
    have h1 : natErr A (n + 1) = natSeq A (n + 2) - Nat.sqrt A := rfl
    have h2 : natSeq A (n + 2)
        = Nat.sqrt A + ((natErr A n * natErr A n
          + (A - Nat.sqrt A * Nat.sqrt A)) / natSeq A (n + 1)) / 2 := by
      rw [hrr, hup]
    rw [h1, h2]
    exact Nat.add_sub_cancel_left _ _
  have hdiv_eq : ((natErr A n * natErr A n + (A - Nat.sqrt A * Nat.sqrt A))
      / natSeq A (n + 1)) / 2
      = (natErr A n * natErr A n + (A - Nat.sqrt A * Nat.sqrt A))
        / (2 * natSeq A (n + 1)) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm (natSeq A (n + 1)) 2]
  rw [hdiv_eq] at herr_eq
  rw [herr_eq]
  exact natErr_le_succ_aux A (natErr A n) (Nat.sqrt A) (natSeq A (n + 1))
    (A - Nat.sqrt A * Nat.sqrt A) hs he hr_eq hAeq ht_le hr0

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight : SqrtUpTight sqrt := sorry
theorem req_mint_backed : MintBacked sqrt := sorry
theorem req_mint_full : MintFull sqrt := sorry
theorem req_mint_live : MintLive sqrt := sorry
theorem req_newton_budget : NewtonBudget sqrt := ⟨7, by decide, fun a => rfl⟩

end OzSqrt
