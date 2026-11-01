import OzSqrt.Spec
import OzSqrt.Lemmas
namespace OzSqrt

def sqrt : SqrtFn := newtonSqrt 7

theorem add_div_sq_ge_aux1 (r s k : Nat) (hsr : r ≤ s) (hk : s ^ 2 / r = s + k)
    (hdm : r * (s ^ 2 / r) + s ^ 2 % r = s ^ 2)
    (hmod : s ^ 2 % r < r) : s - r ≤ k := by
  have hsq : s ^ 2 = s * s := Nat.pow_two s
  have e1 : s * s = r * s + (s - r) * s := by
    rw [← Nat.add_mul]
    have hsplit : r + (s - r) = s := by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hsr
    rw [hsplit]
  have e2 : s ^ 2 = r * s + (r * k + s ^ 2 % r) := by
    rw [hk] at hdm
    have hrm : r * (s + k) = r * s + r * k := Nat.mul_add _ _ _
    rw [hrm] at hdm
    omega
  have e3 : (s - r) * s = r * k + s ^ 2 % r := by omega
  have h4 : (s - r) * r ≤ (s - r) * s := Nat.mul_le_mul_left _ hsr
  have hmk : r * (k + 1) = r * k + r := by rw [Nat.mul_add]; simp
  have h5 : (s - r) * r < r * (k + 1) := by omega
  have h6 : r * (s - r) < r * (k + 1) := by
    rw [Nat.mul_comm r (s - r)]
    exact h5
  have h7 : s - r < k + 1 := Nat.lt_of_mul_lt_mul_left h6
  omega

theorem mul_sub_add_le_sq (s d : Nat) (hds : d ≤ s) : (s - d) * (s + d) ≤ s ^ 2 := by
  have hsub : s - d + d = s := Nat.sub_add_cancel hds
  generalize hu : s - d = u at hsub ⊢
  have hs : s = u + d := by omega
  rw [hs]
  have e1 : u * ((u + d) + d) = u * u + (u * d + u * d) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have e2 : (u + d) ^ 2 = u * u + (u * d + (d * u + d * d)) := by
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have hcomm : d * u = u * d := Nat.mul_comm _ _
  omega

theorem add_div_sq_ge (r s : Nat) (hr : 0 < r) : 2 * s ≤ r + s ^ 2 / r := by
  by_cases hs : s = 0
  · subst hs
    simp
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    by_cases hle : r ≤ s
    · have hdm : r * (s ^ 2 / r) + s ^ 2 % r = s ^ 2 := Nat.div_add_mod _ _
      have hmod : s ^ 2 % r < r := Nat.mod_lt _ hr
      have hsq : s * s = s ^ 2 := (Nat.pow_two s).symm
      have hmul : s * r ≤ s * s := Nat.mul_le_mul_left s hle
      have h1 : s * r ≤ s ^ 2 := by rw [hsq] at hmul; exact hmul
      have h2 : s ≤ s ^ 2 / r := (Nat.le_div_iff_mul_le hr).mpr h1
      obtain ⟨k, hk⟩ : ∃ k, s ^ 2 / r = s + k := ⟨s ^ 2 / r - s, by omega⟩
      have hsk : s - r ≤ k := add_div_sq_ge_aux1 r s k hle hk hdm hmod
      omega
    · have hlt : s < r := by omega
      obtain ⟨d, hd⟩ : ∃ d, r = s + d := ⟨r - s, by omega⟩
      subst hd
      have hdpos : 0 < d := by omega
      by_cases hsd : s ≤ d
      · have hle2 : 2 * s ≤ s + d := by omega
        exact Nat.le_trans hle2 (Nat.le_add_right _ _)
      · have hlt2 : d < s := by omega
        have hds : d ≤ s := Nat.le_of_lt hlt2
        have h1 := mul_sub_add_le_sq s d hds
        have hpos2 : 0 < s + d := by omega
        have h2 : s - d ≤ s ^ 2 / (s + d) := (Nat.le_div_iff_mul_le hpos2).mpr h1
        have h3 : (s - d) + (s + d) = 2 * s := by omega
        have h4 : (s - d) + (s + d) ≤ s ^ 2 / (s + d) + (s + d) := Nat.add_le_add_right h2 _
        have hcomm : s ^ 2 / (s + d) + (s + d) = (s + d) + s ^ 2 / (s + d) := Nat.add_comm _ _
        rw [← h3, ← hcomm]
        exact h4

theorem step_ge_sqrt (a r : Nat) (hr : 0 < r) : a.sqrt ≤ (r + a / r) / 2 := by
  have hs2 : a.sqrt ^ 2 ≤ a := by rw [Nat.pow_two]; exact Nat.sqrt_le _
  have hdiv : a.sqrt ^ 2 / r ≤ a / r := Nat.div_le_div_right hs2
  have hge : 2 * a.sqrt ≤ r + a.sqrt ^ 2 / r := add_div_sq_ge r a.sqrt hr
  have hle : r + a.sqrt ^ 2 / r ≤ r + a / r := Nat.add_le_add_left hdiv _
  have h2s : 2 * a.sqrt ≤ r + a / r := Nat.le_trans hge hle
  omega

theorem mul_add_sub_eq (s e : Nat) (he : e ≤ s) :
    (s + e) * (s - e) + e ^ 2 = s ^ 2 := by
  have hsub : s - e + e = s := Nat.sub_add_cancel he
  generalize hu : s - e = u at hsub ⊢
  have hs : s = u + e := by omega
  rw [hs]
  have hcomm : e * u = u * e := Nat.mul_comm _ _
  have hpow_e : e ^ 2 = e * e := Nat.pow_two e
  have hpow : (u + e) ^ 2 = (u + e) * (u + e) := Nat.pow_two _
  have e1 : ((u + e) + e) * u = u * u + (u * e + u * e) := by
    have h1 : ((u + e) + e) * u = (u * u + e * u) + e * u := by
      rw [Nat.add_mul, Nat.add_mul]
    omega
  have e2 : (u + e) * (u + e) = u * u + (u * e + (e * u + e * e)) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  omega

theorem step_error_exact (a s e d r : Nat) (hs : s = a.sqrt)
    (he : e ≤ s) (hspos : 0 < s) (hr : r = s + e)
    (hd : s ^ 2 + d = a) :
    (r + a / r) / 2 = s + ((e ^ 2 + d) / r) / 2 := by
  have hrpos : 0 < r := by omega
  have hrpos2 : 0 < s + e := by omega
  have hbase : (s + e) * (s - e) + e ^ 2 = s ^ 2 := mul_add_sub_eq s e he
  have ha_eq : a = (e ^ 2 + d) + (s + e) * (s - e) := by omega
  have hdiv : a / (s + e) = (s - e) + (e ^ 2 + d) / (s + e) := by
    rw [ha_eq, Nat.add_mul_div_left _ _ hrpos2, Nat.add_comm]
  have hstep : (r + a / r) / 2 = ((e ^ 2 + d) / (s + e) + 2 * s) / 2 := by
    rw [hr, hdiv]
    have hsum2 : (s + e) + ((s - e) + (e ^ 2 + d) / (s + e))
        = (e ^ 2 + d) / (s + e) + 2 * s := by omega
    rw [hsum2]
  have hfin : ((e ^ 2 + d) / (s + e) + 2 * s) / 2
      = ((e ^ 2 + d) / (s + e)) / 2 + s := by
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  rw [hstep, hr, hfin]
  exact Nat.add_comm _ _

theorem add_div_anti (C u v : Nat) (hu : 0 < u) (huv : u ≤ v) (hvC : v * v ≤ C) :
    v + C / v ≤ u + C / u := by
  have huv2 : u * v ≤ v * v := Nat.mul_le_mul_right v huv
  have huvC : u * v ≤ C := Nat.le_trans huv2 hvC
  obtain ⟨k, hk⟩ : ∃ k, C = u * v + k := ⟨C - u * v, by omega⟩
  have hQu : C / u = v + k / u := by
    rw [hk, Nat.add_comm (u * v) k, Nat.add_mul_div_left _ _ hu, Nat.add_comm]
  have hQv : C / v = u + k / v := by
    have hcomm : u * v = v * u := Nat.mul_comm _ _
    rw [hk, hcomm, Nat.add_comm (v * u) k, Nat.add_mul_div_left _ _ (by omega : 0 < v),
      Nat.add_comm]
  have hdiv : k / v ≤ k / u := Nat.div_le_div_left huv hu
  omega

theorem even_div (q : Nat) : (2 * q) / 2 = q := by
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel _ (by decide)

theorem even_ineq (q : Nat) : (2 * q) ^ 2 + 2 * (2 * q) ≤ (2 * (2 * q) + 3) * (q + 1) := by
  have e1 : (2 * q) * (2 * q) = 4 * (q * q) := by ac_rfl
  have e2 : 2 * (2 * q) = 4 * q := by ac_rfl
  have e3 : (4 * q) * (q + 1) = 4 * (q * q) + 4 * q := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have e4 : 3 * (q + 1) = 3 * q + 3 := by
    rw [Nat.mul_add, Nat.mul_one]
  have hLHS : (2 * q) ^ 2 + 2 * (2 * q) = 4 * (q * q) + 4 * q := by
    rw [Nat.pow_two, e1, e2]
  have hRHS : (2 * (2 * q) + 3) * (q + 1) = 4 * (q * q) + (4 * q + (3 * q + 3)) := by
    have h1 : 2 * (2 * q) = 4 * q := by ac_rfl
    rw [h1]
    rw [Nat.add_mul, e3, e4]
    omega
  omega

theorem odd_ineq (q : Nat) :
    (2 * q + 1) ^ 2 + 2 * (2 * q + 1) ≤ (2 * (2 * q + 1) + 3) * (q + 1) := by
  have hsq : (2 * q + 1) ^ 2 = 4 * (q * q) + (4 * q + 1) := by
    have p1 : (2 * q) * (2 * q) = 4 * (q * q) := by ac_rfl
    have p2 : (2 * q) * 1 = 2 * q := Nat.mul_one _
    have p3 : 1 * (2 * q) = 2 * q := Nat.one_mul _
    have p4 : (1 : Nat) * 1 = 1 := Nat.one_mul 1
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    rw [p1, p2, p3, p4]
    omega
  have h2s : 2 * (2 * q + 1) = 4 * q + 2 := by
    rw [Nat.mul_add, Nat.mul_one]
    have h1 : 2 * (2 * q) = 4 * q := by ac_rfl
    omega
  have hLHS : (2 * q + 1) ^ 2 + 2 * (2 * q + 1) = 4 * (q * q) + (8 * q + 3) := by
    rw [hsq, h2s]
    omega
  have hRHS : (2 * (2 * q + 1) + 3) * (q + 1) = 4 * (q * q) + (9 * q + 5) := by
    have h1 : 2 * (2 * q + 1) = 4 * q + 2 := by
      rw [Nat.mul_add, Nat.mul_one]
      have h2 : 2 * (2 * q) = 4 * q := by ac_rfl
      omega
    rw [h1]
    have f1 : (4 * q + 5) * (q + 1) = 4 * (q * q) + (9 * q + 5) := by
      have g1 : (4 * q) * (q + 1) = 4 * (q * q) + 4 * q := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
      have g2 : 5 * (q + 1) = 5 * q + 5 := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [Nat.add_mul, g1, g2]
      omega
    omega
  omega

theorem bound_L (s : Nat) (hs : 0 < s) :
    ((s / 2 + 1) + (s ^ 2 + 2 * s) / (s / 2 + 1)) / 2 ≤ s + s / 2 + 2 := by
  have hLpos : 0 < s / 2 + 1 := by omega
  have heq : (3 * s + 4) / 2 = s + s / 2 + 2 := by omega
  have hle : (s / 2 + 1) + (s ^ 2 + 2 * s) / (s / 2 + 1) ≤ 3 * s + 4 := by
    have hLle : s / 2 + 1 ≤ s + 1 := by omega
    have hQle : (s ^ 2 + 2 * s) / (s / 2 + 1) ≤ 2 * s + 3 := by
      apply Nat.div_le_of_le_mul
      have hqr : 2 * (s / 2) + s % 2 = s := Nat.div_add_mod s 2
      have hmod : s % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases hr0 : s % 2 = 0
      · have hs2 : s = 2 * (s / 2) := by omega
        generalize hq : s / 2 = q at hs2 hqr ⊢
        rw [hs2]
        have h := even_ineq q
        have hcomm : (2 * (2 * q) + 3) * (q + 1) = (q + 1) * (2 * (2 * q) + 3) :=
          Nat.mul_comm _ _
        rw [hcomm] at h
        exact h
      · have hr1 : s % 2 = 1 := by omega
        have hs2 : s = 2 * (s / 2) + 1 := by omega
        generalize hq : s / 2 = q at hs2 hqr ⊢
        rw [hs2]
        have h := odd_ineq q
        have hcomm : (2 * (2 * q + 1) + 3) * (q + 1) = (q + 1) * (2 * (2 * q + 1) + 3) :=
          Nat.mul_comm _ _
        rw [hcomm] at h
        exact h
    have hadd : (s / 2 + 1) + (s ^ 2 + 2 * s) / (s / 2 + 1) ≤ (s + 1) + (2 * s + 3) :=
      Nat.add_le_add hLle hQle
    have heq2 : (s + 1) + (2 * s + 3) = 3 * s + 4 := by omega
    omega
  have hdiv : ((s / 2 + 1) + (s ^ 2 + 2 * s) / (s / 2 + 1)) / 2 ≤ (3 * s + 4) / 2 :=
    Nat.div_le_div_right hle
  omega

theorem le_sqrt_of_sq_le {a r : Nat} (h : r ^ 2 ≤ a) : r ≤ a.sqrt := by
  by_cases hle : r ≤ a.sqrt
  · exact hle
  · have hlt : a.sqrt < r := Nat.lt_of_not_le hle
    have hle2 : a.sqrt + 1 ≤ r := by omega
    have hpow : (a.sqrt + 1) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hle2 2
    have hlt2 : a < (a.sqrt + 1) * (a.sqrt + 1) := Nat.lt_succ_sqrt _
    have hsq : (a.sqrt + 1) ^ 2 = (a.sqrt + 1) * (a.sqrt + 1) := Nat.pow_two _
    omega

theorem sqrt_pos_of_pos {a : Nat} (h : 0 < a) : 0 < a.sqrt := by
  by_cases hle : 0 < a.sqrt
  · exact hle
  · have h0 : a.sqrt = 0 := by omega
    have hlt : a < (a.sqrt + 1) * (a.sqrt + 1) := Nat.lt_succ_sqrt _
    rw [h0] at hlt
    simp at hlt
    omega

def natStep (a r : Nat) : Nat := (r + a / r) / 2

def natIter (a : Nat) : Nat → Nat → Nat
  | 0, r => r
  | k + 1, r => natIter a k (natStep a r)

def r0Nat (a : Nat) : Nat := 2 ^ (Nat.log2 a / 2)

theorem natIter_zero (a r : Nat) : natIter a 0 r = r := rfl

theorem natIter_succ (a k r : Nat) : natIter a (k + 1) r = natIter a k (natStep a r) := rfl

theorem natStep_pos {a r : Nat} (ha : 0 < a) (hr : 0 < r) : 0 < natStep a r := by
  unfold natStep
  by_cases h1 : r = 1
  · subst h1
    rw [Nat.div_one]
    exact Nat.div_pos (by omega) (by decide)
  · have hr2 : 2 ≤ r := by omega
    have hadd : r ≤ r + a / r := Nat.le_add_right _ _
    have hle : 2 ≤ r + a / r := Nat.le_trans hr2 hadd
    exact Nat.div_pos hle (by decide)

theorem natIter_pos {a : Nat} (ha : 0 < a) (k r : Nat) (hr : 0 < r) :
    0 < natIter a k r := by
  induction k generalizing r with
  | zero => simpa [natIter]
  | succ k ih =>
    rw [natIter_succ]
    exact ih _ (natStep_pos ha hr)

theorem r0Nat_pos (a : Nat) : 0 < r0Nat a := by
  unfold r0Nat
  exact Nat.pow_pos (by decide)

theorem r0Nat_sq_le {a : Nat} (ha : 0 < a) : (r0Nat a) ^ 2 ≤ a := by
  unfold r0Nat
  have hlog : 2 ^ Nat.log2 a ≤ a := by
    have h := (Nat.log2_eq_iff (Nat.ne_of_gt ha)).mp rfl
    exact h.1
  have hhalf : 2 * (Nat.log2 a / 2) ≤ Nat.log2 a := by omega
  have hpow : 2 ^ (2 * (Nat.log2 a / 2)) ≤ 2 ^ Nat.log2 a :=
    Nat.pow_le_pow_of_le (by decide) hhalf
  have hsq : (2 ^ (Nat.log2 a / 2)) ^ 2 = 2 ^ (2 * (Nat.log2 a / 2)) := by
    have hx : Nat.log2 a / 2 + Nat.log2 a / 2 = 2 * (Nat.log2 a / 2) := by omega
    rw [Nat.pow_two, ← Nat.pow_add, hx]
  rw [hsq]
  omega

theorem r0Nat_le_sqrt {a : Nat} (ha : 0 < a) : r0Nat a ≤ a.sqrt :=
  le_sqrt_of_sq_le (r0Nat_sq_le ha)

theorem r0Nat_lt_four {a : Nat} : a < 4 * (r0Nat a) ^ 2 := by
  unfold r0Nat
  have hlt : a < 2 ^ (Nat.log2 a + 1) := Nat.lt_log2_self
  have hexp : Nat.log2 a + 1 ≤ 2 + 2 * (Nat.log2 a / 2) := by omega
  have hpow : 2 ^ (Nat.log2 a + 1) ≤ 2 ^ (2 + 2 * (Nat.log2 a / 2)) :=
    Nat.pow_le_pow_of_le (by decide) hexp
  have hsq : (2 ^ (Nat.log2 a / 2)) ^ 2 = 2 ^ (2 * (Nat.log2 a / 2)) := by
    have hx : Nat.log2 a / 2 + Nat.log2 a / 2 = 2 * (Nat.log2 a / 2) := by omega
    rw [Nat.pow_two, ← Nat.pow_add, hx]
  have h4 : (4 : Nat) = 2 ^ 2 := by decide
  have heq : 4 * (2 ^ (Nat.log2 a / 2)) ^ 2 = 2 ^ (2 + 2 * (Nat.log2 a / 2)) := by
    rw [hsq, h4, Nat.pow_add]
  omega

theorem a_le_sq_add {a : Nat} : a ≤ a.sqrt ^ 2 + 2 * a.sqrt := by
  have hlt : a < (a.sqrt + 1) * (a.sqrt + 1) := Nat.lt_succ_sqrt _
  have hexp : (a.sqrt + 1) * (a.sqrt + 1) = a.sqrt ^ 2 + (2 * a.sqrt + 1) := by
    have hsq : a.sqrt ^ 2 = a.sqrt * a.sqrt := Nat.pow_two _
    have e1 : (a.sqrt + 1) * (a.sqrt + 1)
        = a.sqrt * a.sqrt + (a.sqrt + (a.sqrt + 1)) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    omega
  omega

theorem sqrt_lt_two_r0 {a : Nat} (_ha : 0 < a) : a.sqrt < 2 * r0Nat a := by
  by_cases hle : 2 * r0Nat a ≤ a.sqrt
  · have hpow : (2 * r0Nat a) ^ 2 ≤ a.sqrt ^ 2 := Nat.pow_le_pow_left hle 2
    have hs2 : a.sqrt ^ 2 ≤ a := by rw [Nat.pow_two]; exact Nat.sqrt_le _
    have h4 : (2 * r0Nat a) ^ 2 = 4 * (r0Nat a) ^ 2 := by
      rw [Nat.pow_two, Nat.pow_two]
      ac_rfl
    have hlt : a < 4 * (r0Nat a) ^ 2 := r0Nat_lt_four
    omega
  · have hlt : a.sqrt < 2 * r0Nat a := by omega
    exact hlt

theorem r1_le {a : Nat} (ha : 0 < a) :
    natStep a (r0Nat a) ≤ a.sqrt + a.sqrt / 2 + 2 := by
  have hspos : 0 < a.sqrt := sqrt_pos_of_pos ha
  have hr0pos : 0 < r0Nat a := r0Nat_pos _
  have hr0le : r0Nat a ≤ a.sqrt := r0Nat_le_sqrt ha
  have hs2r : a.sqrt < 2 * r0Nat a := sqrt_lt_two_r0 ha
  have hLle : a.sqrt / 2 + 1 ≤ r0Nat a := by omega
  have hLpos : 0 < a.sqrt / 2 + 1 := by omega
  have hr0sq : (r0Nat a) * (r0Nat a) ≤ a := by
    have h := r0Nat_sq_le ha
    rw [Nat.pow_two] at h
    exact h
  have hmono : r0Nat a + a / r0Nat a ≤ (a.sqrt / 2 + 1) + a / (a.sqrt / 2 + 1) :=
    add_div_anti a _ _ hLpos hLle hr0sq
  have hstep : natStep a (r0Nat a) ≤ ((a.sqrt / 2 + 1) + a / (a.sqrt / 2 + 1)) / 2 := by
    unfold natStep
    exact Nat.div_le_div_right hmono
  have ha_le : a ≤ a.sqrt ^ 2 + 2 * a.sqrt := a_le_sq_add
  have hdiv : a / (a.sqrt / 2 + 1) ≤ (a.sqrt ^ 2 + 2 * a.sqrt) / (a.sqrt / 2 + 1) :=
    Nat.div_le_div_right ha_le
  have hadd : (a.sqrt / 2 + 1) + a / (a.sqrt / 2 + 1)
      ≤ (a.sqrt / 2 + 1) + (a.sqrt ^ 2 + 2 * a.sqrt) / (a.sqrt / 2 + 1) :=
    Nat.add_le_add_left hdiv _
  have hdiv2 : ((a.sqrt / 2 + 1) + a / (a.sqrt / 2 + 1)) / 2
      ≤ ((a.sqrt / 2 + 1) + (a.sqrt ^ 2 + 2 * a.sqrt) / (a.sqrt / 2 + 1)) / 2 :=
    Nat.div_le_div_right hadd
  have hbound := bound_L a.sqrt hspos
  omega

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro a
  unfold sqrt newtonSqrt
  by_cases h0 : a = 0
  · subst h0
    simp
  · rw [if_neg h0]
    have hm : (min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))) (a / iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1)))).toNat
        = Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) := by
      rw [toNat_min, BitVec.toNat_udiv]
    rw [hm]
    have h1 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := Nat.min_le_left _ _
    have h2 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat := Nat.min_le_right _ _
    by_cases hr0 : (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat = 0
    · rw [hr0] at h1 h2 hm ⊢
      simp at h1 ⊢
    · have h3 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat ≤ a.toNat :=
        Nat.mul_le_of_le_div _ _ _ h2
      have h4 : Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) ≤ Nat.min (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat (a.toNat / (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat) * (iterate (newtonStep a) 7 ((1 : U256) <<< (log2 a >>> 1))).toNat :=
        Nat.mul_le_mul (Nat.le_refl _) h1
      omega

theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := ⟨7, by decide, fun a => rfl⟩

end OzSqrt
