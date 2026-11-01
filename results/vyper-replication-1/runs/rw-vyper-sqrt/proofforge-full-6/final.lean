import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt

namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-! ## Nat model of the Newton iteration -/

/-- Scaled radicand `a * 10^10`. -/
def W (a : Nat) : Nat := a * 10 ^ 10

/-- Integer square root of the scaled radicand. -/
def S (a : Nat) : Nat := Nat.sqrt (a * 10 ^ 10)

/-- Seed `a / 2 + 5 * 10^9`. -/
def Z0 (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- One Newton step for `a`: `(x + (a*10^10)/x)/2`. -/
def Nw (a x : Nat) : Nat := ProofForgeFin.Sqrt.newton (a * 10 ^ 10) x

/-- Newton sequence from the seed. -/
def seq (a n : Nat) : Nat := match n with
  | 0 => Z0 a
  | m + 1 => Nw a (seq a m)

open ProofForgeFin.Sqrt

theorem seq_zero (a : Nat) : seq a 0 = Z0 a := rfl
theorem seq_succ (a n : Nat) : seq a (n + 1) = Nw a (seq a n) := rfl

theorem succ_sq (n : Nat) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  have h1 : (n + 1) * (n + 1) = n * (n + 1) + 1 * (n + 1) := Nat.add_mul n 1 (n + 1)
  have h2 : n * (n + 1) = n * n + n * 1 := Nat.mul_add n n 1
  have h3 : (1 : Nat) * (n + 1) = n + 1 := Nat.one_mul _
  omega

theorem seed_sq_succ_gt (a : Nat) :
    a * 10 ^ 10 < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) := by
  have hK : 5 * 10 ^ 9 = 5000000000 := by decide
  have hD : 10 ^ 10 = 10000000000 := by decide
  rw [hK, hD]
  have h4 := four_mul_le_sq (a / 2) 5000000000
  have hsucc := succ_sq (a / 2 + 5000000000)
  omega

theorem seed_ge_sqrt (a : Nat) : S a ≤ Z0 a := by
  unfold S Z0
  have h := seed_sq_succ_gt a
  have hlt : Nat.sqrt (a * 10 ^ 10) < a / 2 + 5 * 10 ^ 9 + 1 :=
    sqrt_lt_of_lt_mul_self h
  omega

theorem z0_pos (a : Nat) : 0 < Z0 a := by
  unfold Z0
  have : 0 < 5 * 10 ^ 9 := by decide
  omega

theorem s_ge_of_ge_one {a : Nat} (h : 1 ≤ a) : 100000 ≤ S a := by
  unfold S
  apply le_sqrt_of_mul_self_le (m := 100000)
  have : (100000 : Nat) * 100000 = 10 ^ 10 := by decide
  rw [this]
  calc 10 ^ 10 = 1 * 10 ^ 10 := (Nat.one_mul _).symm
    _ ≤ a * 10 ^ 10 := Nat.mul_le_mul_right _ h

theorem s_lt_pow {a : Nat} (h : a ≤ 2 ^ 167 - 1) : S a < 2 ^ 101 := by
  unfold S
  apply sqrt_lt_two_pow (k := 101)
  have h10 : (10 : Nat) ^ 10 < 2 ^ 34 := by decide
  have hM : a < 2 ^ 167 := by omega
  have hlt : a * 10 ^ 10 < 2 ^ 167 * 2 ^ 34 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hM) h10 (by decide)
  have heq : 2 ^ 167 * (2 : Nat) ^ 34 = 2 ^ 201 := by
    rw [← Nat.pow_add]
  have hle : (2 : Nat) ^ 201 ≤ 2 ^ (2 * 101) :=
    Nat.pow_le_pow_right (by decide) (by decide)
  exact Nat.lt_of_lt_of_le (heq ▸ hlt) hle

theorem seq_ge_sqrt (a n : Nat) : S a ≤ seq a n := by
  induction n with
  | zero => rw [seq_zero]; exact seed_ge_sqrt a
  | succ m ih =>
    rw [seq_succ]
    rcases Nat.eq_zero_or_pos (seq a m) with h0 | hpos
    · have hS0 : S a = 0 := by omega
      omega
    · exact sqrt_le_newton (a := a * 10 ^ 10) hpos

theorem seq_pos_of_pos {a n : Nat} (h : 1 ≤ a) : 0 < seq a n := by
  have hS : 100000 ≤ S a := s_ge_of_ge_one h
  have hge := seq_ge_sqrt a n
  omega

theorem div_le_s_add_two {a x : Nat} (h1 : 1 ≤ a) (hx : 0 < x) (hle : S a ≤ x) :
    a * 10 ^ 10 / x ≤ S a + 2 := by
  have hS1 : 1 ≤ S a := by
    have h100 := s_ge_of_ge_one h1
    omega
  have hlt : a * 10 ^ 10 < (S a + 1) * (S a + 1) := Nat.lt_succ_sqrt _
  have hsq := succ_sq (S a)
  have hmul : (S a + 3) * S a = S a * S a + 3 * S a := by
    have h1 : (S a + 3) * S a = S a * S a + 3 * S a := Nat.add_mul _ _ _
    exact h1
  have hle2 : (S a + 1) * (S a + 1) ≤ (S a + 3) * x := by
    have hxS : S a * S a + 2 * S a + 1 ≤ S a * S a + 3 * S a := by omega
    have hmon : (S a + 3) * S a ≤ (S a + 3) * x := Nat.mul_le_mul_left _ hle
    omega
  have hlt2 : a * 10 ^ 10 < (S a + 3) * x := Nat.lt_of_lt_of_le hlt hle2
  have hdiv : a * 10 ^ 10 / x < S a + 3 := (Nat.div_lt_iff_lt_mul hx).mpr hlt2
  omega

theorem seq_le_z0_add_two {a n : Nat} (h1 : 1 ≤ a) : seq a n ≤ Z0 a + 2 := by
  induction n with
  | zero => rw [seq_zero]; omega
  | succ m ih =>
    rw [seq_succ]
    unfold Nw ProofForgeFin.Sqrt.newton
    have hpos : 0 < seq a m := seq_pos_of_pos h1
    have hge : S a ≤ seq a m := seq_ge_sqrt a m
    have hdiv : a * 10 ^ 10 / seq a m ≤ S a + 2 := div_le_s_add_two h1 hpos hge
    have hS0 : S a ≤ Z0 a := seed_ge_sqrt a
    omega

theorem seq_err_bound (a n : Nat) (h1 : 1 ≤ a) :
    seq a n - S a ≤ (Z0 a - S a) / 2 ^ n + 2 := by
  induction n with
  | zero =>
    rw [seq_zero]
    have hpow : (2 : Nat) ^ 0 = 1 := Nat.pow_zero _
    rw [hpow, Nat.div_one]
    omega
  | succ m ih =>
    have hpos : 0 < seq a m := seq_pos_of_pos h1
    have hge : S a ≤ seq a m := seq_ge_sqrt a m
    have hstep : Nw a (seq a m) - S a ≤ (seq a m - S a) / 2 + 1 :=
      newton_sub_sqrt_le_half (a := a * 10 ^ 10) hpos hge
    have hseq : seq a (m + 1) = Nw a (seq a m) := seq_succ a m
    rw [hseq]
    have hmono : (seq a m - S a) / 2 + 1 ≤ ((Z0 a - S a) / 2 ^ m + 2) / 2 + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right ih) _
    have hdiv2 : ((Z0 a - S a) / 2 ^ m + 2) / 2 = (Z0 a - S a) / 2 ^ m / 2 + 1 := by
      omega
    have hpow : (2 : Nat) ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ _ _
    have hdiv3 : (Z0 a - S a) / 2 ^ m / 2 = (Z0 a - S a) / 2 ^ (m + 1) := by
      rw [hpow, ← Nat.div_div_eq_div_mul]
    omega

theorem z0_bound {a : Nat} (h : a ≤ 2 ^ 167 - 1) : Z0 a < 2 ^ 167 := by
  unfold Z0
  have hdiv : a / 2 ≤ 2 ^ 166 - 1 := by
    have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right h
    have h2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
    omega
  have hbig : (2 : Nat) ^ 166 - 1 + 5000000000 < 2 ^ 167 := by decide
  have hK : 5 * 10 ^ 9 = 5000000000 := by decide
  rw [hK]
  omega

theorem seq_err_254 {a : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    seq a 254 - S a ≤ 2 := by
  have hb := seq_err_bound a 254 h1
  have hz := z0_bound hM
  have hS0 : S a ≤ Z0 a := seed_ge_sqrt a
  have hlt : Z0 a - S a < 2 ^ 254 := by
    have hle : (2 : Nat) ^ 167 ≤ 2 ^ 254 :=
      Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hdiv0 : (Z0 a - S a) / 2 ^ 254 = 0 :=
    (Nat.div_eq_zero_iff_lt (Nat.pow_pos (by decide : 0 < 2))).mpr hlt
  omega

theorem seq_255_le {a : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    seq a 255 ≤ S a + 1 := by
  have hpos254 : 0 < seq a 254 := seq_pos_of_pos h1
  have hge254 : S a ≤ seq a 254 := seq_ge_sqrt a 254
  have he : seq a 254 - S a ≤ 2 := seq_err_254 h1 hM
  have hsq : (seq a 254 - S a) * (seq a 254 - S a) ≤ 2 * S a := by
    have hmul1 : (seq a 254 - S a) * (seq a 254 - S a) ≤ 2 * 2 :=
      Nat.mul_le_mul he he
    have hS100 := s_ge_of_ge_one h1
    have h2 : 2 * 2 ≤ 2 * S a := by omega
    omega
  have hle : Nw a (seq a 254) ≤ S a + 1 :=
    newton_le_sqrt_add_one (a := a * 10 ^ 10) hpos254 hge254 hsq
  have hseq : seq a 255 = Nw a (seq a 254) := seq_succ a 254
  omega

theorem seq_min_255 {a : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    min (seq a 255) (seq a 256) = S a := by
  have hpos : 0 < seq a 255 := seq_pos_of_pos h1
  have hge1 : S a ≤ seq a 255 := seq_ge_sqrt a 255
  have hle1 : seq a 255 ≤ S a + 1 := seq_255_le h1 hM
  have hseq256 : seq a 256 = Nw a (seq a 255) := seq_succ a 255
  rw [hseq256]
  exact min_newton_eq_sqrt (a := a * 10 ^ 10) hpos hge1 hle1

theorem z0_add_two_le {a : Nat} (h : a ≤ 2 ^ 167 - 1) : Z0 a + 2 ≤ 2 ^ 167 - 1 := by
  unfold Z0
  have hdiv : a / 2 ≤ 2 ^ 166 - 1 := by
    have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right h
    have h2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
    omega
  have hbig : (2 : Nat) ^ 166 - 1 + 5000000000 + 2 ≤ 2 ^ 167 - 1 := by decide
  have hK : 5 * 10 ^ 9 = 5000000000 := by decide
  rw [hK]
  omega

theorem seq_le_M {a n : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    seq a n ≤ 2 ^ 167 - 1 := by
  have hle := seq_le_z0_add_two (a := a) (n := n) h1
  have hz := z0_add_two_le hM
  omega

theorem seed_eq_implies_sqrt (a : Nat) (h : a = Z0 a) : S a = a := by
  unfold Z0 at h
  have hcases : a = 9999999999 ∨ a = 10000000000 := by omega
  unfold S
  rcases hcases with rfl | rfl
  · have hK : (10 : Nat) ^ 10 = 10000000000 := by decide
    rw [hK]
    exact sqrt_eq_of_bounds (by decide) (by decide)
  · have hK : (10 : Nat) ^ 10 = 10000000000 := by decide
    rw [hK]
    exact sqrt_eq_of_bounds (by decide) (by decide)

theorem seq_ge_255_le {a n : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1)
    (hge : 255 ≤ n) : seq a n ≤ S a + 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 255 with hlt | hge2
    · have hm255 : m + 1 = 255 := by omega
      rw [hm255]
      exact seq_255_le h1 hM
    · have hpos : 0 < seq a m := seq_pos_of_pos h1
      have hgeS : S a ≤ seq a m := seq_ge_sqrt a m
      have hleS : seq a m ≤ S a + 1 := ih (by omega)
      have hgeS' : Nat.sqrt (a * 10 ^ 10) ≤ seq a m := hgeS
      have hleS' : seq a m ≤ Nat.sqrt (a * 10 ^ 10) + 1 := hleS
      have hmem := newton_of_mem (a := a * 10 ^ 10) hpos hgeS' hleS'
      have hseq : seq a (m + 1) = Nw a (seq a m) := seq_succ a m
      rw [hseq]
      rcases hmem with h | h
      · have hEq : Nw a (seq a m) = S a := h
        omega
      · obtain ⟨_, hEq2, _⟩ := h
        have hEq : Nw a (seq a m) = S a + 1 := hEq2
        omega

theorem seq_min_ge_255 {a n : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1)
    (hge : 255 ≤ n) : min (seq a n) (seq a (n + 1)) = S a := by
  have hpos : 0 < seq a n := seq_pos_of_pos h1
  have hgeS : S a ≤ seq a n := seq_ge_sqrt a n
  have hleS : seq a n ≤ S a + 1 := seq_ge_255_le h1 hM hge
  have hseq : seq a (n + 1) = Nw a (seq a n) := seq_succ a n
  rw [hseq]
  exact min_newton_eq_sqrt (a := a * 10 ^ 10) hpos hgeS hleS

/-- Nat pair iteration mirroring `loop` with early stop. -/
def pairNat (a : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | f + 1, (y, z) => if z = y then (y, z) else pairNat a f (z, Nw a z)

theorem pairNat_min_ge {a f i : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1)
    (h : 255 ≤ i + f) :
    min (pairNat a f (seq a i, seq a (i + 1))).1
      (pairNat a f (seq a i, seq a (i + 1))).2 = S a := by
  induction f generalizing i with
  | zero =>
    have hi : 255 ≤ i := by omega
    have hmin := seq_min_ge_255 h1 hM hi
    simpa [pairNat] using hmin
  | succ f ih =>
    simp only [pairNat]
    by_cases heq : seq a (i + 1) = seq a i
    · have hfix : Nw a (seq a i) = seq a i := by
        have hseq : seq a (i + 1) = Nw a (seq a i) := seq_succ a i
        omega
      have hpos : 0 < seq a i := seq_pos_of_pos h1
      have hS : seq a i = S a :=
        eq_sqrt_of_newton_eq_self (a := a * 10 ^ 10) hpos hfix
      rw [if_pos heq]
      show min (seq a i) (seq a (i + 1)) = S a
      rw [heq, Nat.min_self]
      exact hS
    · rw [if_neg heq]
      have hNw : Nw a (seq a (i + 1)) = seq a (i + 1 + 1) := by
        have := seq_succ a (i + 1)
        omega
      have hpair : (seq a (i + 1), Nw a (seq a (i + 1)))
          = (seq a (i + 1), seq a (i + 1 + 1)) := by rw [hNw]
      rw [hpair]
      have h2 : 255 ≤ (i + 1) + f := by omega
      exact ih (i := i + 1) h2

theorem seq_sum_le {a n : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1)
    (hpos : 0 < seq a n) :
    a * 10 ^ 10 / seq a n + seq a n ≤ 2 ^ 167 - 1 := by
  have hdiv : a * 10 ^ 10 / seq a n ≤ S a + 2 :=
    div_le_s_add_two h1 hpos (seq_ge_sqrt a n)
  have hseq : seq a n ≤ Z0 a + 2 := seq_le_z0_add_two h1
  have hS : S a < 2 ^ 101 := s_lt_pow hM
  have hz : Z0 a + 2 ≤ 2 ^ 166 - 1 + 5000000000 + 2 := by
    unfold Z0
    have hdiv2 : a / 2 ≤ 2 ^ 166 - 1 := by
      have h1 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hM
      have h2 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by decide
      omega
    have hK : 5 * 10 ^ 9 = 5000000000 := by decide
    rw [hK]
    omega
  have hbig : 2 ^ 101 + (2 ^ 166 - 1 + 5000000000 + 2) + 2 ≤ 2 ^ 167 - 1 := by
    decide
  omega

theorem loop_eq_pairNat {a f i : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    loop (a : Int) f ((seq a i : Nat) : Int) ((seq a (i + 1) : Nat) : Int)
      = some (((pairNat a f (seq a i, seq a (i + 1))).1 : Int),
        ((pairNat a f (seq a i, seq a (i + 1))).2 : Int)) := by
  induction f generalizing i with
  | zero => rfl
  | succ f ih =>
    by_cases heq : seq a (i + 1) = seq a i
    · have heqInt : ((seq a (i + 1) : Nat) : Int) = ((seq a i : Nat) : Int) := by
        rw [heq]
      have hloop : loop (a : Int) (f + 1) ((seq a i : Nat) : Int)
          ((seq a (i + 1) : Nat) : Int)
          = some (((seq a i : Nat) : Int), ((seq a i : Nat) : Int)) := by
        rw [heqInt]
        exact loop_stop _ _ _
      have hpairNat : pairNat a (f + 1) (seq a i, seq a (i + 1))
          = (seq a i, seq a (i + 1)) := by
        simp [pairNat, heq]
      rw [hpairNat, hloop, heq]
    · have hpairNat : pairNat a (f + 1) (seq a i, seq a (i + 1))
          = pairNat a f (seq a (i + 1), Nw a (seq a (i + 1))) := by
        simp [pairNat, heq]
      have hpos : 0 < seq a (i + 1) := seq_pos_of_pos h1
      have hsum : a * 10 ^ 10 / seq a (i + 1) + seq a (i + 1) ≤ 2 ^ 167 - 1 :=
        seq_sum_le h1 hM hpos
      have hstep := loop_step (a := a) (y := seq a i) (z := seq a (i + 1))
        (n := f) hpos heq hsum
      have hNw : Nw a (seq a (i + 1)) = seq a (i + 1 + 1) := by
        have h1 := seq_succ a (i + 1)
        omega
      have hcast : ((((a * 10 ^ 10 / seq a (i + 1) + seq a (i + 1)) / 2 : Nat)) : Int)
          = ((seq a (i + 1 + 1) : Nat) : Int) := by
        have hcomm : (a * 10 ^ 10 / seq a (i + 1) + seq a (i + 1)) / 2
            = (seq a (i + 1) + a * 10 ^ 10 / seq a (i + 1)) / 2 := by
          rw [Nat.add_comm]
        have hNwdef : (seq a (i + 1) + a * 10 ^ 10 / seq a (i + 1)) / 2
            = Nw a (seq a (i + 1)) := rfl
        rw [hcomm, hNwdef, hNw]
      rw [hpairNat, hstep, hcast]
      have hpair2 : (seq a (i + 1), Nw a (seq a (i + 1)))
          = (seq a (i + 1), seq a (i + 1 + 1)) := by rw [hNw]
      rw [hpair2]
      exact ih (i := i + 1)

theorem int_min_nat (m n : Nat) :
    ((min m n : Nat) : Int) = (if (m : Int) < (n : Int) then (m : Int) else (n : Int)) := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · have hmin : min m n = m := Nat.min_eq_left (Nat.le_of_lt hlt)
    have hint : (m : Int) < (n : Int) := by exact_mod_cast hlt
    rw [hmin, if_pos hint]
  · have hmin : min m n = n := Nat.min_eq_right hge
    have hint : ¬ (m : Int) < (n : Int) := by
      intro hc
      have : m < n := by exact_mod_cast hc
      omega
    rw [hmin, if_neg hint]

theorem loop_initial_min {a : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    ∃ y z : Nat, loop (a : Int) 256 ((a : Int)) (((Z0 a : Nat)) : Int)
      = some ((y : Int), (z : Int)) ∧ min y z = S a := by
  have h256 : (256 : Nat) = 255 + 1 := rfl
  rw [h256]
  by_cases heq : a = Z0 a
  · have heqInt : (a : Int) = (((Z0 a : Nat)) : Int) := congrArg _ heq
    refine ⟨a, a, ?_, ?_⟩
    · rw [heqInt]
      exact loop_stop _ _ _
    · have hS : S a = a := seed_eq_implies_sqrt a heq
      omega
  · have hneNat : Z0 a ≠ a := fun hc => heq hc.symm
    have hpos : 0 < Z0 a := z0_pos a
    have hsum : a * 10 ^ 10 / Z0 a + Z0 a ≤ 2 ^ 167 - 1 := by
      have hseq0 : seq a 0 = Z0 a := seq_zero a
      have hpos0 : 0 < seq a 0 := by rw [hseq0]; exact hpos
      have hsum0 := seq_sum_le h1 hM hpos0
      rw [hseq0] at hsum0
      exact hsum0
    have hstep := loop_step (a := a) (y := a) (z := Z0 a) (n := 255) hpos hneNat hsum
    have hseq1 : Nw a (Z0 a) = seq a 1 := by
      have h0 : seq a 0 = Z0 a := seq_zero a
      have h1s : seq a 1 = Nw a (seq a 0) := seq_succ a 0
      rw [h0] at h1s
      exact h1s.symm
    have hcast : ((((a * 10 ^ 10 / Z0 a + Z0 a) / 2 : Nat)) : Int)
        = ((seq a 1 : Nat) : Int) := by
      have hcomm : (a * 10 ^ 10 / Z0 a + Z0 a) / 2
          = (Z0 a + a * 10 ^ 10 / Z0 a) / 2 := by rw [Nat.add_comm]
      have hNwdef : (Z0 a + a * 10 ^ 10 / Z0 a) / 2 = Nw a (Z0 a) := rfl
      rw [hcomm, hNwdef, hseq1]
    rw [hstep, hcast]
    have hloop := loop_eq_pairNat (a := a) (f := 255) (i := 0) h1 hM
    have hmin := pairNat_min_ge (a := a) (f := 255) (i := 0) h1 hM (by omega)
    exact ⟨_, _, hloop, hmin⟩

theorem sqrt_eq_S {a : Nat} (h1 : 1 ≤ a) (hM : a ≤ 2 ^ 167 - 1) :
    sqrt (a : Int) = some (((S a : Nat)) : Int) := by
  unfold sqrt
  have hV := vyperSqrtWith_pos (fun y z => if y < z then y else z) (a := a)
    (by omega : 0 < a) hM
  rw [hV]
  obtain ⟨y, z, hloop, hmin⟩ := loop_initial_min h1 hM
  unfold Z0 at hloop
  rw [hloop]
  simp only [Option.map_some]
  have hfin : (if (y : Int) < (z : Int) then (y : Int) else (z : Int))
      = (((S a : Nat)) : Int) := by
    have hcast := (int_min_nat y z).symm
    rw [hmin] at hcast
    exact hcast
  exact congrArg _ hfin

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  simp [hx]

theorem req_deployed_loop : DeployedLoop sqrt := by
  exact ⟨(fun y z => if y < z then y else z), fun x => rfl⟩

theorem sqrt_zero : sqrt 0 = some 0 := by
  unfold sqrt vyperSqrtWith
  simp

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hdec hnn
  obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
    ⟨x.natAbs, (Int.ofNat_natAbs_of_nonneg hnn).symm⟩
  unfold IsDecimal at hdec
  obtain ⟨_, hmax⟩ := hdec
  have hM : a ≤ 2 ^ 167 - 1 := by
    have hmax' : (a : Int) ≤ MAX_DECIMAL := hmax
    rw [max_decimal_eq] at hmax'
    exact_mod_cast hmax'
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    simp [sqrt_zero]
  · have h1 : 1 ≤ a := hpos
    rw [sqrt_eq_S h1 hM]
    simp

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hdec hsome
  by_cases hxneg : x < 0
  · have hnone := req_sqrt_neg_reverts x hxneg
    rw [hnone] at hsome
    cases hsome
  · have hnn : 0 ≤ x := by omega
    obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
      ⟨x.natAbs, (Int.ofNat_natAbs_of_nonneg hnn).symm⟩
    unfold IsDecimal at hdec
    obtain ⟨_, hmax⟩ := hdec
    have hM : a ≤ 2 ^ 167 - 1 := by
      have hmax' : (a : Int) ≤ MAX_DECIMAL := hmax
      rw [max_decimal_eq] at hmax'
      exact_mod_cast hmax'
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      have h0eq : sqrt (((0 : Nat)) : Int) = some 0 := sqrt_zero
      have hr0 : r = 0 := by
        have h := h0eq.symm.trans hsome
        have := Option.some_inj.mp h
        omega
      subst hr0
      have hD : DIVISOR = 10000000000 := by decide
      rw [hD]
      decide
    · have h1 : 1 ≤ a := hpos
      have hsqrt := sqrt_eq_S h1 hM
      rw [hsqrt] at hsome
      have hr : r = ((S a : Nat) : Int) := Option.some_inj.mp hsome.symm
      subst hr
      have hNat : S a * S a ≤ a * 10 ^ 10 := Nat.sqrt_le _
      have hD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
      rw [hD, ← Int.natCast_mul]
      exact_mod_cast hNat

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hdec hsome
  by_cases hxneg : x < 0
  · have hnone := req_sqrt_neg_reverts x hxneg
    rw [hnone] at hsome
    cases hsome
  · have hnn : 0 ≤ x := by omega
    obtain ⟨a, rfl⟩ : ∃ a : Nat, x = (a : Int) :=
      ⟨x.natAbs, (Int.ofNat_natAbs_of_nonneg hnn).symm⟩
    unfold IsDecimal at hdec
    obtain ⟨_, hmax⟩ := hdec
    have hM : a ≤ 2 ^ 167 - 1 := by
      have hmax' : (a : Int) ≤ MAX_DECIMAL := hmax
      rw [max_decimal_eq] at hmax'
      exact_mod_cast hmax'
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      have h0eq : sqrt (((0 : Nat)) : Int) = some 0 := sqrt_zero
      have hr0 : r = 0 := by
        have h := h0eq.symm.trans hsome
        have := Option.some_inj.mp h
        omega
      subst hr0
      have hD : DIVISOR = 10000000000 := by decide
      rw [hD]
      decide
    · have h1 : 1 ≤ a := hpos
      have hsqrt := sqrt_eq_S h1 hM
      rw [hsqrt] at hsome
      have hr : r = ((S a : Nat) : Int) := Option.some_inj.mp hsome.symm
      subst hr
      have hNat : a * 10 ^ 10 < (S a + 1) * (S a + 1) := Nat.lt_succ_sqrt _
      have hD : DIVISOR = ((10 ^ 10 : Nat) : Int) := divisor_eq
      have hcast : (a : Int) * DIVISOR < ((((S a : Nat)) : Int) + 1) * ((((S a : Nat)) : Int) + 1) := by
        have hcastNat : (((a * 10 ^ 10 : Nat)) : Int)
            < ((((S a + 1) * (S a + 1) : Nat)) : Int) := by
          exact_mod_cast hNat
        have e1 : ((((a * 10 ^ 10 : Nat))) : Int) = (a : Int) * DIVISOR := by
          rw [hD, Int.natCast_mul]
        have e2 : ((((S a + 1) * (S a + 1) : Nat)) : Int)
            = ((((S a : Nat)) : Int) + 1) * ((((S a : Nat)) : Int) + 1) := by
          rw [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
        rw [e1, e2] at hcastNat
        exact hcastNat
      exact hcast

end VyperSqrt
