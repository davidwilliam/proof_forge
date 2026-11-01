import VyperSqrt.Spec
import VyperSqrt.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Int.Lemmas

namespace VyperSqrt

/-- The choice of PR 4486: minimum of the last two iterates. -/
def minFn : Int → Int → Int := fun y z => if y < z then y else z

def sqrt : SqrtFn := vyperSqrtWith minFn

/-! ## Nat Newton setup -/

/-- Newton step on naturals: `(a * 10^10 / z + z) / 2`. Matches `loop_step`. -/
def NN (a z : Nat) : Nat := (a * 10 ^ 10 / z + z) / 2

/-- Seed `a / 2 + 5 * 10^9`. Matches `seed_div` / `seed_add`. -/
def NSeed (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- Nat iterate sequence. -/
def NSeq (a : Nat) : Nat → Nat
  | 0 => NSeed a
  | n + 1 => NN a (NSeq a n)

/-- Previous iterate (`a` at step `0`). -/
def NY (a : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => NSeq a n

/-- `s = ⌊√(a * 10^10)⌋`. -/
def NS (a : Nat) : Nat := Nat.sqrt (a * 10 ^ 10)

/-- Square is never negative (Int). -/
theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h2 : 0 ≤ -x := by omega
    have h3 := Int.mul_nonneg h2 h2
    rwa [Int.neg_mul_neg] at h3

theorem sqrt_sq_le (a : Nat) : NS a * NS a ≤ a * 10 ^ 10 :=
  Nat.sqrt_le _

theorem sqrt_gt (a : Nat) : a * 10 ^ 10 < (NS a + 1) * (NS a + 1) :=
  Nat.lt_succ_sqrt _

theorem s_pos {a : Nat} (ha : 0 < a) : 0 < NS a := by
  cases h : NS a with
  | zero =>
    have h1 : (1 : Nat) ≤ a * 10 ^ 10 := by
      have hh := Nat.mul_le_mul (show 1 ≤ a by omega) (show 1 ≤ 10 ^ 10 by decide)
      simpa using hh
    have h2 := sqrt_gt a
    rw [h] at h2
    simp at h2
    omega
  | succ n => omega

theorem seed_le_M {a : Nat} (h : a ≤ 2 ^ 167 - 1) : NSeed a ≤ 2 ^ 167 - 1 := by
  have e : 5 * 10 ^ 9 + (2 ^ 167 - 1) / 2 ≤ 2 ^ 167 - 1 := by decide
  have h2 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right h
  unfold NSeed
  generalize 2 ^ 167 - 1 = M at *
  omega

/-- `(NSeed a + 1)^2 > a * 10^10`, so `NSeed a ≥ NS a`. -/
theorem seed_succ_sq_gt {a : Nat} :
    a * 10 ^ 10 < (NSeed a + 1) * (NSeed a + 1) := by
  have hqr : a = 2 * (a / 2) + a % 2 := by
    have h := Nat.div_add_mod a 2
    omega
  have hr : a % 2 ≤ 1 := by
    have h := Nat.mod_lt a (show 0 < 2 by decide)
    omega
  have eN : NSeed a + 1 = a / 2 + 5000000001 := by
    have c : 5 * 10 ^ 9 = 5000000000 := by decide
    unfold NSeed
    omega
  have eA : a * 10 ^ 10 = (2 * (a / 2) + a % 2) * 10000000000 := by
    have c10 : (10 : Nat) ^ 10 = 10000000000 := by decide
    rw [← hqr, c10]
  have hsq := int_sq_nonneg (((a / 2 : Nat) : Int) - 4999999999)
  have hr' : ((a % 2 : Nat) : Int) ≤ ((1 : Nat) : Int) :=
    Int.ofNat_le.mpr hr
  have hpos : (0 : Int) < (2 - ((a % 2 : Nat) : Int)) * 10000000000 := by
    omega
  have hID : ((NSeed a + 1 : Nat) : Int) * ((NSeed a + 1 : Nat) : Int)
      - ((a * 10 ^ 10 : Nat) : Int)
      = (((a / 2 : Nat) : Int) - 4999999999) * (((a / 2 : Nat) : Int) - 4999999999)
        + (2 - ((a % 2 : Nat) : Int)) * 10000000000 := by
    rw [eN, eA]
    simp only [Int.natCast_add, Int.natCast_mul, Int.add_mul, Int.mul_add,
      Int.sub_mul, Int.mul_sub]
    omega
  suffices h : ((a * 10 ^ 10 : Nat) : Int)
      < ((NSeed a + 1 : Nat) : Int) * ((NSeed a + 1 : Nat) : Int) by
    rw [← Int.natCast_mul] at h
    exact Int.ofNat_lt.mp h
  omega

/-- The seed is at least the floor root. -/
theorem seed_ge_s {a : Nat} : NS a ≤ NSeed a := by
  have h := seed_succ_sq_gt (a := a)
  have hs1 : NS a < NSeed a + 1 := by
    by_cases hle : NS a < NSeed a + 1
    · exact hle
    · exfalso
      have hle' : NSeed a + 1 ≤ NS a := by omega
      have hle2 : (NSeed a + 1) * (NSeed a + 1) ≤ NS a * NS a :=
        Nat.mul_le_mul hle' hle'
      have hle3 := sqrt_sq_le a
      omega
  omega

/-- `A / z ≤ s` for `z ≥ s + 1`. -/
theorem f_le_s {a z : Nat} (hz : NS a + 1 ≤ z) : a * 10 ^ 10 / z ≤ NS a := by
  have hsq := sqrt_gt a
  have hle : (NS a + 1) * (NS a + 1) ≤ (NS a + 1) * z :=
    Nat.mul_le_mul_left _ hz
  have hlt : a * 10 ^ 10 < (NS a + 1) * z :=
    Nat.lt_of_lt_of_le hsq hle
  have hdiv : a * 10 ^ 10 / z < NS a + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < z)).mpr hlt
  exact Nat.lt_succ_iff.mp hdiv

/-- The root is below `2^101`. -/
theorem s_lt_pow {a : Nat} (hM : a ≤ 2 ^ 167 - 1) : NS a < 2 ^ 101 := by
  have ha167 : a < 2 ^ 167 := by omega
  have hd : (10 : Nat) ^ 10 < 2 ^ 34 := by decide
  have hd0 : (0 : Nat) < 2 ^ 34 := by decide
  have hAlt : a * 10 ^ 10 < 2 ^ 167 * 2 ^ 34 :=
    Nat.mul_lt_mul_of_lt_of_le ha167 (by decide) hd0
  have h201 : (2 : Nat) ^ 167 * 2 ^ 34 = 2 ^ 201 := by decide
  have h202 : (2 : Nat) ^ 202 = (2 ^ 101) * (2 ^ 101) := by decide
  have hlt : (2 : Nat) ^ 201 < 2 ^ 202 :=
    Nat.pow_lt_pow_right (by decide) (by decide)
  have hss : NS a * NS a < (2 ^ 101) * (2 ^ 101) := by
    have h1 := sqrt_sq_le a
    omega
  have hkey : NS a ^ 2 < (2 ^ 101) ^ 2 := by
    rw [Nat.pow_two, Nat.pow_two]
    exact hss
  exact (Nat.pow_lt_pow_iff_left (show (2 : Nat) ≠ 0 by decide)).mp hkey

/-- Pure helpers (no division by variables), proved once by `omega`. -/
theorem halve_aux {w z s : Nat} (h : 2 * w ≤ s + z) (hz : s + 1 ≤ z) :
    2 * (w - (s + 1)) ≤ z - (s + 1) := by
  omega

theorem nn_le_aux {u z s : Nat} (hf : u ≤ s) : 2 * ((u + z) / 2) ≤ s + z := by
  have hmod := Nat.div_add_mod (u + z) 2
  omega

theorem mem_aux {w s : Nat} (hge : s ≤ w) (hle : w ≤ s + 2) :
    (w + s) / 2 = s ∨ (w + s) / 2 = s + 1 := by
  omega

theorem succ_aux {u t : Nat} (hfle : u ≤ t + 1) (hfge : t ≤ u) :
    (u + (t + 1 + 1)) / 2 = t + 1 := by
  omega

theorem ge_aux1 {u z s : Nat} (h : 2 * s - z ≤ u) (h2s : z ≤ 2 * s) :
    s ≤ (u + z) / 2 := by
  omega

theorem ge_aux2 {u z s : Nat} (h : 2 * s < z) : s ≤ (u + z) / 2 := by
  omega

theorem range_aux {u z s a : Nat} (h1 : u ≤ s + 2)
    (hle1 : z ≤ a / 2 + 5 * 10 ^ 9 + 1) (hs : s ≤ 2 ^ 101 - 1)
    (hM : a ≤ 2 ^ 167 - 1) : u + z ≤ 2 ^ 167 - 1 := by
  omega

/-- Newton step stays above the root. -/
theorem step_ge_s {a z : Nat} (ha : 0 < a) (hle : NS a ≤ z) :
    NS a ≤ NN a z := by
  have hs1 : 0 < NS a := s_pos ha
  have hs0 : 0 < z := by omega
  have hA := sqrt_sq_le a
  have c10 : (10 : Nat) ^ 10 = 10000000000 := by decide
  have hA100 : NS a * NS a ≤ a * 10000000000 := by
    rw [← c10]; exact hA
  have hNN : NN a z = (a * 10 ^ 10 / z + z) / 2 := rfl
  by_cases h2s : z ≤ 2 * NS a
  · have hcastN : (2 * NS a - z) * z ≤ a * 10000000000 := by
      suffices hc : ((2 * NS a - z : Nat) : Int) * ((z : Nat) : Int)
          ≤ ((a * 10000000000 : Nat) : Int) from Int.ofNat_le.mp hc
      have hsq := int_sq_nonneg (((z : Nat) : Int) - ((NS a : Nat) : Int))
      have hA' : ((NS a * NS a : Nat) : Int) ≤ ((a * 10000000000 : Nat) : Int) :=
        Int.ofNat_le.mpr hA100
      simp only [Int.natCast_mul] at hA'
      have e1 : (2 * ((NS a : Nat) : Int) - ((z : Nat) : Int)) * ((z : Nat) : Int)
          = 2 * (((NS a : Nat) : Int) * ((z : Nat) : Int))
            - ((z : Nat) : Int) * ((z : Nat) : Int) := by
        simp only [Int.sub_mul]
        rw [Int.mul_assoc]
      have e2 : ((z : Nat) : Int) * ((NS a : Nat) : Int)
          = ((NS a : Nat) : Int) * ((z : Nat) : Int) := Int.mul_comm _ _
      simp only [Int.sub_mul, Int.mul_sub] at hsq
      have hsub : ((2 * NS a - z : Nat) : Int)
          = 2 * ((NS a : Nat) : Int) - ((z : Nat) : Int) := by
        rw [Int.ofNat_sub h2s]
        simp only [Int.natCast_mul]
        omega
      simp only [Int.natCast_mul]
      rw [hsub]
      omega
    have hle : 2 * NS a - z ≤ a * 10 ^ 10 / z := by
      have hcastN10 : (2 * NS a - z) * z ≤ a * 10 ^ 10 := by
        rw [c10]; exact hcastN
      exact (Nat.le_div_iff_mul_le hs0).mpr hcastN10
    rw [hNN]
    exact ge_aux1 hle h2s
  · have h2s' : 2 * NS a < z := by omega
    rw [hNN]
    exact ge_aux2 h2s'

/-- Distance to `NS a + 1` at least halves each step. -/
theorem halve {a z : Nat} (hz : NS a + 1 ≤ z) :
    2 * (NN a z - (NS a + 1)) ≤ z - (NS a + 1) := by
  have hf := f_le_s (a := a) (z := z) hz
  have h2nn : 2 * NN a z ≤ NS a + z := by
    have hNN : NN a z = (a * 10 ^ 10 / z + z) / 2 := rfl
    rw [hNN]
    exact nn_le_aux hf
  exact halve_aux h2nn hz

/-- One step from `s + 1` lands exactly on `s`. -/
theorem step_succ {a : Nat} (ha : 0 < a) : NN a (NS a + 1) = NS a := by
  have hs1 : 0 < NS a := s_pos ha
  obtain ⟨t, ht⟩ : ∃ t, NS a = t + 1 := ⟨NS a - 1, by omega⟩
  rw [ht]
  have hfle : a * 10 ^ 10 / (t + 1 + 1) ≤ t + 1 := by
    have hz : NS a + 1 ≤ t + 1 + 1 := by omega
    have h := f_le_s hz
    rwa [ht] at h
  have hfge : t ≤ a * 10 ^ 10 / (t + 1 + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < t + 1 + 1)).mpr
    have hA := sqrt_sq_le a
    rw [ht] at hA
    have e2 : (t + 1) * (t + 1) = t * (t + 1 + 1) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    omega
  have hNN : NN a (t + 1 + 1) = (a * 10 ^ 10 / (t + 1 + 1) + (t + 1 + 1)) / 2 := rfl
  rw [hNN]
  exact succ_aux hfle hfge

/-- One step from `s` stays in `{s, s + 1}`. -/
theorem step_mem {a : Nat} (ha : 0 < a) :
    NN a (NS a) = NS a ∨ NN a (NS a) = NS a + 1 := by
  have hs1 : 0 < NS a := s_pos ha
  have hge : NS a ≤ a * 10 ^ 10 / NS a :=
    (Nat.le_div_iff_mul_le hs1).mpr (sqrt_sq_le a)
  have hle : a * 10 ^ 10 / NS a ≤ NS a + 2 := by
    apply Nat.div_le_of_le_mul
    have hsq2 := sqrt_gt a
    have e : (NS a + 1) * (NS a + 1) = NS a * (NS a + 2) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    omega
  have hNN : NN a (NS a) = (a * 10 ^ 10 / NS a + NS a) / 2 := rfl
  rw [hNN]
  exact mem_aux hge hle

/-- `A / z ≤ s + 2` for `z ≥ s`. -/
theorem f_le_s2 {a z : Nat} (hs1 : 0 < NS a) (hle : NS a ≤ z) :
    a * 10 ^ 10 / z ≤ NS a + 2 := by
  have h1 : a * 10 ^ 10 / z ≤ a * 10 ^ 10 / NS a :=
    Nat.div_le_div_left hle hs1
  have h2 : a * 10 ^ 10 / NS a ≤ NS a + 2 := by
    apply Nat.div_le_of_le_mul
    have hsq2 := sqrt_gt a
    have e : (NS a + 1) * (NS a + 1) = NS a * (NS a + 2) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    omega
  exact Nat.le_trans h1 h2

theorem s_add2_le_M {a : Nat} (hM : a ≤ 2 ^ 167 - 1) :
    NS a + 2 ≤ 2 ^ 167 - 1 := by
  have hs : NS a ≤ 2 ^ 101 - 1 := by
    have := s_lt_pow hM
    omega
  omega

/-- The Newton update stays in range. -/
theorem range_le_M {a z : Nat} (hM : a ≤ 2 ^ 167 - 1) (ha : 0 < a)
    (hle : NS a ≤ z) (hle1 : z ≤ NSeed a + 1) :
    a * 10 ^ 10 / z + z ≤ 2 ^ 167 - 1 := by
  have hs1 : 0 < NS a := s_pos ha
  have h1 : a * 10 ^ 10 / z ≤ NS a + 2 := f_le_s2 hs1 hle
  have hs : NS a ≤ 2 ^ 101 - 1 := by
    have := s_lt_pow hM
    omega
  have hdef : NSeed a = a / 2 + 5 * 10 ^ 9 := rfl
  have hle1' : z ≤ a / 2 + 5 * 10 ^ 9 + 1 := by omega
  exact range_aux h1 hle1' hs hM

theorem lt_aux {u z s : Nat} (hf : u ≤ s) (hz : s + 1 ≤ z) :
    (u + z) / 2 < z := by
  omega

/-- Newton step strictly decreases above the root. -/
theorem step_lt {a z : Nat} (hz : NS a + 1 ≤ z) : NN a z < z := by
  have hf := f_le_s hz
  have hNN : NN a z = (a * 10 ^ 10 / z + z) / 2 := rfl
  rw [hNN]
  exact lt_aux hf hz

/-- Iterates stay at or above the root. -/
theorem seq_ge_s {a : Nat} (ha : 0 < a) (k : Nat) : NS a ≤ NSeq a k := by
  induction k with
  | zero => exact seed_ge_s
  | succ k ih => exact step_ge_s ha ih

/-- Iterates stay near the seed. -/
theorem seq_le_seed1 {a : Nat} (ha : 0 < a) (k : Nat) :
    NSeq a k ≤ NSeed a + 1 := by
  induction k with
  | zero => exact Nat.le_succ _
  | succ k ih =>
    have e : NSeq a (k + 1) = NN a (NSeq a k) := rfl
    by_cases h : NSeq a k = NS a
    · have hmem := step_mem ha
      rw [e, h]
      cases hmem with
      | inl h1 =>
        rw [h1]
        have := seed_ge_s (a := a)
        omega
      | inr h1 =>
        rw [h1]
        have := seed_ge_s (a := a)
        omega
    · have hsle : NS a ≤ NSeq a k := seq_ge_s ha k
      have hlt : NS a + 1 ≤ NSeq a k := by omega
      have hstep : NN a (NSeq a k) < NSeq a k := step_lt hlt
      rw [e]
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le hstep ih)

/-- Exponential bound: `2^k * e_k ≤ e_0`. -/
theorem seq_exp {a : Nat} (ha : 0 < a) (k : Nat) :
    2 ^ k * (NSeq a k - (NS a + 1)) ≤ NSeed a - (NS a + 1) := by
  induction k with
  | zero =>
    have e0 : NSeq a 0 = NSeed a := rfl
    rw [e0, Nat.pow_zero]
    omega
  | succ k ih =>
    have hkk : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have e1 : NSeq a (k + 1) = NN a (NSeq a k) := rfl
    by_cases h : NSeq a k = NS a
    · have hmem := step_mem ha
      have h0 : NN a (NS a) - (NS a + 1) = 0 := by
        cases hmem with
        | inl h1 => omega
        | inr h1 => omega
      rw [e1, h, h0, hkk]
      exact Nat.zero_le _
    · have hsle : NS a ≤ NSeq a k := seq_ge_s ha k
      have hlt : NS a + 1 ≤ NSeq a k := by omega
      have hhalve := halve hlt
      have h2 : 2 ^ k * (2 * (NN a (NSeq a k) - (NS a + 1)))
          ≤ 2 ^ k * (NSeq a k - (NS a + 1)) :=
        Nat.mul_le_mul_left _ hhalve
      have h3 : 2 ^ k * 2 * (NN a (NSeq a k) - (NS a + 1))
          = 2 ^ k * (2 * (NN a (NSeq a k) - (NS a + 1))) :=
        Nat.mul_assoc _ _ _
      rw [hkk, e1, h3]
      exact Nat.le_trans h2 ih

/-- By step `167` the iterate is `s` or `s + 1`. -/
theorem seq_mem {a : Nat} (hM : a ≤ 2 ^ 167 - 1) (ha : 0 < a) {j : Nat}
    (hj : 167 ≤ j) : NSeq a j = NS a ∨ NSeq a j = NS a + 1 := by
  have hexp := seq_exp ha j
  have hsle := seq_ge_s ha j
  have he0 : NSeed a - (NS a + 1) < 2 ^ 167 := by
    have h2 := seed_le_M hM
    omega
  have h167 : (2 : Nat) ^ 167 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
  have hd0 : NSeq a j - (NS a + 1) = 0 := by
    by_cases h : 1 ≤ NSeq a j - (NS a + 1)
    · exfalso
      have h1 : 2 ^ j * 1 ≤ 2 ^ j * (NSeq a j - (NS a + 1)) :=
        Nat.mul_le_mul_left _ h
      have h11 : 2 ^ j ≤ 2 ^ j * 1 := by omega
      omega
    · omega
  omega

/-- A fixed point above the root is the root. -/
theorem fixed_eq_s {a w : Nat} (_ha : 0 < a) (hle : NS a ≤ w)
    (hfix : NN a w = w) : w = NS a := by
  by_cases h : NS a + 1 ≤ w
  · exfalso
    have hlt := step_lt h
    omega
  · omega

/-- `n` with `n^2 ≤ A < (n+1)^2` is the floor root. -/
theorem eq_sqrt_of {a n : Nat} (h1 : n * n ≤ a * 10 ^ 10)
    (h2 : a * 10 ^ 10 < (n + 1) * (n + 1)) : NS a = n := by
  have hs1 : n ≤ NS a := by
    by_cases h : n ≤ NS a
    · exact h
    · exfalso
      have hlt : NS a < n := by omega
      have hle : (NS a + 1) * (NS a + 1) ≤ n * n :=
        Nat.mul_le_mul (Nat.succ_le_of_lt hlt) (Nat.succ_le_of_lt hlt)
      have hsq := sqrt_gt a
      omega
  have hs2 : NS a ≤ n := by
    by_cases h : NS a ≤ n
    · exact h
    · exfalso
      have hlt : n < NS a := by omega
      have hle : (n + 1) * (n + 1) ≤ NS a * NS a :=
        Nat.mul_le_mul (Nat.succ_le_of_lt hlt) (Nat.succ_le_of_lt hlt)
      have hsq := sqrt_sq_le a
      omega
  omega

/-- If the seed is a fixed point of `a`, it is the root. -/
theorem seed_fixed {a : Nat} (h : NSeed a = a) : NS a = a := by
  have hgt := seed_succ_sq_gt (a := a)
  rw [h] at hgt
  have ha10 : a ≤ 10000000000 := by
    have hseed : a / 2 + 5 * 10 ^ 9 = a := h
    have c : 5 * 10 ^ 9 = 5000000000 := by decide
    omega
  have hle : a * a ≤ a * 10 ^ 10 := Nat.mul_le_mul_left _ ha10
  exact eq_sqrt_of hle hgt

/-- The minimum of two consecutive late iterates is the root. -/
theorem min_pair {y z s : Nat}
    (hy : y = s ∨ y = s + 1) (hz : z = s ∨ z = s + 1)
    (hne : ¬ (y = s + 1 ∧ z = s + 1)) :
    minFn ((y : Nat) : Int) ((z : Nat) : Int) = ((s : Nat) : Int) := by
  unfold minFn
  cases hy with
  | inl hy =>
    cases hz with
    | inl hz =>
      rw [hy, hz, if_neg (by omega)]
    | inr hz =>
      rw [hy, hz, if_pos (Int.ofNat_lt.mpr (Nat.lt_succ_self _))]
  | inr hy =>
    cases hz with
    | inl hz =>
      rw [hy, hz,
        if_neg (show ¬ (((s + 1 : Nat)) : Int) < ((s : Nat) : Int) by omega)]
    | inr hz =>
      rw [hy, hz] at hne ⊢
      exact absurd ⟨rfl, rfl⟩ hne

/-- The loop follows the Nat sequence (or stops early at the root). -/
theorem loop_prefix {a : Nat} (hM : a ≤ 2 ^ 167 - 1) (ha : 0 < a) (k : Nat)
    (hk : k ≤ 256) :
    (loop (a : Int) (256 - k) (↑(NY a k)) (↑(NSeq a k))
        = loop (a : Int) 256 (↑a) (↑(NSeed a))
      ∧ NS a ≤ NSeq a k ∧ NSeq a k ≤ NSeed a + 1
      ∧ 2 ^ k * (NSeq a k - (NS a + 1)) ≤ NSeed a - (NS a + 1)
      ∧ (k = 0 ∨ NS a ≤ NY a k))
    ∨ (loop (a : Int) 256 (↑a) (↑(NSeed a))
        = some (↑(NS a), ↑(NS a))) := by
  revert hk
  induction k with
  | zero =>
    intro _
    refine Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · exact seed_ge_s
    · exact Nat.le_succ _
    · exact seq_exp ha 0
    · exact Or.inl rfl
  | succ k ih =>
    intro hk1
    have hk : k ≤ 256 := by omega
    have hIH := ih hk
    cases hIH with
    | inr hr => exact Or.inr hr
    | inl h =>
      obtain ⟨hL, hsle, hle1, hexp, hY⟩ := h
      obtain ⟨m', hm⟩ : ∃ m', 256 - k = m' + 1 := ⟨(256 - k) - 1, by omega⟩
      have hm2 : 256 - (k + 1) = m' := by omega
      rw [hm] at hL
      by_cases hne : NSeq a k = NY a k
      · have hce : ((NSeq a k : Nat) : Int) = ((NY a k : Nat) : Int) := by
          rw [hne]
        rw [hce, loop_stop] at hL
        have hYk : NY a k = NS a := by
          by_cases hk0 : k = 0
          · subst hk0
            have eY : NY a 0 = a := rfl
            have eV : NSeq a 0 = NSeed a := rfl
            rw [eV, eY] at hne
            have hs := seed_fixed hne
            rw [eY]
            exact hs.symm
          · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            have eY : NY a (k' + 1) = NSeq a k' := rfl
            have eV : NSeq a (k' + 1) = NN a (NSeq a k') := rfl
            rw [eY, eV] at hne
            exact fixed_eq_s ha (seq_ge_s ha k') hne
        rw [hYk] at hL
        exact Or.inr hL.symm
      · have hne' : ((NSeq a k : Nat) : Int) ≠ ((NY a k : Nat) : Int) :=
          fun c => hne (Int.ofNat.inj c)
        have hs1 : 0 < NS a := s_pos ha
        have hpos : 0 < NSeq a k := by
          have hle := seq_ge_s ha k
          omega
        have hAv : a * 10 ^ 10 / NSeq a k ≤ 2 ^ 167 - 1 := by
          have h1 : a * 10 ^ 10 / NSeq a k ≤ NS a + 2 :=
            f_le_s2 hs1 (seq_ge_s ha k)
          exact Nat.le_trans h1 (s_add2_le_M hM)
        have hrange : a * 10 ^ 10 / NSeq a k + NSeq a k ≤ 2 ^ 167 - 1 :=
          range_le_M hM ha (seq_ge_s ha k) (seq_le_seed1 ha k)
        have h1 : ddiv (a : Int) ((NSeq a k : Nat) : Int)
            = some (((a * 10 ^ 10 / NSeq a k : Nat)) : Int) :=
          ddiv_nat hpos hAv
        have h2 : dadd (((a * 10 ^ 10 / NSeq a k : Nat)) : Int)
            (((NSeq a k : Nat)) : Int)
            = some ((((a * 10 ^ 10 / NSeq a k + NSeq a k : Nat))) : Int) :=
          dadd_nat hrange
        have h3 : ddiv ((((a * 10 ^ 10 / NSeq a k + NSeq a k : Nat))) : Int)
            (2 * DIVISOR)
            = some (((NN a (NSeq a k) : Nat)) : Int) := by
          have hd : (2 : Int) * DIVISOR = ((2 * 10 ^ 10 : Nat) : Int) := by
            decide
          have h2' : (a * 10 ^ 10 / NSeq a k + NSeq a k) * 10 ^ 10
              / (2 * 10 ^ 10)
              = (a * 10 ^ 10 / NSeq a k + NSeq a k) / 2 :=
            Nat.mul_div_mul_right _ _ (show 0 < 10 ^ 10 by decide)
          have hM' : (a * 10 ^ 10 / NSeq a k + NSeq a k) * 10 ^ 10
              / (2 * 10 ^ 10) ≤ 2 ^ 167 - 1 := by
            rw [h2']
            exact Nat.le_trans (Nat.div_le_self _ _) hrange
          rw [hd]
          have hdd := ddiv_nat (a := a * 10 ^ 10 / NSeq a k + NSeq a k)
            (b := 2 * 10 ^ 10) (show 0 < 2 * 10 ^ 10 by decide) hM'
          rw [h2'] at hdd
          exact hdd
        have step := loop_step_of (n := m') (hne := hne') (h1 := h1)
          (h2 := h2) (h3 := h3)
        have eY : NY a (k + 1) = NSeq a k := rfl
        have eV : NSeq a (k + 1) = NN a (NSeq a k) := rfl
        refine Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hm2, eY, eV]
          exact step.symm.trans hL
        · exact step_ge_s ha (seq_ge_s ha k)
        · exact seq_le_seed1 ha (k + 1)
        · exact seq_exp ha (k + 1)
        · exact Or.inr (seq_ge_s ha k)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x h
  unfold sqrt vyperSqrtWith
  rw [if_pos h]

theorem req_deployed_loop : DeployedLoop sqrt :=
  ⟨minFn, fun _ => rfl⟩

/-- Non-negative decimals round-trip through `toNat`. -/
theorem toNat_le_M {x : Int} (hx : IsDecimal x) (hx0 : 0 ≤ x) :
    x.toNat ≤ 2 ^ 167 - 1 := by
  have hxt : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
  have h1 : x ≤ MAX_DECIMAL := hx.2
  have h2 : MAX_DECIMAL = ((2 ^ 167 - 1 : Nat) : Int) := max_decimal_eq
  rw [h2, ← hxt] at h1
  exact Int.ofNat_le.mp h1

/-- The routine returns the floor root on positive decimals. -/
theorem main {a : Nat} (hM : a ≤ 2 ^ 167 - 1) (ha : 0 < a) :
    vyperSqrtWith minFn (a : Int) = some (((NS a : Nat)) : Int) := by
  rw [vyperSqrtWith_pos minFn ha hM]
  have nseed : NSeed a = a / 2 + 5 * 10 ^ 9 := rfl
  rw [← nseed]
  have hP := loop_prefix hM ha 256 (by omega : 256 ≤ 256)
  cases hP with
  | inr hr =>
    rw [hr]
    have hmin : minFn (↑(NS a)) (↑(NS a)) = ↑(NS a) :=
      min_pair (Or.inl rfl) (Or.inl rfl) (by omega)
    exact congrArg some hmin
  | inl h =>
    obtain ⟨hL, hsle, hle1, hexp, hY⟩ := h
    have hz : 256 - 256 = 0 := by decide
    rw [hz] at hL
    have h0 : loop (a : Int) 0 (↑(NY a 256)) (↑(NSeq a 256))
        = some (↑(NY a 256), ↑(NSeq a 256)) := rfl
    rw [h0] at hL
    have eY : NY a 256 = NSeq a 255 := rfl
    have eV : NSeq a 256 = NN a (NSeq a 255) := rfl
    have hm255 : NSeq a 255 = NS a ∨ NSeq a 255 = NS a + 1 :=
      seq_mem hM ha (by decide : 167 ≤ 255)
    have hm256 : NSeq a 256 = NS a ∨ NSeq a 256 = NS a + 1 :=
      seq_mem hM ha (by decide : 167 ≤ 256)
    have hne : ¬ (NSeq a 255 = NS a + 1 ∧ NSeq a 256 = NS a + 1) := by
      intro hcon
      have h255 := hcon.1
      have h256 := hcon.2
      rw [eV, h255, step_succ ha] at h256
      omega
    have hy : NY a 256 = NS a ∨ NY a 256 = NS a + 1 := by
      rw [eY]
      exact hm255
    have hne' : ¬ (NY a 256 = NS a + 1 ∧ NSeq a 256 = NS a + 1) := by
      rw [eY]
      exact hne
    have hmin : minFn (↑(NY a 256)) (↑(NSeq a 256)) = ↑(NS a) :=
      min_pair hy hm256 hne'
    rw [← hL]
    exact congrArg some hmin

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hr
  by_cases hx0 : x < 0
  · have hnone : sqrt x = none := by
      unfold sqrt vyperSqrtWith
      rw [if_pos hx0]
    rw [hnone] at hr
    simp at hr
  · have hxnn : 0 ≤ x := by omega
    have hxt : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hxnn
    have hle : x.toNat ≤ 2 ^ 167 - 1 := toNat_le_M hx hxnn
    by_cases ha0 : x.toNat = 0
    · have hx0' : x = 0 := by omega
      rw [hx0'] at hr ⊢
      have hr0 : (sqrt (0 : Int)) = some 0 := by
        unfold sqrt vyperSqrtWith
        simp
      rw [hr0] at hr
      have hrr : (0 : Int) = r := by simpa using hr
      subst hrr
      simp
    · have hmain := main hle (by omega : 0 < x.toNat)
      have hsqrt : sqrt x = some (((NS x.toNat : Nat)) : Int) := by
        rw [← hxt]
        exact hmain
      rw [hsqrt] at hr
      have hrr : (((NS x.toNat : Nat)) : Int) = r := by simpa using hr
      have hN := sqrt_sq_le x.toNat
      have hNc : ((NS x.toNat * NS x.toNat : Nat) : Int)
          ≤ ((x.toNat * 10 ^ 10 : Nat) : Int) := Int.ofNat_le.mpr hN
      simp only [Int.natCast_mul] at hNc
      rw [← hrr, ← hxt, divisor_eq]
      exact hNc

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hr
  by_cases hx0 : x < 0
  · have hnone : sqrt x = none := by
      unfold sqrt vyperSqrtWith
      rw [if_pos hx0]
    rw [hnone] at hr
    simp at hr
  · have hxnn : 0 ≤ x := by omega
    have hxt : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hxnn
    have hle : x.toNat ≤ 2 ^ 167 - 1 := toNat_le_M hx hxnn
    by_cases ha0 : x.toNat = 0
    · have hx0' : x = 0 := by omega
      rw [hx0'] at hr ⊢
      have hr0 : (sqrt (0 : Int)) = some 0 := by
        unfold sqrt vyperSqrtWith
        simp
      rw [hr0] at hr
      have hrr : (0 : Int) = r := by simpa using hr
      subst hrr
      simp
    · have hmain := main hle (by omega : 0 < x.toNat)
      have hsqrt : sqrt x = some (((NS x.toNat : Nat)) : Int) := by
        rw [← hxt]
        exact hmain
      rw [hsqrt] at hr
      have hrr : (((NS x.toNat : Nat)) : Int) = r := by simpa using hr
      have hN := sqrt_gt x.toNat
      have hNc : ((x.toNat * 10 ^ 10 : Nat) : Int)
          < (((NS x.toNat + 1) * (NS x.toNat + 1) : Nat) : Int) :=
        Int.ofNat_lt.mpr hN
      simp only [Int.natCast_mul, Int.natCast_add] at hNc
      have b1 : ((1 : Nat) : Int) = 1 := by decide
      rw [b1] at hNc
      rw [← hrr, ← hxt, divisor_eq]
      exact hNc

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx hx0
  have hxt : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
  have hle : x.toNat ≤ 2 ^ 167 - 1 := toNat_le_M hx hx0
  by_cases ha0 : x.toNat = 0
  · have hx0' : x = 0 := by omega
    rw [hx0']
    have hr0 : (sqrt (0 : Int)) = some 0 := by
      unfold sqrt vyperSqrtWith
      simp
    rw [hr0]
    rfl
  · have hmain := main hle (by omega : 0 < x.toNat)
    have hsqrt : sqrt x = some (((NS x.toNat : Nat)) : Int) := by
      rw [← hxt]
      exact hmain
    rw [hsqrt]
    rfl

end VyperSqrt
