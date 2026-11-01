import VyperSqrt.Spec
import VyperSqrt.Lemmas
/-!
Port of the code the Vyper compiler v0.4.0 (commit e9db8d9f7486eae38f5b86531629019ad28f514e)
inlines for the builtin `sqrt(d: decimal) -> decimal`, `vyper/builtins/functions.py`, class
`Sqrt` (lines 2117 to 2172), with the fix of pull request 4486 (merge commit
2ffc8b3db8b7e32257a72560fa89e7dcf81b5384, released in v0.4.1): after the loop,
`if y < z: z = y`, i.e. the result is the minimum of the last two iterates.
-/
namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith _ x = none
  unfold vyperSqrtWith
  simp [hx]

theorem req_deployed_loop : DeployedLoop sqrt := ⟨_, fun _ => rfl⟩

/-- `2 * u * v ≤ u * u + v * v` on naturals. -/
theorem two_mul_le_add_sq (u v : Nat) : 2 * (u * v) ≤ u * u + v * v := by
  by_cases h : u ≤ v
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    have euv : u * v = u * u + u * k := by rw [hk]; exact Nat.mul_add _ _ _
    have evv : v * v = u * u + (u * k + (u * k + k * k)) := by
      rw [hk, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm k u]
      exact Nat.add_assoc _ _ _
    have hcc : 0 ≤ k * k := Nat.zero_le _
    omega
  · have h2 : v ≤ u := Nat.le_of_not_ge h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h2
    have euv : u * v = v * v + v * k := by rw [hk, Nat.add_mul, Nat.mul_comm k v]
    have euu : u * u = v * v + (v * k + (v * k + k * k)) := by
      rw [hk, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm k v]
      exact Nat.add_assoc _ _ _
    have hcc : 0 ≤ k * k := Nat.zero_le _
    have hc : u * v = v * u := Nat.mul_comm _ _
    omega

/-- Monotonicity of `n * n`. -/
theorem sq_mono {u v : Nat} (h : u ≤ v) : u * u ≤ v * v :=
  Nat.mul_le_mul h h

/-- Scaled value whose root we take: `N = a * 10^10`. -/
def Nv (a : Nat) : Nat := a * 10 ^ 10

/-- Newton seed `z0 = a / 2 + 5 * 10^9`. -/
def Z0v (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- One Newton step `(N / z + z) / 2`. -/
def Nstep (a z : Nat) : Nat := (Nv a / z + z) / 2

/-- Uniqueness of the integer square root. -/
theorem sqrt_unique (w N : Nat) (h1 : w * w ≤ N) (h2 : N < (w + 1) * (w + 1)) :
    w = Nat.sqrt N := by
  have hs1 : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hs2 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by
    have h := Nat.lt_succ_sqrt N
    rwa [Nat.succ_eq_add_one] at h
  by_cases hlt : w < Nat.sqrt N
  · have hle : w + 1 ≤ Nat.sqrt N := hlt
    have := sq_mono hle
    omega
  · by_cases hgt : Nat.sqrt N < w
    · have hle : Nat.sqrt N + 1 ≤ w := hgt
      have h3 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ w * w := Nat.mul_le_mul hle hle
      have h4 : (w + 1) * (w + 1) ≤ w * w ∨ w * w < (w + 1) * (w + 1) := by omega
      omega
    · omega

/-- `a ≤ 2 * (a / 2) + 1`. -/
theorem le_two_div_add_one (a : Nat) : a ≤ 2 * (a / 2) + 1 := by
  have hdm := Nat.div_add_mod a 2
  have hml : a % 2 < 2 := Nat.mod_lt a (by decide)
  omega

/-- The seed square strictly exceeds the scaled value: `(z0 + 1)^2 > N`. -/
theorem seed_sq_gt (a : Nat) : Nv a < (Z0v a + 1) * (Z0v a + 1) := by
  have ha := le_two_div_add_one a
  have hsq := two_mul_le_add_sq (a / 2) (5 * 10 ^ 9)
  have hN : a * 10 ^ 10 ≤ (2 * (a / 2) + 1) * 10 ^ 10 :=
    Nat.mul_le_mul ha (Nat.le_refl _)
  have hexpand : (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1)
      = (a / 2) * (a / 2) + (5 * 10 ^ 9) * (5 * 10 ^ 9) + 1
        + (((a / 2) * (5 * 10 ^ 9) + (a / 2) * (5 * 10 ^ 9))
          + (((a / 2) + (a / 2)) + ((5 * 10 ^ 9) + (5 * 10 ^ 9)))) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    ac_rfl
  unfold Nv Z0v
  omega

/-- The seed is at least the square root. -/
theorem seed_ge_sqrt (a : Nat) :
    Nat.sqrt (Nv a) ≤ Z0v a := by
  by_cases h : Z0v a < Nat.sqrt (Nv a)
  · have hle2 : Z0v a + 1 ≤ Nat.sqrt (Nv a) := h
    have hsq := sq_mono hle2
    have hs := Nat.sqrt_le (Nv a)
    have hg := seed_sq_gt a
    omega
  · omega

/-- `N < (N / w + 1) * w` for `0 < w`. -/
theorem lt_succ_div_mul (a w : Nat) (hw : 0 < w) :
    Nv a < (Nv a / w + 1) * w := by
  have hdm := Nat.div_add_mod (Nv a) w
  have hmod := Nat.mod_lt (Nv a) hw
  have hexp : w * (Nv a / w) + w = (Nv a / w + 1) * w := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm w (Nv a / w)]
  omega

/-- Every Newton iterate stays at or above the root. -/
theorem Nstep_ge_sqrt (a z : Nat) (hz : 0 < z) :
    Nat.sqrt (Nv a) ≤ Nstep a z := by
  unfold Nstep
  by_cases hs : Nat.sqrt (Nv a) = 0
  · rw [hs]
    exact Nat.zero_le _
  · have hs1 : 1 ≤ Nat.sqrt (Nv a) := Nat.pos_of_ne_zero hs
    by_cases hc : (Nv a / z + z) / 2 < Nat.sqrt (Nv a)
    · have h1 : Nv a / z + z < Nat.sqrt (Nv a) * 2 :=
        (Nat.div_lt_iff_lt_mul (by decide)).mp hc
      have hN := lt_succ_div_mul a z hz
      have hqz : Nv a / z + 1 + z ≤ Nat.sqrt (Nv a) * 2 := by omega
      have efunds : (Nv a / z + 1) * z + z * z
          = (Nv a / z + 1 + z) * z :=
        (Nat.add_mul _ _ _).symm
      have hle1b : (Nv a / z + 1 + z) * z ≤ (Nat.sqrt (Nv a) * 2) * z :=
        Nat.mul_le_mul_right z hqz
      have e2s : (Nat.sqrt (Nv a) * 2) * z = 2 * (Nat.sqrt (Nv a) * z) := by
        ac_rfl
      have hsq := two_mul_le_add_sq (Nat.sqrt (Nv a)) z
      have hs2 := Nat.sqrt_le (Nv a)
      omega
    · omega

/-- Above the root, the step is at most the average with the root. -/
theorem Nstep_le_avg (a z : Nat) (hz : Nat.sqrt (Nv a) + 1 ≤ z) :
    Nstep a z ≤ (z + Nat.sqrt (Nv a)) / 2 := by
  have hz0 : 0 < z := by omega
  have hlt : Nv a < (Nat.sqrt (Nv a) + 1) * (Nat.sqrt (Nv a) + 1) := by
    have h := Nat.lt_succ_sqrt (Nv a)
    rwa [Nat.succ_eq_add_one] at h
  have hsq2 : (Nat.sqrt (Nv a) + 1) * (Nat.sqrt (Nv a) + 1)
      ≤ (Nat.sqrt (Nv a) + 1) * z :=
    Nat.mul_le_mul (Nat.le_refl _) hz
  have hN : Nv a < (Nat.sqrt (Nv a) + 1) * z := by omega
  have hq : Nv a / z ≤ Nat.sqrt (Nv a) := by
    have hlt2 : Nv a / z < Nat.sqrt (Nv a) + 1 :=
      (Nat.div_lt_iff_lt_mul hz0).mpr hN
    omega
  unfold Nstep
  exact Nat.div_le_div_right (by omega : Nv a / z + z ≤ z + Nat.sqrt (Nv a))

/-- Above the root, the step strictly decreases. -/
theorem Nstep_lt (a z : Nat) (hz : Nat.sqrt (Nv a) + 1 ≤ z) :
    Nstep a z < z := by
  have hle := Nstep_le_avg a z hz
  have hlt : (z + Nat.sqrt (Nv a)) / 2 < z := by
    have h : z + Nat.sqrt (Nv a) < z * 2 := by omega
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
  omega

/-- A positive fixed point of the step is the root. -/
theorem Nstep_self_eq (a w : Nat) (hw0 : 0 < w) (hw : Nstep a w = w) :
    w = Nat.sqrt (Nv a) := by
  have hqw : w ≤ Nv a / w ∧ Nv a / w ≤ w + 1 := by
    unfold Nstep at hw
    omega
  have hww : w * w ≤ Nv a :=
    (Nat.le_div_iff_mul_le hw0).mp hqw.1
  have hN := lt_succ_div_mul a w hw0
  have hle : (Nv a / w + 1) * w ≤ (w + 2) * w :=
    Nat.mul_le_mul_right w (by omega)
  have e1 : (w + 2) * w = w * w + (w + w) := by
    rw [Nat.add_mul]
    omega
  have e2 : (w + 1) * (w + 1) = w * w + (w + w) + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    ac_rfl
  have h1 : w * w ≤ Nv a := hww
  have h2 : Nv a < (w + 1) * (w + 1) := by omega
  exact sqrt_unique w (Nv a) h1 h2

/-- Numeric literals for the decimal constants. -/
theorem c9 : (5 * 10 ^ 9 : Nat) = 5000000000 := by decide

theorem c10 : (10 ^ 10 : Nat) = 10000000000 := by decide

/-- For a positive input the root is positive. -/
theorem s_pos {a : Nat} (ha : 1 ≤ a) : 1 ≤ Nat.sqrt (Nv a) := by
  by_cases hs : Nat.sqrt (Nv a) = 0
  · have hlt : Nv a < (Nat.sqrt (Nv a) + 1) * (Nat.sqrt (Nv a) + 1) := by
      have h := Nat.lt_succ_sqrt (Nv a)
      rwa [Nat.succ_eq_add_one] at h
    rw [hs] at hlt
    have hN0 : Nv a = 0 := by omega
    have ha0 : a * 10 ^ 10 = 0 := hN0
    have h10 : (10 ^ 10 : Nat) ≠ 0 := by decide
    have hdis := Nat.mul_eq_zero.mp ha0
    omega
  · omega

/-- The quotient stays small: `N / z ≤ s + 2` for `z ≥ s`. -/
theorem q_le_succ2 {a z : Nat} (ha : 1 ≤ a) (hz : Nat.sqrt (Nv a) ≤ z) :
    Nv a / z ≤ Nat.sqrt (Nv a) + 2 := by
  have hs1 := s_pos ha
  have hz0 : 0 < z := by omega
  have hlt : Nv a < (Nat.sqrt (Nv a) + 1) * (Nat.sqrt (Nv a) + 1) := by
    have h := Nat.lt_succ_sqrt (Nv a)
    rwa [Nat.succ_eq_add_one] at h
  have e2 : (Nat.sqrt (Nv a) + 1) * (Nat.sqrt (Nv a) + 1)
      = Nat.sqrt (Nv a) * Nat.sqrt (Nv a)
        + (Nat.sqrt (Nv a) + Nat.sqrt (Nv a)) + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    ac_rfl
  have e3 : (Nat.sqrt (Nv a) + 2) * Nat.sqrt (Nv a)
      = Nat.sqrt (Nv a) * Nat.sqrt (Nv a)
        + (Nat.sqrt (Nv a) + Nat.sqrt (Nv a)) := by
    rw [Nat.add_mul]
    omega
  have hNle : Nv a ≤ (Nat.sqrt (Nv a) + 2) * Nat.sqrt (Nv a) := by omega
  have h3 : (Nat.sqrt (Nv a) + 2) * Nat.sqrt (Nv a)
      ≤ (Nat.sqrt (Nv a) + 2) * z :=
    Nat.mul_le_mul (Nat.le_refl _) hz
  have e4 : (Nat.sqrt (Nv a) + 3) * z
      = (Nat.sqrt (Nv a) + 2) * z + z := by
    have h38 : Nat.sqrt (Nv a) + 3 = (Nat.sqrt (Nv a) + 2) + 1 := by omega
    rw [h38, Nat.add_mul, Nat.one_mul]
  have h4 : Nv a < (Nat.sqrt (Nv a) + 3) * z := by omega
  have h5 : Nv a / z < Nat.sqrt (Nv a) + 3 :=
    (Nat.div_lt_iff_lt_mul hz0).mpr h4
  omega

/-- The step maps `s + 1` to `s`. -/
theorem Nstep_at_succ (a : Nat) :
    Nstep a (Nat.sqrt (Nv a) + 1) = Nat.sqrt (Nv a) := by
  have hle := Nstep_le_avg a (Nat.sqrt (Nv a) + 1) (Nat.le_refl _)
  have hge := Nstep_ge_sqrt a (Nat.sqrt (Nv a) + 1) (by omega)
  omega

/-- The step maps `s` into `{s, s + 1}` (upper half). -/
theorem Nstep_at_sqrt_le {a : Nat} (ha : 1 ≤ a) :
    Nstep a (Nat.sqrt (Nv a)) ≤ Nat.sqrt (Nv a) + 1 := by
  have hq := q_le_succ2 ha (Nat.le_refl _)
  unfold Nstep
  omega

/-- The distance to the root at least halves above the root. -/
theorem Nstep_dist_half (a z : Nat) (hz : Nat.sqrt (Nv a) + 1 ≤ z) :
    Nstep a z - Nat.sqrt (Nv a) ≤ (z - Nat.sqrt (Nv a)) / 2 := by
  have hle := Nstep_le_avg a z hz
  have hge := Nstep_ge_sqrt a z (by omega)
  omega

/-- The root fits in `2^101`. -/
theorem sqrt_bound {a : Nat} (hle : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (Nv a) ≤ 2 ^ 101 := by
  have h5 : (2 ^ 167 - 1) * 10 ^ 10 < 2 ^ 101 * 2 ^ 101 := by decide
  by_cases h : 2 ^ 101 ≤ Nat.sqrt (Nv a)
  · have h1 : 2 ^ 101 * 2 ^ 101
        ≤ Nat.sqrt (Nv a) * Nat.sqrt (Nv a) := Nat.mul_le_mul h h
    have h2 := Nat.sqrt_le (Nv a)
    have h4 : Nv a ≤ (2 ^ 167 - 1) * 10 ^ 10 := by
      have hN : Nv a = a * 10 ^ 10 := rfl
      rw [hN]
      exact Nat.mul_le_mul hle (Nat.le_refl _)
    omega
  · omega

/-- The Newton iterates from the seed. -/
def Nit (a : Nat) : Nat → Nat
  | 0 => Z0v a
  | n + 1 => Nstep a (Nit a n)

/-- All iterates stay at or above the root. -/
theorem Nit_ge {a : Nat} (ha : 1 ≤ a) (n : Nat) :
    Nat.sqrt (Nv a) ≤ Nit a n := by
  induction n with
  | zero =>
    show Nat.sqrt (Nv a) ≤ Z0v a
    exact seed_ge_sqrt a
  | succ n ih =>
    show Nat.sqrt (Nv a) ≤ Nstep a (Nit a n)
    have hs1 := s_pos ha
    have hpos : 0 < Nit a n := by omega
    exact Nstep_ge_sqrt a _ hpos

/-- All iterates stay at or just above the seed. -/
theorem Nit_le {a : Nat} (ha : 1 ≤ a) (n : Nat) :
    Nit a n ≤ Z0v a + 1 := by
  induction n with
  | zero =>
    show Z0v a ≤ Z0v a + 1
    exact Nat.le_succ _
  | succ n ih =>
    show Nstep a (Nit a n) ≤ Z0v a + 1
    have hge := Nit_ge ha n
    have hs1 := s_pos ha
    have h0 := seed_ge_sqrt a
    by_cases hz : Nat.sqrt (Nv a) + 1 ≤ Nit a n
    · have hle := Nstep_le_avg a (Nit a n) hz
      omega
    · have hmem := Nstep_at_sqrt_le ha
      have heq : Nit a n = Nat.sqrt (Nv a) := by omega
      rw [heq]
      omega

/-- The tail reaches `{s, s+1}` within 167 steps. -/
theorem Nit_reach {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) :
    ∃ K, K ≤ 167 ∧ Nit a K ≤ Nat.sqrt (Nv a) + 1 := by
  have hs1 := s_pos ha
  have e167 : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by decide
  have hlt167 : a < 2 ^ 166 * 2 := by omega
  have halt : a / 2 < 2 ^ 166 :=
    (Nat.div_lt_iff_lt_mul (by decide)).mpr hlt167
  have hbig : (5000000000 : Nat) < 2 ^ 166 := by decide
  have hz0lt : Z0v a < 2 ^ 167 := by
    unfold Z0v
    rw [c9]
    omega
  have hd0 : Nit a 0 - Nat.sqrt (Nv a) < 2 ^ 167 := by
    have h1 : Nit a 0 = Z0v a := rfl
    omega
  have hstep : ∀ n, Nat.sqrt (Nv a) + 2 ≤ Nit a n →
      Nit a (n + 1) - Nat.sqrt (Nv a)
        ≤ (Nit a n - Nat.sqrt (Nv a)) / 2 := by
    intro n hn
    have hz : Nat.sqrt (Nv a) + 1 ≤ Nit a n := by omega
    have h := Nstep_dist_half a (Nit a n) hz
    show Nstep a (Nit a n) - Nat.sqrt (Nv a) ≤ _
    exact h
  have key : ∀ n, n ≤ 167 →
      (∃ j, j ≤ n ∧ Nit a j ≤ Nat.sqrt (Nv a) + 1) ∨
      Nit a n - Nat.sqrt (Nv a) ≤ (Nit a 0 - Nat.sqrt (Nv a)) / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro _
      by_cases h : Nit a 0 ≤ Nat.sqrt (Nv a) + 1
      · exact Or.inl ⟨0, Nat.zero_le 0, h⟩
      · right
        rw [Nat.pow_zero, Nat.div_one]
        exact Nat.le_refl _
    | succ n ih =>
      intro hn
      have hn' : n ≤ 167 := by omega
      cases ih hn' with
      | inl h =>
        obtain ⟨j, hj, hjle⟩ := h
        exact Or.inl ⟨j, by omega, hjle⟩
      | inr hle =>
        by_cases h : Nit a n ≤ Nat.sqrt (Nv a) + 1
        · exact Or.inl ⟨n, by omega, h⟩
        · have hn2 : Nat.sqrt (Nv a) + 2 ≤ Nit a n := by omega
          have hs := hstep n hn2
          have e2 : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := by
            have hh := Nat.pow_succ 2 n
            rwa [Nat.succ_eq_add_one] at hh
          right
          rw [e2, ← Nat.div_div_eq_div_mul]
          exact Nat.le_trans hs (Nat.div_le_div_right hle)
  cases key 167 (Nat.le_refl _) with
  | inl h =>
    obtain ⟨K, hK, hKle⟩ := h
    exact ⟨K, hK, hKle⟩
  | inr hle =>
    have hz167 : (0 : Nat) < 2 ^ 167 := by decide
    have h0 : (Nit a 0 - Nat.sqrt (Nv a)) / 2 ^ 167 = 0 :=
      (Nat.div_eq_zero_iff_lt hz167).mpr hd0
    rw [h0] at hle
    have hzz : Nit a 167 - Nat.sqrt (Nv a) = 0 := by omega
    exact ⟨167, Nat.le_refl _, by omega⟩

/-- Every reachable iterate keeps the operations in range. -/
theorem range_ok {a w : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1)
    (hge : Nat.sqrt (Nv a) ≤ w) (hle2 : w ≤ Z0v a + 1) :
    Nv a / w + w ≤ 2 ^ 167 - 1 := by
  have hq := q_le_succ2 ha hge
  have hsB := sqrt_bound hle
  have e167 : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by decide
  have hlt167 : a < 2 ^ 166 * 2 := by omega
  have halt : a / 2 < 2 ^ 166 :=
    (Nat.div_lt_iff_lt_mul (by decide)).mpr hlt167
  have h2166 : (0 : Nat) < 2 ^ 166 := by decide
  have h1 : a / 2 ≤ 2 ^ 166 - 1 := by omega
  have hbig : (5000000000 + 2 ^ 101 + 2 + (2 ^ 166 - 1) : Nat)
      ≤ 2 ^ 167 - 1 := by decide
  have hz : Z0v a = a / 2 + 5 * 10 ^ 9 := rfl
  rw [c9] at hz
  omega

/-- If the seed equals the input, it is the root. -/
theorem seed_eq_self {a : Nat} (ha : 1 ≤ a) (h : a = Z0v a) :
    a = Nat.sqrt (Nv a) := by
  have hdm := Nat.div_add_mod a 2
  have hmod := Nat.mod_lt a (by decide : 0 < 2)
  have h2 : a = a / 2 + 5 * 10 ^ 9 := h
  rw [c9] at h2
  have hu : a / 2 = 5000000000 ∨ a / 2 = 4999999999 := by omega
  cases hu with
  | inl hu1 =>
    have ha0 : a = 10000000000 := by omega
    rw [ha0]
    apply sqrt_unique
    · decide
    · decide
  | inr hu1 =>
    have ha0 : a = 9999999999 := by omega
    rw [ha0]
    apply sqrt_unique
    · decide
    · decide

/-- The loop trajectory: input, then the Newton iterates. -/
def Ev (a : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => Nit a n

/-- One step along the trajectory is a Newton step (past the start). -/
theorem Ev_step {a : Nat} (k : Nat) (hk : 1 ≤ k) :
    Ev a (k + 1) = Nstep a (Ev a k) := by
  cases k with
  | zero => omega
  | succ k => rfl

/-- The loop follows the trajectory until it stops (with the root). -/
theorem loop_corr {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1)
    (J : Nat) (hJ : J ≤ 167) :
    ∀ j, j ≤ J + 1 →
      (loop (↑a : Int) (256 - j) (Ev a j : Int) (Ev a (j + 1) : Int)
        = loop (↑a : Int) 256 (↑a : Int) (↑(Z0v a) : Int)) ∨
      (∃ w : Nat, w = Nat.sqrt (Nv a) ∧
        loop (↑a : Int) 256 (↑a : Int) (↑(Z0v a) : Int)
          = some (((w : Nat) : Int), (((w : Nat) : Int)))) := by
  have hs1 := s_pos ha
  intro j
  induction j with
  | zero =>
    intro _
    left
    have e0 : Ev a 0 = a := rfl
    have e1 : Ev a (0 + 1) = Z0v a := rfl
    rw [Nat.sub_zero, e0, e1]
  | succ j ih =>
    intro hj
    have hj' : j ≤ J + 1 := by omega
    cases ih hj' with
    | inl hL =>
      obtain ⟨m, hm⟩ : ∃ m, 256 - j = m + 1 := ⟨256 - (j + 1), by omega⟩
      by_cases hEq : (Ev a (j + 1) : Int) = (Ev a j : Int)
      · have hNat : Ev a (j + 1) = Ev a j := Int.ofNat_inj.mp hEq
        rw [hm, hEq] at hL
        rw [loop_stop] at hL
        by_cases hj0 : j = 0
        · subst hj0
          have e0 : Ev a 0 = a := rfl
          have e1 : Ev a (0 + 1) = Z0v a := rfl
          have hself : a = Z0v a := by omega
          have hss := seed_eq_self ha hself
          exact Or.inr ⟨Ev a 0, by omega, hL.symm⟩
        · have hk1 : 1 ≤ j := by omega
          have hstep : Ev a (j + 1) = Nstep a (Ev a j) := Ev_step j hk1
          have hfix : Nstep a (Ev a j) = Ev a j := by omega
          have hpos : 0 < Ev a j := by
            have eE : Ev a j = Nit a (j - 1) := by
              cases j with
              | zero => omega
              | succ k => rfl
            have hg := Nit_ge ha (j - 1)
            omega
          have hss := Nstep_self_eq a (Ev a j) hpos hfix
          exact Or.inr ⟨Ev a j, hss, hL.symm⟩
      · have hne : Ev a (j + 1) ≠ Ev a j := fun c => hEq (by rw [c])
        have hz0 : 0 < Ev a (j + 1) := by
          have eE : Ev a (j + 1) = Nit a j := rfl
          have hg := Nit_ge ha j
          omega
        have hge : Nat.sqrt (Nv a) ≤ Ev a (j + 1) := by
          have eE : Ev a (j + 1) = Nit a j := rfl
          have hg := Nit_ge ha j
          omega
        have hleE : Ev a (j + 1) ≤ Z0v a + 1 := by
          have eE : Ev a (j + 1) = Nit a j := rfl
          have hl := Nit_le ha j
          omega
        have hb : Nv a / Ev a (j + 1) + Ev a (j + 1) ≤ 2 ^ 167 - 1 :=
          range_ok ha hle hge hleE
        have hstep : loop (↑a : Int) (256 - (j + 1) + 1) (Ev a j : Int)
            (Ev a (j + 1) : Int)
            = loop (↑a : Int) (256 - (j + 1)) (Ev a (j + 1) : Int)
              (↑(Nstep a (Ev a (j + 1))) : Int) :=
          loop_step _ hz0 hne hb
        have hm2 : 256 - j = (256 - (j + 1)) + 1 := by omega
        rw [hm2] at hL
        have eEv : (a * 10 ^ 10 / Ev a (j + 1) + Ev a (j + 1)) / 2
            = Ev a (j + 1 + 1) :=
          Ev_step (j + 1) (by omega)
        have eN : Nstep a (Ev a (j + 1))
            = (a * 10 ^ 10 / Ev a (j + 1) + Ev a (j + 1)) / 2 := rfl
        rw [eN, eEv] at hstep
        exact Or.inl (hstep.symm.trans hL)
    | inr hR => exact Or.inr hR

/-- From `{s, s+1}` the loop stays there and keeps minimum `s`. -/
theorem loop_tail {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) :
    ∀ m y z, (y = Nat.sqrt (Nv a) ∨ y = Nat.sqrt (Nv a) + 1) →
      (z = Nat.sqrt (Nv a) ∨ z = Nat.sqrt (Nv a) + 1) →
      (y = Nat.sqrt (Nv a) ∨ z = Nat.sqrt (Nv a)) →
      ∃ y' z', loop (↑a : Int) m (↑y : Int) (↑z : Int)
          = some (((y' : Nat) : Int), (((z' : Nat) : Int)))
        ∧ (y' = Nat.sqrt (Nv a) ∨ y' = Nat.sqrt (Nv a) + 1)
        ∧ (z' = Nat.sqrt (Nv a) ∨ z' = Nat.sqrt (Nv a) + 1)
        ∧ (y' = Nat.sqrt (Nv a) ∨ z' = Nat.sqrt (Nv a)) := by
  have hs1 := s_pos ha
  have h0 := seed_ge_sqrt a
  intro m
  induction m with
  | zero =>
    intro y z hym hzm hmin
    exact ⟨y, z, rfl, hym, hzm, hmin⟩
  | succ m IH =>
    intro y z hym hzm hmin
    by_cases hEq : (↑z : Int) = (↑y : Int)
    · have hNat : z = y := Int.ofNat_inj.mp hEq
      have hstop : loop (↑a : Int) (m + 1) (↑y : Int) (↑z : Int)
          = some (((y : Nat) : Int), (((y : Nat) : Int))) := by
        rw [hEq]
        exact loop_stop _ _ _
      have hyS : y = Nat.sqrt (Nv a) := by
        cases hmin with
        | inl h => exact h
        | inr h => omega
      exact ⟨y, y, hstop, Or.inl hyS, Or.inl hyS, Or.inl hyS⟩
    · have hne : z ≠ y := fun c => hEq (by rw [c])
      have hz0 : 0 < z := by omega
      have hgez : Nat.sqrt (Nv a) ≤ z := by omega
      have hlez : z ≤ Z0v a + 1 := by omega
      have hb : Nv a / z + z ≤ 2 ^ 167 - 1 := range_ok ha hle hgez hlez
      have hstep : loop (↑a : Int) (m + 1) (↑y : Int) (↑z : Int)
          = loop (↑a : Int) m (↑z : Int) (↑(Nstep a z) : Int) :=
        loop_step _ hz0 hne hb
      cases hzm with
      | inl hz =>
        have hNzge := Nstep_ge_sqrt a z (by omega)
        have hNzle : Nstep a z ≤ Nat.sqrt (Nv a) + 1 := by
          rw [hz]
          exact Nstep_at_sqrt_le ha
        have hNzmem : Nstep a z = Nat.sqrt (Nv a)
            ∨ Nstep a z = Nat.sqrt (Nv a) + 1 := by omega
        obtain ⟨y', z', hres, hy', hz', hm'⟩ :=
          IH z (Nstep a z) (Or.inl hz) hNzmem (Or.inl hz)
        exact ⟨y', z', hstep.trans hres, hy', hz', hm'⟩
      | inr hz =>
        have hNz : Nstep a z = Nat.sqrt (Nv a) := by
          rw [hz]
          exact Nstep_at_succ a
        obtain ⟨y', z', hres, hy', hz', hm'⟩ :=
          IH z (Nstep a z) (Or.inr hz) (Or.inl hNz) (Or.inr hNz)
        exact ⟨y', z', hstep.trans hres, hy', hz', hm'⟩

/-- The loop ends with minimum exactly the root. -/
theorem loop_result {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) :
    ∃ Y Z : Nat, loop (↑a : Int) 256 (↑a : Int) (↑(Z0v a) : Int)
        = some (((Y : Nat) : Int), (((Z : Nat) : Int)))
      ∧ min Y Z = Nat.sqrt (Nv a) := by
  obtain ⟨J, hJle, hJmem⟩ := Nit_reach ha hle
  have hs1 := s_pos ha
  have hgeJ := Nit_ge ha J
  have eEJ : Ev a (J + 1) = Nit a J := rfl
  have hmem1 : Ev a (J + 1) = Nat.sqrt (Nv a)
      ∨ Ev a (J + 1) = Nat.sqrt (Nv a) + 1 := by omega
  have eEJ2 : Ev a (J + 1 + 1) = Nstep a (Ev a (J + 1)) :=
    Ev_step (J + 1) (by omega)
  cases loop_corr ha hle J hJle (J + 1) (Nat.le_refl _) with
  | inl hL =>
    have hNzge := Nstep_ge_sqrt a (Ev a (J + 1)) (by omega)
    cases hmem1 with
    | inl hy =>
      have hNzle : Nstep a (Ev a (J + 1)) ≤ Nat.sqrt (Nv a) + 1 := by
        rw [hy]
        exact Nstep_at_sqrt_le ha
      have hNzmem : Nstep a (Ev a (J + 1)) = Nat.sqrt (Nv a)
          ∨ Nstep a (Ev a (J + 1)) = Nat.sqrt (Nv a) + 1 := by omega
      obtain ⟨Y, Z, hres, hy', hz', hm'⟩ :=
        loop_tail ha hle (256 - (J + 1)) (Ev a (J + 1))
          (Nstep a (Ev a (J + 1))) (Or.inl hy) hNzmem (Or.inl hy)
      rw [eEJ2] at hL
      have hfin : loop (↑a : Int) 256 (↑a : Int) (↑(Z0v a) : Int)
          = some ((Y : Int), (Z : Int)) := hL.symm.trans hres
      have hmin : min Y Z = Nat.sqrt (Nv a) := by
        cases hm' with
        | inl hY =>
          rw [hY]
          exact Nat.min_eq_left (by omega)
        | inr hZ =>
          rw [hZ]
          exact Nat.min_eq_right (by omega)
      exact ⟨Y, Z, hfin, hmin⟩
    | inr hy =>
      have hNz : Nstep a (Ev a (J + 1)) = Nat.sqrt (Nv a) := by
        rw [hy]
        exact Nstep_at_succ a
      obtain ⟨Y, Z, hres, hy', hz', hm'⟩ :=
        loop_tail ha hle (256 - (J + 1)) (Ev a (J + 1))
          (Nstep a (Ev a (J + 1))) (Or.inr hy) (Or.inl hNz) (Or.inr hNz)
      rw [eEJ2] at hL
      have hfin : loop (↑a : Int) 256 (↑a : Int) (↑(Z0v a) : Int)
          = some ((Y : Int), (Z : Int)) := hL.symm.trans hres
      have hmin : min Y Z = Nat.sqrt (Nv a) := by
        cases hm' with
        | inl hY =>
          rw [hY]
          exact Nat.min_eq_left (by omega)
        | inr hZ =>
          rw [hZ]
          exact Nat.min_eq_right (by omega)
      exact ⟨Y, Z, hfin, hmin⟩
  | inr hR =>
    obtain ⟨w, hw, hres⟩ := hR
    have hmin : min w w = Nat.sqrt (Nv a) := by
      rw [Nat.min_eq_left (Nat.le_refl _)]
      exact hw
    exact ⟨w, w, hres, hmin⟩

/-- The final choice is the cast of the `Nat` minimum. -/
theorem fin_min {e1 e2 s : Nat} (h : min e1 e2 = s) :
    (fun y z => if y < z then y else z) ((e1 : Nat) : Int) ((e2 : Nat) : Int)
      = ((s : Nat) : Int) := by
  by_cases hlt : e1 < e2
  · have hm : min e1 e2 = e1 := Nat.min_eq_left (Nat.le_of_lt hlt)
    have hc : ((e1 : Nat) : Int) < ((e2 : Nat) : Int) := Int.ofNat_lt.mpr hlt
    have heq : e1 = s := hm.symm.trans h
    show (if ((e1 : Nat) : Int) < ((e2 : Nat) : Int) then ((e1 : Nat) : Int)
      else ((e2 : Nat) : Int)) = ((s : Nat) : Int)
    rw [if_pos hc, heq]
  · have hle : e2 ≤ e1 := by omega
    have hm : min e1 e2 = e2 := Nat.min_eq_right hle
    have hc : ¬ ((e1 : Nat) : Int) < ((e2 : Nat) : Int) :=
      fun hh => hlt (Int.ofNat_lt.mp hh)
    have heq : e2 = s := hm.symm.trans h
    show (if ((e1 : Nat) : Int) < ((e2 : Nat) : Int) then ((e1 : Nat) : Int)
      else ((e2 : Nat) : Int)) = ((s : Nat) : Int)
    rw [if_neg hc, heq]

/-- The routine returns the cast of the integer root. -/
theorem sqrt_eq_sqrt {a : Nat} (ha : 1 ≤ a) (hle : a ≤ 2 ^ 167 - 1) :
    sqrt (↑a : Int) = some (↑(Nat.sqrt (Nv a)) : Int) := by
  have ha0 : 0 < a := by omega
  have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) ha0 hle
  obtain ⟨Y, Z, hloop, hmin⟩ := loop_result ha hle
  have eZ : ((Z0v a : Nat) : Int) = ((((a / 2 + 5 * 10 ^ 9 : Nat))) : Int) :=
    rfl
  unfold sqrt
  rw [hpos, ← eZ, hloop]
  exact congrArg some (fin_min hmin)

theorem req_sqrt_total : SqrtTotal sqrt := by
  intro x hx h0x
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : sqrt (0 : Int) = some 0 := by
      show vyperSqrtWith _ 0 = _
      unfold vyperSqrtWith
      simp
    rw [h0]
    rfl
  · obtain ⟨a, rfl⟩ : ∃ a : Nat, x = ↑a := ⟨x.toNat, (Int.toNat_of_nonneg h0x).symm⟩
    have ha : 1 ≤ a := by
      by_cases h : a = 0
      · rw [h] at hx0
        simp at hx0
      · omega
    have hle : a ≤ 2 ^ 167 - 1 := by
      have h2 : (↑a : Int) ≤ MAX_DECIMAL := hx.2
      rw [max_decimal_eq] at h2
      exact Int.ofNat_le.mp h2
    have hsqrt := sqrt_eq_sqrt ha hle
    rw [hsqrt]
    rfl

theorem req_sqrt_not_above : SqrtNotAbove sqrt := by
  intro x r hx hr
  by_cases hneg : x < 0
  · have hn := req_sqrt_neg_reverts x hneg
    rw [hn] at hr
    cases hr
  · have h0x : 0 ≤ x := by omega
    by_cases hx0 : x = 0
    · subst hx0
      have h0 : sqrt (0 : Int) = some 0 := by
        show vyperSqrtWith _ 0 = _
        unfold vyperSqrtWith
        simp
      rw [h0] at hr
      cases hr
      simp
    · obtain ⟨a, rfl⟩ : ∃ a : Nat, x = ↑a := ⟨x.toNat, (Int.toNat_of_nonneg h0x).symm⟩
      have ha : 1 ≤ a := by
        by_cases h : a = 0
        · rw [h] at hx0
          simp at hx0
        · omega
      have hle : a ≤ 2 ^ 167 - 1 := by
        have h2 : (↑a : Int) ≤ MAX_DECIMAL := hx.2
        rw [max_decimal_eq] at h2
        exact Int.ofNat_le.mp h2
      have hsqrt := sqrt_eq_sqrt ha hle
      rw [hsqrt] at hr
      cases hr
      have hss := Nat.sqrt_le (Nv a)
      have h1 : (((Nat.sqrt (Nv a) * Nat.sqrt (Nv a) : Nat)) : Int)
          ≤ ((((a * 10 ^ 10 : Nat))) : Int) := by
        have h2 : Nv a = a * 10 ^ 10 := rfl
        rw [h2] at hss
        exact Int.ofNat_le.mpr hss
      rw [Int.natCast_mul, Int.natCast_mul] at h1
      rw [divisor_eq]
      exact h1

theorem req_sqrt_not_below : SqrtNotBelow sqrt := by
  intro x r hx hr
  by_cases hneg : x < 0
  · have hn := req_sqrt_neg_reverts x hneg
    rw [hn] at hr
    cases hr
  · have h0x : 0 ≤ x := by omega
    by_cases hx0 : x = 0
    · subst hx0
      have h0 : sqrt (0 : Int) = some 0 := by
        show vyperSqrtWith _ 0 = _
        unfold vyperSqrtWith
        simp
      rw [h0] at hr
      cases hr
      simp
    · obtain ⟨a, rfl⟩ : ∃ a : Nat, x = ↑a := ⟨x.toNat, (Int.toNat_of_nonneg h0x).symm⟩
      have ha : 1 ≤ a := by
        by_cases h : a = 0
        · rw [h] at hx0
          simp at hx0
        · omega
      have hle : a ≤ 2 ^ 167 - 1 := by
        have h2 : (↑a : Int) ≤ MAX_DECIMAL := hx.2
        rw [max_decimal_eq] at h2
        exact Int.ofNat_le.mp h2
      have hsqrt := sqrt_eq_sqrt ha hle
      rw [hsqrt] at hr
      cases hr
      have hlt := Nat.lt_succ_sqrt (Nv a)
      rw [Nat.succ_eq_add_one] at hlt
      have h1 : ((((a * 10 ^ 10 : Nat))) : Int)
          < ((((Nat.sqrt (Nv a) + 1) * (Nat.sqrt (Nv a) + 1) : Nat)) : Int) := by
        have h2 : Nv a = a * 10 ^ 10 := rfl
        rw [← h2]
        exact Int.ofNat_lt.mpr hlt
      rw [Int.natCast_mul, Int.natCast_mul] at h1
      have e : (((Nat.sqrt (Nv a) + 1 : Nat)) : Int)
          = ((Nat.sqrt (Nv a) : Nat) : Int) + 1 := by simp
      rw [e] at h1
      rw [divisor_eq]
      exact h1

end VyperSqrt
