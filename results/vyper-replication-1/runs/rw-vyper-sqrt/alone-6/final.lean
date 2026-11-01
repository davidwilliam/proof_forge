import VyperSqrt.Spec
import VyperSqrt.Lemmas
/-!
Fixed `sqrt`: port of the Vyper compiler code with PR 4486 applied, i.e. the
deployed Babylonian loop followed by `if y < z: z = y` (return the minimum of
the last two iterates), so the result is the root rounded down.
-/
namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-! Nat-level mirror of the loop. -/

def nloop (N : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, z => (y, z)
  | n + 1, y, z =>
      if z = y then (y, z) else nloop N n z ((N / z + z) / 2)

def nseq (N z0 : Nat) : Nat → Nat
  | 0 => z0
  | n + 1 => (N / nseq N z0 n + nseq N z0 n) / 2

theorem nloop_zero (N y z : Nat) : nloop N 0 y z = (y, z) := rfl

theorem nloop_succ (N n y z : Nat) :
    nloop N (n + 1) y z =
      if z = y then (y, z) else nloop N n z ((N / z + z) / 2) := rfl

theorem nseq_zero (N z0 : Nat) : nseq N z0 0 = z0 := rfl

theorem nseq_succ (N z0 n : Nat) :
    nseq N z0 (n + 1) = (N / nseq N z0 n + nseq N z0 n) / 2 := rfl

/-! Small arithmetic helpers. -/

/-- `(s-e) * (s+e) ≤ s * s`: difference of squares, no ring needed. -/
theorem sq_sub_mul_le {s e : Nat} (he : e ≤ s) : (s - e) * (s + e) ≤ s * s := by
  have h1 : (s - e) + e = s := Nat.sub_add_cancel he
  have e1 : ((s - e) + e) * (s + e) = (s - e) * (s + e) + e * (s + e) :=
    Nat.add_mul _ _ _
  rw [h1] at e1
  have e2 : s * (s + e) = s * s + s * e := Nat.mul_add _ _ _
  have e3 : e * (s + e) = e * s + e * e := Nat.mul_add _ _ _
  have e4 : s * e = e * s := Nat.mul_comm _ _
  omega

/-- Uniqueness of the integer square root. -/
theorem sqrt_unique {N s z : Nat} (hN1 : s * s ≤ N) (hN2 : N < (s + 1) * (s + 1))
    (u1 : z * z ≤ N) (u2 : N < (z + 1) * (z + 1)) : z = s := by
  have h1 : z ≤ s := by
    by_cases hc : z ≤ s
    · exact hc
    · have hc' : s + 1 ≤ z := by omega
      have h3 : (s + 1) * (s + 1) ≤ z * z := Nat.mul_le_mul hc' hc'
      omega
  have h2 : s ≤ z := by
    by_cases hc : s ≤ z
    · exact hc
    · have hc' : z + 1 ≤ s := by omega
      have h3 : (z + 1) * (z + 1) ≤ s * s := Nat.mul_le_mul hc' hc'
      omega
  omega

/-- Newton step stays above the root: `s ≤ z → s ≤ (N/z+z)/2`. -/
theorem newton_ge {N s z : Nat} (hs1 : 1 ≤ s) (hN1 : s * s ≤ N)
    (hz : s ≤ z) : s ≤ (N / z + z) / 2 := by
  have hzpos : 0 < z := by omega
  suffices h : 2 * s ≤ N / z + z by omega
  by_cases h2 : 2 * s ≤ z
  · exact Nat.le_trans h2 (Nat.le_add_left _ _)
  · have he : z - s ≤ s := by omega
    have hsq := sq_sub_mul_le he
    have r1 : s - (z - s) = 2 * s - z := by omega
    have r2 : s + (z - s) = z := by omega
    rw [r1, r2] at hsq
    have h3 : (2 * s - z) * z ≤ N := Nat.le_trans hsq hN1
    have h4 : 2 * s - z ≤ N / z := (Nat.le_div_iff_mul_le hzpos).mpr h3
    have h5 : 2 * s - z + z = 2 * s := by omega
    omega

/-- Above the root the step at most halves the gap: `z ≥ s+1 → f(z) ≤ s+(z-s)/2`. -/
theorem newton_half {N s z : Nat} (hN2 : N < (s + 1) * (s + 1)) (hz : s + 1 ≤ z) :
    (N / z + z) / 2 ≤ s + (z - s) / 2 := by
  have hzpos : 0 < z := by omega
  have hq : N / z ≤ s := by
    by_cases hc : N / z ≤ s
    · exact hc
    · have hc' : s + 1 ≤ N / z := by omega
      have h3 : (s + 1) * z ≤ N := (Nat.le_div_iff_mul_le hzpos).mp hc'
      have h4 : (s + 1) * (s + 1) ≤ (s + 1) * z := Nat.mul_le_mul_left _ hz
      omega
  have heq : (s + z) / 2 = s + (z - s) / 2 := by omega
  calc (N / z + z) / 2 ≤ (s + z) / 2 := Nat.div_le_div_right (by omega)
    _ = s + (z - s) / 2 := heq

/-- The step maps the root into `{s, s+1}`. -/
theorem newton_at_low {N s : Nat} (hs1 : 1 ≤ s) (hN1 : s * s ≤ N)
    (hN2 : N < (s + 1) * (s + 1)) :
    s ≤ (N / s + s) / 2 ∧ (N / s + s) / 2 ≤ s + 1 := by
  have hspos : 0 < s := hs1
  have h1 : s ≤ N / s := (Nat.le_div_iff_mul_le hspos).mpr hN1
  have h2 : N / s ≤ s + 2 := by
    by_cases hc : N / s ≤ s + 2
    · exact hc
    · have hc' : s + 3 ≤ N / s := by omega
      have h3 : (s + 3) * s ≤ N := (Nat.le_div_iff_mul_le hspos).mp hc'
      have e1 : (s + 1) * (s + 1) = s * s + (s + (s + 1)) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      have e2 : (s + 3) * s = s * s + (s + (s + s)) := by
        simp only [Nat.add_mul]
        omega
      omega
  have g1 : (s + s) / 2 ≤ (N / s + s) / 2 := Nat.div_le_div_right (by omega)
  have e1 : (s + s) / 2 = s := by omega
  have g2 : (N / s + s) / 2 ≤ (s + 2 + s) / 2 := Nat.div_le_div_right (by omega)
  have e2 : (s + 2 + s) / 2 = s + 1 := by omega
  exact ⟨by omega, by omega⟩

/-- The step maps `s+1` exactly to `s`. -/
theorem newton_at_high {N s : Nat} (hs1 : 1 ≤ s) (hN1 : s * s ≤ N)
    (hN2 : N < (s + 1) * (s + 1)) : (N / (s + 1) + (s + 1)) / 2 = s := by
  have hspos : 0 < s + 1 := by omega
  have h1 : N / (s + 1) ≤ s := by
    have hlt : N / (s + 1) < s + 1 := (Nat.div_lt_iff_lt_mul hspos).mpr hN2
    omega
  have h2 : s - 1 ≤ N / (s + 1) := by
    have hsq := sq_sub_mul_le (show 1 ≤ s by omega : 1 ≤ s)
    have h3 : (s - 1) * (s + 1) ≤ N := Nat.le_trans hsq hN1
    exact (Nat.le_div_iff_mul_le hspos).mpr h3
  omega

/-- Fixed points of the Newton step equal the root. -/
theorem newton_fixed {N s z : Nat} (hs1 : 1 ≤ s) (hN1 : s * s ≤ N)
    (hN2 : N < (s + 1) * (s + 1)) (hz1 : 1 ≤ z) (hf : (N / z + z) / 2 = z) :
    z = s := by
  have hzpos : 0 < z := hz1
  have hdm := Nat.div_add_mod (N / z + z) 2
  have hmod : (N / z + z) % 2 ≤ 1 := by
    have := Nat.mod_lt (N / z + z) (by decide : 0 < 2)
    omega
  rw [hf] at hdm
  have hc : N / z = z ∨ N / z = z + 1 := by omega
  have huniq : ∀ {w : Nat}, w * w ≤ N → N < (w + 1) * (w + 1) → w = s :=
    fun u1 u2 => sqrt_unique hN1 hN2 u1 u2
  rcases hc with h | h
  · have hzle : z ≤ N / z := by omega
    have u1 : z * z ≤ N := (Nat.le_div_iff_mul_le hzpos).mp hzle
    have hlt : N / z < z + 1 := by omega
    have u2 : N < (z + 1) * z := (Nat.div_lt_iff_lt_mul hzpos).mp hlt
    have hle : (z + 1) * z ≤ (z + 1) * (z + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have u2' : N < (z + 1) * (z + 1) := by omega
    exact huniq u1 u2'
  · have hzle : z + 1 ≤ N / z := by omega
    have u1 : (z + 1) * z ≤ N := (Nat.le_div_iff_mul_le hzpos).mp hzle
    have e1 : (z + 1) * z = z * z + z := by
      simp only [Nat.add_mul, Nat.one_mul]
    have u1' : z * z ≤ N := by omega
    have hlt : N / z < z + 2 := by omega
    have u2 : N < (z + 2) * z := (Nat.div_lt_iff_lt_mul hzpos).mp hlt
    have e2 : (z + 2) * z = z * z + (z + z) := by
      simp only [Nat.add_mul]
      omega
    have e3 : (z + 1) * (z + 1) = z * z + (z + (z + 1)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    have u2' : N < (z + 1) * (z + 1) := by omega
    exact huniq u1' u2'

/-- The quotient stays small above the root. -/
theorem ndiv_le {N s z : Nat} (hs1 : 1 ≤ s) (hN2 : N < (s + 1) * (s + 1))
    (hz : s ≤ z) : N / z ≤ s + 2 := by
  by_cases hc : N / z ≤ s + 2
  · exact hc
  · have hc' : s + 3 ≤ N / z := by omega
    have hzpos : 0 < z := by omega
    have h3 : (s + 3) * z ≤ N := (Nat.le_div_iff_mul_le hzpos).mp hc'
    by_cases heq : z = s
    · subst z
      have e2 : (s + 3) * s = s * s + (s + (s + s)) := by
        simp only [Nat.add_mul]
        omega
      have e1 : (s + 1) * (s + 1) = s * s + (s + (s + 1)) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      omega
    · have hz' : s + 1 ≤ z := by omega
      have h5 : (s + 1) * (s + 1) ≤ (s + 1) * z := Nat.mul_le_mul_left _ hz'
      have e1 : (s + 1) * (s + 1) = s * s + (s + (s + 1)) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      have h6 : (s + 1) * (s + 1) ≤ (s + 3) * z := by
        have h7 : (s + 1) * z ≤ (s + 3) * z :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      omega

/-- AM-GM: `2*c*q ≤ q*q + c*c`, no ring needed. -/
theorem amgm {q c : Nat} : c * q + c * q ≤ q * q + c * c := by
  by_cases h : q ≤ c
  · have e2 : q + (c - q) = c := by omega
    have c1 : (c - q) * q = q * (c - q) := Nat.mul_comm _ _
    rw [← e2]
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  · have e2 : c + (q - c) = q := by omega
    have c1 : (q - c) * c = c * (q - c) := Nat.mul_comm _ _
    rw [← e2]
    simp only [Nat.add_mul, Nat.mul_add]
    omega

/-- Seed square bound, with the input split as `a = 2*q + r`. -/
theorem seed_sq_aux (q r : Nat) (hr : r ≤ 1) :
    (2 * q + r) * 10 ^ 10
      < (q + 5 * 10 ^ 9 + 1) * (q + 5 * 10 ^ 9 + 1) := by
  have ham := amgm (q := q) (c := 4999999999)
  have e : (q + 5 * 10 ^ 9 + 1) * (q + 5 * 10 ^ 9 + 1)
      = q * q
        + (q * (5 * 10 ^ 9 + 1) + (q * (5 * 10 ^ 9 + 1)
          + (5 * 10 ^ 9 + 1) * (5 * 10 ^ 9 + 1))) := by
    have c : (5 * 10 ^ 9 + 1) * q = q * (5 * 10 ^ 9 + 1) := Nat.mul_comm _ _
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  rw [e]
  omega

/-- The seed squared exceeds the input: `(a/2+5·10^9+1)² > a·10^10`. -/
theorem seed_sq (a : Nat) :
    a * 10 ^ 10 < (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1) := by
  have hdm := Nat.div_add_mod a 2
  have hr : a % 2 ≤ 1 := by
    have := Nat.mod_lt a (by decide : 0 < 2)
    omega
  have key := seed_sq_aux (a / 2) (a % 2) hr
  have eq : a * 10 ^ 10 = (2 * (a / 2) + a % 2) * 10 ^ 10 := by rw [hdm]
  rw [eq]
  exact key

/-- The seed is above the root. -/
theorem seed_ge {a : Nat} (ha : 0 < a) :
    Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9 := by
  by_cases hc : Nat.sqrt (a * 10 ^ 10) ≤ a / 2 + 5 * 10 ^ 9
  · exact hc
  · have hc' : a / 2 + 5 * 10 ^ 9 + 1 ≤ Nat.sqrt (a * 10 ^ 10) := by omega
    have h1 : (a / 2 + 5 * 10 ^ 9 + 1) * (a / 2 + 5 * 10 ^ 9 + 1)
        ≤ Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) :=
      Nat.mul_le_mul hc' hc'
    have h2 := Nat.sqrt_le (a * 10 ^ 10)
    have h3 := seed_sq a
    omega

/-- The root is positive for positive input. -/
theorem s_pos {a : Nat} (ha : 0 < a) : 1 ≤ Nat.sqrt (a * 10 ^ 10) := by
  by_cases hc : 1 ≤ Nat.sqrt (a * 10 ^ 10)
  · exact hc
  · have hz : Nat.sqrt (a * 10 ^ 10) = 0 := by omega
    have hlt := Nat.lt_succ_sqrt (a * 10 ^ 10)
    have e0 : (Nat.sqrt (a * 10 ^ 10)).succ * (Nat.sqrt (a * 10 ^ 10)).succ
        = 1 * 1 := by rw [hz]
    rw [e0] at hlt
    have e1 : (1 : Nat) * 1 = 1 := Nat.mul_one 1
    rw [e1] at hlt
    have hbig : (10 ^ 10 : Nat) ≤ a * 10 ^ 10 := by
      have hmul := Nat.mul_le_mul_right (10 ^ 10) ha
      rw [Nat.one_mul] at hmul
      exact hmul
    omega

/-- The root is small: below `2^101`. -/
theorem s_small {a : Nat} (hle : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ 101 := by
  by_cases hc : Nat.sqrt (a * 10 ^ 10) ≤ 2 ^ 101
  · exact hc
  · have hc' : 2 ^ 101 ≤ Nat.sqrt (a * 10 ^ 10) := by omega
    have h1 : (2 ^ 101) * (2 ^ 101)
        ≤ Nat.sqrt (a * 10 ^ 10) * Nat.sqrt (a * 10 ^ 10) :=
      Nat.mul_le_mul hc' hc'
    have h2 := Nat.sqrt_le (a * 10 ^ 10)
    have h3 : a * 10 ^ 10 ≤ (2 ^ 167 - 1) * 10 ^ 10 :=
      Nat.mul_le_mul_right _ hle
    have d1 : (2 ^ 101) * (2 ^ 101) = 2 ^ 202 := by decide
    have d2 : (2 ^ 167 - 1) * 10 ^ 10 < 2 ^ 202 := by decide
    omega

/-- Seed plus one stays in range. -/
theorem z0_le {a : Nat} (hle : a ≤ 2 ^ 167 - 1) :
    a / 2 + 5 * 10 ^ 9 + 1 ≤ 2 ^ 167 - 1 := by
  have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hle
  have d : (2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 1 ≤ 2 ^ 167 - 1 := by decide
  omega

/-- The loop body stays in decimal range on `[s, z₀+1]`. -/
theorem range_bound {a s z : Nat} (hs1 : 1 ≤ s) (hN2 : a * 10 ^ 10 < (s + 1) * (s + 1))
    (hle : a ≤ 2 ^ 167 - 1) (hss : s ≤ 2 ^ 101)
    (hz : s ≤ z) (hzZ : z ≤ a / 2 + 5 * 10 ^ 9 + 1) :
    a * 10 ^ 10 / z + z ≤ 2 ^ 167 - 1 := by
  have hq : a * 10 ^ 10 / z ≤ s + 2 := by
    have := ndiv_le hs1 hN2 hz
    omega
  have hdiv : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right hle
  have d : 2 ^ 101 + 2 + ((2 ^ 167 - 1) / 2 + 5 * 10 ^ 9 + 1) ≤ 2 ^ 167 - 1 := by
    decide
  omega

/-- The strict decrease step: above the root the step goes down. -/
theorem newton_lt {N s z : Nat} (hN2 : N < (s + 1) * (s + 1)) (hz : s + 1 ≤ z) :
    (N / z + z) / 2 < z := by
  have hzpos : 0 < z := by omega
  have hq : N / z ≤ s := by
    by_cases hc : N / z ≤ s
    · exact hc
    · have hc' : s + 1 ≤ N / z := by omega
      have h3 : (s + 1) * z ≤ N := (Nat.le_div_iff_mul_le hzpos).mp hc'
      have h4 : (s + 1) * (s + 1) ≤ (s + 1) * z := Nat.mul_le_mul_left _ hz
      omega
  have hle : (N / z + z) / 2 ≤ (s + z) / 2 := Nat.div_le_div_right (by omega)
  omega

/-- The `sqrt < (s+1)²` bound in `+1` form. -/
theorem sqrt_lt_succ' {a : Nat} :
    a * 10 ^ 10 < (Nat.sqrt (a * 10 ^ 10) + 1) * (Nat.sqrt (a * 10 ^ 10) + 1) := by
  have h := Nat.lt_succ_sqrt (a * 10 ^ 10)
  simp only [Nat.succ_eq_add_one] at h
  exact h

/-- Gap halving step: above the root the gap at least halves. -/
theorem gap_half_le {a z : Nat} (ha : 0 < a)
    (hz : Nat.sqrt (a * 10 ^ 10) + 1 ≤ z) :
    (a * 10 ^ 10 / z + z) / 2 - Nat.sqrt (a * 10 ^ 10)
      ≤ (z - Nat.sqrt (a * 10 ^ 10)) / 2 := by
  have hN2 := sqrt_lt_succ' (a := a)
  have hle1 := newton_half (N := a * 10 ^ 10) (s := Nat.sqrt (a * 10 ^ 10)) (z := z) hN2 hz
  have hsub : Nat.sqrt (a * 10 ^ 10) + (z - Nat.sqrt (a * 10 ^ 10)) / 2
      - Nat.sqrt (a * 10 ^ 10) = (z - Nat.sqrt (a * 10 ^ 10)) / 2 := by omega
  calc (a * 10 ^ 10 / z + z) / 2 - Nat.sqrt (a * 10 ^ 10)
      ≤ (Nat.sqrt (a * 10 ^ 10) + (z - Nat.sqrt (a * 10 ^ 10)) / 2)
        - Nat.sqrt (a * 10 ^ 10) := Nat.sub_le_sub_right hle1 _
    _ = (z - Nat.sqrt (a * 10 ^ 10)) / 2 := hsub

/-- All iterates stay in `[s, z₀+1]`. -/
theorem nseq_mem {a : Nat} (ha : 0 < a) (hle : a ≤ 2 ^ 167 - 1) (k : Nat) :
    Nat.sqrt (a * 10 ^ 10) ≤ nseq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k
    ∧ nseq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k ≤ a / 2 + 5 * 10 ^ 9 + 1 := by
  induction k with
  | zero =>
    rw [nseq_zero]
    exact ⟨seed_ge ha, by omega⟩
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have hs1 := s_pos ha
    have hN1 := Nat.sqrt_le (a * 10 ^ 10)
    have hN2 := sqrt_lt_succ' (a := a)
    have hge := newton_ge (N := a * 10 ^ 10) (s := Nat.sqrt (a * 10 ^ 10)) hs1 hN1 hlo
    rw [nseq_succ]
    constructor
    · exact hge
    · by_cases hcas : Nat.sqrt (a * 10 ^ 10) + 1
          ≤ nseq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k
      · have hlt := newton_lt (N := a * 10 ^ 10)
          (s := Nat.sqrt (a * 10 ^ 10)) hN2 hcas
        omega
      · have hss : nseq (a * 10 ^ 10) (a / 2 + 5 * 10 ^ 9) k
            = Nat.sqrt (a * 10 ^ 10) := by omega
        have hle1 := (newton_at_low (N := a * 10 ^ 10)
          (s := Nat.sqrt (a * 10 ^ 10)) hs1 hN1 hN2).2
        have hseed := seed_ge ha
        rw [hss]
        omega
