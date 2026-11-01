import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

/-! ## Elementary algebra (no Mathlib) -/

/-- Square expansion. -/
theorem add_sq (x y : Nat) :
    (x + y) * (x + y) = x * x + (x * y + (x * y + y * y)) := by
  have r1 : (x + y) * (x + y) = x * (x + y) + y * (x + y) := Nat.add_mul _ _ _
  have r2 : x * (x + y) = x * x + x * y := Nat.mul_add _ _ _
  have r3 : y * (x + y) = x * y + y * y := by
    rw [Nat.mul_add, Nat.mul_comm y x]
  omega

/-- `(x - y)^2 >= 0`, i.e. `2xy <= x^2 + y^2`, via the substitution for `x <= y`. -/
theorem two_mul_le_add_sq_aux (x d : Nat) :
    2 * (x * (x + d)) ≤ x * x + (x + d) * (x + d) := by
  have e1 := add_sq x d
  have e0 : 2 * (x * (x + d)) = (x * x + x * x) + (x * d + x * d) := by
    have r : x * (x + d) = x * x + x * d := Nat.mul_add _ _ _
    rw [r, Nat.mul_add]
    omega
  omega

/-- `(x - y)^2 >= 0`. -/
theorem two_mul_le_add_sq (a b : Nat) : 2 * (a * b) ≤ a * a + b * b := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact two_mul_le_add_sq_aux a d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : 2 * ((b + d) * b) = 2 * (b * (b + d)) := by ac_rfl
    have e2 : (b + d) * (b + d) + b * b = b * b + (b + d) * (b + d) := by ac_rfl
    rw [e, e2]
    exact two_mul_le_add_sq_aux b d

/-- `g * (2w - g) <= w * w` when `g <= 2w`. -/
theorem newton_step_sq (g w : Nat) (h : g ≤ 2 * w) : g * (2 * w - g) ≤ w * w := by
  obtain ⟨d, h2w⟩ := Nat.exists_eq_add_of_le h
  have hsub : 2 * w - g = d := by omega
  rw [hsub]
  have hgd : g + d = 2 * w := by omega
  have key : 2 * (g * d) ≤ g * g + d * d := two_mul_le_add_sq g d
  have exp : (g + d) * (g + d) = (g * g + d * d) + 2 * (g * d) := by
    have r1 : (g + d) * (g + d) = g * (g + d) + d * (g + d) := Nat.add_mul _ _ _
    have r2 : g * (g + d) = g * g + g * d := Nat.mul_add _ _ _
    have r3 : d * (g + d) = g * d + d * d := by
      rw [Nat.mul_add, Nat.mul_comm d g]
    have t : 2 * (g * d) = g * d + g * d := by omega
    omega
  have e4 : (2 * w) * (2 * w) = (w * w + w * w) + (w * w + w * w) := by
    have h2w2 : (2 : Nat) * w = w + w := by omega
    rw [h2w2, Nat.add_mul, Nat.mul_add]
  rw [hgd] at exp
  omega

/-! ## The `Nat.sqrt` upper bound -/

/-- The iterates of `Nat.sqrt.iter` never exceed the starting guess. -/
theorem iter_le (n : Nat) : ∀ g, Nat.sqrt.iter n g ≤ g := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
    rw [Nat.sqrt.iter.eq_def]
    simp only []
    split
    · next h => exact Nat.le_trans (ih _ h) (Nat.le_of_lt h)
    · exact Nat.le_refl _

/-- One Newton step from `g >= w` stays above `w` when `w * w <= n`. -/
theorem sqrt_newton_ge {n g w q : Nat} (hg : 0 < g) (hw : w ≤ g) (hsq : w * w ≤ n)
    (hq : n / g = q) : w ≤ (g + q) / 2 := by
  apply Classical.byContradiction
  intro hcon
  have hlt : (g + q) / 2 < w := Nat.lt_of_not_ge hcon
  have hle : g + q ≤ 2 * w - 1 := by omega
  have hg2 : g ≤ 2 * w := by omega
  have hmod : n % g < g := Nat.mod_lt _ hg
  have hdecomp : g * q + n % g = n := by
    rw [← hq]
    exact Nat.div_add_mod _ _
  have hmul : g * (q + 1) = g * q + g := by
    rw [show q + 1 = q.succ from rfl, Nat.mul_succ]
  have hN : n < g * (q + 1) := by omega
  have hq2 : q + 1 ≤ 2 * w - g := by omega
  have hstep : g * (q + 1) ≤ g * (2 * w - g) := Nat.mul_le_mul_left _ hq2
  have hsq2 : g * (2 * w - g) ≤ w * w := newton_step_sq g w hg2
  omega

/-- Every `w` with `w * w <= n` is below the value computed by `Nat.sqrt.iter`. -/
theorem sqrt_claim (n : Nat) : ∀ g, 0 < g → ∀ w, w ≤ g → w * w ≤ n →
    w ≤ Nat.sqrt.iter n g := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
    intro hg w hw hsq
    by_cases hn0 : n = 0
    · subst hn0
      have hw0 : w = 0 := by
        have hle : w * w ≤ 0 := hsq
        rw [Nat.le_zero] at hle
        rcases Nat.eq_zero_or_pos w with h | h
        · exact h
        · have : 0 < w * w := by
            have h1 : 1 ≤ w := h
            have h2 : 1 * 1 ≤ w * w := Nat.mul_le_mul h1 h1
            omega
          omega
      subst hw0
      exact Nat.zero_le _
    · have hnext : ∀ q, n / g = q → 0 < (g + q) / 2 := by
        intro q hq
        rcases Nat.lt_or_ge g 2 with hg1 | hg2
        · have hg1' : g = 1 := by omega
          subst hg1'
          rw [Nat.div_one] at hq
          have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
          omega
        · omega
      have hnext' : 0 < (g + n / g) / 2 := hnext _ rfl
      rw [Nat.sqrt.iter.eq_def]
      simp only []
      split
      · next h =>
        have hle : w ≤ (g + n / g) / 2 := sqrt_newton_ge hg hw hsq rfl
        exact (ih _ h) hnext' w hle hsq
      · exact hw

/-- `n < 2 ^ (log2 n + 1)` for nonzero `n`. -/
theorem keylog (n : Nat) (hn : n ≠ 0) : n < 2 ^ (Nat.log2 n + 1) := by
  have h1 : Nat.log2 n < Nat.log2 n + 1 := Nat.lt_succ_self _
  exact (Nat.log2_lt hn).mp h1

/-- The initial guess of `Nat.sqrt` is above the root. -/
theorem init_above (n : Nat) :
    n ≤ (1 <<< (Nat.log2 n / 2 + 1)) * (1 <<< (Nat.log2 n / 2 + 1)) := by
  rcases Nat.lt_or_ge n 1 with hn | hn
  · have hn0 : n = 0 := by omega
    subst hn0
    decide
  · have hn0 : n ≠ 0 := by omega
    have hlog := keylog n hn0
    have hG : (1 : Nat) <<< (Nat.log2 n / 2 + 1) = 2 ^ (Nat.log2 n / 2 + 1) :=
      Nat.one_shiftLeft _
    have hexp : Nat.log2 n + 1 ≤ 2 * (Nat.log2 n / 2 + 1) := by
      have hmod : Nat.log2 n % 2 < 2 := Nat.mod_lt _ (by decide)
      have hdm := Nat.div_add_mod (Nat.log2 n) 2
      omega
    have hpow : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ (2 * (Nat.log2 n / 2 + 1)) :=
      Nat.pow_le_pow_right (by decide) hexp
    have hee : (Nat.log2 n / 2 + 1) + (Nat.log2 n / 2 + 1)
        = 2 * (Nat.log2 n / 2 + 1) := by omega
    have hsq : (2 ^ (Nat.log2 n / 2 + 1)) * (2 ^ (Nat.log2 n / 2 + 1))
        = 2 ^ (2 * (Nat.log2 n / 2 + 1)) := by
      rw [← Nat.pow_add, hee]
    rw [hG]
    omega

/-- The core of the `Nat.sqrt` upper bound, for an arbitrary guess `G` above the root. -/
theorem sqrt_upper_at_guess (n G : Nat) (hGpos : 0 < G) (hab : n ≤ G * G)
    (hsqrt : Nat.sqrt n = Nat.sqrt.iter n G) :
    n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  apply Classical.byContradiction
  intro hcon
  have hge : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ n := by omega
  have hkle : Nat.sqrt n ≤ G := by
    rw [hsqrt]
    exact iter_le n _
  rcases Nat.lt_or_ge (Nat.sqrt n) G with hlt | hge2
  · have hwle : Nat.sqrt n + 1 ≤ G := by omega
    have hcontra := sqrt_claim n G hGpos _ hwle hge
    have hkk : Nat.sqrt.iter n G = Nat.sqrt n := hsqrt.symm
    omega
  · have hkG : Nat.sqrt n = G := by omega
    have hstop : ¬ (G + n / G) / 2 < G := by
      apply Classical.byContradiction
      intro hnn
      have hlt2 : (G + n / G) / 2 < G := by omega
      have e := Nat.sqrt.iter.eq_def n G
      have e2 : Nat.sqrt.iter n G = Nat.sqrt.iter n ((G + n / G) / 2) := by
        rw [e]
        simp only []
        split
        · next h => rfl
        · next h => exact absurd hlt2 h
      have hle2 := iter_le n ((G + n / G) / 2)
      have h1 : Nat.sqrt.iter n G ≤ (G + n / G) / 2 := by
        rw [e2]
        exact hle2
      have h2 : (G + n / G) / 2 < Nat.sqrt.iter n G := by
        rw [← hsqrt, hkG]
        exact hlt2
      have h3 : Nat.sqrt.iter n G < Nat.sqrt.iter n G :=
        Nat.lt_of_le_of_lt h1 h2
      exact Nat.lt_irrefl _ h3
    have hq : G ≤ n / G := by omega
    have hGG : G * G ≤ n := (Nat.le_div_iff_mul_le hGpos).mp hq
    have hexp : (G + 1) * (G + 1) = G * G + (G + (G + 1)) := by
      have r1 : (G + 1) * (G + 1) = G * (G + 1) + 1 * (G + 1) := Nat.add_mul _ _ _
      have e_succ : G + 1 = G.succ := rfl
      have r2 : G * (G + 1) = G * G + G := by
        rw [e_succ, Nat.mul_succ]
      have r3 : (1 : Nat) * (G + 1) = G + 1 := Nat.one_mul _
      omega
    rw [hkG] at hge
    omega

/-- The `Nat.sqrt` upper bound, missing from core. -/
theorem sqrt_upper (n : Nat) : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hn1 : n ≤ 1 := by omega
    have hsq : Nat.sqrt n = n := by
      unfold Nat.sqrt
      split
      · next h => rfl
      · next h => omega
    rw [hsq]
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · decide
    · decide
  · have hsqrt : Nat.sqrt n = Nat.sqrt.iter n (1 <<< (Nat.log2 n / 2 + 1)) := by
      unfold Nat.sqrt
      split
      · next h => omega
      · rfl
    have hGpos : 0 < 1 <<< (Nat.log2 n / 2 + 1) := by
      rw [Nat.one_shiftLeft]
      exact Nat.pow_pos (by decide)
    have hab := init_above n
    exact sqrt_upper_at_guess n _ hGpos hab hsqrt

/-! ## Newton iteration on naturals -/

/-- `N = a * 10^10`: the scaled radicand as a natural number. -/
def newtonN (a : Nat) : Nat := a * 10 ^ 10

/-- The seed `a / 2 + 5 * 10^9`. -/
def newtonSeed (a : Nat) : Nat := a / 2 + 5 * 10 ^ 9

/-- One Newton step `(N / z + z) / 2`. -/
def newtonStep (N z : Nat) : Nat := (N / z + z) / 2

/-- The Newton iterates from the seed. -/
def newtonSeq (a : Nat) : Nat → Nat
  | 0 => newtonSeed a
  | n + 1 => newtonStep (newtonN a) (newtonSeq a n)

/-- Successor square expansion. -/
theorem sq_succ (w : Nat) : (w + 1) * (w + 1) = w * w + (w + (w + 1)) := by
  have e := add_sq w 1
  have h1 : w * 1 = w := Nat.mul_one w
  have h2 : (1 : Nat) * 1 = 1 := Nat.one_mul 1
  omega

/-- `2^167 = 2 * 2^166`. -/
theorem pow167 : (2 : Nat) ^ 167 = 2 * 2 ^ 166 := by
  have h : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by
    show (2 : Nat) ^ (166 + 1) = _
    rw [Nat.pow_succ]
  omega

/-- The true root is at least `1` for positive `a`. -/
theorem newton_s_pos {a : Nat} (ha1 : 1 ≤ a) : 1 ≤ Nat.sqrt (newtonN a) := by
  apply Classical.byContradiction
  intro hcon
  have hs0 : Nat.sqrt (newtonN a) = 0 := by omega
  have hub := sqrt_upper (newtonN a)
  rw [hs0] at hub
  have hN : 10000000000 ≤ newtonN a := by
    unfold newtonN
    have h := Nat.mul_le_mul_right (10 ^ 10) ha1
    have h1 : 1 * 10 ^ 10 = 10000000000 := by decide
    omega
  have h10 : (0 + 1) * (0 + 1) = 1 := by decide
  rw [h10] at hub
  omega

/-- Core inequality `(seed + 1)^2 > N`, fully general (no literals, for `omega`). -/
theorem seed_gt_sq_gen (h r c D : Nat) (hr : r ≤ 1) (hD : D = 2 * c)
    (key : 2 * (h * c) ≤ h * h + c * c) (hrD : r * D ≤ D) :
    (2 * h + r) * D < (h + (c + 1)) * (h + (c + 1)) := by
  have eL : (2 * h + r) * D
      = ((h * c + h * c) + (h * c + h * c)) + r * D := by
    have e1 : (2 * h) * D = (h * c + h * c) + (h * c + h * c) := by
      have e2 : h * (2 * c) = h * c + h * c := by
        rw [← Nat.mul_assoc]
        have h22 : h * 2 = h + h := by omega
        rw [h22, Nat.add_mul]
      calc (2 * h) * D = 2 * (h * D) := by rw [Nat.mul_assoc]
        _ = 2 * (h * (2 * c)) := by rw [hD]
        _ = 2 * (h * c + h * c) := by rw [e2]
        _ = (h * c + h * c) + (h * c + h * c) := by omega
    rw [Nat.add_mul, e1]
  have e := add_sq h (c + 1)
  have f1 : h * (c + 1) = h * c + h := by
    rw [Nat.mul_add, Nat.mul_one]
  have f2 := add_sq c 1
  have g1 : c * 1 = c := Nat.mul_one _
  have g2 : (1 : Nat) * 1 = 1 := Nat.one_mul 1
  have hDc : D = c + c := by omega
  omega

/-- Core inequality: `(seed + 1)^2 > N`, for explicit `h r` with `a = 2h + r`. -/
theorem seed_gt_sq_aux (h r : Nat) (hr : r ≤ 1) :
    (2 * h + r) * 10 ^ 10 < ((h + 5 * 10 ^ 9) + 1) * ((h + 5 * 10 ^ 9) + 1) := by
  have hD : (10 : Nat) ^ 10 = 2 * (5 * 10 ^ 9) := by decide
  have key := two_mul_le_add_sq h (5 * 10 ^ 9)
  have hrD : r * (10 ^ 10) ≤ 10 ^ 10 := by
    have hle := Nat.mul_le_mul_right (10 ^ 10) hr
    have h1 : 1 * (10 ^ 10) = 10 ^ 10 := Nat.one_mul _
    rw [h1] at hle
    exact hle
  have b : (h + 5 * 10 ^ 9) + 1 = h + (5 * 10 ^ 9 + 1) := by ac_rfl
  rw [b]
  exact seed_gt_sq_gen h r (5 * 10 ^ 9) (10 ^ 10) hr hD key hrD

/-- `(seed + 1)^2 > N`. -/
theorem seed_gt_sq {a : Nat} : newtonN a < (newtonSeed a + 1) * (newtonSeed a + 1) := by
  have hdm := Nat.div_add_mod a 2
  have hmod : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have hmain := seed_gt_sq_aux (a / 2) (a % 2) (by omega)
  unfold newtonN newtonSeed
  rw [hdm] at hmain
  exact hmain

/-- The seed is at least the root. -/
theorem seed_ge_s {a : Nat} : Nat.sqrt (newtonN a) ≤ newtonSeed a := by
  apply Classical.byContradiction
  intro hcon
  have hlt : newtonSeed a < Nat.sqrt (newtonN a) := Nat.lt_of_not_ge hcon
  have hle : newtonSeed a + 1 ≤ Nat.sqrt (newtonN a) := hlt
  have hsq1 : (newtonSeed a + 1) * (newtonSeed a + 1)
      ≤ Nat.sqrt (newtonN a) * Nat.sqrt (newtonN a) := Nat.mul_le_mul hle hle
  have hsq2 := Nat.sqrt_le (newtonN a)
  have hgt := seed_gt_sq (a := a)
  omega

/-- `N / z ≤ s` for `z ≥ s + 2`. -/
theorem step_q_le {N s z q : Nat} (hup : N < (s + 1) * (s + 1)) (hz : s + 2 ≤ z)
    (hzpos : 0 < z) (hq : N / z = q) : q ≤ s := by
  have h2 : (s + 1) * (s + 1) ≤ (s + 1) * z := Nat.mul_le_mul_left _ (by omega)
  have h1 : N < (s + 1) * z := by omega
  have h3 : N / z < s + 1 := (Nat.div_lt_iff_lt_mul hzpos).mpr h1
  rw [hq] at h3
  omega

/-- `N / z ≤ s + 2` for `z ≥ s`. -/
theorem step_q_le' {N s z q : Nat} (hs1 : 1 ≤ s) (hup : N < (s + 1) * (s + 1))
    (hz : s ≤ z) (hzpos : 0 < z) (hq : N / z = q) : q ≤ s + 2 := by
  have hNle : N ≤ s * s + (s + s) := by
    have e := sq_succ s
    omega
  have e2 : s * s + (s + s) = s * (s + 2) := by
    have h22 : s * 2 = s + s := by omega
    calc s * s + (s + s) = s * s + s * 2 := by rw [← h22]
      _ = s * (s + 2) := by rw [← Nat.mul_add]
  have hdiv : (s * s + (s + s)) / s = s + 2 := by
    rw [e2]
    exact Nat.mul_div_cancel_left _ hs1
  have hle : N / s ≤ s + 2 := by
    rw [← hdiv]
    exact Nat.div_le_div_right hNle
  have h2 : N / z ≤ N / s := Nat.div_le_div_left hz (by omega : 0 < s)
  rw [hq] at h2
  omega

/-- Error halving above `s + 1`. -/
theorem step_halve {N s z q : Nat} (hup : N < (s + 1) * (s + 1)) (hz : s + 2 ≤ z)
    (hzpos : 0 < z) (hq : N / z = q) : (q + z) / 2 ≤ s + (z - s) / 2 := by
  have hqle := step_q_le hup hz hzpos hq
  have hqs : q + z ≤ s + z := by omega
  have h1 : (q + z) / 2 ≤ (s + z) / 2 := Nat.div_le_div_right hqs
  have hZZ : z = s + (z - s) := by omega
  have h2 : (s + z) / 2 = s + (z - s) / 2 := by omega
  omega

/-- Strict descent above `s + 1`. -/
theorem step_descend {N s z q : Nat} (hup : N < (s + 1) * (s + 1)) (hz : s + 2 ≤ z)
    (hzpos : 0 < z) (hq : N / z = q) : (q + z) / 2 < z := by
  have hqle := step_q_le hup hz hzpos hq
  omega

/-- A fixed point of the Newton step is the floor. -/
theorem step_fixed {N w q : Nat} (hw : 0 < w) (hq : N / w = q)
    (hfix : (q + w) / 2 = w) : w * w ≤ N ∧ N < (w + 1) * (w + 1) := by
  have h2w : 2 * w ≤ q + w ∧ q + w < 2 * w + 2 := by
    constructor <;> omega
  rcases (by omega : q = w ∨ q = w + 1) with hqw | hqw
  · have hN1 : w * w ≤ N := by
      have h := Nat.mul_div_le N w
      rw [hq, hqw] at h
      exact h
    have hmod : N % w < w := Nat.mod_lt _ hw
    have hdecomp : w * w + N % w = N := by
      have hda := Nat.div_add_mod N w
      rw [hq, hqw] at hda
      exact hda
    have hmul : w * (w + 1) = w * w + w := by
      rw [show w + 1 = w.succ from rfl, Nat.mul_succ]
    have hle : w * (w + 1) ≤ (w + 1) * (w + 1) :=
      Nat.mul_le_mul_right _ (by omega : w ≤ w + 1)
    have e := sq_succ w
    refine ⟨?_, ?_⟩
    · exact hN1
    · omega
  · have hN1 : w * w ≤ N := by
      have h := Nat.mul_div_le N w
      rw [hq, hqw] at h
      have hle : w * w ≤ w * (w + 1) := Nat.mul_le_mul_left _ (by omega : w ≤ w + 1)
      exact Nat.le_trans hle h
    have hmod : N % w < w := Nat.mod_lt _ hw
    have hdecomp : w * (w + 1) + N % w = N := by
      have hda := Nat.div_add_mod N w
      rw [hq, hqw] at hda
      exact hda
    have hmul : w * (w + 1) = w * w + w := by
      rw [show w + 1 = w.succ from rfl, Nat.mul_succ]
    have e := sq_succ w
    refine ⟨?_, ?_⟩
    · exact hN1
    · omega

/-- The trap `{s, s+1}` is invariant and both values satisfy the bounds. -/
theorem step_trap {N s w q : Nat} (hs1 : 1 ≤ s) (hlo : s * s ≤ N)
    (hup : N < (s + 1) * (s + 1)) (hw1 : s ≤ w) (hw2 : w ≤ s + 1)
    (hwpos : 0 < w) (hq : N / w = q) :
    s ≤ (q + w) / 2 ∧ (q + w) / 2 ≤ s + 1 := by
  rcases (by omega : w = s ∨ w = s + 1) with hws | hws
  · rw [hws] at hq hwpos hw1 hw2 ⊢
    have hqlo : s ≤ q := by
      have h := (Nat.le_div_iff_mul_le hwpos).mpr hlo
      rw [hq] at h
      exact h
    have hqup : q ≤ s + 2 := by
      have hNle : N ≤ s * s + (s + s) := by
        have e := sq_succ s
        omega
      have e2 : s * s + (s + s) = s * (s + 2) := by
        have h22 : s * 2 = s + s := by omega
        calc s * s + (s + s) = s * s + s * 2 := by rw [← h22]
          _ = s * (s + 2) := by rw [← Nat.mul_add]
      have hdiv : (s * s + (s + s)) / s = s + 2 := by
        rw [e2]
        exact Nat.mul_div_cancel_left _ hs1
      have hle : N / s ≤ s + 2 := by
        rw [← hdiv]
        exact Nat.div_le_div_right hNle
      rw [hq] at hle
      exact hle
    constructor <;> omega
  · rw [hws] at hq
    have hwpos' : 0 < s + 1 := by omega
    have hlt : N / (s + 1) < s + 1 := (Nat.div_lt_iff_lt_mul hwpos').mpr hup
    rw [hq] at hlt
    have hqlo : s ≤ q + 1 := by
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hs1
      have hle : t * (t + 1 + 1) ≤ N := by
        have e1 : t * (t + 1 + 1) = t * t + (t + t) := by
          have r : t * (t + 1 + 1) = t * (t + 1) + t * 1 := Nat.mul_add _ _ _
          have r2 : t * (t + 1) = t * t + t := by
            rw [Nat.mul_add, Nat.mul_one]
          have h1 : t * 1 = t := Nat.mul_one t
          omega
        have e2 := sq_succ t
        have b : (1 + t) * (1 + t) = (t + 1) * (t + 1) := by ac_rfl
        have hle2 : t * t + (t + t) ≤ (1 + t) * (1 + t) := by
          rw [b]
          omega
        have hlo' : (1 + t) * (1 + t) ≤ N := by
          rw [← ht]
          exact hlo
        have hle2' : t * (t + 1 + 1) ≤ (1 + t) * (1 + t) := by
          rw [e1]
          exact hle2
        exact Nat.le_trans hle2' hlo'
      have b2 : t + 1 + 1 = 1 + t + 1 := by ac_rfl
      rw [b2] at hle
      have hpos : 0 < 1 + t + 1 := by omega
      have hle3 : t ≤ N / (1 + t + 1) := (Nat.le_div_iff_mul_le hpos).mpr hle
      rw [← ht, hq] at hle3
      omega
    constructor <;> omega

/-- All Newton iterates stay above the root. -/
theorem seq_ge_s {a : Nat} (ha1 : 1 ≤ a) : ∀ i, Nat.sqrt (newtonN a) ≤ newtonSeq a i := by
  intro i
  induction i with
  | zero => rw [newtonSeq.eq_1]; exact seed_ge_s
  | succ i ih =>
    have hs1 := newton_s_pos ha1
    have hpos : 0 < newtonSeq a i := by omega
    have h := sqrt_newton_ge (n := newtonN a) (g := newtonSeq a i)
      (w := Nat.sqrt (newtonN a)) (q := newtonN a / newtonSeq a i)
      hpos ih (Nat.sqrt_le _) rfl
    have b : newtonSeq a i + newtonN a / newtonSeq a i
        = newtonN a / newtonSeq a i + newtonSeq a i := Nat.add_comm _ _
    rw [b] at h
    rw [newtonSeq.eq_2]
    unfold newtonStep
    exact h

/-- One step stays below `seed + 1`, for plain variables. -/
theorem step_le_seed {N s z q seed : Nat}
    (hs1 : 1 ≤ s) (hup : N < (s + 1) * (s + 1)) (hlo : s * s ≤ N)
    (hge : s ≤ z) (hzpos : 0 < z) (hq : N / z = q)
    (ih : z ≤ seed + 1) (hse : s ≤ seed) :
    (q + z) / 2 ≤ seed + 1 := by
  rcases Nat.lt_or_ge z (s + 2) with hlt | hge2
  · have hz2 : z ≤ s + 1 := by omega
    have hq2 := step_q_le' hs1 hup hge hzpos hq
    omega
  · have h1 := step_halve hup hge2 hzpos hq
    have h2 : (z - s) / 2 ≤ z - s := Nat.div_le_self _ _
    have h3 : z - s ≤ seed + 1 - s := by omega
    omega

/-- All Newton iterates stay below `seed + 1`. -/
theorem seq_le {a : Nat} (ha1 : 1 ≤ a) :
    ∀ i, newtonSeq a i ≤ newtonSeed a + 1 := by
  intro i
  induction i with
  | zero => rw [newtonSeq.eq_1]; exact Nat.le_succ _
  | succ i ih =>
    have hs1 := newton_s_pos ha1
    have hup := sqrt_upper (newtonN a)
    have hlo := Nat.sqrt_le (newtonN a)
    have hge := seq_ge_s ha1 i
    have hzpos : 0 < newtonSeq a i := by omega
    have hse := seed_ge_s (a := a)
    have h := step_le_seed (N := newtonN a) (s := Nat.sqrt (newtonN a))
      (z := newtonSeq a i) (q := newtonN a / newtonSeq a i) (seed := newtonSeed a)
      hs1 hup hlo hge hzpos rfl ih hse
    rw [newtonSeq.eq_2]
    unfold newtonStep
    exact h

/-- The error halves above `s + 1`. -/
theorem seq_err_halve {a : Nat} (ha1 : 1 ≤ a) {i : Nat}
    (hi : Nat.sqrt (newtonN a) + 2 ≤ newtonSeq a i) :
    newtonSeq a (i + 1) - Nat.sqrt (newtonN a)
      ≤ (newtonSeq a i - Nat.sqrt (newtonN a)) / 2 := by
  have hup := sqrt_upper (newtonN a)
  have hge : Nat.sqrt (newtonN a) ≤ newtonSeq a i := seq_ge_s ha1 i
  have hzpos : 0 < newtonSeq a i := by omega
  have h1 := step_halve (N := newtonN a) (s := Nat.sqrt (newtonN a))
    (z := newtonSeq a i) (q := newtonN a / newtonSeq a i) hup hi hzpos rfl
  rw [newtonSeq.eq_2]
  unfold newtonStep
  have h4 := Nat.sub_le_sub_right h1 (Nat.sqrt (newtonN a))
  have h5 : Nat.sqrt (newtonN a) + (newtonSeq a i - Nat.sqrt (newtonN a)) / 2
      - Nat.sqrt (newtonN a) = (newtonSeq a i - Nat.sqrt (newtonN a)) / 2 := by
    omega
  rw [h5] at h4
  exact h4

/-- The root is below `2^101`. -/
theorem s_lt_pow {a : Nat} (haMax : a ≤ 2 ^ 167 - 1) :
    Nat.sqrt (newtonN a) < 2 ^ 101 := by
  apply Classical.byContradiction
  intro hcon
  have hge : 2 ^ 101 ≤ Nat.sqrt (newtonN a) := by omega
  have hsq : (2 ^ 101) * (2 ^ 101)
      ≤ Nat.sqrt (newtonN a) * Nat.sqrt (newtonN a) := Nat.mul_le_mul hge hge
  have hle := Nat.sqrt_le (newtonN a)
  have h10 : (10 : Nat) ^ 10 ≤ 2 ^ 34 := by decide
  have hN : newtonN a < 2 ^ 201 := by
    unfold newtonN
    have e1 : a * 10 ^ 10 ≤ a * 2 ^ 34 := Nat.mul_le_mul_left _ h10
    have e2 : a * 2 ^ 34 ≤ (2 ^ 167 - 1) * 2 ^ 34 := Nat.mul_le_mul_right _ haMax
    have e3 : (2 ^ 167 - 1) * 2 ^ 34 < 2 ^ 167 * 2 ^ 34 := by
      have hpos : 0 < (2 : Nat) ^ 34 := Nat.pow_pos (by decide)
      have h1 : (1 : Nat) ≤ 2 ^ 167 := Nat.one_le_pow _ _ (by decide)
      have hlt : 2 ^ 167 - 1 < 2 ^ 167 := by omega
      exact (Nat.mul_lt_mul_right hpos).mpr hlt
    have e4 : 2 ^ 167 * 2 ^ 34 = 2 ^ 201 := by
      have hcc : (167 : Nat) + 34 = 201 := by decide
      rw [← hcc, Nat.pow_add]
    rw [e4] at e3
    exact Nat.lt_of_le_of_lt (Nat.le_trans e1 e2) e3
  have e5 : (2 ^ 101) * (2 ^ 101) = 2 ^ 202 := by
    have hcc : (101 : Nat) + 101 = 202 := by decide
    rw [← hcc, Nat.pow_add]
  have e6 : (2 : Nat) ^ 201 < 2 ^ 202 := Nat.pow_lt_pow_right (by decide) (by decide)
  omega

/-- The seed is below `2^167`. -/
theorem seed_lt_pow {a : Nat} (haMax : a ≤ 2 ^ 167 - 1) : newtonSeed a < 2 ^ 167 := by
  unfold newtonSeed
  have h1 : a / 2 ≤ 2 ^ 166 - 1 := by
    have h2 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right haMax
    have h3 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by
      have p := pow167
      omega
    omega
  have h4 : (5 * 10 ^ 9 : Nat) ≤ 2 ^ 166 := by decide
  have p167 := pow167
  omega

/-- Joint bignum bound: `s + 2 + (seed + 1) ≤ 2^167 - 1`. -/
theorem bignum_bound (s seed : Nat) (hs : s ≤ 2 ^ 101)
    (hseed : seed ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9) :
    s + 2 + (seed + 1) ≤ 2 ^ 167 - 1 := by
  have hs165 : (2 : Nat) ^ 101 ≤ 2 ^ 165 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have d1 : 5 * 10 ^ 9 + 3 ≤ (2 : Nat) ^ 33 := by decide
  have d2 : (2 : Nat) ^ 33 ≤ 2 ^ 165 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have p165 : (2 : Nat) ^ 165 + 2 ^ 165 = 2 ^ 166 := by
    have h : (2 : Nat) ^ 166 = 2 ^ 165 * 2 := by
      show (2 : Nat) ^ (165 + 1) = _
      rw [Nat.pow_succ]
    omega
  have p167 : (2 : Nat) ^ 167 = 2 ^ 166 + 2 ^ 166 := by
    have h : (2 : Nat) ^ 167 = 2 ^ 166 * 2 := by
      show (2 : Nat) ^ (166 + 1) = _
      rw [Nat.pow_succ]
    omega
  omega

/-- Every Newton step stays in decimal range. -/
theorem sum_le_max {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) (i : Nat) :
    newtonN a / newtonSeq a i + newtonSeq a i ≤ 2 ^ 167 - 1 := by
  have hs1 := newton_s_pos ha1
  have hup := sqrt_upper (newtonN a)
  have hge : Nat.sqrt (newtonN a) ≤ newtonSeq a i := seq_ge_s ha1 i
  have hzpos : 0 < newtonSeq a i := by omega
  have hq : newtonN a / newtonSeq a i ≤ Nat.sqrt (newtonN a) + 2 :=
    step_q_le' hs1 hup hge hzpos rfl
  have hle : newtonSeq a i ≤ newtonSeed a + 1 := seq_le ha1 i
  have hs : Nat.sqrt (newtonN a) ≤ 2 ^ 101 := by
    have h := s_lt_pow haMax
    omega
  have hseed : newtonSeed a ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9 := by
    unfold newtonSeed
    have h1 : a / 2 ≤ 2 ^ 166 - 1 := by
      have h2 : a / 2 ≤ (2 ^ 167 - 1) / 2 := Nat.div_le_div_right haMax
      have h3 : (2 ^ 167 - 1) / 2 = 2 ^ 166 - 1 := by
        have p := pow167
        omega
      omega
    omega
  have hb := bignum_bound (Nat.sqrt (newtonN a)) (newtonSeed a) hs hseed
  omega

/-- The scaled error `e_i * 2^i` stays below the seed while above the trap. -/
theorem seq_err_bound {a : Nat} (ha1 : 1 ≤ a) {B : Nat}
    (hall : ∀ i, i ≤ B → Nat.sqrt (newtonN a) + 2 ≤ newtonSeq a i) :
    ∀ i, i ≤ B → (newtonSeq a i - Nat.sqrt (newtonN a)) * 2 ^ i ≤ newtonSeed a := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [newtonSeq.eq_1, Nat.pow_zero, Nat.mul_one]
    have hse := seed_ge_s (a := a)
    omega
  | succ i ih =>
    intro hi
    have hi' : i ≤ B := by omega
    have ih' := ih hi'
    have hhi := hall i hi'
    have hh := seq_err_halve ha1 hhi
    have h2e : 2 * (newtonSeq a (i + 1) - Nat.sqrt (newtonN a))
        ≤ newtonSeq a i - Nat.sqrt (newtonN a) := by
      have hd := Nat.div_mul_le_self (newtonSeq a i - Nat.sqrt (newtonN a)) 2
      omega
    have e1 : (newtonSeq a (i + 1) - Nat.sqrt (newtonN a)) * 2 ^ (i + 1)
        = (2 * (newtonSeq a (i + 1) - Nat.sqrt (newtonN a))) * 2 ^ i := by
      rw [Nat.pow_succ]
      ac_rfl
    have e2 : (2 * (newtonSeq a (i + 1) - Nat.sqrt (newtonN a))) * 2 ^ i
        ≤ (newtonSeq a i - Nat.sqrt (newtonN a)) * 2 ^ i :=
      Nat.mul_le_mul_right _ h2e
    omega

/-- The iterates reach the trap within 167 steps. -/
theorem trap_entry {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) :
    ∃ j, j ≤ 167 ∧ newtonSeq a j ≤ Nat.sqrt (newtonN a) + 1 := by
  apply Classical.byContradiction
  intro hcon
  have hall : ∀ i, i ≤ 167 → Nat.sqrt (newtonN a) + 2 ≤ newtonSeq a i := by
    intro i hi
    apply Classical.byContradiction
    intro hc
    apply hcon
    exact ⟨i, hi, by omega⟩
  have hbound := seq_err_bound ha1 hall 167 (by omega : 167 ≤ 167)
  have hge167 := hall 167 (by omega : 167 ≤ 167)
  have he167 : 2 ≤ newtonSeq a 167 - Nat.sqrt (newtonN a) := by omega
  have hseed := seed_lt_pow haMax
  have hmul := Nat.mul_le_mul_right (2 ^ 167) he167
  omega

/-- One deployed-loop step follows the Newton sequence. -/
theorem loop_link {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) (i : Nat)
    (hi : i ≤ 254) (habove : Nat.sqrt (newtonN a) + 2 ≤ newtonSeq a i) :
    loop (a : Int) (255 - i) (newtonSeq a i : Int) (newtonSeq a (i + 1) : Int)
      = loop (a : Int) (255 - (i + 1)) (newtonSeq a (i + 1) : Int)
        (newtonSeq a (i + 2) : Int) := by
  have hs1 := newton_s_pos ha1
  have hup := sqrt_upper (newtonN a)
  have hge : Nat.sqrt (newtonN a) ≤ newtonSeq a i := seq_ge_s ha1 i
  have hzpos : 0 < newtonSeq a i := by omega
  have hge1 : Nat.sqrt (newtonN a) ≤ newtonSeq a (i + 1) := seq_ge_s ha1 (i + 1)
  have hzpos1 : 0 < newtonSeq a (i + 1) := by omega
  have hdesc := step_descend (N := newtonN a) (s := Nat.sqrt (newtonN a))
    (z := newtonSeq a i) (q := newtonN a / newtonSeq a i) hup habove hzpos rfl
  have hZZ : newtonSeq a (i + 1)
      = (newtonN a / newtonSeq a i + newtonSeq a i) / 2 :=
    newtonSeq.eq_2 _ _
  have hne : (newtonSeq a (i + 1) : Int) ≠ (newtonSeq a i : Int) := by
    intro hcon
    have heq : newtonSeq a (i + 1) = newtonSeq a i := Int.ofNat.inj hcon
    omega
  have hfuel : 255 - i = (255 - (i + 1)) + 1 := by omega
  rw [hfuel]
  have h1 : ddiv (a : Int) ((newtonSeq a (i + 1) : Nat) : Int)
      = some ((newtonN a / newtonSeq a (i + 1) : Nat) : Int) :=
    ddiv_nat hzpos1 (by
      have hq := step_q_le' (N := newtonN a) (s := Nat.sqrt (newtonN a)) hs1 hup hge1
        hzpos1 (rfl : newtonN a / newtonSeq a (i + 1) = _)
      have hq' : a * 10 ^ 10 / newtonSeq a (i + 1) ≤ Nat.sqrt (newtonN a) + 2 := hq
      have h2s : Nat.sqrt (newtonN a) + 2 ≤ 2 ^ 167 - 1 := by
        have h1 := s_lt_pow haMax
        have h2 : (2 : Nat) ^ 101 < 2 ^ 167 :=
          Nat.pow_lt_pow_right (by decide) (by decide)
        omega
      omega)
  have h2 : dadd ((newtonN a / newtonSeq a (i + 1) : Nat) : Int)
      ((newtonSeq a (i + 1) : Nat) : Int)
      = some (((newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1) : Nat)) : Int) :=
    dadd_nat (sum_le_max ha1 haMax (i + 1))
  have h3 : ddiv ((newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1) : Nat) : Int)
      (2 * DIVISOR)
      = some ((newtonSeq a (i + 2) : Nat) : Int) := by
    have hb10 : (2 : Int) * DIVISOR = ((2 * 10 ^ 10 : Nat) : Int) := by decide
    have hbound3 : (newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1)) * 10 ^ 10
        / (2 * 10 ^ 10) ≤ 2 ^ 167 - 1 := by
      have hle := sum_le_max ha1 haMax (i + 1)
      have hdiv := Nat.div_le_self
        (newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1)) 2
      have heq := Nat.mul_div_mul_right
        (newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1)) 2
        (by decide : 0 < 10 ^ 10)
      rw [heq]
      exact Nat.le_trans hdiv hle
    have e3 := ddiv_nat (a := newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1))
      (b := 2 * 10 ^ 10) (by decide : 0 < 2 * 10 ^ 10) hbound3
    rw [← hb10] at e3
    have hval : (newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1)) * 10 ^ 10
        / (2 * 10 ^ 10) = newtonSeq a (i + 2) := by
      have heq := Nat.mul_div_mul_right
        (newtonN a / newtonSeq a (i + 1) + newtonSeq a (i + 1)) 2
        (by decide : 0 < 10 ^ 10)
      have hZZ2 : newtonSeq a (i + 2)
          = newtonStep (newtonN a) (newtonSeq a (i + 1)) := newtonSeq.eq_2 _ _
      unfold newtonStep at hZZ2
      rw [heq]
      exact hZZ2.symm
    rw [hval] at e3
    exact e3
  exact loop_step_of _ hne h1 h2 h3

/-- Chaining the links from `0` to `j`. -/
theorem loop_chain {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) (j : Nat)
    (hj : j ≤ 167) (hall : ∀ k, k < j → Nat.sqrt (newtonN a) + 2 ≤ newtonSeq a k) :
    loop (a : Int) 255 (newtonSeq a 0 : Int) (newtonSeq a 1 : Int)
      = loop (a : Int) (255 - j) (newtonSeq a j : Int) (newtonSeq a (j + 1) : Int) := by
  have key : ∀ i, i ≤ j → loop (a : Int) 255 (newtonSeq a 0 : Int) (newtonSeq a 1 : Int)
      = loop (a : Int) (255 - i) (newtonSeq a i : Int) (newtonSeq a (i + 1) : Int) := by
    intro i
    induction i with
    | zero =>
      intro _
      rfl
    | succ i ih =>
      intro hi
      have hi' : i ≤ j := by omega
      have ih' := ih hi'
      have hlt : i < j := by omega
      have habove := hall i hlt
      have hi254 : i ≤ 254 := by omega
      have hlink := loop_link ha1 haMax i hi254 habove
      rw [ih']
      exact hlink
  exact key j (Nat.le_refl _)

/-- The loop from a trap pair returns a trap pair. -/
theorem trap_loop {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) :
    ∀ (t : Nat) {w1 w2 : Nat},
    Nat.sqrt (newtonN a) ≤ w1 → w1 ≤ Nat.sqrt (newtonN a) + 1 →
    Nat.sqrt (newtonN a) ≤ w2 → w2 ≤ Nat.sqrt (newtonN a) + 1 →
    ¬ (w1 = Nat.sqrt (newtonN a) + 1 ∧ w2 = Nat.sqrt (newtonN a) + 1) →
    ∃ Y Z : Nat, loop (a : Int) t (w1 : Int) (w2 : Int) = some ((Y : Int), (Z : Int))
      ∧ Nat.sqrt (newtonN a) ≤ Y ∧ Y ≤ Nat.sqrt (newtonN a) + 1
      ∧ Nat.sqrt (newtonN a) ≤ Z ∧ Z ≤ Nat.sqrt (newtonN a) + 1
      ∧ ¬ (Y = Nat.sqrt (newtonN a) + 1 ∧ Z = Nat.sqrt (newtonN a) + 1) := by
  intro t
  induction t with
  | zero =>
    intro w1 w2 hw1lo hw1hi hw2lo hw2hi hne
    exact ⟨w1, w2, rfl, hw1lo, hw1hi, hw2lo, hw2hi, hne⟩
  | succ t ih =>
    intro w1 w2 hw1lo hw1hi hw2lo hw2hi hne
    have hs1 := newton_s_pos ha1
    have hup := sqrt_upper (newtonN a)
    have hlo := Nat.sqrt_le (newtonN a)
    by_cases heq : w1 = w2
    · subst heq
      rw [loop_stop]
      exact ⟨w1, w1, rfl, hw1lo, hw1hi, hw1lo, hw1hi, hne⟩
    · have hwpos : 0 < w2 := by omega
      have hfw := step_trap (N := newtonN a) (s := Nat.sqrt (newtonN a))
        (w := w2) (q := newtonN a / w2) hs1 hlo hup hw2lo hw2hi hwpos rfl
      have hnb : ¬ (w2 = Nat.sqrt (newtonN a) + 1
          ∧ (newtonN a / w2 + w2) / 2 = Nat.sqrt (newtonN a) + 1) := by
        intro hcon
        obtain ⟨h1, h2⟩ := hcon
        have hwpos' : 0 < Nat.sqrt (newtonN a) + 1 := by omega
        have hlt : newtonN a / (Nat.sqrt (newtonN a) + 1) < Nat.sqrt (newtonN a) + 1 :=
          (Nat.div_lt_iff_lt_mul hwpos').mpr hup
        have hlt2 : newtonN a / w2 < Nat.sqrt (newtonN a) + 1 := by
          rw [h1]
          exact hlt
        have hfle : (newtonN a / w2 + w2) / 2 ≤ Nat.sqrt (newtonN a) := by omega
        omega
      obtain ⟨Y, Z, hYZ, hYlo, hYhi, hZlo, hZhi, hnb'⟩ :=
        ih hw2lo hw2hi hfw.1 hfw.2 hnb
      refine ⟨Y, Z, ?_, hYlo, hYhi, hZlo, hZhi, hnb'⟩
      have hne' : (w2 : Int) ≠ (w1 : Int) := by
        intro hcon
        have heq2 : w2 = w1 := Int.ofNat.inj hcon
        omega
      have h1 : ddiv (a : Int) ((w2 : Nat) : Int)
          = some ((newtonN a / w2 : Nat) : Int) := by
        have hbound : newtonN a / w2 ≤ 2 ^ 167 - 1 := by
          have hq := step_q_le' (N := newtonN a) (s := Nat.sqrt (newtonN a)) hs1 hup
            hw2lo hwpos (rfl : newtonN a / w2 = _)
          have hs : Nat.sqrt (newtonN a) ≤ 2 ^ 101 := by
            have h := s_lt_pow haMax
            omega
          have hmax : Nat.sqrt (newtonN a) + 2 ≤ 2 ^ 167 - 1 := by
            have h2 : (2 : Nat) ^ 101 < 2 ^ 167 :=
              Nat.pow_lt_pow_right (by decide) (by decide)
            omega
          omega
        exact ddiv_nat hwpos hbound
      have h2 : dadd ((newtonN a / w2 : Nat) : Int) ((w2 : Nat) : Int)
          = some (((newtonN a / w2 + w2 : Nat)) : Int) := by
        have hsum : newtonN a / w2 + w2 ≤ 2 ^ 167 - 1 := by
          have hq := step_q_le' (N := newtonN a) (s := Nat.sqrt (newtonN a)) hs1 hup
            hw2lo hwpos (rfl : newtonN a / w2 = _)
          have hs : Nat.sqrt (newtonN a) ≤ 2 ^ 101 := by
            have h := s_lt_pow haMax
            omega
          have hb := bignum_bound (Nat.sqrt (newtonN a)) (Nat.sqrt (newtonN a)) hs
            (by omega : Nat.sqrt (newtonN a) ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9)
          omega
        exact dadd_nat hsum
      have h3 : ddiv ((newtonN a / w2 + w2 : Nat) : Int) (2 * DIVISOR)
          = some ((((newtonN a / w2 + w2) / 2 : Nat)) : Int) := by
        have hb10 : (2 : Int) * DIVISOR = ((2 * 10 ^ 10 : Nat) : Int) := by decide
        have hbound3 : (newtonN a / w2 + w2) * 10 ^ 10 / (2 * 10 ^ 10)
            ≤ 2 ^ 167 - 1 := by
          have hle : newtonN a / w2 + w2 ≤ 2 ^ 167 - 1 := by
            have hq := step_q_le' (N := newtonN a) (s := Nat.sqrt (newtonN a)) hs1 hup
              hw2lo hwpos (rfl : newtonN a / w2 = _)
            have hs : Nat.sqrt (newtonN a) ≤ 2 ^ 101 := by
              have h := s_lt_pow haMax
              omega
            have hb := bignum_bound (Nat.sqrt (newtonN a)) (Nat.sqrt (newtonN a)) hs
              (by omega : Nat.sqrt (newtonN a) ≤ 2 ^ 166 - 1 + 5 * 10 ^ 9)
            omega
          have hdiv := Nat.div_le_self (newtonN a / w2 + w2) 2
          have heq := Nat.mul_div_mul_right (newtonN a / w2 + w2) 2
            (by decide : 0 < 10 ^ 10)
          rw [heq]
          exact Nat.le_trans hdiv hle
        have e3 := ddiv_nat (a := newtonN a / w2 + w2) (b := 2 * 10 ^ 10)
          (by decide : 0 < 2 * 10 ^ 10) hbound3
        rw [← hb10] at e3
        have hval : (newtonN a / w2 + w2) * 10 ^ 10 / (2 * 10 ^ 10)
            = (newtonN a / w2 + w2) / 2 :=
          Nat.mul_div_mul_right _ _ (by decide : 0 < 10 ^ 10)
        rw [hval] at e3
        exact e3
      have hstep := loop_step_of (x := (a : Int)) (y := (w1 : Int)) (z := (w2 : Int))
        t hne' h1 h2 h3
      rw [hstep]
      exact hYZ

/-- First fuel index where the Newton sequence enters the trap. -/
theorem trap_entry_min {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) :
    ∃ j, j ≤ 167 ∧ newtonSeq a j ≤ Nat.sqrt (newtonN a) + 1
      ∧ ∀ k, k < j → Nat.sqrt (newtonN a) + 2 ≤ newtonSeq a k := by
  obtain ⟨j0, hj0, hp0⟩ := trap_entry ha1 haMax
  have key : ∀ B, (∃ j, j ≤ B ∧ newtonSeq a j ≤ Nat.sqrt (newtonN a) + 1)
      → ∃ j, j ≤ B ∧ newtonSeq a j ≤ Nat.sqrt (newtonN a) + 1
        ∧ ∀ k, k < j → Nat.sqrt (newtonN a) + 2 ≤ newtonSeq a k := by
    intro B
    induction B with
    | zero =>
      intro h
      obtain ⟨j, hj, hp⟩ := h
      have hj0 : j = 0 := by omega
      subst hj0
      exact ⟨0, by omega, hp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ B ih =>
      intro h
      rcases Classical.em (∃ j, j ≤ B ∧ newtonSeq a j ≤ Nat.sqrt (newtonN a) + 1)
        with hB | hB
      · obtain ⟨j, hj, hp, hmin⟩ := ih hB
        exact ⟨j, by omega, hp, hmin⟩
      · obtain ⟨j, hj, hp⟩ := h
        have hjB : j = B + 1 := by
          apply Classical.byContradiction
          intro hcon
          apply hB
          exact ⟨j, by omega, hp⟩
        subst hjB
        refine ⟨B + 1, by omega, hp, ?_⟩
        intro k hk
        apply Classical.byContradiction
        intro hc
        apply hB
        refine ⟨k, by omega, ?_⟩
        omega
  exact key 167 ⟨j0, hj0, hp0⟩

/-- Uniqueness of the floored root from two-sided bounds. -/
theorem sqrt_eq_of_bounds {N w : Nat} (hlo : w * w ≤ N) (hup : N < (w + 1) * (w + 1)) :
    Nat.sqrt N = w := by
  have hGpos : 0 < 1 <<< (Nat.log2 N / 2 + 1) := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_pos (by decide)
  have hab := init_above N
  have hG : w ≤ 1 <<< (Nat.log2 N / 2 + 1) := by
    apply Classical.byContradiction
    intro hcon
    have h2 : 1 <<< (Nat.log2 N / 2 + 1) + 1 ≤ w := by omega
    have h3 := Nat.mul_le_mul h2 h2
    have h1 := Nat.le_trans hlo hab
    have e := sq_succ (1 <<< (Nat.log2 N / 2 + 1))
    omega
  have hs1 := sqrt_claim N _ hGpos _ hG hlo
  rcases Nat.lt_or_ge N 2 with hn | hn
  · have hn1 : N ≤ 1 := by omega
    have hsq : Nat.sqrt N = N := by
      unfold Nat.sqrt
      split
      · next h => rfl
      · next h => omega
    rw [hsq]
    have hw1 : w ≤ 1 := by
      apply Classical.byContradiction
      intro hcon
      have h2 : 2 ≤ w := by omega
      have h3 : 2 * 2 ≤ w * w := Nat.mul_le_mul h2 h2
      omega
    rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl <;> omega
  · have hsqrt : Nat.sqrt N = Nat.sqrt.iter N (1 <<< (Nat.log2 N / 2 + 1)) := by
      unfold Nat.sqrt
      split
      · next h => omega
      · rfl
    have hs2 : Nat.sqrt N ≤ w := by
      apply Classical.byContradiction
      intro hcon
      have hlt : w + 1 ≤ Nat.sqrt N := by omega
      have hsq := Nat.mul_le_mul hlt hlt
      have hle := Nat.sqrt_le N
      omega
    rw [hsqrt] at hs2 ⊢
    omega

/-- The deployed loop lands in the trap, with the two required bounds. -/
theorem loop_final {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) :
    ∃ Y Z : Nat, loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
      = some ((Y : Int), (Z : Int))
      ∧ Nat.sqrt (newtonN a) ≤ Y ∧ Y ≤ Nat.sqrt (newtonN a) + 1
      ∧ Nat.sqrt (newtonN a) ≤ Z ∧ Z ≤ Nat.sqrt (newtonN a) + 1
      ∧ ¬ (Y = Nat.sqrt (newtonN a) + 1 ∧ Z = Nat.sqrt (newtonN a) + 1) := by
  obtain ⟨j, hj, hjtrap, hmin⟩ := trap_entry_min ha1 haMax
  have hgej : Nat.sqrt (newtonN a) ≤ newtonSeq a j := seq_ge_s ha1 j
  have hs1 := newton_s_pos ha1
  have hzpos : 0 < newtonSeq a j := by omega
  have hfw := step_trap (N := newtonN a) (s := Nat.sqrt (newtonN a)) (w := newtonSeq a j)
    (q := newtonN a / newtonSeq a j) (newton_s_pos ha1) (Nat.sqrt_le _)
    (sqrt_upper _) hgej hjtrap hzpos rfl
  have hZZ : newtonSeq a (j + 1) = (newtonN a / newtonSeq a j + newtonSeq a j) / 2 :=
    newtonSeq.eq_2 _ _
  rw [← hZZ] at hfw
  have hnb : ¬ (newtonSeq a j = Nat.sqrt (newtonN a) + 1
      ∧ newtonSeq a (j + 1) = Nat.sqrt (newtonN a) + 1) := by
    intro hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [hZZ, h1] at h2
    have hwpos' : 0 < Nat.sqrt (newtonN a) + 1 := by omega
    have hlt : newtonN a / (Nat.sqrt (newtonN a) + 1) < Nat.sqrt (newtonN a) + 1 :=
      (Nat.div_lt_iff_lt_mul hwpos').mpr (sqrt_upper _)
    omega
  rcases Classical.em ((a : Int) = ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)) with heq | heq
  · have ha : a = a / 2 + 5 * 10 ^ 9 := Int.ofNat.inj heq
    have hcases : a = 9999999999 ∨ a = 10000000000 := by omega
    have hstop : loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
        = some ((a : Int), (a : Int)) := by
      rw [← heq]
      exact loop_stop _ _ _
    rcases hcases with rfl | rfl
    · have hlo : 9999999999 * 9999999999 ≤ newtonN 9999999999 := by decide
      have hup : newtonN 9999999999 < (9999999999 + 1) * (9999999999 + 1) := by decide
      have hs_eq := sqrt_eq_of_bounds hlo hup
      refine ⟨9999999999, 9999999999, hstop, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · omega
      · intro hcon
        omega
    · have hlo : 10000000000 * 10000000000 ≤ newtonN 10000000000 := by decide
      have hup : newtonN 10000000000 < (10000000000 + 1) * (10000000000 + 1) := by decide
      have hs_eq := sqrt_eq_of_bounds hlo hup
      refine ⟨10000000000, 10000000000, hstop, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · omega
      · intro hcon
        omega
  · have eN : newtonN a = a * 10 ^ 10 := rfl
    have eSeed : newtonSeed a = a / 2 + 5 * 10 ^ 9 := rfl
    have eSeedI : (newtonSeed a : Int) = ((a / 2 + 5 * 10 ^ 9 : Nat) : Int) :=
      congrArg (fun n : Nat => ((n : Int))) eSeed
    have heq' : (a : Int) ≠ (newtonSeed a : Int) := by
      rw [eSeedI]
      exact heq
    have hstep := loop_step (a := a) (y := a) (z := newtonSeed a) (n := 255)
      (by rw [eSeed]; omega)
      (fun h => heq' (congrArg (fun n : Nat => ((n : Int))) h).symm)
      (by rw [← eN, ← newtonSeq.eq_1 a]; exact sum_le_max ha1 haMax 0)
    have hX : (a * 10 ^ 10 / newtonSeed a + newtonSeed a) / 2 = newtonSeq a 1 := by
      rw [show (1 : Nat) = 0 + 1 from rfl]
      exact (newtonSeq.eq_2 a 0).symm
    have eX1I : (((a * 10 ^ 10 / newtonSeed a + newtonSeed a) / 2 : Nat) : Int)
        = (newtonSeq a 1 : Int) := congrArg _ hX
    have eZZ0I : (newtonSeq a 0 : Int) = (newtonSeed a : Int) :=
      congrArg _ (newtonSeq.eq_1 a)
    have hstep' : loop (a : Int) 256 (a : Int) ((a / 2 + 5 * 10 ^ 9 : Nat) : Int)
        = loop (a : Int) 255 (newtonSeq a 0 : Int) (newtonSeq a 1 : Int) := by
      have h := hstep
      rw [eX1I, ← eZZ0I] at h
      exact h
    have hchain := loop_chain ha1 haMax j hj hmin
    obtain ⟨Y, Z, hYZ, hYlo, hYhi, hZlo, hZhi, hnb'⟩ :=
      trap_loop ha1 haMax (255 - j) hgej hjtrap hfw.1 hfw.2 hnb
    refine ⟨Y, Z, ?_, hYlo, hYhi, hZlo, hZhi, hnb'⟩
    rw [hstep', hchain, hYZ]

/-- On a positive decimal, the fixed routine returns the floored root. -/
theorem sqrt_correct_nat {a : Nat} (ha1 : 1 ≤ a) (haMax : a ≤ 2 ^ 167 - 1) :
    vyperSqrtWith (fun y z => if y < z then y else z) (a : Int)
      = some ((Nat.sqrt (newtonN a) : Nat) : Int) := by
  have hpos := vyperSqrtWith_pos (fun y z => if y < z then y else z) (by omega) haMax
  rw [hpos]
  obtain ⟨Y, Z, hloop, hYlo, hYhi, hZlo, hZhi, hnb⟩ := loop_final ha1 haMax
  rw [hloop, Option.map_some]
  have hmin : (if (Y : Int) < (Z : Int) then (Y : Int) else (Z : Int))
      = ((Nat.sqrt (newtonN a) : Nat) : Int) := by
    rcases (by omega : Y = Nat.sqrt (newtonN a) ∨ Y = Nat.sqrt (newtonN a) + 1)
      with rfl | rfl
    · rcases (by omega : Z = Nat.sqrt (newtonN a) ∨ Z = Nat.sqrt (newtonN a) + 1)
        with rfl | rfl
      · rw [if_neg (by omega)]
      · rw [if_pos (by omega)]
    · rcases (by omega : Z = Nat.sqrt (newtonN a) ∨ Z = Nat.sqrt (newtonN a) + 1)
        with rfl | rfl
      · rw [if_neg (by omega)]
      · exact absurd ⟨rfl, rfl⟩ hnb
  exact congrArg _ hmin

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

/-- The routine returns `some 0` on `0`. -/
theorem sqrt_zero : sqrt 0 = some 0 := by
  show vyperSqrtWith (fun y z => if y < z then y else z) (0 : Int) = some 0
  unfold vyperSqrtWith
  rw [if_neg (by decide), if_pos rfl]

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := by
  intro x r hdec hsqrt
  by_cases hx : x < 0
  · have hnone : sqrt x = none := by
      show vyperSqrtWith (fun y z => if y < z then y else z) x = none
      unfold vyperSqrtWith
      rw [if_pos hx]
    rw [hnone] at hsqrt
    simp at hsqrt
  · have hnn : 0 ≤ x := by omega
    have hxa : x = ((x.toNat : Nat) : Int) := (Int.toNat_of_nonneg hnn).symm
    have haMax : x.toNat ≤ 2 ^ 167 - 1 := by
      have h2 := hdec.2
      rw [max_decimal_eq, hxa] at h2
      exact_mod_cast h2
    by_cases ha0 : x.toNat = 0
    · have hx0 : x = 0 := by
        have hle : x ≤ 0 := Int.toNat_eq_zero.mp ha0
        omega
      rw [hx0, sqrt_zero] at hsqrt
      have hr0 : r = 0 := (Option.some_inj.mp hsqrt).symm
      rw [hr0, hx0]
      decide
    · have ha1' : 1 ≤ x.toNat := by omega
      have e := sqrt_correct_nat ha1' haMax
      have hxr : sqrt x = some ((Nat.sqrt (newtonN x.toNat) : Nat) : Int) := by
        rw [hxa]
        show vyperSqrtWith (fun y z => if y < z then y else z) _ = _
        exact e
      have hr : r = ((Nat.sqrt (newtonN x.toNat) : Nat) : Int) := by
        rw [hxr] at hsqrt
        exact (Option.some_inj.mp hsqrt).symm
      have h1 : ((Nat.sqrt (newtonN x.toNat) : Nat) : Int)
          * ((Nat.sqrt (newtonN x.toNat) : Nat) : Int)
          ≤ ((newtonN x.toNat : Nat) : Int) := by
        exact_mod_cast Nat.sqrt_le _
      have h2 : ((newtonN x.toNat : Nat) : Int) = x * DIVISOR := by
        have eN : newtonN x.toNat = x.toNat * 10 ^ 10 := rfl
        rw [eN, Int.natCast_mul, divisor_eq, ← hxa]
      rw [hr, ← h2]
      exact h1

theorem req_sqrt_not_below   : SqrtNotBelow sqrt := by
  intro x r hdec hsqrt
  by_cases hx : x < 0
  · have hnone : sqrt x = none := by
      show vyperSqrtWith (fun y z => if y < z then y else z) x = none
      unfold vyperSqrtWith
      rw [if_pos hx]
    rw [hnone] at hsqrt
    simp at hsqrt
  · have hnn : 0 ≤ x := by omega
    have hxa : x = ((x.toNat : Nat) : Int) := (Int.toNat_of_nonneg hnn).symm
    have haMax : x.toNat ≤ 2 ^ 167 - 1 := by
      have h2 := hdec.2
      rw [max_decimal_eq, hxa] at h2
      exact_mod_cast h2
    by_cases ha0 : x.toNat = 0
    · have hx0 : x = 0 := by
        have hle : x ≤ 0 := Int.toNat_eq_zero.mp ha0
        omega
      rw [hx0, sqrt_zero] at hsqrt
      have hr0 : r = 0 := (Option.some_inj.mp hsqrt).symm
      rw [hr0, hx0]
      decide
    · have ha1' : 1 ≤ x.toNat := by omega
      have e := sqrt_correct_nat ha1' haMax
      have hxr : sqrt x = some ((Nat.sqrt (newtonN x.toNat) : Nat) : Int) := by
        rw [hxa]
        show vyperSqrtWith (fun y z => if y < z then y else z) _ = _
        exact e
      have hr : r = ((Nat.sqrt (newtonN x.toNat) : Nat) : Int) := by
        rw [hxr] at hsqrt
        exact (Option.some_inj.mp hsqrt).symm
      have h3 : ((newtonN x.toNat : Nat) : Int)
          < (((Nat.sqrt (newtonN x.toNat) : Nat) : Int) + 1)
            * (((Nat.sqrt (newtonN x.toNat) : Nat) : Int) + 1) := by
        exact_mod_cast sqrt_upper _
      have h2 : ((newtonN x.toNat : Nat) : Int) = x * DIVISOR := by
        have eN : newtonN x.toNat = x.toNat * 10 ^ 10 := rfl
        rw [eN, Int.natCast_mul, divisor_eq, ← hxa]
      rw [hr, ← h2]
      exact h3

theorem req_sqrt_total       : SqrtTotal sqrt := by
  intro x hdec hnn
  show (vyperSqrtWith (fun y z => if y < z then y else z) x).isSome
  have hxa : x = ((x.toNat : Nat) : Int) := (Int.toNat_of_nonneg hnn).symm
  have haMax : x.toNat ≤ 2 ^ 167 - 1 := by
    have h2 := hdec.2
    rw [max_decimal_eq, hxa] at h2
    exact_mod_cast h2
  by_cases ha0 : x.toNat = 0
  · have hx0 : x = 0 := by
      have hle : x ≤ 0 := Int.toNat_eq_zero.mp ha0
      omega
    rw [hx0]
    show (sqrt 0).isSome
    rw [sqrt_zero]
    rfl
  · have ha1' : 1 ≤ x.toNat := by omega
    have e := sqrt_correct_nat ha1' haMax
    rw [hxa, e]
    rfl

theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith (fun y z => if y < z then y else z) x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop    : DeployedLoop sqrt := by
  exact ⟨(fun y z => if y < z then y else z), fun x => rfl⟩

end VyperSqrt
