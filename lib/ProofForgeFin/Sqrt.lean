/-!
# The integer square root and the Newton step

Facts about Lean core's `Nat.sqrt` (the floor of the square root, `Nat.sqrt_le` and
`Nat.lt_succ_sqrt`) and about one step of Newton's method on natural numbers,
`newton a x = (x + a / x) / 2`, the step integer square-root routines repeat. Write
`s = Nat.sqrt a` and `x - s` for the error of an iterate above the root.

* The root from its bounds: `sqrt_eq_of_bounds` (uniqueness), `le_sqrt_of_mul_self_le`,
  `sqrt_lt_of_lt_mul_self`, `sqrt_le_sqrt`, and powers of two: `two_pow_le_sqrt`
  (`2^(2k) ≤ a → 2^k ≤ s`), `sqrt_lt_two_pow` (`a < 2^(2k) → s < 2^k`).
* AM-GM with floors: from any positive iterate the step never goes below the root
  (`sqrt_le_newton`); `two_mul_newton_mul_le` (`2 * newton a x * x ≤ x * x + a`).
* The exact error relation: `newton_err_above` (`s ≤ x`) and `newton_err_below` (`x ≤ s`) give
  `2 * x * (newton a x - s) ≤ d * d + 2 * s` for the distance `d` between `x` and `s`.
* Its consequences above the root: quadratic convergence `newton_sub_sqrt_le_sq_div`
  (`newton a x - s ≤ (x - s)^2 / (2 * s) + 1`), the halving bound `newton_sub_sqrt_le_half`
  (`newton a x - s ≤ (x - s) / 2 + 1`), strict decrease `newton_lt_self` (`s < x`), and the only
  fixed point `eq_sqrt_of_newton_eq_self`.
* The end of the iteration: `newton_le_sqrt_add_one` (a square error at most `2 * s` gives the root
  or the root plus one), `newton_eq_or_succ` (a square error at most `s` gives the root, or the
  root plus one with `s * (s + 1) ≤ a`), `newton_of_mem` (from the root or the root plus one the
  step stays there), and the corrections that return the root: `min_div_eq_sqrt`
  (`min x (a / x)`), `sub_ite_eq_sqrt` (`x - 1` when `a / x < x`), `min_newton_eq_sqrt`
  (the smaller of two successive iterates).
-/

namespace ProofForgeFin.Sqrt

/-- One step of Newton's method for the square root of `a` on natural numbers, from the iterate
`x`: `(x + a / x) / 2`, both divisions rounded down. -/
def newton (a x : Nat) : Nat := (x + a / x) / 2

/-! ## The root from its bounds -/

/-- AM-GM on natural numbers: `4 * u * v ≤ (u + v) * (u + v)`. -/
theorem four_mul_le_sq (u v : Nat) : 4 * u * v ≤ (u + v) * (u + v) := by
  rcases Nat.le_total u v with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; grind
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; grind

/-- Squares are monotone: `m ≤ n → m * m ≤ n * n`. -/
theorem mul_self_le_mul_self {m n : Nat} (h : m ≤ n) : m * m ≤ n * n := Nat.mul_le_mul h h

/-- Squares reflect strict order: `m * m < n * n → m < n`. -/
theorem lt_of_mul_self_lt_mul_self {m n : Nat} (h : m * m < n * n) : m < n := by
  rcases Nat.lt_or_ge m n with h' | h'
  · exact h'
  · exact absurd h (Nat.not_lt.mpr (mul_self_le_mul_self h'))

/-- Any `m` with `m * m ≤ a` is at most the root. -/
theorem le_sqrt_of_mul_self_le {m a : Nat} (h : m * m ≤ a) : m ≤ Nat.sqrt a := by
  have := Nat.lt_succ_sqrt a
  exact Nat.le_of_lt_succ (lt_of_mul_self_lt_mul_self (Nat.lt_of_le_of_lt h this))

/-- Any `m` with `a < m * m` is above the root. -/
theorem sqrt_lt_of_lt_mul_self {m a : Nat} (h : a < m * m) : Nat.sqrt a < m :=
  lt_of_mul_self_lt_mul_self (Nat.lt_of_le_of_lt (Nat.sqrt_le a) h)

/-- The root is the unique `r` with `r * r ≤ a < (r + 1) * (r + 1)`. -/
theorem sqrt_eq_of_bounds {r a : Nat} (h1 : r * r ≤ a) (h2 : a < (r + 1) * (r + 1)) :
    Nat.sqrt a = r :=
  Nat.le_antisymm (Nat.le_of_lt_succ (sqrt_lt_of_lt_mul_self h2)) (le_sqrt_of_mul_self_le h1)

/-- `r = Nat.sqrt a` exactly when `r * r ≤ a < (r + 1) * (r + 1)`. -/
theorem eq_sqrt_iff {r a : Nat} : r = Nat.sqrt a ↔ r * r ≤ a ∧ a < (r + 1) * (r + 1) := by
  constructor
  · rintro rfl; exact ⟨Nat.sqrt_le a, Nat.lt_succ_sqrt a⟩
  · rintro ⟨h1, h2⟩; exact (sqrt_eq_of_bounds h1 h2).symm

/-- The root is monotone. -/
theorem sqrt_le_sqrt {a b : Nat} (h : a ≤ b) : Nat.sqrt a ≤ Nat.sqrt b :=
  le_sqrt_of_mul_self_le (Nat.le_trans (Nat.sqrt_le a) h)

/-- The root of `m * m` is `m`. -/
theorem sqrt_mul_self (m : Nat) : Nat.sqrt (m * m) = m :=
  sqrt_eq_of_bounds (Nat.le_refl _) (Nat.mul_self_lt_mul_self (Nat.lt_succ_self m))

/-- The root of a positive number is positive. -/
theorem sqrt_pos {a : Nat} (h : 0 < a) : 0 < Nat.sqrt a :=
  le_sqrt_of_mul_self_le (m := 1) (by omega)

/-- `2^(2k) ≤ a` gives `2^k ≤ Nat.sqrt a`. -/
theorem two_pow_le_sqrt {k a : Nat} (h : 2 ^ (2 * k) ≤ a) : 2 ^ k ≤ Nat.sqrt a := by
  apply le_sqrt_of_mul_self_le
  rw [← Nat.pow_add, show k + k = 2 * k by omega]; exact h

/-- `a < 2^(2k)` gives `Nat.sqrt a < 2^k`. -/
theorem sqrt_lt_two_pow {k a : Nat} (h : a < 2 ^ (2 * k)) : Nat.sqrt a < 2 ^ k := by
  apply sqrt_lt_of_lt_mul_self
  rw [← Nat.pow_add, show k + k = 2 * k by omega]; exact h

/-! ## One Newton step -/

/-- The step times twice the iterate is at most `x * x + a`. -/
theorem two_mul_newton_mul_le (a x : Nat) : 2 * newton a x * x ≤ x * x + a := by
  unfold newton
  have h1 : 2 * ((x + a / x) / 2) ≤ x + a / x := Nat.mul_div_le _ 2
  have h2 : a / x * x ≤ a := Nat.div_mul_le_self a x
  have h3 : 2 * ((x + a / x) / 2) * x ≤ (x + a / x) * x := Nat.mul_le_mul_right x h1
  rw [Nat.add_mul] at h3
  omega

/-- AM-GM with floors: from any positive iterate, one step never goes below the root. -/
theorem sqrt_le_newton {a x : Nat} (hx : 0 < x) : Nat.sqrt a ≤ newton a x := by
  unfold newton
  apply Nat.le_div_iff_mul_le (by decide) |>.mpr
  -- `a < (a / x + 1) * x`, AM-GM on `x` and `a / x + 1`, and `s * s ≤ a`
  have hq : a < (a / x + 1) * x := by
    rw [Nat.succ_mul]; exact Nat.lt_div_mul_add hx
  have hs := Nat.sqrt_le a
  have amgm := four_mul_le_sq x (a / x + 1)
  apply Nat.le_of_not_lt
  intro hlt
  have h2 : x + (a / x + 1) ≤ Nat.sqrt a * 2 := by omega
  have h3 := mul_self_le_mul_self h2
  have : 4 * x * (a / x + 1) ≤ 4 * a := by
    have := Nat.le_trans amgm h3
    have e : Nat.sqrt a * 2 * (Nat.sqrt a * 2) = 4 * (Nat.sqrt a * Nat.sqrt a) := by grind
    rw [e] at this; omega
  have : 4 * a < 4 * x * (a / x + 1) := by
    rw [Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_left (by rw [Nat.mul_comm]; exact hq) (by decide)
  omega

/-- The exact error relation above the root: for `s ≤ x`,
`2 * x * (newton a x - s) ≤ (x - s) * (x - s) + 2 * s`. -/
theorem newton_err_above {a x : Nat} (hx : 0 < x) (h : Nat.sqrt a ≤ x) :
    2 * x * (newton a x - Nat.sqrt a) ≤ (x - Nat.sqrt a) * (x - Nat.sqrt a) + 2 * Nat.sqrt a := by
  have hn := sqrt_le_newton (a := a) hx
  have h1 := two_mul_newton_mul_le a x
  have h2 := Nat.lt_succ_sqrt a
  generalize Nat.sqrt a = s at *
  generalize newton a x = n at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left]
  have : a ≤ s * s + 2 * s := by simp only [Nat.succ_eq_add_one] at h2; grind
  grind

/-- The exact error relation below the root: for `0 < x ≤ s`,
`2 * x * (newton a x - s) ≤ (s - x) * (s - x) + 2 * s`. -/
theorem newton_err_below {a x : Nat} (hx : 0 < x) (h : x ≤ Nat.sqrt a) :
    2 * x * (newton a x - Nat.sqrt a) ≤ (Nat.sqrt a - x) * (Nat.sqrt a - x) + 2 * Nat.sqrt a := by
  have hn := sqrt_le_newton (a := a) hx
  have h1 := two_mul_newton_mul_le a x
  have h2 := Nat.lt_succ_sqrt a
  generalize Nat.sqrt a = s at *
  generalize newton a x = n at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left]
  have : a ≤ (x + d) * (x + d) + 2 * (x + d) := by simp only [Nat.succ_eq_add_one] at h2; grind
  grind

/-- Quadratic convergence above a positive root: the error after one step is at most the square
of the error over twice the root, plus one unit for the floors. -/
theorem newton_sub_sqrt_le_sq_div {a x : Nat} (hs : 0 < Nat.sqrt a) (h : Nat.sqrt a ≤ x) :
    newton a x - Nat.sqrt a ≤ (x - Nat.sqrt a) * (x - Nat.sqrt a) / (2 * Nat.sqrt a) + 1 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le hs h
  have e := newton_err_above (a := a) hx h
  generalize Nat.sqrt a = s at *
  generalize newton a x - s = m at *
  have h2 : 2 * s * m ≤ 2 * x * m := Nat.mul_le_mul_right m (by omega)
  have h3 : 2 * s * m ≤ (x - s) * (x - s) + 2 * s * 1 := by omega
  rw [← Nat.add_mul_div_left _ _ (by omega : 0 < 2 * s)]
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  rw [Nat.mul_comm]; omega

/-- The halving bound above the root: the error after one step is at most half the error plus
one unit. Useful far from the root, where the quadratic bound is weak. -/
theorem newton_sub_sqrt_le_half {a x : Nat} (hx : 0 < x) (h : Nat.sqrt a ≤ x) :
    newton a x - Nat.sqrt a ≤ (x - Nat.sqrt a) / 2 + 1 := by
  have e := newton_err_above (a := a) hx h
  generalize Nat.sqrt a = s at *
  generalize newton a x - s = m at *
  have h1 : (x - s) * (x - s) ≤ (x - s) * x := Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 * s ≤ 2 * x := by omega
  -- `2 * x * m ≤ (x - s + 2) * x`
  have h3 : 2 * m * x ≤ (x - s + 2) * x := by
    rw [Nat.add_mul]; rw [show 2 * m * x = 2 * x * m by grind]; omega
  have h4 : 2 * m ≤ x - s + 2 := Nat.le_of_mul_le_mul_right h3 hx
  omega

/-- Above the root the step strictly decreases. -/
theorem newton_lt_self {a x : Nat} (h : Nat.sqrt a < x) : newton a x < x := by
  unfold newton
  have hx : 0 < x := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have hsq : a < x * x := by
    have := Nat.lt_succ_sqrt a
    exact Nat.lt_of_lt_of_le this (mul_self_le_mul_self h)
  have : a / x < x := (Nat.div_lt_iff_lt_mul hx).mpr hsq
  omega

/-- The only positive fixed point of the step is the root. -/
theorem eq_sqrt_of_newton_eq_self {a x : Nat} (hx : 0 < x) (h : newton a x = x) :
    x = Nat.sqrt a := by
  have h1 := sqrt_le_newton (a := a) hx
  rcases Nat.lt_or_ge (Nat.sqrt a) x with h2 | h2
  · exact absurd h (Nat.ne_of_lt (newton_lt_self h2))
  · omega

/-! ## The end of the iteration -/

/-- A square error at most `2 * s` above the root: one step gives the root or the root plus one. -/
theorem newton_le_sqrt_add_one {a x : Nat} (hx : 0 < x) (h : Nat.sqrt a ≤ x)
    (hd : (x - Nat.sqrt a) * (x - Nat.sqrt a) ≤ 2 * Nat.sqrt a) : newton a x ≤ Nat.sqrt a + 1 := by
  have e := newton_err_above (a := a) hx h
  have hn := sqrt_le_newton (a := a) hx
  generalize Nat.sqrt a = s at *
  generalize newton a x = n at *
  apply Nat.le_of_not_lt
  intro hlt
  have h2 : 2 * x * 2 ≤ 2 * x * (n - s) := Nat.mul_le_mul_left _ (by omega)
  have : x ≤ s := by omega
  have hxs : x = s := by omega
  subst hxs
  simp at e
  have : 2 * x * 2 ≤ 2 * x := by omega
  omega

/-- A square error at most `s` above the root: one step gives the root, or the root plus one and
then `s * (s + 1) ≤ a`. -/
theorem newton_eq_or_succ {a x : Nat} (hx : 0 < x) (h : Nat.sqrt a ≤ x)
    (hd : (x - Nat.sqrt a) * (x - Nat.sqrt a) ≤ Nat.sqrt a) :
    newton a x = Nat.sqrt a ∨ (newton a x = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a) := by
  have hle := newton_le_sqrt_add_one (a := a) hx h (by omega)
  have hn := sqrt_le_newton (a := a) hx
  have h1 := two_mul_newton_mul_le a x
  rcases Nat.lt_or_ge (newton a x) (Nat.sqrt a + 1) with h2 | h2
  · left; omega
  · right
    have hn1 : newton a x = Nat.sqrt a + 1 := by omega
    refine ⟨hn1, ?_⟩
    rw [hn1] at h1
    generalize Nat.sqrt a = s at *
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_sub_cancel_left] at hd
    -- `a ≥ 2 * (s + 1) * (s + d) - (s + d)^2 = s * s + 2 * s + 2 * d - d * d`
    grind

/-- From the root or the root plus one, the step gives the root, except from the root itself when
`s * s + 2 * s ≤ a` (then `a + 1` is a square), where it gives the root plus one: the iterates
alternate between the two. -/
theorem newton_of_mem {a x : Nat} (hx : 0 < x) (h1 : Nat.sqrt a ≤ x) (h2 : x ≤ Nat.sqrt a + 1) :
    newton a x = Nat.sqrt a ∨
      (x = Nat.sqrt a ∧ newton a x = Nat.sqrt a + 1 ∧ Nat.sqrt a * Nat.sqrt a + 2 * Nat.sqrt a ≤ a) := by
  have hn := sqrt_le_newton (a := a) hx
  have hup := Nat.lt_succ_sqrt a
  have hlo := Nat.sqrt_le a
  generalize Nat.sqrt a = s at *
  simp only [Nat.succ_eq_add_one] at hup
  unfold newton at *
  rcases (show x = s ∨ x = s + 1 by omega) with rfl | rfl
  · -- `a / x ≤ x + 2`
    have : a / x < x + 3 := (Nat.div_lt_iff_lt_mul hx).mpr (by grind)
    rcases Nat.lt_or_ge (a / x) (x + 2) with h3 | h3
    · left; omega
    · right
      have : (x + 2) * x ≤ a := (Nat.le_div_iff_mul_le hx).mp h3
      refine ⟨rfl, ?_, ?_⟩
      · omega
      · grind
  · left
    have : a / (s + 1) < s + 1 := (Nat.div_lt_iff_lt_mul hx).mpr hup
    omega

/-- The final correction `min x (a / x)` returns the root from the root, or from the root plus one
when `s * (s + 1) ≤ a`. -/
theorem min_div_eq_sqrt {a x : Nat} (hx : 0 < x)
    (h : x = Nat.sqrt a ∨ (x = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a)) :
    min x (a / x) = Nat.sqrt a := by
  have hup := Nat.lt_succ_sqrt a
  have hlo := Nat.sqrt_le a
  generalize Nat.sqrt a = s at *
  simp only [Nat.succ_eq_add_one] at hup
  rcases h with rfl | ⟨rfl, h⟩
  · have : x ≤ a / x := (Nat.le_div_iff_mul_le hx).mpr hlo
    omega
  · have h1 : s ≤ a / (s + 1) := (Nat.le_div_iff_mul_le hx).mpr h
    have h2 : a / (s + 1) < s + 1 := (Nat.div_lt_iff_lt_mul hx).mpr hup
    omega

/-- The final correction `x - (if a / x < x then 1 else 0)` returns the root under the
hypotheses of `min_div_eq_sqrt`. -/
theorem sub_ite_eq_sqrt {a x : Nat} (hx : 0 < x)
    (h : x = Nat.sqrt a ∨ (x = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a)) :
    x - (if a / x < x then 1 else 0) = Nat.sqrt a := by
  have hup := Nat.lt_succ_sqrt a
  have hlo := Nat.sqrt_le a
  generalize Nat.sqrt a = s at *
  simp only [Nat.succ_eq_add_one] at hup
  rcases h with rfl | ⟨rfl, h⟩
  · have : x ≤ a / x := (Nat.le_div_iff_mul_le hx).mpr hlo
    rw [ite_eq_right (by omega)]; rfl
  · have h2 : a / (s + 1) < s + 1 := (Nat.div_lt_iff_lt_mul hx).mpr hup
    rw [ite_eq_left h2]; rfl

/-- The smaller of an iterate at the root or the root plus one and the next iterate is the root. -/
theorem min_newton_eq_sqrt {a x : Nat} (hx : 0 < x) (h1 : Nat.sqrt a ≤ x) (h2 : x ≤ Nat.sqrt a + 1) :
    min x (newton a x) = Nat.sqrt a := by
  have hn := sqrt_le_newton (a := a) hx
  have hm := newton_of_mem hx h1 h2
  generalize Nat.sqrt a = s at *
  generalize newton a x = n at *
  rw [Nat.min_def]
  split <;> omega

end ProofForgeFin.Sqrt
