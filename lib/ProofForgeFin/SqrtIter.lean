import ProofForgeFin.Sqrt
/-!
# Newton iteration for the integer square root

`newtonIter a k x` applies `k` steps of `newton a x = (x + a / x) / 2` to `x`. Write
`s = Nat.sqrt a`.

* Unfolding: `newtonIter_succ` (the first step first), `newtonIter_succ'` (the last step last),
  `newtonIter_add`, `newtonIter_eq_repeat` (`Nat.repeat` of the step).
* Staying above the root: `sqrt_le_newton_of_le`, `sqrt_le_newtonIter`,
  `sqrt_le_newtonIter_of_le`; bounded by the start: `newton_le_max`, `newtonIter_le_max`.
* The error after `k` steps above the root, for any start `x` with `s ≤ x`:
  `newtonIter_sub_sqrt_le_half_pow` (`(x - s) / 2^k + 2`), and in relative form
  `newton_sub_sqrt_le_div_mul` (an error at most `s / m + 2` becomes at most
  `s / (2 * m * m) + 2`) and `newtonIter_sub_sqrt_le_two_pow` (an error at most `s / 2^j + 2`
  becomes at most `s / 2^((j + 1) * 2^k - 1) + 2` after `k` steps).
* From below the root: `newton_sub_sqrt_le_of_le` (any positive `x ≤ s`) and
  `newton_sub_sqrt_le_of_lt_two_mul` (`x ≤ s < 2 * x` gives an error at most `s / 4 + 2`);
  `newtonIter_sub_sqrt_le_of_lt_two_mul`: after `k + 1` steps from such an `x` the error is at
  most `s / 2^(3 * 2^k - 1) + 2`.
* Reaching the root or the root plus one: `newton_eq_or_succ_of_le_add_two` (from `s ≤ x ≤ s + 2`),
  `mul_self_le_of_le_div_add_two`, `newton_eq_or_succ_of_err` (an error at most `s / m + 2` with
  `s / m + 8 ≤ m`), `div_two_pow_add_eight_le` (the size condition from `s < 2^b`),
  `newtonIter_eq_or_succ_of_lt_two_mul` (from `x ≤ s < 2 * x`, `k + 2` steps suffice when
  `s < 2^b` and `b + 3 ≤ 2 * (3 * 2^k - 1)`), and `newtonIter_of_mem` (once at the root or the
  root plus one, every later iterate is the root or the root plus one).
* Power-of-two estimates through `Nat.log2`: `two_pow_half_log2_le_sqrt` and
  `sqrt_lt_two_mul_two_pow_half_log2` (`2^(log2 a / 2) ≤ s < 2 * 2^(log2 a / 2)` for `0 < a`).
* Sizes for machine words: `add_div_le_of_sqrt_le` (`x + a / x ≤ x + s + 2` above a positive
  root), `div_lt_of_sqrt_lt_mul`, `sqrt_lt_two_pow_of_lt` and `mul_self_sqrt_lt_two_pow`.
* The root rounded up: `le_mul_self_sqrt_add_ite` and `sqrt_add_ite_sub_one_mul_self_lt`; the
  order of the root as equivalences: `le_sqrt_iff`, `sqrt_lt_iff`, `lt_sqrt_add_one_mul_self`.
* Error bounds in multiplicative form, `e * D ≤ s + c * D`: `le_div_add_of_mul_le`,
  `div_add_le_of_add_mul_le` and `mul_self_le_of_mul_le` (the final squaring with an arbitrary
  scale `D`).
* Squares and powers of two without `ring`: `add_mul_self_eq`, `sub_mul_self_add_eq`,
  `two_mul_le_add_mul_self`, `two_pow_mul_two_pow`, `two_mul_mul_two_mul`,
  `two_pow_sub_mul_two_pow`, `div_mul_div_le`, `mul_self_lt_mul_self_iff`,
  `mul_self_le_mul_self_iff`, `lt_two_pow_of_mul_self_lt`.
* The root by structural search, which `decide` evaluates on literals (it does not unfold
  `Nat.sqrt`): `sqrtSearch`, `sqrtSearch_eq_min`, `sqrt_eq_sqrtSearch`, `sqrt_le_self`.
* Newton steps on `w`-bit words: `toNat_newton_word` (`((x + a / x) >>> 1).toNat` is `newton` on
  the values when the sum does not wrap), `toNat_newton_word_of_sqrt_le`, `sqrt_toNat_lt_two_pow`.
-/

namespace ProofForgeFin.Sqrt

/-- `newtonIter a k x`: `k` Newton steps for the root of `a`, starting from `x`. -/
def newtonIter (a : Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => newtonIter a k (newton a x)

/-! ## Unfolding -/

/-- No step leaves the start. -/
theorem newtonIter_zero (a x : Nat) : newtonIter a 0 x = x := rfl

/-- `k + 1` steps: the first step, then `k` steps. -/
theorem newtonIter_succ (a k x : Nat) : newtonIter a (k + 1) x = newtonIter a k (newton a x) := rfl

/-- `k + 1` steps: `k` steps, then one more. -/
theorem newtonIter_succ' (a k x : Nat) : newtonIter a (k + 1) x = newton a (newtonIter a k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [newtonIter_succ, ih, newtonIter_succ]

/-- `j + k` steps are `j` steps and then `k` steps. -/
theorem newtonIter_add (a j k x : Nat) : newtonIter a (j + k) x = newtonIter a k (newtonIter a j x) := by
  induction j generalizing x with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih => rw [Nat.add_right_comm, newtonIter_succ, ih, newtonIter_succ]

/-- One step is `newton`. -/
theorem newtonIter_one (a x : Nat) : newtonIter a 1 x = newton a x := rfl

/-! ## Staying above the root -/

/-- From any iterate at or above the root, the step stays at or above the root. -/
theorem sqrt_le_newton_of_le {a x : Nat} (h : Nat.sqrt a ≤ x) : Nat.sqrt a ≤ newton a x := by
  rcases Nat.eq_zero_or_pos (Nat.sqrt a) with h0 | h0
  · rw [h0]; exact Nat.zero_le _
  · exact sqrt_le_newton (Nat.lt_of_lt_of_le h0 h)

/-- From an iterate at or above the root, every later iterate is at or above the root. -/
theorem sqrt_le_newtonIter_of_le {a x : Nat} (k : Nat) (h : Nat.sqrt a ≤ x) :
    Nat.sqrt a ≤ newtonIter a k x := by
  induction k with
  | zero => exact h
  | succ k ih => rw [newtonIter_succ']; exact sqrt_le_newton_of_le ih

/-- From any positive start, every iterate after the first step is at or above the root. -/
theorem sqrt_le_newtonIter {a x k : Nat} (hx : 0 < x) (hk : 0 < k) : Nat.sqrt a ≤ newtonIter a k x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [Nat.zero_add, newtonIter_succ]
  exact sqrt_le_newtonIter_of_le j (sqrt_le_newton hx)

/-- The iterates of a positive start stay positive when the root is positive. -/
theorem newtonIter_pos {a x : Nat} (k : Nat) (hs : 0 < Nat.sqrt a) (hx : 0 < x) : 0 < newtonIter a k x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hx
  · exact Nat.lt_of_lt_of_le hs (sqrt_le_newtonIter hx hk)

/-- At or above the root, the step is at most the larger of the iterate and the root plus one. -/
theorem newton_le_max {a x : Nat} (h : Nat.sqrt a ≤ x) : newton a x ≤ max x (Nat.sqrt a + 1) := by
  rcases Nat.lt_or_ge (Nat.sqrt a) x with h1 | h1
  · have := newton_lt_self h1; omega
  · have hx : x = Nat.sqrt a := Nat.le_antisymm h1 h
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · have : newton a x = 0 := by rw [h0]; unfold newton; rw [Nat.div_zero]
      omega
    · have := newton_le_sqrt_add_one (a := a) h0 h (by rw [hx, Nat.sub_self]; exact Nat.zero_le _)
      omega

/-- From an iterate at or above the root, every later iterate is at most the larger of the start
and the root plus one. -/
theorem newtonIter_le_max {a x : Nat} (k : Nat) (h : Nat.sqrt a ≤ x) :
    newtonIter a k x ≤ max x (Nat.sqrt a + 1) := by
  induction k with
  | zero => exact Nat.le_max_left _ _
  | succ k ih =>
    rw [newtonIter_succ']
    have := newton_le_max (sqrt_le_newtonIter_of_le k h)
    omega

/-! ## The error after `k` steps above the root -/

/-- The halving bound with no positivity hypothesis: at or above the root the error after one
step is at most half the error plus one. -/
theorem newton_sub_sqrt_le_half' {a x : Nat} (h : Nat.sqrt a ≤ x) :
    newton a x - Nat.sqrt a ≤ (x - Nat.sqrt a) / 2 + 1 := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · have : newton a x = 0 := by rw [h0]; unfold newton; rw [Nat.div_zero]
    omega
  · exact newton_sub_sqrt_le_half h0 h

/-- The error after `k` steps from any start at or above the root is at most the starting error
divided by `2^k`, plus two. -/
theorem newtonIter_sub_sqrt_le_half_pow {a x : Nat} (k : Nat) (h : Nat.sqrt a ≤ x) :
    newtonIter a k x - Nat.sqrt a ≤ (x - Nat.sqrt a) / 2 ^ k + 2 := by
  induction k with
  | zero => rw [Nat.pow_zero, Nat.div_one]; exact Nat.le_add_right _ _
  | succ k ih =>
    rw [newtonIter_succ']
    have h1 := newton_sub_sqrt_le_half' (sqrt_le_newtonIter_of_le k h)
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    generalize (x - Nat.sqrt a) / 2 ^ k = q at ih ⊢
    omega

/-- Quadratic convergence in relative form: at or above a positive root, an error at most
`s / m + 2` becomes at most `s / (2 * m * m) + 2` after one step. -/
theorem newton_sub_sqrt_le_div_mul {a x m : Nat} (hs : 0 < Nat.sqrt a) (hm : 0 < m)
    (h : Nat.sqrt a ≤ x) (hd : x - Nat.sqrt a ≤ Nat.sqrt a / m + 2) :
    newton a x - Nat.sqrt a ≤ Nat.sqrt a / (2 * m * m) + 2 := by
  have hx : 0 < x := Nat.lt_of_lt_of_le hs h
  have e := newton_err_above (a := a) hx h
  generalize Nat.sqrt a = s at *
  generalize newton a x - s = m' at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left] at hd e
  generalize hq : s / m = q at hd
  generalize hQ : s / (2 * m * m) = Q
  have hqm : q * m ≤ s := by rw [← hq]; exact Nat.div_mul_le_self s m
  have hmm : 0 < 2 * m * m := Nat.mul_pos (Nat.mul_pos (by decide) hm) hm
  have hQs : s < (Q + 1) * (2 * m * m) := by
    rw [← hQ, Nat.succ_mul]; exact Nat.lt_div_mul_add hmm
  have hqs : q ≤ s := Nat.le_trans (Nat.le_mul_of_pos_right q hm) hqm
  -- `q * q < 2 * s * (Q + 1)`
  have h1 : q * m * (q * m) ≤ s * s := Nat.mul_le_mul hqm hqm
  have h2 : s * s < s * ((Q + 1) * (2 * m * m)) := Nat.mul_lt_mul_of_pos_left hQs hs
  have h3 : q * q * (m * m) < 2 * s * (Q + 1) * (m * m) := by
    have e1 : q * m * (q * m) = q * q * (m * m) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm m q m, ← Nat.mul_assoc]
    have e2 : s * ((Q + 1) * (2 * m * m)) = 2 * s * (Q + 1) * (m * m) := by
      rw [Nat.mul_assoc 2 m m, Nat.mul_comm (Q + 1), Nat.mul_assoc 2 (m * m), ← Nat.mul_assoc s,
        Nat.mul_comm s 2, Nat.mul_assoc 2 s, Nat.mul_comm (m * m) (Q + 1), Nat.mul_assoc 2 s,
        ← Nat.mul_assoc s, Nat.mul_assoc 2]
    omega
  have h4 : q * q < 2 * s * (Q + 1) := Nat.lt_of_mul_lt_mul_right h3
  -- `d * d ≤ q * q + 2 * q + 2 * d`
  have h5 : d * d ≤ d * (q + 2) := Nat.mul_le_mul_left d hd
  have h6 : d * q ≤ (q + 2) * q := Nat.mul_le_mul_right q hd
  apply Nat.le_of_not_lt
  intro hlt
  have h7 : 2 * (s + d) * (Q + 3) ≤ 2 * (s + d) * m' := Nat.mul_le_mul_left _ hlt
  have e3 : 2 * (s + d) * (Q + 3) = 2 * s * (Q + 1) + 4 * s + 2 * d * Q + 6 * d := by grind
  have e4 : d * (q + 2) = d * q + 2 * d := by grind
  have e5 : (q + 2) * q = q * q + 2 * q := by grind
  omega

/-- At or above a positive root, an error at most `s / 2^j + 2` becomes at most
`s / 2^((j + 1) * 2^k - 1) + 2` after `k` steps. -/
theorem newtonIter_sub_sqrt_le_two_pow {a x j : Nat} (k : Nat) (hs : 0 < Nat.sqrt a)
    (h : Nat.sqrt a ≤ x) (hd : x - Nat.sqrt a ≤ Nat.sqrt a / 2 ^ j + 2) :
    newtonIter a k x - Nat.sqrt a ≤ Nat.sqrt a / 2 ^ ((j + 1) * 2 ^ k - 1) + 2 := by
  induction k generalizing x j with
  | zero => rw [Nat.pow_zero, Nat.mul_one, Nat.add_sub_cancel]; exact hd
  | succ k ih =>
    rw [newtonIter_succ]
    have h1 := newton_sub_sqrt_le_div_mul hs (Nat.two_pow_pos j) h hd
    have e : 2 * 2 ^ j * 2 ^ j = 2 ^ (2 * j + 1) := by
      rw [Nat.pow_succ, Nat.two_mul j, Nat.pow_add, Nat.mul_comm (2 ^ j * 2 ^ j) 2, Nat.mul_assoc]
    rw [e] at h1
    have h2 := ih (sqrt_le_newton_of_le h) h1
    have e2 : (2 * j + 1 + 1) * 2 ^ k = (j + 1) * 2 ^ (k + 1) := by rw [Nat.pow_succ]; grind
    rw [e2] at h2
    exact h2

/-! ## From below the root -/

/-- From any positive iterate at or below the root, the error after one step is at most
`((s - x) * (s - x) + 2 * s) / (2 * x)`. -/
theorem newton_sub_sqrt_le_of_le {a x : Nat} (hx : 0 < x) (h : x ≤ Nat.sqrt a) :
    newton a x - Nat.sqrt a ≤ ((Nat.sqrt a - x) * (Nat.sqrt a - x) + 2 * Nat.sqrt a) / (2 * x) := by
  have e := newton_err_below (a := a) hx h
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  rw [Nat.mul_comm]; exact e

/-- From an iterate below the root by less than a factor of two (`x ≤ s < 2 * x`), the error after
one step is at most `s / 4 + 2`. -/
theorem newton_sub_sqrt_le_of_lt_two_mul {a x : Nat} (hx : 0 < x) (h1 : x ≤ Nat.sqrt a)
    (h2 : Nat.sqrt a < 2 * x) : newton a x - Nat.sqrt a ≤ Nat.sqrt a / 4 + 2 := by
  have e := newton_err_below (a := a) hx h1
  generalize Nat.sqrt a = s at *
  generalize newton a x - s = m at *
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
  rw [Nat.add_sub_cancel_left] at e
  generalize hQ : (x + t) / 4 = Q
  have hQs : x + t < (Q + 1) * 4 := by
    rw [← hQ, Nat.succ_mul]; exact Nat.lt_div_mul_add (by decide)
  apply Nat.le_of_not_lt
  intro hlt
  have h3 : 2 * x * (Q + 3) ≤ 2 * x * m := Nat.mul_le_mul_left _ (by omega)
  have h4 : x * (x + t) ≤ x * (4 * Q + 3) := Nat.mul_le_mul_left _ (by omega)
  have h5 : t * (t + 1) ≤ t * x := Nat.mul_le_mul_left _ (by omega)
  have h6 : (t + 1) * x ≤ x * x := Nat.mul_le_mul_right _ (by omega)
  have e1 : 2 * x * (Q + 3) = 2 * (x * Q) + 6 * x := by grind
  have e2 : x * (x + t) = x * x + t * x := by grind
  have e3 : x * (4 * Q + 3) = 4 * (x * Q) + 3 * x := by grind
  have e4 : t * (t + 1) = t * t + t := by grind
  have e5 : (t + 1) * x = t * x + x := by grind
  omega

/-- From an iterate below the root by less than a factor of two (`x ≤ s < 2 * x`), after `k + 1`
steps the iterate is at or above the root with an error at most `s / 2^(3 * 2^k - 1) + 2`. -/
theorem newtonIter_sub_sqrt_le_of_lt_two_mul {a x : Nat} (k : Nat) (hx : 0 < x) (h1 : x ≤ Nat.sqrt a)
    (h2 : Nat.sqrt a < 2 * x) :
    Nat.sqrt a ≤ newtonIter a (k + 1) x ∧
      newtonIter a (k + 1) x - Nat.sqrt a ≤ Nat.sqrt a / 2 ^ (3 * 2 ^ k - 1) + 2 := by
  have hs : 0 < Nat.sqrt a := Nat.lt_of_lt_of_le hx h1
  have l1 := sqrt_le_newton (a := a) hx
  have d1 := newton_sub_sqrt_le_of_lt_two_mul hx h1 h2
  rw [show Nat.sqrt a / 4 = Nat.sqrt a / 2 ^ 2 from rfl] at d1
  rw [newtonIter_succ]
  exact ⟨sqrt_le_newtonIter_of_le k l1, newtonIter_sub_sqrt_le_two_pow k hs l1 d1⟩

/-! ## Reaching the root or the root plus one -/

/-- From an iterate between the root and the root plus two, one step gives the root, or the root
plus one and then `s * (s + 1) ≤ a`. -/
theorem newton_eq_or_succ_of_le_add_two {a x : Nat} (hx : 0 < x) (h1 : Nat.sqrt a ≤ x)
    (h2 : x ≤ Nat.sqrt a + 2) :
    newton a x = Nat.sqrt a ∨ (newton a x = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a) := by
  rcases Nat.lt_or_ge x (Nat.sqrt a + 2) with h3 | h3
  · rcases newton_of_mem hx h1 (by omega) with h4 | ⟨_, h4, h5⟩
    · exact Or.inl h4
    · refine Or.inr ⟨h4, ?_⟩
      have : Nat.sqrt a * (Nat.sqrt a + 1) = Nat.sqrt a * Nat.sqrt a + Nat.sqrt a := by grind
      omega
  · have hn := sqrt_le_newton (a := a) hx
    have hup := Nat.lt_succ_sqrt a
    have hx2 : x = Nat.sqrt a + 2 := by omega
    unfold newton at *
    generalize Nat.sqrt a = s at *
    subst hx2
    simp only [Nat.succ_eq_add_one] at hup
    have hd : a / (s + 2) < s + 1 := (Nat.div_lt_iff_lt_mul hx).mpr (by grind)
    rcases Nat.lt_or_ge (a / (s + 2)) s with h4 | h4
    · left; omega
    · right
      have h5 : s * (s + 2) ≤ a := (Nat.le_div_iff_mul_le hx).mp h4
      refine ⟨by omega, ?_⟩
      have : s * (s + 1) ≤ s * (s + 2) := Nat.mul_le_mul_left s (by omega)
      omega

/-- An error at most `s / m + 2` squares to at most `s` when `4 ≤ s` and `s / m + 8 ≤ m`. -/
theorem mul_self_le_of_le_div_add_two {s m e : Nat} (hs : 4 ≤ s) (hm : s / m + 8 ≤ m)
    (he : e ≤ s / m + 2) : e * e ≤ s := by
  generalize hq : s / m = q at hm he
  have hqm : q * m ≤ s := by rw [← hq]; exact Nat.div_mul_le_self s m
  have h1 : e * e ≤ (q + 2) * (q + 2) := Nat.mul_le_mul he he
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0
    have : (0 + 2) * (0 + 2) = 4 := rfl
    omega
  · have h2 : q * (q + 8) ≤ q * m := Nat.mul_le_mul_left q hm
    have e1 : (q + 2) * (q + 2) = q * q + 4 * q + 4 := by grind
    have e2 : q * (q + 8) = q * q + 8 * q := by grind
    omega

/-- At or above the root with an error at most `s / m + 2`, where `s / m + 8 ≤ m`, one step gives
the root, or the root plus one and then `s * (s + 1) ≤ a`. -/
theorem newton_eq_or_succ_of_err {a x m : Nat} (hx : 0 < x) (h : Nat.sqrt a ≤ x)
    (hm : Nat.sqrt a / m + 8 ≤ m) (hd : x - Nat.sqrt a ≤ Nat.sqrt a / m + 2) :
    newton a x = Nat.sqrt a ∨ (newton a x = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a) := by
  rcases Nat.eq_zero_or_pos (Nat.sqrt a / m) with h0 | h0
  · exact newton_eq_or_succ_of_le_add_two hx h (by omega)
  · have hm0 : 0 < m := by omega
    have hqm : Nat.sqrt a / m * m ≤ Nat.sqrt a := Nat.div_mul_le_self _ m
    have h4 : 4 ≤ Nat.sqrt a := by
      have : 1 * m ≤ Nat.sqrt a / m * m := Nat.mul_le_mul_right m h0
      omega
    exact newton_eq_or_succ hx h (mul_self_le_of_le_div_add_two h4 hm hd)

/-- The size condition of `newton_eq_or_succ_of_err` at `m = 2^n` from `s < 2^b`, when `3 ≤ n`
and `b + 3 ≤ 2 * n`. -/
theorem div_two_pow_add_eight_le {s b n : Nat} (hs : s < 2 ^ b) (hn : 3 ≤ n) (hb : b + 3 ≤ 2 * n) :
    s / 2 ^ n + 8 ≤ 2 ^ n := by
  have e : 2 ^ n = 2 ^ (n - 3) * 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add, Nat.sub_add_cancel hn]
  have h1 : s < 2 ^ (n - 3) * 2 ^ n := by
    rw [← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega))
  have h2 : s / 2 ^ n < 2 ^ (n - 3) := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).mpr h1
  rw [e] at h2 ⊢
  have := Nat.two_pow_pos (n - 3)
  omega

/-- From a positive iterate below the root by less than a factor of two (`x ≤ s < 2 * x`),
`k + 2` steps give the root, or the root plus one and then `s * (s + 1) ≤ a`, whenever
`s < 2^b`, `0 < k` and `b + 3 ≤ 2 * (3 * 2^k - 1)`. -/
theorem newtonIter_eq_or_succ_of_lt_two_mul {a x b k : Nat} (hx : 0 < x) (h1 : x ≤ Nat.sqrt a)
    (h2 : Nat.sqrt a < 2 * x) (hs : Nat.sqrt a < 2 ^ b) (hk : 0 < k)
    (hb : b + 3 ≤ 2 * (3 * 2 ^ k - 1)) :
    newtonIter a (k + 2) x = Nat.sqrt a ∨
      (newtonIter a (k + 2) x = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a) := by
  obtain ⟨l, d⟩ := newtonIter_sub_sqrt_le_of_lt_two_mul k hx h1 h2
  have hk2 : 2 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk; simpa using this
  have hm := div_two_pow_add_eight_le hs (n := 3 * 2 ^ k - 1) (by omega) hb
  rw [newtonIter_succ']
  exact newton_eq_or_succ_of_err (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hx h1) l) l hm d

/-- The step keeps an iterate at the root, or at the root plus one with `s * (s + 1) ≤ a`, in
that set. -/
theorem newton_mem_of_mem {a y : Nat}
    (h : y = Nat.sqrt a ∨ (y = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a)) :
    newton a y = Nat.sqrt a ∨ (newton a y = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a) := by
  rcases Nat.eq_zero_or_pos y with h0 | h0
  · left
    have : newton a y = 0 := by rw [h0]; unfold newton; rw [Nat.div_zero]
    omega
  · exact newton_eq_or_succ_of_le_add_two h0 (by omega) (by omega)

/-- Once an iterate is the root or the root plus one, every later iterate is the root, or the root
plus one and then `s * (s + 1) ≤ a`. -/
theorem newtonIter_of_mem {a x : Nat} (k : Nat) (hk : 0 < k) (hx : 0 < x) (h1 : Nat.sqrt a ≤ x)
    (h2 : x ≤ Nat.sqrt a + 1) :
    newtonIter a k x = Nat.sqrt a ∨
      (newtonIter a k x = Nat.sqrt a + 1 ∧ Nat.sqrt a * (Nat.sqrt a + 1) ≤ a) := by
  induction k with
  | zero => exact absurd hk (Nat.lt_irrefl 0)
  | succ k ih =>
    rw [newtonIter_succ']
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [newtonIter_zero]; exact newton_eq_or_succ_of_le_add_two hx h1 (by omega)
    · exact newton_mem_of_mem (ih hk')

/-! ## Power-of-two estimates through `Nat.log2` -/

/-- The power of two `2^(log2 a / 2)` is at most the root of a positive `a`. -/
theorem two_pow_half_log2_le_sqrt {a : Nat} (h : 0 < a) : 2 ^ (Nat.log2 a / 2) ≤ Nat.sqrt a := by
  have h1 := Nat.log2_self_le (n := a) (by omega)
  apply le_sqrt_of_mul_self_le
  rw [← Nat.pow_add]
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) h1

/-- The root of `a` is below twice the power of two `2^(log2 a / 2)`. -/
theorem sqrt_lt_two_mul_two_pow_half_log2 (a : Nat) : Nat.sqrt a < 2 * 2 ^ (Nat.log2 a / 2) := by
  have h2 := Nat.lt_log2_self (n := a)
  generalize Nat.log2 a = L at *
  apply sqrt_lt_of_lt_mul_self
  have e : 2 * 2 ^ (L / 2) * (2 * 2 ^ (L / 2)) = 2 ^ (L / 2 + 1 + (L / 2 + 1)) := by
    rw [Nat.pow_add, Nat.pow_succ]; grind
  rw [e]
  exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))

/-! ## Sizes for machine words -/

/-- At or above a positive root, `x + a / x ≤ x + s + 2`: the sum a Newton step computes is at
most the iterate plus the root plus two. -/
theorem add_div_le_of_sqrt_le {a x : Nat} (hs : 0 < Nat.sqrt a) (h : Nat.sqrt a ≤ x) :
    x + a / x ≤ x + Nat.sqrt a + 2 := by
  have hup := Nat.lt_succ_sqrt a
  have h1 : a / x ≤ a / Nat.sqrt a := Nat.div_le_div_left h hs
  generalize Nat.sqrt a = s at *
  simp only [Nat.succ_eq_add_one] at hup
  have h2 : a / s < s + 3 := (Nat.div_lt_iff_lt_mul hs).mpr (by grind)
  omega

/-- Below the root by a factor less than `c` (`s < c * x`), `a / x < c * c * x`. -/
theorem div_lt_of_sqrt_lt_mul {a x c : Nat} (hx : 0 < x) (h : Nat.sqrt a < c * x) : a / x < c * c * x := by
  apply (Nat.div_lt_iff_lt_mul hx).mpr
  have hup := Nat.lt_succ_sqrt a
  have h1 : Nat.sqrt a + 1 ≤ c * x := h
  have h2 := mul_self_le_mul_self h1
  simp only [Nat.succ_eq_add_one] at hup
  have e : c * x * (c * x) = c * c * x * x := by grind
  omega

/-- The root of a number below `2^(2k)` is below `2^k`; any `w ≤ 2 * k` bound applies. -/
theorem sqrt_lt_two_pow_of_lt {a w k : Nat} (ha : a < 2 ^ w) (hw : w ≤ 2 * k) : Nat.sqrt a < 2 ^ k :=
  sqrt_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hw))

/-- The square of the root of `a` is below `2^w` when `a` is. -/
theorem mul_self_sqrt_lt_two_pow {a w : Nat} (ha : a < 2 ^ w) : Nat.sqrt a * Nat.sqrt a < 2 ^ w :=
  Nat.lt_of_le_of_lt (Nat.sqrt_le a) ha

/-! ## The order of the root and the root rounded up -/

/-- `m ≤ Nat.sqrt a` exactly when `m * m ≤ a`. -/
theorem le_sqrt_iff {m a : Nat} : m ≤ Nat.sqrt a ↔ m * m ≤ a :=
  ⟨fun h => Nat.le_trans (mul_self_le_mul_self h) (Nat.sqrt_le a), le_sqrt_of_mul_self_le⟩

/-- `Nat.sqrt a < m` exactly when `a < m * m`. -/
theorem sqrt_lt_iff {m a : Nat} : Nat.sqrt a < m ↔ a < m * m := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_sqrt a) (mul_self_le_mul_self h)
  · exact sqrt_lt_of_lt_mul_self

/-- `a < (Nat.sqrt a + 1) * (Nat.sqrt a + 1)`. -/
theorem lt_sqrt_add_one_mul_self (a : Nat) : a < (Nat.sqrt a + 1) * (Nat.sqrt a + 1) :=
  Nat.lt_succ_sqrt a

/-- The root rounded up, `s + (if s * s < a then 1 else 0)`, squared is at least `a`. -/
theorem le_mul_self_sqrt_add_ite (a : Nat) :
    a ≤ (Nat.sqrt a + (if Nat.sqrt a * Nat.sqrt a < a then 1 else 0)) *
      (Nat.sqrt a + (if Nat.sqrt a * Nat.sqrt a < a then 1 else 0)) := by
  have h1 := Nat.lt_succ_sqrt a
  have h0 := Nat.sqrt_le a
  generalize Nat.sqrt a = s at *
  simp only [Nat.succ_eq_add_one] at h1
  by_cases h : s * s < a
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h, Nat.add_zero]; omega

/-- The root rounded up is the least such number: one less, squared, is below `a` (when the
rounded-up root is positive). -/
theorem sqrt_add_ite_sub_one_mul_self_lt {a : Nat}
    (h : 0 < Nat.sqrt a + (if Nat.sqrt a * Nat.sqrt a < a then 1 else 0)) :
    (Nat.sqrt a + (if Nat.sqrt a * Nat.sqrt a < a then 1 else 0) - 1) *
      (Nat.sqrt a + (if Nat.sqrt a * Nat.sqrt a < a then 1 else 0) - 1) < a := by
  have h0 := Nat.sqrt_le a
  generalize Nat.sqrt a = s at *
  by_cases hc : s * s < a
  · rw [ite_eq_left hc, Nat.add_sub_cancel]; exact hc
  · rw [ite_eq_right hc, Nat.add_zero] at h ⊢
    have : s - 1 < s := by omega
    have := Nat.mul_self_lt_mul_self this
    omega

/-- `newtonIter` is `Nat.repeat` of the step. -/
theorem newtonIter_eq_repeat (a k x : Nat) : newtonIter a k x = Nat.repeat (newton a) k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [newtonIter_succ', ih]; rfl

/-! ## Error bounds in multiplicative form -/

/-- From `e * D ≤ s + c * D` with `0 < D`: `e ≤ s / D + c`. -/
theorem le_div_add_of_mul_le {e D s c : Nat} (hD : 0 < D) (h : e * D ≤ s + c * D) : e ≤ s / D + c := by
  have h1 : (e - c) * D = e * D - c * D := Nat.sub_mul e c D
  have h2 : e - c ≤ s / D := (Nat.le_div_iff_mul_le hD).mpr (by omega)
  omega

/-- From `s + c * D ≤ D * D` with `0 < D`: `s / D + c ≤ D`. -/
theorem div_add_le_of_add_mul_le {s c D : Nat} (hD : 0 < D) (h : s + c * D ≤ D * D) : s / D + c ≤ D := by
  have hc : c ≤ D := Nat.le_of_mul_le_mul_right (Nat.le_trans (Nat.le_add_left _ _) h) hD
  have h1 : (D - c) * D = D * D - c * D := Nat.sub_mul D c D
  have h2 : s ≤ (D - c) * D := by omega
  have h3 : s / D ≤ D - c := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact h2)
  omega

/-- The final squaring in multiplicative form: from `e * D ≤ s + 2 * D`, `4 ≤ s` and
`s + 8 * D ≤ D * D`, the square of `e` is at most `s`. -/
theorem mul_self_le_of_mul_le {e D s : Nat} (hs : 4 ≤ s) (hD : s + 8 * D ≤ D * D) (h : e * D ≤ s + 2 * D) :
    e * e ≤ s := by
  have hD0 : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · subst h0; simp at hD; omega
    · exact h0
  exact mul_self_le_of_le_div_add_two hs (div_add_le_of_add_mul_le hD0 hD) (le_div_add_of_mul_le hD0 h)

/-! ## Squares and powers of two -/

/-- `(a + b) * (a + b) = a * a + 2 * a * b + b * b`. -/
theorem add_mul_self_eq (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by grind

/-- For `b ≤ a`: `(a - b) * (a - b) + 2 * a * b = a * a + b * b`. -/
theorem sub_mul_self_add_eq {a b : Nat} (h : b ≤ a) : (a - b) * (a - b) + 2 * a * b = a * a + b * b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]; grind

/-- `2 * a * b ≤ a * a + b * b`. -/
theorem two_mul_le_add_mul_self (a b : Nat) : 2 * a * b ≤ a * a + b * b := by
  rcases Nat.le_total b a with h | h
  · have := sub_mul_self_add_eq h; omega
  · have := sub_mul_self_add_eq h
    have e : 2 * b * a = 2 * a * b := by grind
    have e2 : b * b + a * a = a * a + b * b := Nat.add_comm _ _
    omega

/-- `2^k * 2^k = 2^(2 * k)`. -/
theorem two_pow_mul_two_pow (k : Nat) : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
  rw [← Nat.pow_add, Nat.two_mul]

/-- `(2 * x) * (2 * x) = 4 * (x * x)`. -/
theorem two_mul_mul_two_mul (x : Nat) : 2 * x * (2 * x) = 4 * (x * x) := by grind

/-- `2^(k - c) * 2^c = 2^k` for `c ≤ k`. -/
theorem two_pow_sub_mul_two_pow {c k : Nat} (h : c ≤ k) : 2 ^ (k - c) * 2 ^ c = 2 ^ k := by
  rw [← Nat.pow_add, Nat.sub_add_cancel h]

/-- `(x / D) * (x / D) ≤ x * x / (D * D)`. -/
theorem div_mul_div_le (x D : Nat) : x / D * (x / D) ≤ x * x / (D * D) := by
  rcases Nat.eq_zero_or_pos D with h | h
  · subst h; simp
  · apply (Nat.le_div_iff_mul_le (Nat.mul_pos h h)).mpr
    have h1 : x / D * D ≤ x := Nat.div_mul_le_self x D
    have h2 := Nat.mul_le_mul h1 h1
    have e : x / D * (x / D) * (D * D) = x / D * D * (x / D * D) := by grind
    omega

/-- Squares are strictly monotone: `m * m < n * n ↔ m < n`. -/
theorem mul_self_lt_mul_self_iff {m n : Nat} : m * m < n * n ↔ m < n :=
  ⟨lt_of_mul_self_lt_mul_self, Nat.mul_self_lt_mul_self⟩

/-- Squares are monotone: `m * m ≤ n * n ↔ m ≤ n`. -/
theorem mul_self_le_mul_self_iff {m n : Nat} : m * m ≤ n * n ↔ m ≤ n := by
  constructor
  · intro h; apply Nat.le_of_not_lt; intro h'; have := Nat.mul_self_lt_mul_self h'; omega
  · exact mul_self_le_mul_self

/-- A number whose square is below `2^(2 * k)` is below `2^k`. -/
theorem lt_two_pow_of_mul_self_lt {x k : Nat} (h : x * x < 2 ^ (2 * k)) : x < 2 ^ k := by
  rw [← two_pow_mul_two_pow] at h
  exact lt_of_mul_self_lt_mul_self h

/-! ## The root by search, for evaluation -/

/-- `sqrtSearch k a`: the largest `r ≤ k` with `r * r ≤ a`, by structural recursion on `k`, so
that `decide` evaluates it on literals (`Nat.sqrt` is defined by well-founded recursion, which
`decide` does not unfold). -/
def sqrtSearch : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => if (k + 1) * (k + 1) ≤ a then k + 1 else sqrtSearch k a

/-- `sqrtSearch k a` is the smaller of `k` and the root of `a`. -/
theorem sqrtSearch_eq_min (k a : Nat) : sqrtSearch k a = min k (Nat.sqrt a) := by
  induction k with
  | zero => rw [Nat.zero_min]; rfl
  | succ k ih =>
    show (if (k + 1) * (k + 1) ≤ a then k + 1 else sqrtSearch k a) = min (k + 1) (Nat.sqrt a)
    by_cases h : (k + 1) * (k + 1) ≤ a
    · rw [ite_eq_left h]; have := le_sqrt_of_mul_self_le h; omega
    · rw [ite_eq_right h, ih]; have := sqrt_lt_of_lt_mul_self (Nat.lt_of_not_le h); omega

/-- The root of `a` is at most `a`. -/
theorem sqrt_le_self (a : Nat) : Nat.sqrt a ≤ a := by
  rcases Nat.eq_zero_or_pos (Nat.sqrt a) with h | h
  · omega
  · exact Nat.le_trans (Nat.le_mul_of_pos_right _ h) (Nat.sqrt_le a)

/-- The root of `a` is `sqrtSearch a a`, which `decide` evaluates on literals. -/
theorem sqrt_eq_sqrtSearch (a : Nat) : Nat.sqrt a = sqrtSearch a a := by
  rw [sqrtSearch_eq_min]; have := sqrt_le_self a; omega

/-! ## Newton steps on machine words -/

/-- A Newton step on `w`-bit words, `(x + a / x) >>> 1`, is `newton` on the values when the sum
`x + a / x` does not wrap. -/
theorem toNat_newton_word {w : Nat} (a x : BitVec w) (h : x.toNat + a.toNat / x.toNat < 2 ^ w) :
    ((x + a / x) >>> 1).toNat = newton a.toNat x.toNat := by
  unfold newton
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_udiv,
    Nat.mod_eq_of_lt h, Nat.pow_one]

/-- At or above a positive root, a Newton step on `w`-bit words is `newton` on the values when
`x + s + 2 < 2^w`. -/
theorem toNat_newton_word_of_sqrt_le {w : Nat} {a x : BitVec w} (hs : 0 < Nat.sqrt a.toNat)
    (h : Nat.sqrt a.toNat ≤ x.toNat) (hw : x.toNat + Nat.sqrt a.toNat + 2 < 2 ^ w) :
    ((x + a / x) >>> 1).toNat = newton a.toNat x.toNat :=
  toNat_newton_word a x (Nat.lt_of_le_of_lt (add_div_le_of_sqrt_le hs h) hw)

/-- The root of the value of a `w`-bit word is below `2^k` when `w ≤ 2 * k`. -/
theorem sqrt_toNat_lt_two_pow {w k : Nat} (x : BitVec w) (h : w ≤ 2 * k) : Nat.sqrt x.toNat < 2 ^ k :=
  sqrt_lt_two_pow_of_lt x.isLt h

end ProofForgeFin.Sqrt
