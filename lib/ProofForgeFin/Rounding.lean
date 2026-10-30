/-!
# Rounding division on natural numbers

Money code computes quotients in integer units and chooses a rounding direction for each one.
This module fixes two quotient operations and their exact bounds:

* `a / b`, Lean's division on `Nat`, rounds down (the floor of the rational `a / b`);
* `ceilDiv a b` rounds up (the ceiling of `a / b`).

Every bound is stated by cross-multiplication, so `q * b ≤ a` reads "`q` is at most the exact
quotient". Division by zero returns 0 for both operations, as `Nat.div` does; lemmas that need a
positive divisor take `0 < b` as a hypothesis.

The forms in which deployed code writes the ceiling (`(a + b - 1) / b`, `(a + (b - 1)) / b`,
and `if a = 0 then 0 else (a - 1) / b + 1` in Balancer's `FixedPoint.divUp`) are all proved equal
to `ceilDiv` for a positive divisor.
-/

namespace ProofForgeFin

/-! ## Rounding down -/

/-- The floor quotient times the divisor is at most the dividend. -/
theorem div_mul_le (a b : Nat) : a / b * b ≤ a := Nat.div_mul_le_self a b

/-- The dividend is below the floor quotient plus one, times the divisor. -/
theorem lt_div_add_one_mul (a b : Nat) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a / b) b]
  omega

/-- Floor division: `a / b` is the exact quotient rounded down, so it lies within one unit below
the exact value. -/
theorem floor_spec (a b : Nat) (hb : 0 < b) : a / b * b ≤ a ∧ a < (a / b + 1) * b :=
  ⟨div_mul_le a b, lt_div_add_one_mul a b hb⟩

/-- The remainder lost by floor division is below the divisor. -/
theorem sub_div_mul_lt (a b : Nat) (hb : 0 < b) : a - a / b * b < b := by
  have := lt_div_add_one_mul a b hb
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- A number with the two floor bounds is the floor quotient. -/
theorem div_eq_of_bounds {a b q : Nat} (h1 : q * b ≤ a) (h2 : a < (q + 1) * b) : a / b = q := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at h2
    · exact h
  have hle : q ≤ a / b := (Nat.le_div_iff_mul_le hb).2 h1
  have hlt : a / b < q + 1 := (Nat.div_lt_iff_lt_mul hb).2 h2
  omega

/-- `q ≤ a / b` exactly when `q * b ≤ a`. -/
theorem le_div_iff {a b q : Nat} (hb : 0 < b) : q ≤ a / b ↔ q * b ≤ a :=
  Nat.le_div_iff_mul_le hb

/-- `a / b < q` exactly when `a < q * b`. -/
theorem div_lt_iff {a b q : Nat} (hb : 0 < b) : a / b < q ↔ a < q * b :=
  Nat.div_lt_iff_lt_mul hb

/-- Floor division is monotone in the dividend. -/
theorem div_mono_left {a a' : Nat} (b : Nat) (h : a ≤ a') : a / b ≤ a' / b :=
  Nat.div_le_div_right h

/-- Floor division is antitone in a positive divisor. -/
theorem div_anti_right (a : Nat) {b b' : Nat} (hb : 0 < b) (h : b ≤ b') : a / b' ≤ a / b :=
  Nat.div_le_div_left h hb

/-- `m ≤ d * q` gives `m / d ≤ q`. -/
theorem div_le_of_le_mul' {m d q : Nat} (h : m ≤ q * d) : m / d ≤ q := by
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm]; exact h

/-- Floor division respects the order of rationals: `a / b ≤ c / d` exactly (by
cross-multiplication, `a * d ≤ c * b`) gives `a / b ≤ c / d` rounded down. -/
theorem div_le_div_of_mul_le {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  apply (Nat.le_div_iff_mul_le hd).2
  apply Nat.le_of_mul_le_mul_right _ hb
  calc a / b * d * b = a / b * b * d := Nat.mul_right_comm _ _ _
    _ ≤ a * d := Nat.mul_le_mul_right d (div_mul_le a b)
    _ ≤ c * b := h

/-- A share `t ≤ s` of an amount `a`, rounded down, is at most `a`: `t * a / s ≤ a`. This is
the reason a redemption of at most every outstanding share never pays out more than the assets. -/
theorem mul_div_le_of_le {t a s : Nat} (h : t ≤ s) : t * a / s ≤ a := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp
  · exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right a h)

/-- Floor of an exact multiple. -/
theorem mul_div_cancel_right (a : Nat) {b : Nat} (hb : 0 < b) : a * b / b = a :=
  Nat.mul_div_cancel a hb

/-- Floor division twice is floor division by the product. -/
theorem div_div (a b c : Nat) : a / b / c = a / (b * c) := Nat.div_div_eq_div_mul a b c

/-- Rounding two parts down separately loses at least as much as rounding their sum:
`a / c + b / c ≤ (a + b) / c`. -/
theorem div_add_div_le (a b c : Nat) : a / c + b / c ≤ (a + b) / c := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp
  · apply (Nat.le_div_iff_mul_le hc).2
    rw [Nat.add_mul]
    exact Nat.add_le_add (div_mul_le a c) (div_mul_le b c)

/-- Rounding two parts down separately loses less than one unit more than rounding their sum:
`(a + b) / c ≤ a / c + b / c + 1`. -/
theorem div_add_le_div_add_div_add_one (a b c : Nat) : (a + b) / c ≤ a / c + b / c + 1 := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp
  · have h1 := lt_div_add_one_mul a c hc
    have h2 := lt_div_add_one_mul b c hc
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hc).2
    rw [Nat.succ_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_mul, Nat.one_mul] at h1 h2
    omega

/-- The bound used to turn a scaled potential into an amount: from `X * D ≤ Y * D + P`,
`X ≤ Y + P / D` (the remainder `P` is rounded down once). -/
theorem le_add_div_of_mul_le {X Y P D : Nat} (hD : 0 < D) (h : X * D ≤ Y * D + P) :
    X ≤ Y + P / D := by
  have h1 : (X - Y) * D ≤ P := by rw [Nat.sub_mul]; omega
  have h2 : X - Y ≤ P / D := (Nat.le_div_iff_mul_le hD).2 h1
  omega

/-! ## Rounding up -/

/-- Division rounded up: the least `q` with `a ≤ q * b` (for `0 < b`). Division by zero
returns 0. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Ceiling division: `ceilDiv a b` is the exact quotient rounded up, so it lies within one unit
above the exact value. -/
theorem ceilDiv_spec (a b : Nat) (hb : 0 < b) :
    a ≤ ceilDiv a b * b ∧ ceilDiv a b * b < a + b := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  rw [Nat.mul_comm ((a + b - 1) / b) b]
  omega

/-- The dividend is at most the ceiling quotient times the divisor. -/
theorem le_ceilDiv_mul (a b : Nat) (hb : 0 < b) : a ≤ ceilDiv a b * b := (ceilDiv_spec a b hb).1

/-- The ceiling quotient times the divisor is below the dividend plus the divisor. -/
theorem ceilDiv_mul_lt (a b : Nat) (hb : 0 < b) : ceilDiv a b * b < a + b :=
  (ceilDiv_spec a b hb).2

/-- A number with the two ceiling bounds is the ceiling quotient. -/
theorem ceilDiv_eq_of_bounds {a b q : Nat} (hb : 0 < b) (h1 : a ≤ q * b) (h2 : q * b < a + b) :
    ceilDiv a b = q := by
  unfold ceilDiv
  apply div_eq_of_bounds
  · omega
  · rw [Nat.add_mul, Nat.one_mul]; omega

/-- `ceilDiv a b ≤ q` exactly when `a ≤ q * b`. -/
theorem ceilDiv_le_iff {a b q : Nat} (hb : 0 < b) : ceilDiv a b ≤ q ↔ a ≤ q * b := by
  unfold ceilDiv
  constructor
  · intro h
    have := ceilDiv_spec a b hb
    unfold ceilDiv at this
    exact Nat.le_trans this.1 (Nat.mul_le_mul_right b h)
  · intro h
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hb).2
    rw [Nat.succ_mul]
    omega

/-- `q < ceilDiv a b` exactly when `q * b < a`. -/
theorem lt_ceilDiv_iff {a b q : Nat} (hb : 0 < b) : q < ceilDiv a b ↔ q * b < a := by
  have := ceilDiv_le_iff (a := a) (q := q) hb
  constructor
  · intro h; exact Nat.lt_of_not_le fun h' => absurd (this.2 h') (Nat.not_le_of_lt h)
  · intro h; exact Nat.lt_of_not_le fun h' => absurd (this.1 h') (Nat.not_le_of_lt h)

/-- The form `(a + (b - 1)) / b`, used by Balancer's `scaleUp`. -/
theorem ceilDiv_eq_add_pred (a b : Nat) (hb : 0 < b) : ceilDiv a b = (a + (b - 1)) / b := by
  unfold ceilDiv
  congr 1
  omega

/-- The form `if a = 0 then 0 else (a - 1) / b + 1`, used by Balancer's `FixedPoint.mulUp` and
`FixedPoint.divUp`, which avoid the overflow of `a + b - 1`. -/
theorem ceilDiv_eq_ite (a b : Nat) (hb : 0 < b) :
    ceilDiv a b = if a = 0 then 0 else (a - 1) / b + 1 := by
  unfold ceilDiv
  split
  · subst_vars
    simp only [Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)
  · have : a + b - 1 = (a - 1) + 1 * b := by omega
    rw [this, Nat.add_mul_div_right _ _ hb]

/-- The ceiling of zero is zero. -/
@[simp] theorem ceilDiv_zero_left (b : Nat) : ceilDiv 0 b = 0 := by
  unfold ceilDiv
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp
  · exact Nat.div_eq_of_lt (by omega)

/-- The ceiling of an exact multiple is the multiplier. -/
theorem ceilDiv_mul_cancel (a : Nat) {b : Nat} (hb : 0 < b) : ceilDiv (a * b) b = a :=
  ceilDiv_eq_of_bounds hb (Nat.le_refl _) (by omega)

/-- Rounding down never exceeds rounding up. -/
theorem div_le_ceilDiv (a b : Nat) : a / b ≤ ceilDiv a b := by
  unfold ceilDiv
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp
  · exact Nat.div_le_div_right (by omega)

/-- Rounding up exceeds rounding down by at most one unit. -/
theorem ceilDiv_le_div_add_one (a b : Nat) : ceilDiv a b ≤ a / b + 1 := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; unfold ceilDiv; simp
  · apply (ceilDiv_le_iff hb).2
    exact Nat.le_of_lt (lt_div_add_one_mul a b hb)

/-- Rounding up equals rounding down exactly when the divisor divides the dividend. -/
theorem ceilDiv_eq_div_iff (a b : Nat) (hb : 0 < b) : ceilDiv a b = a / b ↔ a % b = 0 := by
  have h1 := Nat.div_add_mod a b
  constructor
  · intro h
    have := le_ceilDiv_mul a b hb
    rw [h, Nat.mul_comm] at this
    omega
  · intro h
    apply ceilDiv_eq_of_bounds hb
    · rw [Nat.mul_comm]; omega
    · rw [Nat.mul_comm]; omega

/-- With a nonzero remainder, rounding up is rounding down plus one. -/
theorem ceilDiv_eq_div_add_one (a b : Nat) (hb : 0 < b) (h : a % b ≠ 0) :
    ceilDiv a b = a / b + 1 := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  apply ceilDiv_eq_of_bounds hb
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega

/-- Ceiling division is monotone in the dividend. -/
theorem ceilDiv_mono_left {a a' : Nat} (b : Nat) (h : a ≤ a') : ceilDiv a b ≤ ceilDiv a' b := by
  unfold ceilDiv
  exact Nat.div_le_div_right (by omega)

/-- Ceiling division is antitone in a positive divisor. -/
theorem ceilDiv_anti_right (a : Nat) {b b' : Nat} (hb : 0 < b) (h : b ≤ b') :
    ceilDiv a b' ≤ ceilDiv a b := by
  apply (ceilDiv_le_iff (Nat.lt_of_lt_of_le hb h)).2
  exact Nat.le_trans (le_ceilDiv_mul a b hb) (Nat.mul_le_mul_left _ h)

/-- A positive dividend has a positive ceiling quotient. -/
theorem ceilDiv_pos {a b : Nat} (hb : 0 < b) (ha : 0 < a) : 0 < ceilDiv a b :=
  (lt_ceilDiv_iff hb).2 (by simpa using ha)

/-- `ceilDiv a b * b ≤ a + b - 1`: the overshoot of the ceiling is below the divisor. -/
theorem ceilDiv_mul_sub_lt (a b : Nat) (hb : 0 < b) : ceilDiv a b * b - a < b := by
  have := ceilDiv_mul_lt a b hb
  omega

/-- Ceiling division respects the order of rationals. -/
theorem ceilDiv_le_ceilDiv_of_mul_le {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : ceilDiv a b ≤ ceilDiv c d := by
  apply (ceilDiv_le_iff hb).2
  apply Nat.le_of_mul_le_mul_right _ hd
  calc a * d ≤ c * b := h
    _ ≤ ceilDiv c d * d * b := Nat.mul_le_mul_right b (le_ceilDiv_mul c d hd)
    _ = ceilDiv c d * b * d := Nat.mul_right_comm _ _ _

/-! ## Sums of rounded parts -/

/-- Rounding every element of a list down loses at most the total: the sum of the floors, times
the divisor, is at most the sum. -/
theorem sum_div_mul_le (l : List Nat) (c : Nat) : (l.map (· / c)).sum * c ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    have := div_mul_le a c
    omega

/-- Rounding every element of a list down loses less than one unit per element: the sum is
below the sum of the floors plus the length, times the divisor. -/
theorem sum_lt_sum_div_add_length_mul (l : List Nat) (c : Nat) (hc : 0 < c) (hl : l ≠ []) :
    l.sum < ((l.map (· / c)).sum + l.length) * c := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    have ha := lt_div_add_one_mul a c hc
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rcases l with _ | ⟨b, l⟩
    · simpa using ha
    · have := ih (by simp)
      simp only [Nat.add_mul, Nat.one_mul] at *
      omega

/-- The sum of the floors is at most the floor of the sum. -/
theorem sum_div_le_div_sum (l : List Nat) (c : Nat) : (l.map (· / c)).sum ≤ l.sum / c := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; induction l <;> simp_all
  · exact (Nat.le_div_iff_mul_le hc).2 (sum_div_mul_le l c)

end ProofForgeFin
