/-!
# Integer roots of a quadratic

For `q(x) = a x² - 2 b x + c` with `a > 0` the smaller real root is `(b - √(b² - a c)) / a`.
Integer code computes it as `(b - s) / a` with `s` an integer square root of `d = b² - a c`.
Which side of the real root the result lands on depends on the rounding of the square root and
of the division. This module states both sides on natural-number inputs, as such code computes
them, and compares a point at or below the smaller root with any rational point where `q` is not
positive.

* `quad_nonneg_of_sqrt_ge`: with `d ≤ s * s` (the square root rounded up, or any upper bound of
  it) and `x * a ≤ b - s` (the division rounded down), `2 b x ≤ a x² + c` and `a x ≤ b`: `x` is
  at or below the smaller root.
* `quad_neg_of_sqrt_le`: with `s * s ≤ d` (the square root rounded down) and `b - s < a y ≤ b`,
  `a y² + c < 2 b y`: `y` lies strictly between the roots. With `y = x + 1` and
  `x = (b - s) / a`, the integer after the computed root is past the smaller root.
* `factor_neg_of_lt_vertex`: below the vertex `b / a` the quadratic decreases strictly, in the
  factored form used by `le_of_quad_nonpos`.
* `le_of_quad_nonpos`: an `x` at or below the smaller root is at most every rational point
  `N / t` (`t > 0`) where `q` is not positive (`a N² + c t² ≤ 2 b t N`).

Every statement is cross-multiplied; no real number or square root of a non-square appears.
-/

namespace ProofForgeFin.QuadRoot

/-- The computed smaller root with the square root rounded up is at or below the real smaller
root: from `a * c ≤ b * b`, `b * b - a * c ≤ s * s`, `s ≤ b` and `x * a ≤ b - s`, the quadratic
is not negative at `x` (`2 b x ≤ a x² + c`) and `x` is at most the vertex (`a x ≤ b`). -/
theorem quad_nonneg_of_sqrt_ge {a b c s x : Nat} (ha : 0 < a) (h1 : a * c ≤ b * b)
    (h2 : b * b - a * c ≤ s * s) (h3 : s ≤ b) (h4 : x * a ≤ b - s) :
    2 * (b : Int) * x ≤ a * x * x + c ∧ (a : Int) * x ≤ b := by
  have h5 : s ≤ b - x * a := by omega
  have h6 : s * s ≤ (b - x * a) * (b - x * a) := Nat.mul_le_mul h5 h5
  have hxa : x * a ≤ b := by omega
  have e1 : ((b - x * a : Nat) : Int) = b - x * a := by omega
  have k1 : ((b * b - a * c : Nat) : Int) ≤ ((b - x * a) * (b - x * a) : Nat) :=
    Int.ofNat_le.mpr (Nat.le_trans h2 h6)
  have e2 : ((b * b - a * c : Nat) : Int) = (b : Int) * b - a * c := by
    rw [Int.ofNat_sub h1]; simp [Int.natCast_mul]
  have e3 : (((b - x * a) * (b - x * a) : Nat) : Int) = ((b : Int) - x * a) * ((b : Int) - x * a) := by
    rw [Int.natCast_mul, e1]
  rw [e2, e3] at k1
  have k2 : 0 ≤ (a : Int) * (a * x * x + c - 2 * b * x) := by
    have : (a : Int) * (a * x * x + c - 2 * b * x) =
        ((b : Int) - x * a) * ((b : Int) - x * a) - (b * b - a * c) := by grind
    omega
  have ha' : (0 : Int) < a := by omega
  have k3 : 0 ≤ (a : Int) * x * x + c - 2 * b * x := by
    rcases Int.lt_or_le ((a : Int) * x * x + c - 2 * b * x) 0 with h | h
    · have := Int.mul_neg_of_pos_of_neg ha' h; omega
    · exact h
  refine ⟨by omega, ?_⟩
  have : ((x * a : Nat) : Int) ≤ b := by exact_mod_cast hxa
  rw [Int.natCast_mul] at this
  grind

/-- The integer after a computed smaller root with the square root rounded down is past the real
smaller root: from `a * c ≤ b * b`, `s * s ≤ b * b - a * c`, `b < a * y + s` and `a * y ≤ b`, the
quadratic is negative at `y`. -/
theorem quad_neg_of_sqrt_le {a b c s y : Nat} (ha : 0 < a) (h1 : a * c ≤ b * b)
    (h2 : s * s ≤ b * b - a * c) (h3 : b < a * y + s) (h4 : a * y ≤ b) :
    (a : Int) * y * y + c < 2 * b * y := by
  have h5 : b - a * y < s := by omega
  have h6 : (b - a * y) * (b - a * y) < s * s := Nat.mul_self_lt_mul_self h5
  have e1 : ((b - a * y : Nat) : Int) = b - a * y := by omega
  have k1 : (((b - a * y) * (b - a * y) : Nat) : Int) < ((b * b - a * c : Nat) : Int) :=
    Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le h6 h2)
  have e2 : ((b * b - a * c : Nat) : Int) = (b : Int) * b - a * c := by
    rw [Int.ofNat_sub h1]; simp [Int.natCast_mul]
  rw [e2, Int.natCast_mul, e1] at k1
  have k2 : (a : Int) * (a * y * y + c - 2 * b * y) < 0 := by
    have : (a : Int) * (a * y * y + c - 2 * b * y) =
        ((b : Int) - a * y) * ((b : Int) - a * y) - (b * b - a * c) := by grind
    omega
  have ha' : (0 : Int) < a := by omega
  have k3 : (a : Int) * y * y + c - 2 * b * y < 0 := by
    rcases Int.lt_or_le ((a : Int) * y * y + c - 2 * b * y) 0 with h | h
    · exact h
    · have := Int.mul_nonneg (Int.le_of_lt ha') h; omega
  omega

/-- Below the vertex the quadratic decreases strictly. For `t > 0`, `u < t v` and `a v ≤ b`, the
difference `t² (a v² - 2 b v) - (a u² - 2 b t u)`, which is `t²` times the difference of the
quadratic at `v` and at `u / t`, factors as `(t v - u) (a (t v + u) - 2 b t)`, and this product is
negative. -/
theorem factor_neg_of_lt_vertex {a b v u t : Int} (ha : 0 < a) (ht : 0 < t) (hlt : u < t * v) (hv : a * v ≤ b) :
    (t * v - u) * (a * (t * v + u) - 2 * b * t) < 0 := by
  have h1 : 0 < t * v - u := by omega
  have h2 : a * (t * v + u) - 2 * b * t < 0 := by
    have e1 : a * u < a * (t * v) := Int.mul_lt_mul_of_pos_left hlt ha
    have e2 : a * (t * v) ≤ b * t := by
      have := Int.mul_le_mul_of_nonneg_left hv (Int.le_of_lt ht)
      grind
    grind
  exact Int.mul_neg_of_pos_of_neg h1 h2

/-- An `x` at or below the smaller root (`2 b x ≤ a x² + c`, `a x ≤ b`) is at most every rational
point `N / t` (`t > 0`) where the quadratic is not positive, `a N² + c t² ≤ 2 b t N`:
`t * x ≤ N`. -/
theorem le_of_quad_nonpos {a b c x N t : Int} (ha : 0 < a) (ht : 0 < t)
    (hq : 2 * b * x ≤ a * x * x + c) (hxb : a * x ≤ b)
    (hH : a * N * N + c * t * t ≤ 2 * b * t * N) : t * x ≤ N := by
  apply Int.not_lt.mp
  intro hlt
  have h3 := factor_neg_of_lt_vertex ha ht hlt hxb
  have h4 : 0 ≤ t * t * (a * x * x + c - 2 * b * x) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.le_of_lt ht) (Int.le_of_lt ht)) (by omega)
  have e : t * t * (a * x * x + c - 2 * b * x) - (a * N * N + c * t * t - 2 * b * t * N) =
      (t * x - N) * (a * (t * x + N) - 2 * b * t) := by grind
  omega

end ProofForgeFin.QuadRoot
