/-!
# Composed roundings

Integer code often rounds twice: it rounds `n / d` down to `q₁`, then rounds `q₁ * m / e` down to
`q₂`; or it rounds a value down and then rounds a fraction of the result up. These lemmas bound the
composed result against the exact value by cross-multiplication, so that a proof never handles a
rational number.

* `mul_le_of_floor_floor`: two roundings down in a row stay at or below the exact value:
  `x ≤ q₂`, `q₂ * e ≤ q₁ * m` and `q₁ * d ≤ n` give `x * e * d ≤ n * m`.
* `le_of_floor_le_floor`: a quotient rounded down is at most an upper bound of the same quotient:
  `u * c ≤ x * k`, `x ≤ q`, `q * k ≤ m * c` and `c > 0` give `u ≤ m`.
* `ceil_frac_floor_bounds`: `v / c` rounded down, then the fraction `f / k < 1` of it rounded up,
  is within one unit of the exact `f * v / (k * c)`.
-/

namespace ProofForgeFin.RoundCompose

/-- Two roundings down in a row stay at or below the exact value: if `q₁ * d ≤ n` (`q₁` is at most
`n / d`) and `q₂ * e ≤ q₁ * m` (`q₂` is at most `q₁ * m / e`), every `x ≤ q₂` satisfies
`x * e * d ≤ n * m` (`x` is at most `n * m / (d * e)`). -/
theorem mul_le_of_floor_floor {x q₁ q₂ n m d e : Nat} (hx : x ≤ q₂) (h2 : q₂ * e ≤ q₁ * m)
    (h1 : q₁ * d ≤ n) : x * e * d ≤ n * m := by
  have k1 : x * e ≤ q₁ * m := Nat.le_trans (Nat.mul_le_mul_right e hx) h2
  have k2 : x * e * d ≤ q₁ * m * d := Nat.mul_le_mul_right d k1
  have k3 : q₁ * d * m ≤ n * m := Nat.mul_le_mul_right m h1
  have e1 : q₁ * m * d = q₁ * d * m := by rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]
  omega

/-- A value at most `x * k / c` is at most every upper bound `m` of a quotient `q * k / c` with
`x ≤ q`: from `u * c ≤ x * k`, `x ≤ q`, `q * k ≤ m * c` and `0 < c`, `u ≤ m`. -/
theorem le_of_floor_le_floor {u c x k q m : Nat} (hc : 0 < c) (h1 : u * c ≤ x * k) (hx : x ≤ q)
    (h2 : q * k ≤ m * c) : u ≤ m := by
  apply Nat.le_of_mul_le_mul_right _ hc
  have : x * k ≤ q * k := Nat.mul_le_mul_right k hx
  omega

/-- `v / c` rounded down, then the fraction `f / k` of it rounded up, with `f < k`: from
`u * c ≤ v < (u + 1) * c` and `u * f ≤ x * k < u * f + k`, the result `x` is within one unit of the
exact `f * v / (k * c)`: `f * v < k * c * (x + 1)` and `k * c * x < f * v + k * c`. -/
theorem ceil_frac_floor_bounds {f k v c u x : Nat} (hf : f < k) (hc : 0 < c) (f1 : u * c ≤ v)
    (g1 : v < (u + 1) * c) (f2 : u * f ≤ x * k) (g2 : x * k < u * f + k) :
    f * v < k * c * (x + 1) ∧ k * c * x < f * v + k * c := by
  have k1 : f * v ≤ f * ((u + 1) * c) := Nat.mul_le_mul_left f (Nat.le_of_lt g1)
  have k2 : u * f * c ≤ x * k * c := Nat.mul_le_mul_right c f2
  have k3 : f * c < k * c := Nat.mul_lt_mul_of_pos_right hf hc
  have k4 : x * k * c < (u * f + k) * c := Nat.mul_lt_mul_of_pos_right g2 hc
  have k5 : f * (u * c) ≤ f * v := Nat.mul_le_mul_left f f1
  have e1 : f * ((u + 1) * c) = u * f * c + f * c := by grind
  have e2 : k * c * (x + 1) = x * k * c + k * c := by grind
  have e4 : (u * f + k) * c = f * (u * c) + k * c := by grind
  have e5 : k * c * x = x * k * c := by grind
  omega

end ProofForgeFin.RoundCompose
