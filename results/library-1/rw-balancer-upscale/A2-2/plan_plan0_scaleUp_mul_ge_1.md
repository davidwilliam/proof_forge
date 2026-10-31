Short proof plan: Use the division algorithm on `a * r + ONE - 1` with divisor `ONE`. Since the remainder is `< ONE`, the quotient multiplied by `ONE` must be at least `a * r`. Rewriting `scaleUp` into this ceiling form then gives the result directly.

```lean
theorem plan1_one_pos : 0 < ONE := by sorry

theorem plan1_div_mod_eq : ∀ (m k : Nat), (m / k) * k + m % k = m := by sorry

theorem plan1_mod_lt_pos : ∀ (m k : Nat), 0 < k → m % k < k := by sorry

theorem plan1_le_ceil_mul : ∀ (n d : Nat), 0 < d → n ≤ (n + d - 1) / d * d := by sorry

theorem plan1_scaleUp_eq_ceil : ∀ (a r : Nat), scaleUp a r = (a * r + ONE - 1) / ONE := by sorry
```