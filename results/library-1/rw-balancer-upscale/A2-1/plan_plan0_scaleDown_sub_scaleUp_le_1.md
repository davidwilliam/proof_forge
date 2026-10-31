Rewrite the truncated subtraction as a sum inequality: show the down-scaled original balance is at most the down-scaled remaining balance plus the up-scaled removed amount. First handle the exact multiplicative splitting when `t ≤ b`, extend it to an inequality for all `t`, prove the corresponding division-by-`ONE` addition bound, then unfold `scaleDown`/`scaleUp` and combine them; the target follows by `omega`.

```lean
theorem plan1_sub_add_mul_eq (b t r : Nat) (h : t ≤ b) :
    b * r = (b - t) * r + t * r := by sorry

theorem plan1_mul_le_sub_mul_add (b t r : Nat) :
    b * r ≤ (b - t) * r + t * r := by sorry

theorem plan1_div_add_le (u v : Nat) :
    (u + v) / ONE ≤ u / ONE + (v + (ONE - 1)) / ONE := by sorry

theorem plan1_scaleDown_le_add_scaleUp (b t r : Nat) :
    scaleDown b r ≤ scaleDown (b - t) r + scaleUp t r := by sorry
```