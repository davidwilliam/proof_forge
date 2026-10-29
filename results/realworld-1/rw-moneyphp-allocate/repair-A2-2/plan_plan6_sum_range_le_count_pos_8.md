Bound each key by `S - 1` when it is positive and by `0` when it is zero. Sum this pointwise bound over `List.range n` by monotonicity of list sums, then rewrite the summed indicator as `S - 1` times the length of the filter of positive keys, which is exactly the claimed right-hand side.

```lean
theorem plan8_pointwise_le_indicator (S x : Int) (h0 : 0 ≤ x) (hS : x < S) :
    x ≤ (if 0 < x then S - 1 else 0) := by sorry

theorem plan8_sum_le_of_pointwise (n : Nat) (f g : Nat → Int)
    (h : ∀ i, i < n → f i ≤ g i) :
    ((List.range n).map f).sum ≤ ((List.range n).map g).sum := by sorry

theorem plan8_sum_indicator_eq_mul_filter (keys : List Int) (n : Nat) (e : Int) :
    ((List.range n).map (fun j => if 0 < keys.getD j 0 then e else 0)).sum =
      e * (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) := by sorry

theorem plan8_sum_le_indicator_sum (keys : List Int) (n : Nat) (S : Int)
    (hkeys : ∀ j, j < n → 0 ≤ keys.getD j 0 ∧ keys.getD j 0 < S) :
    ((List.range n).map (fun j => keys.getD j 0)).sum ≤
      ((List.range n).map (fun j => if 0 < keys.getD j 0 then S - 1 else 0)).sum := by sorry
```