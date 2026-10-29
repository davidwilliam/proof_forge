(1) **Proof plan:** Unfold `split` and split on `n = 0` (impossible for a `some` result) and on the sign of `amount`. The underlying natural-number shares have sum `n * q + min r n` by the existing `cons_base_sum4`. Since `r = amount.natAbs % n < n`, this equals `amount.natAbs` by division-with-remainder. Casting that sum to `Int` gives `amount` in the nonnegative case, and its negation gives `amount` in the negative case. The helpers below isolate the list-sum casts, the division/min arithmetic, and the two signed base-sum computations.

(2)
```lean
theorem plan0_sum_map_coe (l : List Nat) :
    (l.map fun k : Nat => (k : Int)).sum = ((l.sum : Nat) : Int) := by sorry

theorem plan0_sum_map_neg_coe (l : List Nat) :
    (l.map fun k : Nat => -(k : Int)).sum = -((l.sum : Nat) : Int) := by sorry

theorem plan0_div_add_min (an n : Nat) (hn : 0 < n) :
    n * (an / n) + min (an % n) n = an := by sorry

theorem plan0_base_sum_coe (n q r : Nat) :
    (((List.range n).map fun p => q + if p < r then 1 else 0).map
      fun k : Nat => (k : Int)).sum
      = ((n * q + min r n : Nat) : Int) := by sorry

theorem plan0_base_sum_neg_coe (n q r : Nat) :
    (((List.range n).map fun p => q + if p < r then 1 else 0).map
      fun k : Nat => -(k : Int)).sum
      = -((n * q + min r n : Nat) : Int) := by sorry
```