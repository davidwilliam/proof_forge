Proof plan: Split by the sign of `amount`. Pointwise, `keyAt` is either `amount * r - base * S` or its reverse, so the mapped sum becomes a difference of two mapped sums. Evaluate the amount-multiple sum as `amount * ratios.sum` and the base-multiple sum as `(sum of bases) * S`; commutativity of multiplication then gives the two sign cases, and the target follows by case split.

```lean
theorem plan7_keyAt_eq (amount : Int) (S : Nat) (r : Nat) :
    keyAt amount S r =
      if 0 ≤ amount then amount * (r : Int) - baseAt amount S r * (S : Int)
      else baseAt amount S r * (S : Int) - amount * (r : Int) := by sorry

theorem plan7_sum_map_sub (l : List Nat) (f g : Nat → Int) :
    (l.map (fun r => f r - g r)).sum = (l.map f).sum - (l.map g).sum := by sorry

theorem plan7_sum_map_amount_mul (amount : Int) (l : List Nat) :
    (l.map (fun r : Nat => amount * (r : Int))).sum = amount * (l.sum : Int) := by sorry

theorem plan7_sum_map_base_mul (amount : Int) (S : Nat) (l : List Nat) :
    (l.map (fun r : Nat => baseAt amount S r * (S : Int))).sum =
      (l.map (baseAt amount S)).sum * (S : Int) := by sorry

theorem plan7_sum_keys_of_nonneg (amount : Int) (S : Nat) (ratios : List Nat)
    (ha : 0 ≤ amount) :
    (ratios.map (keyAt amount S)).sum =
      amount * (ratios.sum : Int) - (S : Int) * (ratios.map (baseAt amount S)).sum := by sorry

theorem plan7_sum_keys_of_neg (amount : Int) (S : Nat) (ratios : List Nat)
    (ha : ¬ 0 ≤ amount) :
    (ratios.map (keyAt amount S)).sum =
      (S : Int) * (ratios.map (baseAt amount S)).sum - amount * (ratios.sum : Int) := by sorry
```