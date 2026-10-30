(1) **Proof plan:** Split the fair-share sum over `List.range n` into its constant part and its extra-cent indicator part. First sum a constant over a range, then count how many indices in a range lie below a bound; separately handling bounds at least the range length and bounds inside the range by induction, splitting off the last index with `List.range_succ`. Reassembling gives `n * (amount / n) + amount % n`, which equals `amount` by `Nat.div_add_mod` after casting to `Int`.

(2)
```lean
theorem plan1_sumOver_append {α : Type} (l1 l2 : List α) (f : α → Int) :
    sumOver (l1 ++ l2) f = sumOver l1 f + sumOver l2 f := by sorry

theorem plan1_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem plan1_sumOver_range_ite_ge (n m : Nat) (h : n ≤ m) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (n : Int) := by sorry

theorem plan1_sumOver_range_ite_le (m n : Nat) (h : m ≤ n) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by sorry

theorem plan1_sum_fairShare_range_eq (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int))
      = (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) := by sorry

theorem plan1_int_mul_div_add_mod (amount n : Nat) :
    (n : Int) * ((amount / n : Nat) : Int) + ((amount % n : Nat) : Int) = (amount : Int) := by sorry
```