(1) Proof plan: Avoid the failed `Nat.min` route for the range-indicator sum. First decompose `List.range (n+1)` from the front, shifting indices by one. Use that decomposition inductively to evaluate both the indicator sum and, for a duplicate-free list, the sum obtained by looking up each element's `indexOf?`. Then split `fairShare` into its constant quotient part and its one-cent indicator part, sum those parts separately, and recombine them with `Nat.div_add_mod`. Finally, transfer the range computation back to `r.recipients` through `shareOf`/`indexOf?`, using positivity of the length from nonemptiness.

```lean
theorem plan1_sum_range_succ_shift (n : Nat) (f : Nat → Int) :
    sumOver (List.range (n + 1)) f =
      f 0 + sumOver (List.range n) (fun i => f (i + 1)) := by sorry

theorem plan1_sumOver_via_indexOf (l : List AccountId) (f : Nat → Int)
    (hl : l.Nodup) :
    sumOver l
        (fun a => match indexOf? l a with
          | some i => f i
          | none => (0 : Int)) =
      sumOver (List.range l.length) (fun i => f i) := by sorry

theorem plan1_fairShare_cast (amount n i : Nat) :
    (fairShare amount n i : Int) =
      (amount / n : Int) + (if i < amount % n then (1 : Int) else 0) := by sorry

theorem plan1_sum_range_indicator (n m : Nat) (hm : m ≤ n) :
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) =
      (m : Int) := by sorry

theorem plan1_fairShare_sum_range (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) =
      (amount : Int) := by sorry

theorem plan1_sum_recipients_shareOf_eq_range (r : Request)
    (hl : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int)) =
      sumOver (List.range r.recipients.length)
        (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry
```