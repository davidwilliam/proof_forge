**Proof plan.** Prove the target by induction on `l`. For the empty list both sides are `0`. For `x :: xs`, split the sum into the head term and the tail sum. The head has index `0`; for an element of the tail, its index in `x :: xs` is one more than its index in `xs`, using `Nodup` to ensure the head is not repeated. Rewrite the tail via `sumOver_congr` to a shifted function, apply the induction hypothesis, and finish by decomposing `List.range (xs.length + 1)` head-first. The range decomposition itself is built from the easier last-element decomposition.

```lean
theorem plan3_sumOver_range_succ_last (n : Nat) (g : Nat → Int) :
    sumOver (List.range (n + 1)) g = sumOver (List.range n) g + g n := by sorry

theorem plan3_sumOver_range_succ_head (n : Nat) (g : Nat → Int) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by sorry

theorem plan3_indexOf_cons_head (x : AccountId) (xs : List AccountId) (g : Nat → Int) :
    (match indexOf? (x :: xs) x with
     | some i => g i
     | none => 0) = g 0 := by sorry

theorem plan3_indexOf_cons_tail (x a : AccountId) (xs : List AccountId)
    (g : Nat → Int) (hne : x ≠ a) :
    (match indexOf? (x :: xs) a with
     | some i => g i
     | none => 0)
      = (match indexOf? xs a with
         | some i => g (i + 1)
         | none => 0) := by sorry
```