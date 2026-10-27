**Proof plan**

First show `shareOf` vanishes outside `r.recipients`. A general subset lemma then reduces the sum over the duplicate-free account list to the sum over the recipient list. Next, rewrite each recipient's share through its `indexOf?` position and use the previously established index-shift sum to convert the recipient sum into a sum over `List.range r.recipients.length`. Finally, split `fairShare` into its constant quotient part and its indicator remainder part: these sum to `n * (amount / n)` and `amount % n`, respectively, whose total is `amount` by `Nat.div_add_mod`. Positivity of the length follows from `r.recipients ≠ []`.

```lean
theorem plan1_shareOf_eq_zero_of_not_mem (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) : shareOf r a = 0 := by sorry

theorem plan1_sumOver_eq_of_vanishing_outside (f : AccountId → Int)
    {l sub : List AccountId} (hl : l.Nodup) (hsub : sub.Nodup)
    (hsubset : ∀ x ∈ sub, x ∈ l)
    (hzero : ∀ x ∈ l, x ∉ sub → f x = 0) :
    sumOver l f = sumOver sub f := by sorry

theorem plan1_sum_indicator_min (n r : Nat) :
    sumOver (List.range n) (fun i => if i < r then (1 : Int) else 0)
      = ((Nat.min n r : Nat) : Int) := by sorry

theorem plan1_sum_range_fairShare (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n)
        (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem plan1_sumOver_recipients_shareOf_eq_range (r : Request)
    (hrec : r.recipients.Nodup) :
    sumOver r.recipients (fun a => (shareOf r a : Int))
      = sumOver (List.range r.recipients.length)
          (fun i => (fairShare r.amount r.recipients.length i : Int)) := by sorry
```