**Proof plan.** Prove `sumOver s.accounts (shareOf r ·) = r.amount` by transporting the sum to recipients, then to an index range. The key range identity is `range (n+1) = 0 :: map (·+1) (range n)`, which together with a `sumOver`-over-`map` lemma makes the previously failing `sumOver_eq_range` induction routine (cons case: peel index `0`, shift the rest). The range sum of `fairShare` splits, via `sumOver_add`, into a constant part `n * (amount / n)` and an indicator part counting the first `amount % n` indices, closing by `Nat.div_add_mod`. Finally, an erase lemma for `sumOver` over a `Nodup` list makes the subset argument (recipients ⊆ accounts, `shareOf = 0` off recipients) a routine induction, giving the accounts sum from the recipients sum.

```lean
theorem plan1_range_succ_cons (n : Nat) :
    List.range (n + 1) = 0 :: List.map (fun i => i + 1) (List.range n) := by sorry

theorem plan1_sumOver_map {α β : Type} (l : List α) (h : α → β) (f : β → Int) :
    sumOver (List.map h l) f = sumOver l (fun a => f (h a)) := by sorry

theorem plan1_sumOver_range_const (n : Nat) (c : Int) :
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem plan1_sumOver_range_indicator (n k : Nat) (hk : k ≤ n) :
    sumOver (List.range n) (fun i => if i < k then (1 : Int) else 0) = (k : Int) := by sorry

theorem plan1_fairShare_range_sum (amount n : Nat) (hn : 0 < n) :
    sumOver (List.range n) (fun i => (fairShare amount n i : Int)) = (amount : Int) := by sorry

theorem plan1_sumOver_erase_mem (l : List AccountId) (hl : l.Nodup)
    (a : AccountId) (ha : a ∈ l) (f : AccountId → Int) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry
```