**Proof plan.** In the invalid case, `step` is the identity, so conservation is immediate. In the valid case, accounts are unchanged and each balance is `expectedBalance`: decompose its sum over `s.accounts` into the old total, minus `amount` charged to the source (present in `s.accounts`, duplicate-free), plus all credited shares. Shares vanish off `r.recipients`, so by the subset lemma the credited sum may be taken over `r.recipients`; the offset `indexOf?` lemma rewrites that as a sum over positions `0, …, n-1`. Finally, `fairShare` is the constant quotient `amount / n` plus a `1`-indicator for the first `amount % n` positions, whose range sums are `n * (amount / n)` and `amount % n`; `Nat.div_add_mod` gives exactly `amount`, cancelling the debit.

```lean
theorem plan0_sumOver_range_const : ∀ (n : Nat) (c : Int),
    sumOver (List.range n) (fun _ => c) = (n : Int) * c := by sorry

theorem plan0_sumOver_range_indicator : ∀ (n m : Nat), m ≤ n →
    sumOver (List.range n) (fun i => if i < m then (1 : Int) else 0) = (m : Int) := by sorry

theorem plan0_sumOver_range_fairShare : ∀ (amount n : Nat), 0 < n →
    sumOver (List.range n) (fun i => ((fairShare amount n i : Nat) : Int)) =
      (amount : Int) := by sorry

theorem plan0_sumOver_indexOf_offset : ∀ (amount n k : Nat) (l : List AccountId),
    l.Nodup →
    sumOver l (fun a => match indexOf? l a with
      | some i => ((fairShare amount n (k + i) : Nat) : Int)
      | none => 0) =
    sumOver (List.range l.length) (fun i => ((fairShare amount n (k + i) : Nat) : Int)) := by sorry

theorem plan0_sumOver_eq_of_subset : ∀ (l sub : List AccountId) (f : AccountId → Int),
    l.Nodup → sub.Nodup →
    (∀ x ∈ sub, x ∈ l) →
    (∀ x, x ∉ sub → f x = 0) →
    sumOver l f = sumOver sub f := by sorry

theorem plan0_sumOver_expectedBalance : ∀ (s : State) (r : Request),
    s.accounts.Nodup → r.source ∈ s.accounts →
    sumOver s.accounts (fun a => expectedBalance s r a) =
      total s - (r.amount : Int) +
        sumOver s.accounts (fun a => ((shareOf r a : Nat) : Int)) := by sorry
```