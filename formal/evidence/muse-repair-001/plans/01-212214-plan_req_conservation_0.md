(1) **Proof plan:** In the success case, `ValidPayout` must hold (otherwise the outcome would be `rejected`). The account list is unchanged, so expand `total` over `s.accounts` and rewrite the new balances as `expectedBalance`. Using `sumOver_add`, `sumOver_sub`, and the supplied `sumOver_ite_eq`, the source deduction contributes exactly `r.amount`. It therefore suffices to prove that the `shareOf` amounts over all accounts sum to `r.amount`. This follows by: shifting a sum over `List.range`, identifying the sum over a duplicate-free recipient list with a sum over its index range, computing the range sum of `fairShare` (the quotient part contributes `n * (amount / n)` and the indicator part contributes `amount % n`), and finally extending the recipient sum to the account universe because `shareOf` is zero outside the recipients (via an erase/subset sum lemma).

(2)
```lean
theorem plan0_sumOver_range_succ_shift (g : Nat → Int) (n : Nat) :
    sumOver (List.range (n + 1)) g
      = g 0 + sumOver (List.range n) (fun i => g (i + 1)) := by sorry

theorem plan0_sumOver_indexOf?_range (l : List AccountId) (g : Nat → Nat) (hl : l.Nodup) :
    sumOver l (fun a => (((match indexOf? l a with | some i => g i | none => 0) : Nat) : Int))
      = sumOver (List.range l.length) (fun i => ((g i : Nat) : Int)) := by sorry

theorem plan0_sum_range_fairShare_prefix (amount n k : Nat) :
    sumOver (List.range k) (fun i => ((fairShare amount n i : Nat) : Int))
      = ((k : Nat) : Int) * (((amount / n : Nat)) : Int)
        + (((min k (amount % n) : Nat)) : Int) := by sorry

theorem plan0_sumOver_recipients_fairShare (amount : Nat) (l : List AccountId)
    (hl : l.Nodup) (hne : l ≠ []) :
    sumOver l (fun a => (((match indexOf? l a with
      | some i => fairShare amount l.length i
      | none => 0) : Nat) : Int)) = (amount : Int) := by sorry

theorem plan0_sumOver_erase_add (l : List AccountId) (f : AccountId → Int) (a : AccountId)
    (hl : l.Nodup) (ha : a ∈ l) :
    f a + sumOver (l.erase a) f = sumOver l f := by sorry

theorem plan0_sumOver_eq_of_support_subset (big small : List AccountId)
    (f : AccountId → Int) (hbig : big.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hsupport : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry
```