## Proof plan

Prove the accounts-sum by first proving a general reindexing principle for `sumOver`: over two duplicate-free lists, if every element of the second occurs in the first and the summand vanishes outside the second, the sums agree. Prove this by induction on the first list, generalizing the second. For a head belonging to the second list, split both sums using the `erase` decomposition (`sumOver l f = f a + sumOver (l.erase a) f`); for a head outside it, the head term is zero. Erase preserves `Nodup` and its members are unequal members of the original list. Applied with `f a = (shareOf r a : Int)`, `l₁ = s.accounts`, and `l₂ = r.recipients`, the zero condition is `indexOf?_eq_none`, the inclusion is from `ValidPayout`, and the remaining recipients-sum is `arch0_sum_shareOf_recipients_amount`.

```lean
theorem plan0_shareOf_int_eq_zero (r : Request) (a : AccountId)
    (h : a ∉ r.recipients) : (shareOf r a : Int) = 0 := by sorry

theorem plan0_sumOver_eq_add_sumOver_erase (f : AccountId → Int)
    (l : List AccountId) (a : AccountId) (hl : l.Nodup) (hmem : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry

theorem plan0_of_mem_erase (a b : AccountId) (l : List AccountId)
    (h : a ∈ l.erase b) : a ≠ b ∧ a ∈ l := by sorry

theorem plan0_nodup_erase (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) : (l.erase a).Nodup := by sorry

theorem plan0_sumOver_eq_of_subset_of_eq_zero (f : AccountId → Int)
    (l1 l2 : List AccountId) (hl1 : l1.Nodup) (hl2 : l2.Nodup)
    (hsub : ∀ x ∈ l2, x ∈ l1) (hzero : ∀ x ∈ l1, x ∉ l2 → f x = 0) :
    sumOver l1 f = sumOver l2 f := by sorry

theorem plan0_sum_shareOf_accounts_eq_amount (s : State) (r : Request)
    (hv : ValidPayout s r) :
    sumOver s.accounts (fun a => (shareOf r a : Int)) = (r.amount : Int) := by sorry
```