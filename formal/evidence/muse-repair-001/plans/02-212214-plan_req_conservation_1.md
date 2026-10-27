(1) Proof plan: The existing support-subset attempt is missing `small.Nodup`, without which it is false for duplicated recipients. Prove conservation by first showing that a sum supported on `small` is unchanged when summed over the larger duplicate-free account list. Isolate the list bookkeeping: vanishing sums, removing one element with `List.erase`, membership and duplicate-freeness of `erase`, and finally the subset-sum equality by induction on `small`. Combined with the already-established fact that recipient shares sum to `amount`, this makes the total-balance calculation in `req_conservation` a routine `sumOver` rewrite followed by `omega`.

(2)
```lean
theorem plan1_sumOver_eq_zero_of_forall_zero (l : List AccountId) (f : AccountId → Int)
    (h : ∀ a ∈ l, f a = 0) :
    sumOver l f = 0 := by sorry

theorem plan1_sumOver_erase_add (l : List AccountId) (f : AccountId → Int) (a : AccountId)
    (hl : l.Nodup) (ha : a ∈ l) :
    f a + sumOver (l.erase a) f = sumOver l f := by sorry

theorem plan1_mem_erase_iff_of_nodup {l : List AccountId} {x a : AccountId}
    (hl : l.Nodup) :
    x ∈ l.erase a ↔ x ≠ a ∧ x ∈ l := by sorry

theorem plan1_nodup_erase (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (l.erase a).Nodup := by sorry

theorem plan1_sumOver_eq_of_support_subset (big small : List AccountId)
    (f : AccountId → Int) (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hsupport : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry
```