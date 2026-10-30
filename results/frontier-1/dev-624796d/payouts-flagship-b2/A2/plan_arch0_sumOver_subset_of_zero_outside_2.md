(1) **Proof plan.** Strengthen the zero hypothesis to only concern elements of `l`: it is preserved after removing the head of `sub` from `l`, whereas the global hypothesis is not needed for that element. First prove that a sum of zeros is zero, that a duplicate-free list’s sum splits as the value at a member plus the sum over the erased list, and the needed membership/`Nodup` facts for `List.erase`. Then induct on `sub`, generalizing `l`: the empty case uses the zero-sum lemma; for `a :: sub`, split `l` at `a` with the erase lemma, cancel `f a`, and apply the induction hypothesis to `List.erase l a` and `sub`. The original theorem follows immediately because its global zero hypothesis implies the localized one.

(2)
```lean
theorem plan2_sumOver_eq_zero_of_all_zero (l : List AccountId) (f : AccountId → Int)
    (h : ∀ a ∈ l, f a = 0) :
    sumOver l f = 0 := by sorry

theorem plan2_sumOver_erase_add (l : List AccountId) (f : AccountId → Int)
    (hl : l.Nodup) {a : AccountId} (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by sorry

theorem plan2_mem_erase_of_mem_ne {l : List AccountId} {a x : AccountId}
    (hx : x ∈ l) (hne : x ≠ a) :
    x ∈ List.erase l a := by sorry

theorem plan2_nodup_erase_of_nodup (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (List.erase l a).Nodup := by sorry

theorem plan2_sumOver_subset_of_zero_in_list (l sub : List AccountId)
    (f : AccountId → Int)
    (hl : l.Nodup) (hsub : sub.Nodup)
    (hsubset : ∀ x ∈ sub, x ∈ l)
    (hzero : ∀ a ∈ l, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by sorry
```