**Proof plan.** Prove the two halves of `plan0_sortedIdxs_props` separately and combine them. Membership for `sortedIdxs` goes by induction on `n`, unfolding one step with `sortedIdxs_succ` and using the existing `insertIdx_mem_hlp4` characterisation (`x ∈ insertIdx rems a l ↔ x = a ∨ x ∈ l`), closing the arithmetic step with `omega`. For `Nodup`, first show insertion of a fresh index into a duplicate-free list stays duplicate-free (induction on the list, splitting on the comparison in `insertIdx`, again using `insertIdx_mem_hlp4`); then induct on `n`, where freshness of `n` in `sortedIdxs rems n` is exactly the membership lemma just proved. The target is the conjunction of these two facts.

```lean
theorem plan2_insertIdx_nodup (rems : List Nat) (i : Nat) (l : List Nat)
    (hnd : l.Nodup) (hi : i ∉ l) : (insertIdx rems i l).Nodup := by sorry

theorem plan2_sortedIdxs_mem (rems : List Nat) (n i : Nat) :
    i ∈ sortedIdxs rems n ↔ i < n := by sorry

theorem plan2_sortedIdxs_nodup (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup := by sorry

theorem plan2_sortedIdxs_props (rems : List Nat) (n : Nat) :
    (sortedIdxs rems n).Nodup ∧ ∀ i : Nat, i ∈ sortedIdxs rems n ↔ i < n := by sorry
```