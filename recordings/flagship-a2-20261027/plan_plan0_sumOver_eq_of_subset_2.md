(1) Proof plan: Split the sum over `l` at any prescribed member using `List.erase`: nodup is preserved by erasure, membership in an erasure gives the original membership and (under nodup) inequality to the erased element, and membership is preserved when erasing a different element. Hence `sumOver l f = f a + sumOver (l.erase a) f` for `a ∈ l`. Then prove a localized form of the subset lemma; where `f` is only assumed to vanish on elements of `l` outside `sub`; by induction on `l` generalizing `sub`: if the head is outside `sub` it contributes `0` and the induction hypothesis applies; if it is inside `sub`, split both sums at the head via the erase lemma and apply the induction hypothesis to the tail and the erased `sub`, using the membership/nodup erase facts. The original statement follows immediately since its global vanishing hypothesis implies the localized one.

(2)
```lean
theorem plan2_nodup_erase (l : List AccountId) (a : AccountId) (hl : l.Nodup) :
    (l.erase a).Nodup := by sorry

theorem plan2_mem_erase_of_mem_ne (l : List AccountId) (a b : AccountId)
    (ha : a ∈ l) (hne : a ≠ b) : a ∈ l.erase b := by sorry

theorem plan2_mem_of_mem_erase (l : List AccountId) (a b : AccountId)
    (ha : a ∈ l.erase b) : a ∈ l := by sorry

theorem plan2_ne_of_mem_erase_of_nodup (l : List AccountId) (a b : AccountId)
    (hl : l.Nodup) (ha : a ∈ l.erase b) : a ≠ b := by sorry

theorem plan2_sumOver_erase_add (l : List AccountId) (hl : l.Nodup)
    (f : AccountId → Int) (a : AccountId) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (l.erase a) f := by sorry

theorem plan2_sumOver_eq_of_subset_local {l sub : List AccountId}
    (hl : l.Nodup) (hsubnd : sub.Nodup) (hsub : ∀ x ∈ sub, x ∈ l)
    (f : AccountId → Int) (hz : ∀ a ∈ l, a ∉ sub → f a = 0) :
    sumOver l f = sumOver sub f := by sorry
```