(1) The stated lemma is false without deduplication of `small`: for `big = [1]`, `small = [1, 1]`, and `f 1 = 1`, the hypotheses hold but the sums are `1` and `2`. Add `small.Nodup`; available for recipients from `ValidPayout`. Prove the corrected statement by induction on `big`: if the head occurs in `small`, remove it from both lists using erase-addition, erase-membership, and preservation of `Nodup`; otherwise its contribution is zero by the support hypothesis and the induction hypothesis applies unchanged.

(2)
```lean
theorem plan0_erase_add_for_support (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    f a + sumOver (l.erase a) f = sumOver l f := by sorry

theorem plan0_mem_erase_for_support {l : List AccountId} {x a : AccountId}
    (hl : l.Nodup) :
    x ∈ l.erase a ↔ x ≠ a ∧ x ∈ l := by sorry

theorem plan0_nodup_erase_for_support (l : List AccountId) (a : AccountId)
    (hl : l.Nodup) :
    (l.erase a).Nodup := by sorry

theorem plan0_sumOver_support_subset_with_nodup (big small : List AccountId)
    (f : AccountId → Int) (hbig : big.Nodup) (hsmall : small.Nodup)
    (hsub : ∀ x ∈ small, x ∈ big)
    (hsupport : ∀ x ∈ big, x ∉ small → f x = 0) :
    sumOver big f = sumOver small f := by sorry
```