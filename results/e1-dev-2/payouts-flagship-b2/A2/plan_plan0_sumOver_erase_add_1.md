Split the list at the first occurrence of `a`. Erasing `a` then removes exactly that occurrence, while the sum over the split list decomposes into the sum before `a`, the term `f a`, and the sum after `a`; reassociating integer addition gives the result.

```lean
theorem plan1_exists_split_of_mem (l : List AccountId) (a : AccountId) (ha : a ∈ l) :
    ∃ l1 l2 : List AccountId, l = l1 ++ a :: l2 ∧ a ∉ l1 := by sorry

theorem plan1_erase_append_cons (l1 l2 : List AccountId) (a : AccountId)
    (h : a ∉ l1) :
    List.erase (l1 ++ a :: l2) a = l1 ++ l2 := by sorry

theorem plan1_sumOver_append_cons (l1 l2 : List AccountId) (a : AccountId)
    (f : AccountId → Int) :
    sumOver (l1 ++ a :: l2) f = f a + (sumOver l1 f + sumOver l2 f) := by sorry

theorem plan1_sumOver_erase_add_final (l : List AccountId) (f : AccountId → Int)
    (a : AccountId) (hl : l.Nodup) (ha : a ∈ l) :
    sumOver l f = f a + sumOver (List.erase l a) f := by sorry
```