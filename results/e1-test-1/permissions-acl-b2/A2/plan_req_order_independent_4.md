Short proof plan: an outcome depends only on the valid-query test (which does not involve `entries`) and on `decision s.entries r`. `decision` depends only on whether the filtered allow/deny lists are empty and on their `maxDepth` values, which depend only on membership in those filtered lists. A permutation preserves membership, hence preserves membership in the allow/deny filters, their emptiness and maxima, the decision, and finally the first component of `step`.

```lean
theorem plan4_mem_iff_of_perm {l l' : List Entry} (h : l.Perm l') (x : Entry) :
    x ∈ l ↔ x ∈ l' := by sorry

theorem plan4_maxDepth_eq_of_mem_iff {es1 es2 : List Entry}
    (h : ∀ x, x ∈ es1 ↔ x ∈ es2) : maxDepth es1 = maxDepth es2 := by sorry

theorem plan4_isEmpty_eq_of_mem_iff {es1 es2 : List Entry}
    (h : ∀ x, x ∈ es1 ↔ x ∈ es2) : es1.isEmpty = es2.isEmpty := by sorry

theorem plan4_decision_eq_of_mem_iff {l1 l2 : List Entry} (r : Request)
    (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : decision l1 r = decision l2 r := by sorry

theorem plan4_step_fst_eq_of_perm (s : State) (r : Request) (l : List Entry)
    (h : l.Perm s.entries) :
    (step { s with entries := l } r).1 = (step s r).1 := by sorry
```