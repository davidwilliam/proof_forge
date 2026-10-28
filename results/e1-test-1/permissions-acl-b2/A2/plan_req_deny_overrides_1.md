If granted, then `decision` is true (`gj_learn2`). Under `Overridden`, the filtered deny list is nonempty, so truth of `decision` forces `maxDepth denies < maxDepth allows`. But the overriding deny bounds every matching allow's depth, hence `maxDepth allows ≤ maxDepth denies` by `do_bounded4`/`do_mem_le4` and the filtered-membership lemmas, a contradiction by `omega`. Therefore `decision` is not true and the outcome cannot be `.granted`.

```lean
theorem plan1_denies_not_empty_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = false := by sorry

theorem plan1_decision_true_lt_of_denies_not_empty (l : List Entry) (r : Request) (hdec : decision l r = true) (hne : ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)).isEmpty = false) : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) < maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) := by sorry

theorem plan1_allow_depth_le_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) (a : Entry) (ha : a ∈ (l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) : depth a ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by sorry

theorem plan1_maxDepth_allows_le_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) : maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .allow)) ≤ maxDepth ((l.filter (matchesB · r)).filter (fun e => e.effect == .deny)) := by sorry

theorem plan1_decision_not_true_of_overridden (l : List Entry) (r : Request) (h : Overridden l r) : decision l r ≠ true := by sorry

theorem plan1_step_not_granted_of_overridden (s : State) (r : Request) (h : Overridden s.entries r) : (step s r).1 ≠ .granted := by sorry
```