If `ValidEntry s e` holds, each boolean test in `acceptable s e` must succeed: the accounts list is duplicate-free, the lines are non-empty, every line uses a known account, every amount is non-zero, the line sum is zero, and the entry ID is not already posted. Converting the membership and non-vanishing hypotheses with `List.all`, and the non-membership hypothesis with `List.contains`, gives `acceptable s e = true`; unfolding `step` on that branch then yields outcome `.ok`.

```lean
theorem plan0_isEmpty_false_of_ne_nil {ls : List Line} (h : ls ≠ []) : (!ls.isEmpty) = true := by sorry

theorem plan0_all_contains_of_forall_mem {accounts : List AccountId} {ls : List Line} (h : ∀ l ∈ ls, l.1 ∈ accounts) : ls.all (fun l => accounts.contains l.1) = true := by sorry

theorem plan0_all_bne_of_forall_ne {ls : List Line} (h : ∀ l ∈ ls, l.2 ≠ 0) : ls.all (fun l => l.2 != 0) = true := by sorry

theorem plan0_not_contains_of_not_mem {posted : List EntryId} {id : EntryId} (h : id ∉ posted) : (!posted.contains id) = true := by sorry

theorem plan0_acceptable_true_of_valid {s : State} {e : Entry} (h : ValidEntry s e) : acceptable s e = true := by sorry

theorem plan0_fst_step_ok_of_acceptable {s : State} {e : Entry} (h : acceptable s e = true) : (step s e).1 = Outcome.ok := by sorry
```