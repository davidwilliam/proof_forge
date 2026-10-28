Proof plan: unfold a valid `post` to its explicit successor state, so its journal is `s.journal ++ [e]` and its `reversed` list is unchanged. Then `e.id` is in the appended journal's IDs and, by validity of the post, is not reversed, giving `ValidReverse` for the successor state. Finally, a valid `reverse` always returns `.ok` by definition of `step`.

```lean
theorem plan1_step_post_eq (s : State) (e : Entry) (h : ValidPost s e) :
    step s (.post e) =
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a,
                     journal := s.journal ++ [e] }) := by sorry

theorem plan1_mem_ids_append_self (j : List Entry) (e : Entry) :
    e.id ∈ ids (j ++ [e]) := by sorry

theorem plan1_validReverse_after_post (s : State) (e : Entry) (h : ValidPost s e) :
    ValidReverse (step s (.post e)).2 e.id := by sorry

theorem plan1_reverse_ok_of_valid (s : State) (i : EntryId) (h : ValidReverse s i) :
    (step s (.reverse i)).1 = .ok := by sorry
```