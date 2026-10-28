If posting succeeds, the post must have been valid; otherwise `step` would reject. Unfolding a valid post gives the appended journal and increased balances, and `e.id` is fresh for the old journal, so searching the appended journal finds `e`. Since `e.id` was also not reversed, the following reversal succeeds and pointwise computes `(balance + net) - net = balance`, hence the balances are restored by function extensionality.

```lean
theorem plan0_valid_of_post_ok (s : State) (e : Entry) (h : (step s (.post e)).1 = .ok) : ValidPost s e := by sorry

theorem plan0_step_post_eq (s : State) (e : Entry) (hv : ValidPost s e) : step s (.post e) = (.ok, { s with balance := fun a => s.balance a + netOf e.lines a, journal := s.journal ++ [e] }) := by sorry

theorem plan0_findEntry_append_notMem (j1 j2 : List Entry) (i : EntryId) (h : i ∉ ids j1) : findEntry (j1 ++ j2) i = findEntry j2 i := by sorry

theorem plan0_findEntry_append_singleton (j : List Entry) (e : Entry) (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by sorry

theorem plan0_reverse_after_post_ok (s : State) (e : Entry) (hv : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by sorry

theorem plan0_balance_after_reverse_post (s : State) (e : Entry) (hv : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance := by sorry
```