Short proof plan: From a successful post, first recover `ValidPost s e`. Its freshness conditions give `e.id ∉ ids s.journal`, so searching `s.journal ++ [e]` finds exactly `e`; hence the posted entry is valid to reverse, `revLines` after the post returns `e.lines`, and the reverse balance computes `(s.balance a + netOf e.lines a) - netOf e.lines a = s.balance a`. Funext then gives the required balance equality, paired with the reverse succeeding.

```lean
theorem plan0_findEntry_append_self (j : List Entry) (e : Entry) (h : e.id ∉ ids j) : findEntry (j ++ [e]) e.id = some e := by sorry

theorem plan0_validPost_of_post_ok (s : State) (e : Entry) (h : (step s (.post e)).1 = .ok) : ValidPost s e := by sorry

theorem plan0_validReverse_after_post (s : State) (e : Entry) (h : ValidPost s e) : ValidReverse (step s (.post e)).2 e.id := by sorry

theorem plan0_revLines_after_post (s : State) (e : Entry) (h : ValidPost s e) : revLines (step s (.post e)).2 e.id = e.lines := by sorry

theorem plan0_reverse_after_post_ok (s : State) (e : Entry) (h : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).1 = .ok := by sorry

theorem plan0_reverse_after_post_balance (s : State) (e : Entry) (h : ValidPost s e) : (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance := by sorry
```