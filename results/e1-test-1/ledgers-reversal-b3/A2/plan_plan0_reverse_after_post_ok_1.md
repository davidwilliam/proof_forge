Short proof plan: First compute the successful post as an explicit state update. From that, the posted state's journal is `s.journal ++ [e]` and its reversed list is still `s.reversed`. Validity gives `e.id ∉ ids s.journal`, so a general append-singleton lookup lemma shows the posted entry is found, and validity also gives `e.id ∉ s.reversed`, so the entry is not already reversed. Finally, a general reverse-branch lemma says that any state whose journal finds the target entry and whose reversed list omits it reverses with outcome `.ok`; applying it to the posted state proves `plan0_reverse_after_post_ok`.

```lean
theorem plan1_post_eq (s : State) (e : Entry) (hv : ValidPost s e) :
    step s (.post e) =
      (.ok, { s with balance := fun a => s.balance a + netOf e.lines a,
                     journal := s.journal ++ [e] }) := by sorry

theorem plan1_findEntry_append_singleton (j : List Entry) (e : Entry)
    (h : e.id ∉ ids j) :
    findEntry (j ++ [e]) e.id = some e := by sorry

theorem plan1_post_state_finds_and_fresh (s : State) (e : Entry)
    (hv : ValidPost s e) :
    findEntry ((step s (.post e)).2.journal) e.id = some e ∧
      e.id ∉ (step s (.post e)).2.reversed := by sorry

theorem plan1_reverse_ok_of_find (t : State) (i : EntryId) (e : Entry)
    (hf : findEntry t.journal i = some e) (hr : i ∉ t.reversed) :
    (step t (.reverse i)).1 = .ok := by sorry
```