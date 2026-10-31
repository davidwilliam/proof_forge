**Proof plan**

`InvR` tracks equality of parent counts, parent quantities, cumulative sent amounts, and the bound that every recorded child belongs to an existing parent. The parent case is already handled by `invR_parent5`, and the acknowledgement case leaves the whole system unchanged. For a fill, updating a child's `done` field changes neither `sentFor` (via `sentFor_set_done`) nor the parent quantities and sent amounts, and it preserves the parent bound because the updated child keeps its parent. The only substantial case is routing: split on the guard in `step`. If the guard fails, the state and recorded kids are unchanged. If it succeeds, the router increments `sent` for parent `id` by exactly `min liq (qty - sent)`, while the truth appends one kid `⟨id, c, 0⟩`; a single-append formula for `sentFor` shows these two updates agree for `id` and are unchanged for all other parents, and `id < nParents = nOrders` gives the parent bound for the new kid. Assembling the four event cases then proves `plan0_invR_preserved` by `cases e`.

```lean
theorem plan1_sentFor_append_single : ∀ (l : List Kid) (id c j : Nat),
    sentFor (l ++ [⟨id, c, 0⟩]) j = sentFor l j + (if id = j then c else 0) := by sorry

theorem plan1_invR_route_of_no : ∀ (b : Build) (x : Sys) (id liq : Nat),
    InvR x →
    ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    InvR (advance step b x (.route id liq)) := by sorry

theorem plan1_invR_route_of_yes : ∀ (b : Build) (x : Sys) (id liq : Nat),
    InvR x →
    (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) →
    InvR (advance step b x (.route id liq)) := by sorry

theorem plan1_invR_route : ∀ (b : Build) (x : Sys) (id liq : Nat),
    InvR x → InvR (advance step b x (.route id liq)) := by sorry

theorem plan1_invR_fill : ∀ (b : Build) (x : Sys) (k q : Nat),
    InvR x → InvR (advance step b x (.fill k q)) := by sorry

theorem plan1_invR_ack : ∀ (b : Build) (x : Sys) (k : Nat),
    InvR x → InvR (advance step b x (.ack k)) := by sorry
```