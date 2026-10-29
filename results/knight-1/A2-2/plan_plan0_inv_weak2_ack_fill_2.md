**Proof plan:** `ack` leaves both state and truth unchanged, so it preserves `InvWeak2` trivially. For `fill`, the router only updates `cum` and a child's `done` field, while the truth only updates that child's `done`; hence `nParents`, `nOrders`, every parent's `sent`/`qty`, and every truth `sent`/`qty` are unchanged, and membership in the updated kids list still gives a parent below `nOrders`. Combining these component facts rebuilds all five conjuncts of `InvWeak2`, and the conjunction in the target follows from the separate `ack` and `fill` preservation lemmas.

```lean
theorem plan2_ack_preserves (b : Build) (x : Sys) (k : Nat) :
    InvWeak2 x → InvWeak2 (advance step b x (.ack k)) := by sorry

theorem plan2_fill_parents_eq (b : Build) (x : Sys) (k q id : Nat) :
    ((advance step b x (.fill k q)).st.parents id).sent = (x.st.parents id).sent ∧
    ((advance step b x (.fill k q)).st.parents id).qty = (x.st.parents id).qty := by sorry

theorem plan2_fill_counts_truth_eq (b : Build) (x : Sys) (k q : Nat) :
    (advance step b x (.fill k q)).st.nParents = x.st.nParents ∧
    (advance step b x (.fill k q)).tr.nOrders = x.tr.nOrders ∧
    (∀ id, (advance step b x (.fill k q)).tr.sent id = x.tr.sent id) ∧
    (∀ id, (advance step b x (.fill k q)).tr.qty id = x.tr.qty id) := by sorry

theorem plan2_fill_kids_bound (b : Build) (x : Sys) (k q : Nat) :
    (∀ k0 ∈ x.tr.kids, k0.parent < x.tr.nOrders) →
    ∀ k0 ∈ (advance step b x (.fill k q)).tr.kids,
      k0.parent < (advance step b x (.fill k q)).tr.nOrders := by sorry

theorem plan2_fill_preserves (b : Build) (x : Sys) (k q : Nat) :
    InvWeak2 x → InvWeak2 (advance step b x (.fill k q)) := by sorry
```