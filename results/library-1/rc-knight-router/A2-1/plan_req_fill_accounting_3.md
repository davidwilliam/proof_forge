**Proof plan.** The stronger invariant `InvFull` is already proved at `start` (`invFull_start`), for parent events (`invFull_parent4`), and for acknowledgements (`invFull_ack6`). It remains to preserve it under routing and fills. Routing does not change any parent's cumulative quantity or any truth execution (reuse `adv_route_st_parents_cum5` and `adv_route_exec_eq`), and it appends at most one new child, at the old length, with `done = 0`, while the weaker `Inv` part is `plan0_inv_advance_route`. For a fill, the child-correspondence component of `InvFull` identifies the router's child record with the venue's kid, so the state and the truth add exactly the same `min q (qty - done)` to exactly the same parent, and the updated child record still matches; the weaker `Inv` part is `plan0_inv_advance_fill`. Combining all four event cases with `run_induction` gives `InvFull` after every run, whose `cum` component is precisely `FillAccounting`.

```lean
theorem plan3_invFull_advance_route (b : Build) (x : Sys) (id liq : Nat)
    (hx : InvFull x) : InvFull (advance step b x (.route id liq)) := by sorry

theorem plan3_fill_children_step (b : Build) (x : Sys) (k q : Nat)
    (hx : InvFull x) :
    ∀ (idx : Nat) (c : Kid), (advance step b x (.fill k q)).tr.kids[idx]? = some c →
      (advance step b x (.fill k q)).st.children idx = (⟨c.parent, c.qty, c.done⟩ : ChildRec) := by sorry

theorem plan3_fill_cum_step (b : Build) (x : Sys) (k q : Nat)
    (hx : InvFull x) :
    ∀ j : Nat, ((advance step b x (.fill k q)).st.parents j).cum
      = (advance step b x (.fill k q)).tr.exec j := by sorry

theorem plan3_invFull_advance_fill (b : Build) (x : Sys) (k q : Nat)
    (hx : InvFull x) : InvFull (advance step b x (.fill k q)) := by sorry

theorem plan3_invFull_run (b : Build) (evs : List Event) :
    InvFull (run step b evs) := by sorry

theorem plan3_req_fill_accounting : FillAccounting step := by sorry
```