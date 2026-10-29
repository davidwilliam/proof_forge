Proof plan: first prove the router-state invariant that, for every existing parent, `sent ≤ qty` is preserved by one `advance` step (case split on the event; routing adds `min liq (qty - sent)`, filling/ack change neither field, and a new parent starts with `sent = 0`). Lift this to arbitrary runs by `run_induction`. Then transfer it to the truth using the already-proved `plan0_run_invariants_proof`, which identifies router `qty`/`sent` with truth `qty`/`sent` for existing parents. For a non-existent parent, all recorded kids have `parent < nOrders ≤ id`, so its truth `sent` is `0`. Combining the two cases gives `NeverOverroute`.

```lean
theorem plan3_advance_sent_le_qty (b : Build) (x : Sys) (e : Event)
    (h : ∀ id, id < x.st.nParents →
      (x.st.parents id).sent ≤ (x.st.parents id).qty) :
    ∀ id, id < (advance step b x e).st.nParents →
      ((advance step b x e).st.parents id).sent ≤
        ((advance step b x e).st.parents id).qty := by sorry

theorem plan3_run_sent_le_qty (b : Build) (evs : List Event) (id : Nat)
    (hid : id < (run step b evs).st.nParents) :
    ((run step b evs).st.parents id).sent ≤
      ((run step b evs).st.parents id).qty := by sorry

theorem plan3_tr_sent_le_qty_of_lt (b : Build) (evs : List Event) (id : Nat)
    (hid : id < (run step b evs).tr.nOrders) :
    (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id := by sorry

theorem plan3_tr_sent_eq_zero_of_ge (b : Build) (evs : List Event) (id : Nat)
    (hid : (run step b evs).tr.nOrders ≤ id) :
    (run step b evs).tr.sent id = 0 := by sorry

theorem plan3_never_overroute_all : NeverOverroute step := by sorry
```