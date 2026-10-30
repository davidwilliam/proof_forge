The candidate routes from its internal `nParents`, `qty`, and `sent` fields, whereas `expectedRoute` uses the truth’s `nOrders`, `qty`, and `sent`. The existing `InvR` invariant connects exactly these quantities and also bounds child-order parents, which is needed when a new parent is added. Prove `InvR` is preserved by each kind of event, lift it to arbitrary runs by `run_induction`, and then unfold `step` and `expectedRoute` so their two routing conditions and amounts coincide.

```lean
theorem plan0_invR_parent (b : Build) (x : Sys) (q : Nat) (flag : Bool) :
    InvR x → InvR (advance step b x (Event.parent q flag)) := by sorry

theorem plan0_invR_route (b : Build) (x : Sys) (id liq : Nat) :
    InvR x → InvR (advance step b x (Event.route id liq)) := by sorry

theorem plan0_invR_ack (b : Build) (x : Sys) (k : Nat) :
    InvR x → InvR (advance step b x (Event.ack k)) := by sorry

theorem plan0_invR_fill (b : Build) (x : Sys) (k q : Nat) :
    InvR x → InvR (advance step b x (Event.fill k q)) := by sorry

theorem plan0_invR_run (b : Build) (evs : List Event) :
    InvR (run step b evs) := by sorry

theorem plan0_route_eq_of_invR (b : Build) (x : Sys) (id liq : Nat) :
    InvR x → (step b x.st (Event.route id liq)).2 = expectedRoute x.tr id liq := by sorry
```