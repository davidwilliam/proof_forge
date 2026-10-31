(1) **Proof plan:** Establish the candidate's state–truth invariant `Inv` for every reachable system. Prove preservation separately for each event constructor—parent, route, ack, and fill—then lift preservation through `run` using induction on the event list. Finally, under `Inv`, the state's parent count, ordered quantity, and sent quantity agree with the truth, so `routeBySent`'s condition and child quantity are exactly those in `expectedRoute`. Applying this to `run step b evs` proves `RoutesAvailable`.

(2)
```lean
theorem plan0_inv_advance_parent (b : Build) (x : Sys) (q : Nat) (f : Bool)
    (hx : Inv x) : Inv (advance step b x (.parent q f)) := by sorry

theorem plan0_inv_advance_route (b : Build) (x : Sys) (id liq : Nat)
    (hx : Inv x) : Inv (advance step b x (.route id liq)) := by sorry

theorem plan0_inv_advance_ack (b : Build) (x : Sys) (k : Nat)
    (hx : Inv x) : Inv (advance step b x (.ack k)) := by sorry

theorem plan0_inv_advance_fill (b : Build) (x : Sys) (k q : Nat)
    (hx : Inv x) : Inv (advance step b x (.fill k q)) := by sorry

theorem plan0_inv_run (b : Build) (evs : List Event) :
    Inv (run step b evs) := by sorry

theorem plan0_route_output_of_inv (b : Build) (x : Sys) (id liq : Nat)
    (hx : Inv x) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by sorry
```