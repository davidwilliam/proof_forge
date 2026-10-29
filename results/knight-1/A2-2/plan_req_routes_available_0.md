(1) Proof plan: Use the candidate's `InvWeak2` invariant, which connects the router state to the venue truth: parent counts agree, recorded `sent` equals actually sent shares, recorded `qty` agrees for existing parents, every sent child belongs to an existing parent, and `sent ≤ qty`. Preserve this invariant separately for parent creation, routing, and acknowledgement/fill events; the fill and acknowledgement cases do not affect `sent`, `qty`, or parent existence. Then obtain the invariant after any event sequence by `run_induction`. Finally, for a routing event, unfold `routeBySent` and `expectedRoute`: the invariant makes their bounds, remaining quantities, and emitted child quantities identical, whether or not the parent exists.

(2)
```lean
theorem plan0_inv_weak2_parent (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    InvWeak2 x → InvWeak2 (advance step b x (.parent q f)) := by sorry

theorem plan0_inv_weak2_route (b : Build) (x : Sys) (id liq : Nat) :
    InvWeak2 x → InvWeak2 (advance step b x (.route id liq)) := by sorry

theorem plan0_inv_weak2_ack_fill (b : Build) (x : Sys) (k q : Nat) :
    InvWeak2 x →
      InvWeak2 (advance step b x (.ack k)) ∧
        InvWeak2 (advance step b x (.fill k q)) := by sorry

theorem plan0_inv_weak2_run (b : Build) (evs : List Event) :
    InvWeak2 (run step b evs) := by sorry

theorem plan0_route_output_of_inv_weak2 (x : Sys) (id liq : Nat) :
    InvWeak2 x →
      (routeBySent x.st id liq).2 = expectedRoute x.tr id liq := by sorry

theorem plan0_routes_available_aux (b : Build) (evs : List Event) (id liq : Nat) :
    (step b (run step b evs).st (.route id liq)).2 =
      expectedRoute (run step b evs).tr id liq := by sorry
```