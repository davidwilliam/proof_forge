Short proof plan: establish the invariant `InvR` for every reachable system: the state's parent count matches the truth's order count, recorded quantities match truth quantities for existing parents, and recorded sent amounts match `sentFor` on the truth's kids. This invariant is preserved by a single `advance` step and therefore holds after any `run`. For a route event, both the implementation's output and `expectedRoute` are conditional on the same bound and on `min liq (qty - sent)`; `InvR` makes those conditions and quantities coincide, so the outputs are equal.

```lean
theorem plan0_invR_preserved : ∀ (b : Build) (x : Sys) (e : Event), InvR x → InvR (advance step b x e) := by sorry

theorem plan0_invR_run : ∀ (b : Build) (evs : List Event), InvR (run step b evs) := by sorry

theorem plan0_step_route_out : ∀ (b : Build) (s : State) (id liq : Nat), (step b s (.route id liq)).2 = (if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩] else []) := by sorry

theorem plan0_expectedRoute_eq : ∀ (t : Truth) (id liq : Nat), expectedRoute t id liq = (if id < t.nOrders ∧ 0 < min liq (t.qty id - t.sent id) then [⟨id, min liq (t.qty id - t.sent id)⟩] else []) := by sorry

theorem plan0_routes_of_invR : ∀ (b : Build) (evs : List Event) (id liq : Nat), InvR (run step b evs) → (step b (run step b evs).st (.route id liq)).2 = expectedRoute (run step b evs).tr id liq := by sorry
```