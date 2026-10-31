Strengthen the induction hypothesis to the already-defined full invariant `Inv`, which simultaneously records the parent/child table lengths, child synchronization, sent quantities, cumulative executed quantities, parent quantities, and the bound on every child's parent. The only genuinely new bookkeeping is for `fill`: truth updates the recorded execution by the capped amount `min q (c.qty - c.done)` for the child’s parent, and the router performs the same update to its cumulative field. Prove this fill calculation, prove `Inv` is preserved by each of the four event forms, induct over the event list with `run_induction`, and finally project the cumulative component of `Inv (run step b evs)`.

```lean
theorem plan2_observe_fill_exec : ∀ (t : Truth) (k q id : Nat), (t.observe (.fill k q)).exec id = t.exec id + (match t.kids[k]? with | some c => if c.parent = id then min q (c.qty - c.done) else 0 | none => 0) := by sorry

theorem plan2_inv_parent : ∀ (b : Build) (x : Sys) (q : Nat) (f : Bool), Inv x → Inv (advance step b x (.parent q f)) := by sorry

theorem plan2_inv_route : ∀ (b : Build) (x : Sys) (id liq : Nat), Inv x → Inv (advance step b x (.route id liq)) := by sorry

theorem plan2_inv_ack : ∀ (b : Build) (x : Sys) (k : Nat), Inv x → Inv (advance step b x (.ack k)) := by sorry

theorem plan2_inv_fill : ∀ (b : Build) (x : Sys) (k q : Nat), Inv x → Inv (advance step b x (.fill k q)) := by sorry

theorem plan2_run_inv : ∀ (b : Build) (evs : List Event), Inv (run step b evs) := by sorry
```