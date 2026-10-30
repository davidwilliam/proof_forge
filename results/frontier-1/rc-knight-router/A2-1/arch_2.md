(1) **Proof plan:** Use `arch2_Inv`, an alias for the already-developed `arch0_Inv`, as the single shared invariant. It records equality of parent/child counts, equality of each parent's `qty`/`sent`/`cum` with the specification-computed quantities, correspondence between child records and truth records, and `sent ≤ qty`. Its preservation is split into one small lemma per event constructor (`parent`, `route`, `ack`, `fill`); these are discharged respectively by the existing parent/route/ack preservation work and by the existing fill-accounting pieces (`plan2_*` quantity/sent/cum lemmas and `plan5_*` child-record lemmas). Folding preservation over an event list gives the invariant for every `run`. From that invariant, routing follows from `arch0_route_output_of_inv`/`arch1_routes_of_inv`, never-overrouting and fill accounting are direct projections, no-excess-execution is `exec ≤ sent ≤ qty`, and stop-when-filled follows from `arch1_no_child_of_filled` combined with the generic `exec_le_sent`.

(2)

```lean
def arch2_Inv (x : Sys) : Prop :=
  arch0_Inv x

theorem arch2_inv_start : arch2_Inv start := by sorry

theorem arch2_inv_parent_step (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch2_Inv x → arch2_Inv (advance step b x (.parent q f)) := by sorry

theorem arch2_inv_route_step (b : Build) (x : Sys) (id liq : Nat) :
    arch2_Inv x → arch2_Inv (advance step b x (.route id liq)) := by sorry

theorem arch2_inv_ack_step (b : Build) (x : Sys) (k : Nat) :
    arch2_Inv x → arch2_Inv (advance step b x (.ack k)) := by sorry

theorem arch2_inv_fill_step (b : Build) (x : Sys) (k q : Nat) :
    arch2_Inv x → arch2_Inv (advance step b x (.fill k q)) := by sorry

theorem arch2_inv_advance (b : Build) (x : Sys) (e : Event) :
    arch2_Inv x → arch2_Inv (advance step b x e) := by sorry

theorem arch2_inv_run (b : Build) (evs : List Event) :
    arch2_Inv (run step b evs) := by sorry

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  exact arch1_routes_of_inv b (run step b evs) id liq (arch2_inv_run b evs)

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  exact arch1_sent_le_of_inv (run step b evs) (arch2_inv_run b evs) id

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hfilled c hc
  exact arch1_no_child_of_filled b (run step b evs) (arch2_inv_run b evs)
    e id hfilled (exec_le_sent step b evs id) c hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  exact Nat.le_trans (exec_le_sent step b evs id)
    (arch1_sent_le_of_inv (run step b evs) (arch2_inv_run b evs) id)

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id hid
  exact arch1_cum_of_inv (run step b evs) (arch2_inv_run b evs) id hid
```