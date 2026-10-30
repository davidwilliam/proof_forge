(1) **Plan.** Reuse the already-established invariant `arch0_Inv (run step b evs)`, proved by `arch0_inv_run`. It synchronizes parent/child counts, parent `qty`/`sent`/`cum` with the truth, child records with truth kids, and `sent ≤ qty`. From it: routes are computed by `arch1_routes_of_inv`; never-overroute is its `sent ≤ qty` component; fill accounting is its `cum = exec` component; no-excess follows on runs from the generic `exec_le_sent` plus `sent ≤ qty`. For stop-when-filled, the only possible output comes from `route` (via `arch0_output_cases`); if its parent were the filled parent, the invariant would give `qty - sent = 0`, contradicting a positive routed quantity. The needed `exec ≤ sent` hypothesis is supplied separately by `exec_le_sent`, since it is not part of `arch0_Inv` for an arbitrary abstract state.

(2)

```lean
theorem arch1_routes_of_inv (b : Build) (x : Sys) (id liq : Nat)
    (h : arch0_Inv x) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  sorry

theorem arch1_sent_le_of_inv (x : Sys) (h : arch0_Inv x) (id : Nat) :
    x.tr.sent id ≤ x.tr.qty id := by
  sorry

theorem arch1_cum_of_inv (x : Sys) (h : arch0_Inv x) (id : Nat)
    (hid : id < x.tr.nOrders) :
    (x.st.parents id).cum = x.tr.exec id := by
  sorry

theorem arch1_exec_le_qty_run (b : Build) (evs : List Event) (id : Nat) :
    (run step b evs).tr.exec id ≤ (run step b evs).tr.qty id := by
  sorry

theorem arch1_no_child_of_filled (b : Build) (x : Sys) (h : arch0_Inv x)
    (e : Event) (id : Nat)
    (hfilled : x.tr.exec id = x.tr.qty id)
    (hle : x.tr.exec id ≤ x.tr.sent id)
    (c : Child) (hc : c ∈ (step b x.st e).2) :
    c.parent ≠ id := by
  sorry

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  exact arch1_routes_of_inv b (run step b evs) id liq (arch0_inv_run b evs)

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  exact arch1_sent_le_of_inv (run step b evs) (arch0_inv_run b evs) id

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hfilled c hc
  exact arch1_no_child_of_filled b (run step b evs) (arch0_inv_run b evs)
    e id hfilled (exec_le_sent step b evs id) c hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  exact arch1_exec_le_qty_run b evs id

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id hid
  exact arch1_cum_of_inv (run step b evs) (arch0_inv_run b evs) id hid
```