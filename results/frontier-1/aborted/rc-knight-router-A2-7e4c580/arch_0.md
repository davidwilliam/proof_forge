Fixed `le_trans` (unavailable in this core-only environment) by deriving the transitivity step with explicit hypotheses and `omega`; everything else is unchanged.

```lean
def arch0_Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, id < x.tr.nOrders →
    (x.st.parents id).qty = x.tr.qty id ∧
    (x.st.parents id).sent = x.tr.sent id ∧
    (x.st.parents id).cum = x.tr.exec id ∧
    (x.st.parents id).sent ≤ (x.st.parents id).qty) ∧
  (∀ id, x.tr.nOrders ≤ id → x.tr.qty id = 0) ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ k kid, x.tr.kids[k]? = some kid →
    (x.st.children k).parent = kid.parent ∧
    (x.st.children k).qty = kid.qty ∧
    (x.st.children k).done = kid.done) ∧
  (∀ kid, kid ∈ x.tr.kids → kid.parent < x.tr.nOrders)

theorem arch0_inv_start : arch0_Inv start := by sorry

theorem arch0_inv_advance_parent (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch0_Inv x → arch0_Inv (advance step b x (.parent q f)) := by sorry

theorem arch0_inv_advance_route (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) := by sorry

theorem arch0_inv_advance_ack (b : Build) (x : Sys) (k : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.ack k)) := by sorry

theorem arch0_inv_advance_fill (b : Build) (x : Sys) (k q : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.fill k q)) := by sorry

theorem arch0_inv_advance (b : Build) (x : Sys) (e : Event) :
    arch0_Inv x → arch0_Inv (advance step b x e) := by sorry

theorem arch0_inv_run (b : Build) (evs : List Event) :
    arch0_Inv (run step b evs) := by sorry

theorem arch0_route_of_inv (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x →
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by sorry

theorem arch0_bound_of_inv (x : Sys) :
    arch0_Inv x → ∀ id, x.tr.sent id ≤ x.tr.qty id := by sorry

theorem arch0_no_output_of_filled (b : Build) (x : Sys) (e : Event) (id : Nat) :
    arch0_Inv x →
    x.tr.exec id = x.tr.qty id →
    ∀ c ∈ (step b x.st e).2, c.parent ≠ id := by sorry

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> refine ⟨?_, ?_⟩ <;>
    first
      | exact t8a
      | exact t8b
      | exact t8c
      | exact t8d
      | exact e8a
      | exact e8b
      | exact e8c
      | exact e8d

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  exact arch0_route_of_inv b (run step b evs) id liq (arch0_inv_run b evs)

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  exact arch0_bound_of_inv (run step b evs) (arch0_inv_run b evs) id

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hfilled c hc
  exact arch0_no_output_of_filled b (run step b evs) e id
    (arch0_inv_run b evs) hfilled c hc

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  have h1 := exec_le_sent step b evs id
  have h2 := arch0_bound_of_inv (run step b evs) (arch0_inv_run b evs) id
  omega

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id hid
  have h := (arch0_inv_run b evs).2.1 id hid
  exact h.2.2.1
```