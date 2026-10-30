Fixed the `StopWhenFilled` derivation: it now converts the emitted child’s parent to `id` without an ambiguous substitution, obtains the parent bound by rewriting with the invariant’s parent-count equality rather than `omega`, and only then derives that the remaining routable quantity is zero.

```lean
def arch0_Inv (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ id, id < x.tr.nOrders →
    (x.st.parents id).qty = x.tr.qty id ∧
    (x.st.parents id).sent = x.tr.sent id ∧
    (x.st.parents id).cum = x.tr.exec id) ∧
  (∀ k, k < x.tr.kids.length →
    ∃ kid, x.tr.kids[k]? = some kid ∧
      x.st.children k = ⟨kid.parent, kid.qty, kid.done⟩ ∧
      kid.parent < x.tr.nOrders) ∧
  (∀ id, x.tr.sent id ≤ x.tr.qty id)

theorem arch0_inv_start : arch0_Inv start := by
  sorry

theorem arch0_inv_parent_step (b : Build) (x : Sys) (q : Nat) (f : Bool) :
    arch0_Inv x → arch0_Inv (advance step b x (.parent q f)) := by
  sorry

theorem arch0_inv_route_step (b : Build) (x : Sys) (id liq : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.route id liq)) := by
  sorry

theorem arch0_inv_ack_step (b : Build) (x : Sys) (k : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.ack k)) := by
  sorry

theorem arch0_inv_fill_step (b : Build) (x : Sys) (k q : Nat) :
    arch0_Inv x → arch0_Inv (advance step b x (.fill k q)) := by
  sorry

theorem arch0_inv_advance (b : Build) (x : Sys) (e : Event) :
    arch0_Inv x → arch0_Inv (advance step b x e) := by
  sorry

theorem arch0_inv_run (b : Build) (evs : List Event) :
    arch0_Inv (run step b evs) := by
  sorry

theorem arch0_nParents_eq_of_inv {x : Sys} (h : arch0_Inv x) :
    x.st.nParents = x.tr.nOrders := by
  sorry

theorem arch0_parent_qty_of_inv {x : Sys} (h : arch0_Inv x)
    {id : Nat} (hid : id < x.tr.nOrders) :
    (x.st.parents id).qty = x.tr.qty id := by
  sorry

theorem arch0_parent_sent_of_inv {x : Sys} (h : arch0_Inv x)
    {id : Nat} (hid : id < x.tr.nOrders) :
    (x.st.parents id).sent = x.tr.sent id := by
  sorry

theorem arch0_parent_cum_of_inv {x : Sys} (h : arch0_Inv x)
    {id : Nat} (hid : id < x.tr.nOrders) :
    (x.st.parents id).cum = x.tr.exec id := by
  sorry

theorem arch0_sent_le_qty_of_inv {x : Sys} (h : arch0_Inv x) (id : Nat) :
    x.tr.sent id ≤ x.tr.qty id := by
  sorry

theorem arch0_route_output_of_inv (b : Build) (x : Sys) (id liq : Nat)
    (h : arch0_Inv x) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  sorry

theorem arch0_output_cases (b : Build) (s : State) (e : Event) (c : Child) :
    c ∈ (step b s e).2 →
    ∃ pid liq,
      e = .route pid liq ∧
      c = ⟨pid, min liq ((s.parents pid).qty - (s.parents pid).sent)⟩ ∧
      pid < s.nParents ∧
      0 < min liq ((s.parents pid).qty - (s.parents pid).sent) := by
  sorry

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  exact arch0_route_output_of_inv b (run step b evs) id liq
    (arch0_inv_run b evs)

theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  exact arch0_sent_le_qty_of_inv (arch0_inv_run b evs) id

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hfilled c hc heq
  have hInv : arch0_Inv (run step b evs) := arch0_inv_run b evs
  obtain ⟨pid, liq, _he, hcEq, hlt, hpos⟩ :=
    arch0_output_cases b (run step b evs).st e c hc
  have hpid : pid = id := by
    have h2 : c.parent = id := heq
    rw [hcEq] at h2
    exact h2
  have hidPid : pid < (run step b evs).tr.nOrders := by
    rw [← arch0_nParents_eq_of_inv hInv]
    exact hlt
  have hid : id < (run step b evs).tr.nOrders := by
    rw [← hpid]
    exact hidPid
  have hqty := arch0_parent_qty_of_inv hInv hid
  have hsent := arch0_parent_sent_of_inv hInv hid
  have hsent_le := arch0_sent_le_qty_of_inv hInv id
  have hexec_le := exec_le_sent step b evs id
  have hrouteZero :
      ((run step b evs).st.parents pid).qty -
        ((run step b evs).st.parents pid).sent = 0 := by
    rw [hpid, hqty, hsent]
    omega
  rw [hrouteZero] at hpos
  simp at hpos

theorem req_no_excess_execution : NoExcessExecution step := by
  intro b evs id
  exact Nat.le_trans
    (exec_le_sent step b evs id)
    (arch0_sent_le_qty_of_inv (arch0_inv_run b evs) id)

theorem req_fill_accounting : FillAccounting step := by
  intro b evs id hid
  exact arch0_parent_cum_of_inv (arch0_inv_run b evs) hid
```