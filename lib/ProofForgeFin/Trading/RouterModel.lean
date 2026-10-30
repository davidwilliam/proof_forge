import ProofForgeFin.Trading.Router
/-!
# A child-order router with its requirements proved

The model of `realworld/tasks/rc-knight-router`, stated over the library's venue model and
proved once. Parent orders are numbered in arrival order and carry a tag of any type (the task's
flag); routing opportunities offer liquidity; execution reports name a child order by position.
The facts of a run (`Facts`: the parent quantities and every child order sent with its executed
shares) are computed from the events and the router's output, never from the router's state.

`step` is a router that sends `Router.routeQty` on each routing opportunity and advances the
cumulative executed quantity of a parent by what the venue executed. Over every sequence of
events, including duplicate, oversized and unknown execution reports:

* `route_out`: a routing opportunity sends exactly `expectedRoute` (the liquidity capped at the
  shares not yet sent, nothing for an unknown parent or an empty route);
* `sent_le_qty`: the shares sent for a parent never exceed its quantity (never overroute);
* `executed_le_sent`, `executed_le_qty`: the shares executed never exceed the shares sent, nor
  the quantity;
* `stop_when_filled`: once a parent is executed in full, no event sends a child order for it;
* `cum_eq_executed`: the router's cumulative executed quantity equals what the venues executed.

A specification with its own state, event and fact types uses these results by defining its
router through `step` and showing that its run maps to `run` (a structural, per-event
commutation; `ProofForgeFinDemo.Trading.KnightRouter` does this for the task).
-/

namespace ProofForgeFin.Trading.RouterModel

open ProofForgeFin.Seq ProofForgeFin.Ledger ProofForgeFin.Trading.Router

universe u

variable {α : Type u}

/-- Inputs to the router. -/
inductive Event (α : Type u) where
  /-- A new parent order of quantity `qty` with tag `tag`; parents are numbered in arrival
  order. -/
  | parent (qty : Nat) (tag : α)
  /-- A routing opportunity for parent `id`: venues show `liq` shares. -/
  | route (id liq : Nat)
  /-- An execution report: `q` shares of child order `k` executed. -/
  | fill (k q : Nat)
  /-- Any other event (an acknowledgement); the router does nothing. -/
  | other

/-- The facts of a run: the number of parent orders, their quantities, and every child order
sent with its executed shares. -/
structure Facts where
  /-- The number of parent orders. -/
  nOrders : Nat
  /-- The quantity of each parent order. -/
  qty : Nat → Nat
  /-- Every child order sent, in order. -/
  kids : List (Child Nat)

/-- No parent order, no child order. -/
def Facts.empty : Facts := ⟨0, fun _ => 0, []⟩

/-- The effect of an event at the venues: a new parent order is recorded with its quantity; an
execution report executes at most the unexecuted shares of the child order it names, nothing
for a child order that was never sent. -/
def Facts.observe (t : Facts) : Event α → Facts
  | .parent q _ => { t with nOrders := t.nOrders + 1, qty := upd t.qty t.nOrders q }
  | .fill k q => { t with kids := execute t.kids k q }
  | _ => t

/-- The child orders the router sent are appended with nothing executed. -/
def Facts.record (t : Facts) (out : List (Nat × Nat)) : Facts := { t with kids := send t.kids out }

/-- The router's record of a parent order. -/
structure PRec (α : Type u) where
  /-- The parent quantity. -/
  qty : Nat
  /-- The tag the parent order arrived with. -/
  tag : α
  /-- The shares sent in child orders. -/
  sent : Nat
  /-- The cumulative executed quantity. -/
  cum : Nat

/-- Router state: parent records `0` to `nParents - 1` and child records `0` to
`nChildren - 1`, in function tables. -/
structure RState (α : Type u) where
  /-- The number of parent orders. -/
  nParents : Nat
  /-- The parent records. -/
  parents : Nat → PRec α
  /-- The number of child orders. -/
  nChildren : Nat
  /-- The child records. -/
  children : Nat → Child Nat

/-- The state before any event, with default tag `d` in the unused parent records. -/
def RState.init (d : α) : RState α := ⟨0, fun _ => ⟨0, d, 0, 0⟩, 0, fun _ => ⟨0, 0, 0⟩⟩

/-- The router: the next state and the child orders sent, as pairs of parent and quantity. -/
def step (s : RState α) : Event α → RState α × List (Nat × Nat)
  | .parent q a => ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, a, 0, 0⟩ }, [])
  | .route id liq =>
    if id < s.nParents ∧ 0 < routeQty liq (s.parents id).qty (s.parents id).sent then
      ({ s with
          parents := upd s.parents id
            { s.parents id with sent := (s.parents id).sent + routeQty liq (s.parents id).qty (s.parents id).sent },
          nChildren := s.nChildren + 1,
          children := upd s.children s.nChildren (fresh id (routeQty liq (s.parents id).qty (s.parents id).sent)) },
       [(id, routeQty liq (s.parents id).qty (s.parents id).sent)])
    else (s, [])
  | .fill k q =>
    if k < s.nChildren then
      ({ s with
          parents := upd s.parents (s.children k).parent
            { s.parents (s.children k).parent with
              cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) },
          children := upd s.children k
            { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } },
       [])
    else (s, [])
  | .other => (s, [])

/-- A run in progress: the router's state and the facts so far. -/
structure Sys (α : Type u) where
  /-- The router's state. -/
  st : RState α
  /-- The facts. -/
  tr : Facts

/-- One event: the venues observe it, the router processes it, its output is recorded. -/
def advance (x : Sys α) (e : Event α) : Sys α := ⟨(step x.st e).1, (x.tr.observe e).record (step x.st e).2⟩

/-- Before any event. -/
def start (d : α) : Sys α := ⟨RState.init d, Facts.empty⟩

/-- The child order a routing opportunity calls for. -/
def expectedRoute (t : Facts) (id liq : Nat) : List (Nat × Nat) :=
  if id < t.nOrders ∧ 0 < routeQty liq (t.qty id) (sent t.kids id) then
    [(id, routeQty liq (t.qty id) (sent t.kids id))]
  else []

/-- The router's records agree with the facts. -/
structure Inv (x : Sys α) : Prop where
  /-- The router counts the parent orders. -/
  np : x.st.nParents = x.tr.nOrders
  /-- The child orders sent are the router's child table. -/
  kids : x.tr.kids = table x.st.children x.st.nChildren
  /-- The router records each parent's quantity. -/
  qty : ∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id
  /-- The router's `sent` counters agree with the shares sent. -/
  sentCtr : Counts Child.parent Child.qty (fun id => (x.st.parents id).sent) x.tr.kids
  /-- The router's `cum` counters agree with the shares executed. -/
  cumCtr : Counts Child.parent Child.done (fun id => (x.st.parents id).cum) x.tr.kids
  /-- Every child order belongs to a parent order. -/
  kpar : ∀ c ∈ x.tr.kids, c.parent < x.tr.nOrders
  /-- No child order is executed beyond its quantity. -/
  dq : DoneLeQty x.tr.kids
  /-- No parent is overrouted. -/
  le : ∀ id, sent x.tr.kids id ≤ x.tr.qty id

/-- The invariant holds before any event. -/
theorem inv_start (d : α) : Inv (start d) :=
  ⟨rfl, rfl, by simp [start, Facts.empty], fun _ => rfl, fun _ => rfl, by simp [start, Facts.empty],
    by simp [start, Facts.empty, DoneLeQty], fun _ => Nat.zero_le _⟩

/-- Every event preserves the invariant. -/
theorem inv_advance : Preserves (advance (α := α)) Inv := by
  intro ⟨st, tr⟩ e h
  obtain ⟨np, kids, qty, hsent, cum, kpar, dq, le⟩ := h
  simp only at np kids qty hsent cum kpar dq le
  have hs : ∀ id, sent tr.kids id = (st.parents id).sent := fun id => (hsent id).symm
  cases e with
  | parent q a =>
    have hn : ∀ c ∈ tr.kids, c.parent ≠ st.nParents := fun c hc => by have := kpar c hc; omega
    refine ⟨by simp [advance, step, Facts.observe, Facts.record, np], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [advance, step, Facts.observe, Facts.record, send, List.map_nil, List.append_nil]
    · exact kids
    · intro id hid
      by_cases e : id = st.nParents
      · subst e; simp [np]
      · rw [upd_ne _ _ e, upd_ne _ _ (by omega)]; exact qty id (by omega)
    · exact (hsent.upd_zero hn).congr (fun id => comp_upd_apply PRec.sent _ _ _ id)
    · exact (cum.upd_zero hn).congr (fun id => comp_upd_apply PRec.cum _ _ _ id)
    · intro c hc; have := kpar c hc; omega
    · exact dq
    · intro id
      by_cases e : id = st.nParents
      · subst e
        rw [show sent tr.kids st.nParents = 0 from sumFor_eq_zero_of_forall_ne _ _ hn]; exact Nat.zero_le _
      · rw [upd_ne _ _ (by omega)]; exact le id
  | route id liq =>
    simp only [advance, step]
    split
    · rename_i hc
      have hid : id < tr.nOrders := np ▸ hc.1
      have hle := add_routeQty_le (liq := liq) (le id)
      rw [hs id, ← qty id hid] at hle
      simp only [Facts.observe, Facts.record, send, List.map_cons, List.map_nil]
      refine ⟨np, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [kids, table_upd_succ]
      · intro j hj; rw [comp_upd_apply PRec.qty]; unfold upd; split
        · subst j; exact qty id hid
        · exact qty j hj
      · exact (hsent.append_one (fresh id _)).congr (fun j => comp_upd_apply PRec.sent _ _ _ j)
      · refine (cum.append_zero (fun c hc => by simp at hc; subst hc; rfl)).congr (fun j => ?_)
        rw [comp_upd_apply PRec.cum]; unfold upd; split <;> simp_all
      · intro c hc; simp only [List.mem_append, List.mem_singleton] at hc; rcases hc with hc | rfl
        · exact kpar c hc
        · exact hid
      · exact doneLeQty_send dq [(id, _)]
      · intro j
        rw [sent_append]
        by_cases e : id = j
        · subst e; simp only [sent_cons, fresh, sent_nil, ite_true, Nat.add_zero]
          rw [hs id, ← qty id hid]; exact hle
        · simp only [sent_cons, fresh, sent_nil, e, ite_false, Nat.add_zero]; exact le j
    · simp only [Facts.observe, Facts.record, send, List.map_nil, List.append_nil]
      exact ⟨np, kids, qty, hsent, cum, kpar, dq, le⟩
  | fill k q =>
    simp only [advance, step]
    split
    · rename_i hk
      have hget : tr.kids[k]? = some (st.children k) := by rw [kids]; exact getElem?_table _ hk
      have hmem := List.mem_of_getElem? hget
      simp only [Facts.observe, Facts.record, send, List.map_nil, List.append_nil, execute_of_some hget]
      let c' : Child Nat := { st.children k with done := (st.children k).done + min q ((st.children k).qty - (st.children k).done) }
      refine ⟨np, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [kids]; exact set_table _ hk _
      · intro j hj; rw [comp_upd_apply PRec.qty]; unfold upd; split
        · subst j; exact qty _ hj
        · exact qty j hj
      · refine (hsent.set_eq hget (c' := c') rfl rfl).congr (fun j => ?_)
        rw [comp_upd_apply PRec.sent]; unfold upd; split <;> simp_all
      · exact (cum.set_add hget (c' := c') rfl rfl).congr (fun j => comp_upd_apply PRec.cum _ _ _ j)
      · intro c hc
        rcases List.mem_or_eq_of_mem_set hc with hc | rfl
        · exact kpar c hc
        · exact kpar (st.children k) hmem
      · rw [← execute_of_some hget]; exact doneLeQty_execute dq k q
      · intro j
        show sumFor Child.parent Child.qty _ j ≤ _
        rw [sumFor_set_eq _ _ hget (c' := c') rfl rfl]; exact le j
    · rename_i hk
      have hnone : tr.kids[k]? = none := by rw [kids]; exact getElem?_table_of_le _ (by omega)
      simp only [Facts.observe, Facts.record, send, List.map_nil, List.append_nil, execute_of_none hnone]
      exact ⟨np, kids, qty, hsent, cum, kpar, dq, le⟩
  | other =>
    simp only [advance, step, Facts.observe, Facts.record, send, List.map_nil, List.append_nil]
    exact ⟨np, kids, qty, hsent, cum, kpar, dq, le⟩

/-- The invariant holds after every sequence of events. -/
theorem inv_run (d : α) (evs : List (Event α)) : Inv (run advance (start d) evs) :=
  run_invariant inv_advance (inv_start d) evs

/-- REQ-ROUTES-AVAILABLE: after any sequence of events, a routing opportunity sends exactly
`expectedRoute`. -/
theorem route_out (d : α) (evs : List (Event α)) (id liq : Nat) :
    (step (run advance (start d) evs).st (.route id liq)).2 = expectedRoute (run advance (start d) evs).tr id liq := by
  have h := inv_run d evs
  simp only [step, expectedRoute]
  by_cases hid : id < (run advance (start d) evs).tr.nOrders
  · have hs : sent (run advance (start d) evs).tr.kids id = ((run advance (start d) evs).st.parents id).sent :=
      (h.sentCtr id).symm
    rw [h.np, h.qty id hid, hs]
    split <;> rfl
  · have h1 : ¬ id < (run advance (start d) evs).st.nParents := by rw [h.np]; exact hid
    simp [h1, hid]

/-- REQ-NEVER-OVERROUTE: the shares sent for a parent never exceed its quantity. -/
theorem sent_le_qty (d : α) (evs : List (Event α)) (id : Nat) :
    sent (run advance (start d) evs).tr.kids id ≤ (run advance (start d) evs).tr.qty id :=
  (inv_run d evs).le id

/-- The shares executed for a parent never exceed the shares sent. -/
theorem executed_le_sent' (d : α) (evs : List (Event α)) (id : Nat) :
    executed (run advance (start d) evs).tr.kids id ≤ sent (run advance (start d) evs).tr.kids id :=
  executed_le_sent (inv_run d evs).dq id

/-- REQ-NO-EXCESS-EXECUTION: the shares executed for a parent never exceed its quantity. -/
theorem executed_le_qty' (d : α) (evs : List (Event α)) (id : Nat) :
    executed (run advance (start d) evs).tr.kids id ≤ (run advance (start d) evs).tr.qty id :=
  Nat.le_trans (executed_le_sent' d evs id) (sent_le_qty d evs id)

/-- REQ-STOP-WHEN-FILLED: once a parent is executed in full, no event sends a child order
for it. -/
theorem stop_when_filled (d : α) (evs : List (Event α)) (e : Event α) (id : Nat)
    (h : executed (run advance (start d) evs).tr.kids id = (run advance (start d) evs).tr.qty id) :
    ∀ o ∈ (step (run advance (start d) evs).st e).2, o.1 ≠ id := by
  intro o ho
  cases e with
  | route j liq =>
    rw [route_out, expectedRoute] at ho
    split at ho
    · rename_i hcond
      simp only [List.mem_singleton] at ho
      subst ho
      intro hj
      simp only at hj
      rw [hj] at hcond
      have := routeQty_eq_zero_of_filled (liq := liq) (executed_le_sent' d evs id) (sent_le_qty d evs id) h
      omega
    · simp at ho
  | parent q a => simp [step] at ho
  | other => simp [step] at ho
  | fill k q => simp only [step] at ho; split at ho <;> simp at ho

/-- REQ-FILL-ACCOUNTING: the router's cumulative executed quantity for every parent equals the
shares the venues executed in its child orders. -/
theorem cum_eq_executed (d : α) (evs : List (Event α)) (id : Nat) :
    ((run advance (start d) evs).st.parents id).cum = executed (run advance (start d) evs).tr.kids id :=
  (inv_run d evs).cumCtr id

end ProofForgeFin.Trading.RouterModel
