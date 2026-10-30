import ProofForgeFin.Trading.RouterModel
/-!
# Demonstration: the six requirements of `rc-knight-router` with the library

The definitions in the first section are copied without change from
`realworld/tasks/rc-knight-router/spec/OrderRouter/Spec.lean`. The task files are not imported or
modified.

The second section defines a router (every code version takes one path, as the accepted repairs
do) and proves all six requirements for it. The reference solution
(`reference/SolutionA.lean`) states a seven-field invariant and proves it event by event with the
task's helper lemmas about `sentFor`, `execFor` and `List.set`. Here the facts of a run are
identified with library notions once:

* `sentFor` and `execFor` are `Router.sumFor` with the projections `Kid.qty` and `Kid.done`;
* the list of child orders is `Router.table` of the router's child records, so a new child
  order is `Router.table_comp_upd_succ` and an execution is `Router.set_table_comp`;
* the router's `sent` and `cum` counters are `Router.Counts` of those sums, advanced by
  `Counts.append_one`, `Counts.append_zero`, `Counts.set_add`, `Counts.set_eq` and reset by
  `Counts.upd_zero`;
* the route is `Router.routeQty`, so REQ-NEVER-OVERROUTE is `Router.add_routeQty_le` and
  REQ-STOP-WHEN-FILLED is `Router.routeQty_eq_zero_of_filled`;
* the induction over events is `Seq.run_invariant` after `run_eq` identifies the task's `run`
  (a left fold) with the library's.
-/

namespace ProofForgeFinDemo.Trading.KnightRouter

open ProofForgeFin ProofForgeFin.Trading

/-! ## Copied from `spec/OrderRouter/Spec.lean` -/

/-- The code version a server runs. `rlp` is the new code; `legacy` is a server to which the
new code was not copied, where the Power Peg code is still present and callable. -/
inductive Build where
  | rlp
  | legacy
  deriving DecidableEq, Repr

/-- A child order as sent to a venue: the parent order it represents and its share
quantity. Child orders are numbered 0, 1, 2, ... in the order they are sent. -/
structure Child where
  parent : Nat
  qty    : Nat
  deriving DecidableEq, Repr

/-- Inputs to the router. Parent orders are numbered 0, 1, 2, ... in arrival order.
`route id liq` is a routing opportunity for parent `id`: venues show `liq` shares
available. `ack k` acknowledges child order `k`. `fill k q` is an execution report:
`q` shares of child order `k` were executed. -/
inductive Event where
  | parent (qty : Nat) (flag : Bool)
  | route (id : Nat) (liq : Nat)
  | ack (child : Nat)
  | fill (child : Nat) (q : Nat)
  deriving DecidableEq, Repr

/-- Function update. -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun j => if j = k then v else f j

/-! ## Router state (the implementation reads and writes it) -/

/-- The router's record of a parent order: its quantity and flag, the shares it has sent in
child orders, and its cumulative executed quantity (the "cumulative quantity function" of
paragraph 14 of the order). -/
structure ParentRec where
  qty  : Nat
  flag : Bool
  sent : Nat
  cum  : Nat
  deriving DecidableEq, Repr

/-- The router's record of a child order: its parent, quantity and executed shares. -/
structure ChildRec where
  parent : Nat
  qty    : Nat
  done   : Nat
  deriving DecidableEq, Repr

/-- Router state: parent records `0` to `nParents - 1` and child records `0` to
`nChildren - 1`. -/
structure State where
  nParents  : Nat
  parents   : Nat → ParentRec
  nChildren : Nat
  children  : Nat → ChildRec

/-- The router's state before any event. -/
def init : State :=
  { nParents := 0, parents := fun _ => ⟨0, false, 0, 0⟩,
    nChildren := 0, children := fun _ => ⟨0, 0, 0⟩ }

/-- A router: given the server's code version, its state and an event, the next state and
the child orders it sends in response. -/
abbrev Impl := Build → State → Event → State × List Child

/-! ## What actually happened (computed by this file, not by the router) -/

/-- A child order with the number of its shares executed at the venue. -/
structure Kid where
  parent : Nat
  qty    : Nat
  done   : Nat
  deriving DecidableEq, Repr

/-- The facts of a run: how many parent orders arrived and their quantities, and every child
order sent, in order, with its executed shares. -/
structure Truth where
  nOrders : Nat
  qty     : Nat → Nat
  kids    : List Kid

/-- Shares sent in the child orders of `kids` for parent `id`. -/
def sentFor : List Kid → Nat → Nat
  | [], _ => 0
  | k :: ks, id => (if k.parent = id then k.qty else 0) + sentFor ks id

/-- Shares executed in the child orders of `kids` for parent `id`. -/
def execFor : List Kid → Nat → Nat
  | [], _ => 0
  | k :: ks, id => (if k.parent = id then k.done else 0) + execFor ks id

/-- Cumulative shares sent in child orders for parent `id`: the sum of the quantities of
every child order sent for it so far. -/
def Truth.sent (t : Truth) (id : Nat) : Nat := sentFor t.kids id

/-- Cumulative shares executed for parent `id`: the sum of the executed shares of every
child order sent for it so far. -/
def Truth.exec (t : Truth) (id : Nat) : Nat := execFor t.kids id

/-- No parent order, no child order. -/
def Truth.empty : Truth := { nOrders := 0, qty := fun _ => 0, kids := [] }

/-- The effect of an event at the venues. A new parent order is recorded with its quantity.
An execution report for child order `k` executes at most the shares of `k` that are still
unexecuted, so a report larger than the order executes only the rest, and a report for a
child order that was never sent executes nothing. -/
def Truth.observe (t : Truth) : Event → Truth
  | .parent q _ => { t with nOrders := t.nOrders + 1, qty := upd t.qty t.nOrders q }
  | .fill k q =>
    match t.kids[k]? with
    | some c => { t with kids := t.kids.set k { c with done := c.done + min q (c.qty - c.done) } }
    | none => t
  | _ => t

/-- Child orders sent by the router are appended, with nothing executed yet. -/
def Truth.record (t : Truth) (out : List Child) : Truth :=
  { t with kids := t.kids ++ out.map (fun c => ⟨c.parent, c.qty, 0⟩) }

/-- A run in progress: the router's state and the facts so far. -/
structure Sys where
  st : State
  tr : Truth

/-- Before any event. -/
def start : Sys := ⟨init, Truth.empty⟩

/-- One event: the venues observe it, the router processes it, and the child orders it sends
are recorded. -/
def advance (step : Impl) (b : Build) (x : Sys) (e : Event) : Sys :=
  ⟨(step b x.st e).1, (x.tr.observe e).record (step b x.st e).2⟩

/-- Run the router on a server with code version `b` over a sequence of events. -/
def run (step : Impl) (b : Build) (evs : List Event) : Sys :=
  evs.foldl (advance step b) start

/-- The child order a routing opportunity calls for: the available liquidity, capped at the
parent's shares not yet sent; none when that is zero or the parent does not exist. -/
def expectedRoute (t : Truth) (id liq : Nat) : List Child :=
  if id < t.nOrders ∧ 0 < min liq (t.qty id - t.sent id) then
    [⟨id, min liq (t.qty id - t.sent id)⟩]
  else []

/-- A normal order: 300 shares, three routing opportunities of 100 shares, each child order
executed in full, then one more routing opportunity. -/
def normalOrder (flag : Bool) : List Event :=
  [.parent 300 flag, .route 0 100, .fill 0 100, .route 0 100, .fill 1 100,
   .route 0 100, .fill 2 100, .route 0 100]

/-! ## Requirements -/

/-- REQ-NORMAL-ORDER-ROUTED: on every code version and for either flag value, a normal
300-share order with three routing opportunities of 100 shares is sent as exactly three
child orders of 100 shares, all 300 shares are executed, and the fourth routing opportunity
sends nothing. -/
def NormalOrderRouted (step : Impl) : Prop :=
  ∀ b flag, (run step b (normalOrder flag)).tr.kids = [⟨0, 100, 100⟩, ⟨0, 100, 100⟩, ⟨0, 100, 100⟩] ∧
    (run step b (normalOrder flag)).tr.exec 0 = 300

/-- REQ-ROUTES-AVAILABLE: after any sequence of events, a routing opportunity for an
existing parent sends exactly one child order for the available liquidity capped at the
parent's shares not yet sent, and nothing when that is zero or the parent does not exist. -/
def RoutesAvailable (step : Impl) : Prop :=
  ∀ b evs id liq, (step b (run step b evs).st (.route id liq)).2 = expectedRoute (run step b evs).tr id liq

/-- REQ-NEVER-OVERROUTE: on every code version, for every flag value, every parent order and
every sequence of events, the cumulative shares sent in child orders for a parent never
exceed its quantity. -/
def NeverOverroute (step : Impl) : Prop :=
  ∀ b evs id, (run step b evs).tr.sent id ≤ (run step b evs).tr.qty id

/-- REQ-STOP-WHEN-FILLED: once a parent order has been executed completely, no event makes the
router send another child order for it. -/
def StopWhenFilled (step : Impl) : Prop :=
  ∀ b evs e id, (run step b evs).tr.exec id = (run step b evs).tr.qty id →
    ∀ c ∈ (step b (run step b evs).st e).2, c.parent ≠ id

/-- REQ-NO-EXCESS-EXECUTION: the shares executed for a parent order never exceed its
quantity, so no execution is left without a customer order to match it. -/
def NoExcessExecution (step : Impl) : Prop :=
  ∀ b evs id, (run step b evs).tr.exec id ≤ (run step b evs).tr.qty id

/-- REQ-FILL-ACCOUNTING: the router's cumulative executed quantity for every parent order
equals the shares actually executed in its child orders. -/
def FillAccounting (step : Impl) : Prop :=
  ∀ b evs id, id < (run step b evs).tr.nOrders →
    ((run step b evs).st.parents id).cum = (run step b evs).tr.exec id

/-! ## Re-proved with the library -/

/-- Task events as library router events; an acknowledgement does nothing. -/
def toEv : Event → RouterModel.Event Bool
  | .parent q f => .parent q f
  | .route id liq => .route id liq
  | .ack _ => .other
  | .fill k q => .fill k q

/-- The task's router state as the library's. -/
def toAbs (s : State) : RouterModel.RState Bool :=
  ⟨s.nParents, fun i => ⟨(s.parents i).qty, (s.parents i).flag, (s.parents i).sent, (s.parents i).cum⟩,
   s.nChildren, fun k => ⟨(s.children k).parent, (s.children k).qty, (s.children k).done⟩⟩

/-- The library's router state as the task's. -/
def ofAbs (r : RouterModel.RState Bool) : State :=
  ⟨r.nParents, fun i => ⟨(r.parents i).qty, (r.parents i).tag, (r.parents i).sent, (r.parents i).cum⟩,
   r.nChildren, fun k => ⟨(r.children k).parent, (r.children k).qty, (r.children k).done⟩⟩

/-- The router: `RouterModel.step` on the task's state, for every code version and flag. -/
def step : Impl := fun _ s e =>
  (ofAbs (RouterModel.step (toAbs s) (toEv e)).1, (RouterModel.step (toAbs s) (toEv e)).2.map fun o => ⟨o.1, o.2⟩)

/-- A fact of the run as a library child order. -/
def toChild (k : Kid) : Router.Child Nat := ⟨k.parent, k.qty, k.done⟩

/-- The task's facts as the library's. -/
def toFacts (t : Truth) : RouterModel.Facts := ⟨t.nOrders, t.qty, t.kids.map toChild⟩

/-- A task run in progress as a library one. -/
def toSys (x : Sys) : RouterModel.Sys Bool := ⟨toAbs x.st, toFacts x.tr⟩

/-- `sentFor` is the library's `sent`. -/
theorem sentFor_eq (l : List Kid) (id : Nat) : sentFor l id = Router.sent (l.map toChild) id := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp only [sentFor, List.map_cons, Router.sent_cons, ih]; rfl

/-- `execFor` is the library's `executed`. -/
theorem execFor_eq (l : List Kid) (id : Nat) : execFor l id = Router.executed (l.map toChild) id := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp only [execFor, List.map_cons, Router.executed_cons, ih]; rfl

/-- One task event is one library event. -/
theorem advance_eq (b : Build) (x : Sys) (e : Event) :
    toSys (advance step b x e) = RouterModel.advance (toSys x) (toEv e) := by
  obtain ⟨st, tr⟩ := x
  simp only [advance, toSys, RouterModel.advance, step]
  congr 1
  generalize (RouterModel.step (toAbs st) (toEv e)).2 = out
  have hrec : ∀ t : Truth, toFacts (t.record (out.map fun o => ⟨o.1, o.2⟩)) = (toFacts t).record out := by
    intro t; simp [Truth.record, RouterModel.Facts.record, toFacts, Router.send, Router.fresh, toChild]
  rw [hrec]
  congr 1
  cases e with
  | parent q f => rfl
  | route id liq => rfl
  | ack k => rfl
  | fill k q =>
    simp only [Truth.observe, toEv, RouterModel.Facts.observe, toFacts]
    cases h : tr.kids[k]? with
    | none => simp [Router.execute, h]
    | some c =>
      have h' : (tr.kids.map toChild)[k]? = some (toChild c) := by simp [h]
      simp only [Router.execute_of_some h', List.map_set]; rfl

/-- A task run is a library run. -/
theorem run_eq (b : Build) (evs : List Event) :
    toSys (run step b evs) = Seq.run RouterModel.advance (RouterModel.start false) (evs.map toEv) := by
  unfold run
  rw [← List.foldl_map]
  suffices ∀ x, toSys (evs.foldl (advance step b) x) = Seq.run RouterModel.advance (toSys x) (evs.map toEv) by
    rw [List.foldl_map]; exact this start
  induction evs with
  | nil => intro; rfl
  | cons e es ih => intro x; simp only [List.foldl_cons, List.map_cons, Seq.run_cons, ih, advance_eq]

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> decide

theorem req_routes_available : RoutesAvailable step := by
  intro b evs id liq
  have h := RouterModel.route_out false (evs.map toEv) id liq
  rw [← run_eq] at h
  show (RouterModel.step (toSys (run step b evs)).st (.route id liq)).2.map _ = _
  rw [h]
  simp only [RouterModel.expectedRoute, expectedRoute, toSys, toFacts, Truth.sent, sentFor_eq, Router.routeQty]
  split
  · rename_i hc; simp only [hc, and_self, ↓reduceIte, List.map_cons, List.map_nil]
  · rename_i hc; simp only [hc, ↓reduceIte, List.map_nil]

theorem req_never_overroute : NeverOverroute step := fun b evs id => by
  have := RouterModel.sent_le_qty false (evs.map toEv) id
  rw [← run_eq] at this
  rw [Truth.sent, sentFor_eq]; exact this

theorem req_stop_when_filled : StopWhenFilled step := by
  intro b evs e id hfull c hc
  have h := RouterModel.stop_when_filled false (evs.map toEv) (toEv e) id
  rw [← run_eq] at h
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hc
  exact h (by rw [Truth.exec, execFor_eq] at hfull; exact hfull) o ho

theorem req_no_excess_execution : NoExcessExecution step := fun b evs id => by
  have := RouterModel.executed_le_qty' false (evs.map toEv) id
  rw [← run_eq] at this
  rw [Truth.exec, execFor_eq]; exact this

theorem req_fill_accounting : FillAccounting step := fun b evs id _ => by
  have := RouterModel.cum_eq_executed false (evs.map toEv) id
  rw [← run_eq] at this
  rw [Truth.exec, execFor_eq]; exact this

end ProofForgeFinDemo.Trading.KnightRouter
