/-!
# Child-order router specification (protected)

A model of an automated order router of the kind described in the SEC order against Knight
Capital Americas LLC (Release No. 34-70694, October 16, 2013), reconstructed from the SEC
findings. Knight's code is not public; nothing here is Knight's code.

The router receives parent orders and, as liquidity becomes available, sends child orders
to trading venues for execution (paragraph 12 of the order). Each parent order carries a
flag; in the order, the flag that formerly activated "Power Peg" was repurposed for the
Retail Liquidity Program (paragraph 13). Each server runs one code version, and on
August 1, 2012 one of the eight servers still had the Power Peg code (paragraphs 15 and 16).

Every requirement is a predicate over an implementation `step : Impl` and quantifies over
every code version, every flag value, every parent order and every sequence of events
(new parent orders, routing opportunities, acknowledgements and execution reports,
including reports for unknown child orders and reports larger than the order). The
locked challenge (`OrderRouter/Challenge.lean`) applies each one to the definition hole
`OrderRouter.step`.

The quantities the requirements talk about (shares ordered, shares sent in child orders,
shares executed) are computed by this file from the event sequence and the child orders the
router emitted, never from the router's own state, so a router cannot satisfy them by
under-reporting.
-/

namespace OrderRouter

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

end OrderRouter
