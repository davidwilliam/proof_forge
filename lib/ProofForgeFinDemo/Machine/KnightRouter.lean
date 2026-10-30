import ProofForgeFin
/-!
# Demonstration: `rc-knight-router` with `ProofForgeFin.Machine`

The definitions in the first section are copied without change from
`realworld/tasks/rc-knight-router/spec/OrderRouter/Spec.lean`; the router `step`, the invariant
`Inv`, `inv_start` and `inv_advance` are copied without change from `reference/SolutionA.lean`.
The task files are not imported or modified.

The task keeps the facts of a run (`Truth`: the child orders sent and their executed shares,
computed by the specification) apart from the router's own counters (`ParentRec.sent`,
`ParentRec.cum`), and every requirement compares the two or bounds the facts. Its `run` is a left
fold of `advance`, which runs the router and records its output: the coupled step
`Machine.couple` of the library.

* `run_eq`, `run_induction`, `run_snoc`: the task's `run` is `Seq.run`, so the induction
  principles of `Seq` and `Machine` apply.
* `advance_couple`, `advance_of_eq`, `run_pair`: `advance` is `Machine.couple` of the router and
  the specification's observer, under the map `Sys → State × Truth`; a whole-state step equation
  turns a run in progress into a plain pair.
* The whole of the task's `OrderRouter/Lemmas.lean` re-proved from the library: `sentFor` and
  `execFor` are `Machine.keyTotal` (per-key totals of a list of records), so the append and
  `List.set` lemmas are `keyTotal_append`, `keyTotal_set_eq` and `keyTotal_set_add`,
  `execFor_le_sentFor` is `keyTotal_le_keyTotal`, and `done_le_qty` is an induction over
  `Seq.run`.
* `reqs_of_invariant`: the last step of every proof of this task, for every router. A router
  whose coupled system keeps an invariant that gives `sent ≤ qty`, `cum = exec` for every existing
  parent, the expected child order on a routing opportunity and none on other events satisfies
  REQ-ROUTES-AVAILABLE, REQ-NEVER-OVERROUTE, REQ-STOP-WHEN-FILLED, REQ-NO-EXCESS-EXECUTION and
  REQ-FILL-ACCOUNTING.
* The reference router: its per-event invariant proof runs unchanged on the re-proved lemmas,
  and its six requirements follow (`reqs`, and `req_normal_order_routed` by computation).
-/

namespace ProofForgeFinDemo.Machine.Knight

open ProofForgeFin ProofForgeFin.Machine

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

/-! ## The task's run is the library's -/

/-- `run` is `Seq.run` of `advance` from `start`. -/
theorem run_eq (step : Impl) (b : Build) (evs : List Event) :
    run step b evs = Seq.run (advance step b) start evs :=
  (Seq.run_eq_foldl _ _ _).symm

/-- `run_induction` of the task's `Lemmas.lean`. -/
theorem run_induction (step : Impl) (b : Build) (P : Sys → Prop) (h0 : P start)
    (hs : ∀ x e, P x → P (advance step b x e)) : ∀ evs, P (run step b evs) :=
  fun evs => run_eq step b evs ▸ Seq.run_invariant hs h0 evs

/-- `run_snoc` of the task's `Lemmas.lean`. -/
theorem run_snoc (step : Impl) (b : Build) (evs : List Event) (e : Event) :
    run step b (evs ++ [e]) = advance step b (run step b evs) e := by
  rw [run_eq, run_eq, Seq.run_snoc]

/-! ## `advance` is a coupled step -/

/-- A run in progress as a pair. -/
def Sys.toPair (x : Sys) : State × Truth := (x.st, x.tr)

/-- The specification's observer: the venues observe the event, then the router's output is
recorded. -/
def observer (t : Truth) (e : Event) (out : List Child) : Truth := (t.observe e).record out

/-- `advance` is the library's coupled step of the router and the observer. -/
theorem advance_couple (step : Impl) (b : Build) (x : Sys) (e : Event) :
    (advance step b x e).toPair = couple (step b) observer x.toPair e := rfl

/-- An event whose router step is known as a whole-state equation `step b x.st e = (s', out)`:
the run in progress becomes the plain pair of `s'` and the observed facts, with no projection of
the router's result left inside. Rewriting with this equation first, and only then projecting,
avoids the mismatch between a hypothesis stated over a rewritten literal and a lemma stated over
`advance`. -/
theorem advance_of_eq {step : Impl} {b : Build} {x : Sys} {e : Event} {s' : State}
    {out : List Child} (h : step b x.st e = (s', out)) :
    (advance step b x e).toPair = (s', observer x.tr e out) := by
  rw [advance_couple]; exact couple_of_eq h

/-- The router part of the same step, through `machine_norm`. -/
theorem advance_st_of_eq {step : Impl} {b : Build} {x : Sys} {e : Event} {s' : State}
    {out : List Child} (h : step b x.st e = (s', out)) : (advance step b x e).st = s' := by
  unfold advance
  machine_norm
  rw [h]

/-- A run as a pair is the library's coupled run. -/
theorem run_pair (step : Impl) (b : Build) (evs : List Event) :
    (run step b evs).toPair = Seq.run (couple (step b) observer) (init, Truth.empty) evs := by
  rw [run_eq]
  exact Simulates.run (abs := Sys.toPair) (fun x e => advance_couple step b x e) start evs

/-! ## Venue facts of the task's `Lemmas.lean` -/

/-- Shares sent, as a library sum. -/
theorem sentFor_eq (l : List Kid) (id : Nat) :
    sentFor l id = (l.map fun k => if k.parent = id then k.qty else 0).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [sentFor, ih]

/-- Shares executed, as a library sum. -/
theorem execFor_eq (l : List Kid) (id : Nat) :
    execFor l id = (l.map fun k => if k.parent = id then k.done else 0).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [execFor, ih]

/-- Shares sent are the library's per-key total of the child orders' quantities. -/
theorem sentFor_kt (l : List Kid) (id : Nat) : sentFor l id = keyTotal Kid.parent Kid.qty l id :=
  sentFor_eq l id

/-- Shares executed are the library's per-key total of the child orders' executed shares. -/
theorem execFor_kt (l : List Kid) (id : Nat) : execFor l id = keyTotal Kid.parent Kid.done l id :=
  execFor_eq l id

/-! The remaining lemmas of the task's `OrderRouter/Lemmas.lean`, from `keyTotal`. -/

@[simp] theorem run_nil (step : Impl) (b : Build) : run step b [] = start := rfl
@[simp] theorem sentFor_nil (id : Nat) : sentFor [] id = 0 := rfl
@[simp] theorem execFor_nil (id : Nat) : execFor [] id = 0 := rfl

@[simp] theorem sentFor_cons (k : Kid) (ks : List Kid) (id : Nat) :
    sentFor (k :: ks) id = (if k.parent = id then k.qty else 0) + sentFor ks id := rfl

@[simp] theorem execFor_cons (k : Kid) (ks : List Kid) (id : Nat) :
    execFor (k :: ks) id = (if k.parent = id then k.done else 0) + execFor ks id := rfl

@[simp] theorem sentFor_append (l₁ l₂ : List Kid) (id : Nat) :
    sentFor (l₁ ++ l₂) id = sentFor l₁ id + sentFor l₂ id := by
  simp only [sentFor_kt, keyTotal_append]

@[simp] theorem execFor_append (l₁ l₂ : List Kid) (id : Nat) :
    execFor (l₁ ++ l₂) id = execFor l₁ id + execFor l₂ id := by
  simp only [execFor_kt, keyTotal_append]

/-- Newly sent child orders have nothing executed. -/
@[simp] theorem execFor_new (out : List Child) (id : Nat) :
    execFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id = 0 := by
  rw [execFor_kt]
  exact keyTotal_eq_zero_of_field _ _ (fun x hx => by obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; rfl) id

/-- Recording executions on one child order leaves the shares sent unchanged. -/
theorem sentFor_set_done (l : List Kid) (k : Nat) (c : Kid) (d : Nat) (h : l[k]? = some c) (id : Nat) :
    sentFor (l.set k { c with done := d }) id = sentFor l id := by
  rw [sentFor_kt, sentFor_kt]
  exact keyTotal_set_eq Kid.parent Kid.qty (x' := { c with done := d }) h rfl rfl id

/-- Recording `x` more executed shares on child order `k` adds `x` to its parent's total. -/
theorem execFor_set_done (l : List Kid) (k : Nat) (c : Kid) (x : Nat) (h : l[k]? = some c) (id : Nat) :
    execFor (l.set k { c with done := c.done + x }) id = execFor l id + (if c.parent = id then x else 0) := by
  rw [execFor_kt, execFor_kt]
  exact keyTotal_set_add Kid.parent Kid.done (x' := { c with done := c.done + x }) h rfl rfl id

/-- `execFor_le_sentFor` of the task's `Lemmas.lean`: a pointwise bound on the summands. -/
theorem execFor_le_sentFor (l : List Kid) (h : ∀ k ∈ l, k.done ≤ k.qty) (id : Nat) :
    execFor l id ≤ sentFor l id := by
  rw [execFor_eq, sentFor_eq]
  exact Ledger.sum_map_le_sum_map l (fun k hk => by split <;> simp [h k hk])

/-- `done_le_qty` of the task's `Lemmas.lean`: the venue model never executes more shares of a
child order than its quantity, whatever the router does. -/
theorem done_le_qty (step : Impl) (b : Build) (evs : List Event) :
    ∀ k ∈ (run step b evs).tr.kids, k.done ≤ k.qty := by
  refine run_induction step b (fun x => ∀ k ∈ x.tr.kids, k.done ≤ k.qty) (by simp [start, Truth.empty]) ?_ evs
  intro x e hx k hk
  simp only [advance, Truth.record, List.mem_append, List.mem_map] at hk
  rcases hk with hk | ⟨c, _, rfl⟩
  · cases e with
    | fill j q =>
      simp only [Truth.observe] at hk
      split at hk
      · next c hc =>
        rcases List.mem_or_eq_of_mem_set hk with hk | rfl
        · exact hx k hk
        · have := hx c (List.mem_of_getElem? hc); simp only; omega
      · exact hx k hk
    | _ => exact hx k hk
  · exact Nat.zero_le _

/-- `exec_le_sent` of the task's `Lemmas.lean`. -/
theorem exec_le_sent (step : Impl) (b : Build) (evs : List Event) (id : Nat) :
    (run step b evs).tr.exec id ≤ (run step b evs).tr.sent id :=
  execFor_le_sentFor _ (done_le_qty step b evs) id

/-! ## The last step, for every router -/

/-- Five of the six requirements from an invariant of the coupled system, for every router.
`Inv` is any property of the run in progress that holds at the start and that every event
preserves, on every code version, and that gives: shares sent at most the quantity, the router's
cumulative quantity equal to the shares executed for every existing parent, the expected child
order on a routing opportunity, and no child order on any other event. -/
theorem reqs_of_invariant (step : Impl) (Inv : Build → Sys → Prop) (h0 : ∀ b, Inv b start)
    (hs : ∀ b x e, Inv b x → Inv b (advance step b x e))
    (hle : ∀ b x, Inv b x → ∀ id, x.tr.sent id ≤ x.tr.qty id)
    (hcum : ∀ b x, Inv b x → ∀ id, id < x.tr.nOrders → (x.st.parents id).cum = x.tr.exec id)
    (hroute : ∀ b x id liq, Inv b x → (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq)
    (hquiet : ∀ b x e, Inv b x → (∀ id liq, e ≠ .route id liq) → (step b x.st e).2 = []) :
    RoutesAvailable step ∧ NeverOverroute step ∧ StopWhenFilled step ∧
      NoExcessExecution step ∧ FillAccounting step := by
  have hinv : ∀ b evs, Inv b (run step b evs) := fun b => run_induction step b (Inv b) (h0 b) (hs b)
  refine ⟨fun b evs id liq => hroute b _ id liq (hinv b evs), fun b evs id => hle b _ (hinv b evs) id,
    ?_, fun b evs id => Nat.le_trans (exec_le_sent step b evs id) (hle b _ (hinv b evs) id),
    fun b evs id hid => hcum b _ (hinv b evs) id hid⟩
  intro b evs e id hfull c hc
  have hle' := hle b _ (hinv b evs) id
  have hex := exec_le_sent step b evs id
  cases e with
  | route j liq =>
    rw [hroute b _ j liq (hinv b evs)] at hc
    simp only [expectedRoute] at hc
    split at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      intro hj
      simp only at hj
      subst hj
      omega
    · simp at hc
  | parent q f => rw [hquiet b _ _ (hinv b evs) (fun _ _ h => by cases h)] at hc; simp at hc
  | ack k => rw [hquiet b _ _ (hinv b evs) (fun _ _ h => by cases h)] at hc; simp at hc
  | fill k q => rw [hquiet b _ _ (hinv b evs) (fun _ _ h => by cases h)] at hc; simp at hc

/-! ## The reference router

The router, the invariant `Inv` and its per-event proof `inv_advance` are copied without change
from `reference/SolutionA.lean`; `inv_advance` uses the lemmas of the task's `Lemmas.lean`, which
are re-proved above from the library. The requirements then follow from `reqs_of_invariant`; the
reference solution proves each of them again from its invariant. -/

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq =>
    if id < s.nParents ∧ 0 < min liq ((s.parents id).qty - (s.parents id).sent) then
      ({ s with parents := upd s.parents id
                  { s.parents id with sent := (s.parents id).sent + min liq ((s.parents id).qty - (s.parents id).sent) },
                nChildren := s.nChildren + 1,
                children := upd s.children s.nChildren
                  ⟨id, min liq ((s.parents id).qty - (s.parents id).sent), 0⟩ },
       [⟨id, min liq ((s.parents id).qty - (s.parents id).sent)⟩])
    else (s, [])
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      ({ s with parents := upd s.parents (s.children k).parent
                  { s.parents (s.children k).parent with
                    cum := (s.parents (s.children k).parent).cum + min q ((s.children k).qty - (s.children k).done) },
                children := upd s.children k
                  { s.children k with done := (s.children k).done + min q ((s.children k).qty - (s.children k).done) } },
       [])
    else (s, [])

/-- The router's records agree with the facts of the run. -/
structure Inv (x : Sys) : Prop where
  np   : x.st.nParents = x.tr.nOrders
  nc   : x.st.nChildren = x.tr.kids.length
  par  : ∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id ∧
           (x.st.parents id).sent = x.tr.sent id ∧ (x.st.parents id).cum = x.tr.exec id
  out  : ∀ id, x.tr.nOrders ≤ id → x.tr.sent id = 0 ∧ x.tr.exec id = 0
  kid  : ∀ k, k < x.tr.kids.length →
           x.tr.kids[k]? = some ⟨(x.st.children k).parent, (x.st.children k).qty, (x.st.children k).done⟩
  kpar : ∀ c ∈ x.tr.kids, c.parent < x.tr.nOrders
  le   : ∀ id, x.tr.sent id ≤ x.tr.qty id

theorem inv_start : Inv start := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [start, init, Truth.empty, Truth.sent, Truth.exec]

-- The copied proof has one unused simp argument; the linter is silenced for it only.
set_option linter.unusedSimpArgs false in
theorem inv_advance (b : Build) (x : Sys) (e : Event) (h : Inv x) : Inv (advance step b x e) := by
  obtain ⟨np, nc, par, out, kid, kpar, le⟩ := h
  cases e with
  | parent q f =>
    simp only [advance, step, Truth.observe, Truth.record, List.map_nil, List.append_nil]
    refine ⟨by simp [np], nc, ?_, ?_, kid, ?_, ?_⟩ <;> dsimp only
    · intro id hid
      simp only [Truth.sent, Truth.exec] at *
      by_cases h : id = x.tr.nOrders
      · subst h; have := out _ (Nat.le_refl _); simp [upd, np, this]
      · have := par id (by omega); simp [upd, np, h, this]
    · intro id hid; exact out id (by omega)
    · intro c hc; have := kpar c hc; omega
    · intro id
      simp only [Truth.sent] at *
      by_cases h : id = x.tr.nOrders
      · subst h; have := (out _ (Nat.le_refl _)).1; simp [upd, this]
      · simp [upd, h]; exact le id
  | route id liq =>
    simp only [advance, step, Truth.observe]
    by_cases hc : id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      simp only [Truth.record, List.map_cons, List.map_nil]
      have hp := par id (by omega)
      refine ⟨np, by simp [nc], ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro j hj
        simp only [Truth.sent, Truth.exec, sentFor_append, execFor_append, sentFor_cons, execFor_cons,
          sentFor_nil, execFor_nil] at *
        by_cases h : j = id
        · subst h; simp [upd, hp]
        · have := par j hj; simp [upd, h, this, Ne.symm h]
      · intro j hj
        have := out j hj
        simp only [Truth.sent, Truth.exec, sentFor_append, execFor_append, sentFor_cons, execFor_cons,
          sentFor_nil, execFor_nil] at *
        have : id ≠ j := by omega
        simp [this, out j hj]
      · intro k hk
        simp only [List.length_append, List.length_cons, List.length_nil] at hk
        by_cases h : k = x.tr.kids.length
        · subst h; simp [upd, nc]
        · have hk' : k < x.tr.kids.length := by omega
          rw [List.getElem?_append_left hk', kid k hk']
          simp [upd, nc, show k ≠ x.tr.kids.length from h]
      · intro c hc'
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with hc' | rfl
        · exact kpar c hc'
        · simp; omega
      · intro j
        simp only [Truth.sent, sentFor_append, sentFor_cons, sentFor_nil] at *
        by_cases h : id = j
        · subst h; have := hp.1; have := hp.2.1; simp only [Truth.sent] at *; simp; omega
        · simp [h]; exact le j
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      simp only [Truth.record, List.map_nil, List.append_nil]
      exact ⟨np, nc, par, out, kid, kpar, le⟩
  | ack k =>
    simp only [advance, step, Truth.observe, Truth.record, List.map_nil, List.append_nil]
    exact ⟨np, nc, par, out, kid, kpar, le⟩
  | fill k q =>
    simp only [advance, step]
    by_cases hk : k < x.st.nChildren
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk)]
      have hkk : k < x.tr.kids.length := by omega
      have hget := kid k hkk
      simp only [Truth.observe, hget, Truth.record, List.map_nil, List.append_nil]
      have hcp := kpar _ (List.mem_of_getElem? hget)
      simp only at hcp
      refine ⟨np, by simp [nc], ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro j hj
        simp only [Truth.sent, Truth.exec]
        rw [sentFor_set_done _ _ _ _ hget, execFor_set_done _ _ _ _ hget]
        have := par j hj
        simp only [Truth.sent, Truth.exec] at this
        by_cases h : j = (x.st.children k).parent
        · subst h; simp [upd, this]
        · simp [upd, h, this, Ne.symm h]
      · intro j hj
        simp only [Truth.sent, Truth.exec]
        rw [sentFor_set_done _ _ _ _ hget, execFor_set_done _ _ _ _ hget]
        have := out j hj
        simp only [Truth.sent, Truth.exec] at this
        have : (x.st.children k).parent ≠ j := by omega
        simp [*]
      · intro k' hk'
        simp only [List.length_set] at hk'
        rw [List.getElem?_set]
        by_cases h : k = k'
        · subst h; simp [upd, hk']
        · simp [h, upd, Ne.symm h, kid k' hk']
      · intro c hc'
        rcases List.mem_or_eq_of_mem_set hc' with hc' | rfl
        · exact kpar c hc'
        · exact hcp
      · intro j
        simp only [Truth.sent]
        rw [sentFor_set_done _ _ _ _ hget]
        exact le j
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
      have hnone : x.tr.kids[k]? = none := by
        rw [List.getElem?_eq_none_iff]; omega
      simp only [Truth.observe, hnone, Truth.record, List.map_nil, List.append_nil]
      exact ⟨np, nc, par, out, kid, kpar, le⟩


/-- The routing output for a run in progress satisfying the invariant (the reference proves it
for `run step b evs` only; the proof is the same). -/
theorem route_out (b : Build) (x : Sys) (h : Inv x) (id liq : Nat) :
    (step b x.st (.route id liq)).2 = expectedRoute x.tr id liq := by
  simp only [step, expectedRoute]
  by_cases hid : id < x.tr.nOrders
  · have hp := h.par id hid
    rw [h.np, hp.1, hp.2.1]
    split <;> simp_all
  · have h1 : ¬ (id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) := by
      rw [h.np]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- Events other than routing opportunities send nothing. -/
theorem quiet (b : Build) (s : State) (e : Event) (hne : ∀ id liq, e ≠ .route id liq) :
    (step b s e).2 = [] := by
  cases e with
  | route id liq => exact absurd rfl (hne id liq)
  | parent q f => rfl
  | ack k => rfl
  | fill k q => simp only [step]; split <;> rfl

theorem req_normal_order_routed : NormalOrderRouted step := by
  intro b flag
  cases b <;> cases flag <;> decide

/-- REQ-ROUTES-AVAILABLE, REQ-NEVER-OVERROUTE, REQ-STOP-WHEN-FILLED, REQ-NO-EXCESS-EXECUTION and
REQ-FILL-ACCOUNTING for the reference router, from `reqs_of_invariant`. -/
theorem reqs : RoutesAvailable step ∧ NeverOverroute step ∧ StopWhenFilled step ∧
    NoExcessExecution step ∧ FillAccounting step :=
  reqs_of_invariant step (fun _ x => Inv x) (fun _ => inv_start) (fun b x e h => inv_advance b x e h)
    (fun _ _ h id => h.le id) (fun _ _ h id hid => (h.par id hid).2.2)
    (fun b x id liq h => route_out b x h id liq) (fun b x e _ hne => quiet b x.st e hne)

theorem req_routes_available : RoutesAvailable step := reqs.1
theorem req_never_overroute : NeverOverroute step := reqs.2.1
theorem req_stop_when_filled : StopWhenFilled step := reqs.2.2.1
theorem req_no_excess_execution : NoExcessExecution step := reqs.2.2.2.1
theorem req_fill_accounting : FillAccounting step := reqs.2.2.2.2

end ProofForgeFinDemo.Machine.Knight
