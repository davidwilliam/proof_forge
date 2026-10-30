import ProofForgeFin
/-!
# Tactic tests: `rc-knight-router`

A harness run on `realworld/tasks/rc-knight-router` (`results/knight-1/A2-1`, the run that proved
five of the six requirements and ran out of budget on REQ-FILL-ACCOUNTING) failed in the final
assembly on goals full of unreduced projections and updates: `{ st := st, tr := tr }.st`,
`(x.st, []).fst`, `upd f k v j`, `if True ∧ True then ...`. The accepted run
(`results/knight-1/A2-2`) proves its two invariants with 84 theorems and 753 lines of proof,
most of them lemmas that unfold one projection or one update.

The first section copies the model without change from
`realworld/tasks/rc-knight-router/spec/OrderRouter/Spec.lean` (the model and the
requirements), the second the lemmas it uses from `spec/OrderRouter/Lemmas.lean`, the third the
implementation and the invariants of the accepted repair `results/knight-1/A2-2/final.lean`
(`routeBySent`, `step`, `InvWeak2`, `InvFillAcc`, `my_sentFor_ge`, `my_execFor_ge`; the unused
build argument of `step` is written `_`). The task files are not imported or modified.

The tests: goals copied from the error messages of the failed attempts (in
`results/knight-1/*/events.jsonl`), each closed by one tactic, next to a proof without the
automation; and the two invariants of the accepted repair over every sequence of events, with
`run_induction`, `step_cases` and `grind`.
-/

namespace ProofForgeFinDemo.Router

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

/-! ## Copied from `spec/OrderRouter/Lemmas.lean` -/

@[simp] theorem sentFor_nil (id : Nat) : sentFor [] id = 0 := rfl
@[simp] theorem execFor_nil (id : Nat) : execFor [] id = 0 := rfl

@[simp] theorem sentFor_cons (k : Kid) (ks : List Kid) (id : Nat) :
    sentFor (k :: ks) id = (if k.parent = id then k.qty else 0) + sentFor ks id := rfl

@[simp] theorem execFor_cons (k : Kid) (ks : List Kid) (id : Nat) :
    execFor (k :: ks) id = (if k.parent = id then k.done else 0) + execFor ks id := rfl

@[simp] theorem sentFor_append (l₁ l₂ : List Kid) (id : Nat) :
    sentFor (l₁ ++ l₂) id = sentFor l₁ id + sentFor l₂ id := by
  induction l₁ with
  | nil => simp
  | cons k ks ih => simp [ih]; omega

@[simp] theorem execFor_append (l₁ l₂ : List Kid) (id : Nat) :
    execFor (l₁ ++ l₂) id = execFor l₁ id + execFor l₂ id := by
  induction l₁ with
  | nil => simp
  | cons k ks ih => simp [ih]; omega

/-- Newly sent child orders have nothing executed. -/
@[simp] theorem execFor_new (out : List Child) (id : Nat) :
    execFor (out.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id = 0 := by
  induction out with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- Shares sent in newly sent child orders, as a sum over the router's output. -/
theorem sentFor_new_cons (c : Child) (cs : List Child) (id : Nat) :
    sentFor ((c :: cs).map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id
      = (if c.parent = id then c.qty else 0) + sentFor (cs.map (fun c => (⟨c.parent, c.qty, 0⟩ : Kid))) id := rfl

/-- Recording executions on one child order leaves the shares sent unchanged. -/
theorem sentFor_set_done (l : List Kid) (k : Nat) (c : Kid) (d : Nat) (h : l[k]? = some c) (id : Nat) :
    sentFor (l.set k { c with done := d }) id = sentFor l id := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp at h; subst h; simp
    | succ k => simp at h; simp [ih k h]

/-- Recording `x` more executed shares on child order `k` adds `x` to its parent's total. -/
theorem execFor_set_done (l : List Kid) (k : Nat) (c : Kid) (x : Nat) (h : l[k]? = some c) (id : Nat) :
    execFor (l.set k { c with done := c.done + x }) id = execFor l id + (if c.parent = id then x else 0) := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero =>
      simp at h; subst h
      simp only [List.set_cons_zero, execFor_cons]
      split <;> omega
    | succ k =>
      simp at h
      simp only [List.set_cons_succ, execFor_cons, ih k h]
      omega

/-! ## Copied from `results/knight-1/A2-2/final.lean` (the accepted repair) -/

def routeBySent (s : State) (id liq : Nat) : State × List Child :=
  let p := s.parents id
  let c := min liq (p.qty - p.sent)
  if id < s.nParents ∧ 0 < c then
    ({ s with parents := upd s.parents id { p with sent := p.sent + c },
              nChildren := s.nChildren + 1,
              children := upd s.children s.nChildren ⟨id, c, 0⟩ }, [⟨id, c⟩])
  else (s, [])

def step : Impl := fun _ s e =>
  match e with
  | .parent q f =>
    ({ s with nParents := s.nParents + 1, parents := upd s.parents s.nParents ⟨q, f, 0, 0⟩ }, [])
  | .route id liq => routeBySent s id liq
  | .ack _ => (s, [])
  | .fill k q =>
    if k < s.nChildren then
      let c := s.children k
      let x := min q (c.qty - c.done)
      let p := s.parents c.parent
      ({ s with parents := upd s.parents c.parent { p with cum := p.cum + x },
                children := upd s.children k { c with done := c.done + x } }, [])
    else (s, [])

def InvWeak2 (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  (∀ id, (x.st.parents id).sent = x.tr.sent id) ∧
  (∀ id, id < x.tr.nOrders → (x.st.parents id).qty = x.tr.qty id) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ∧
  (∀ id, (x.st.parents id).sent ≤ (x.st.parents id).qty)

theorem my_sentFor_ge (l : List Kid) (n id : Nat) (h : ∀ k ∈ l, k.parent < n) (hle : n ≤ id) : sentFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [sentFor_cons]
    have ha : a.parent ≠ id := by
      have hlt := h a (by simp)
      omega
    have ht : ∀ k ∈ as, k.parent < n := fun k hk => h k (by simp [hk])
    simp [ha, ih ht]

theorem my_execFor_ge (l : List Kid) (n id : Nat) (h : ∀ k ∈ l, k.parent < n) (hle : n ≤ id) : execFor l id = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [execFor_cons]
    have ha : a.parent ≠ id := by
      have hlt := h a (by simp)
      omega
    have ht : ∀ k ∈ as, k.parent < n := fun k hk => h k (by simp [hk])
    simp [ha, ih ht]

def InvFillAcc (x : Sys) : Prop :=
  x.st.nParents = x.tr.nOrders ∧
  x.st.nChildren = x.tr.kids.length ∧
  (∀ (k : Nat) (c : Kid), x.tr.kids[k]? = some c → x.st.children k = ⟨c.parent, c.qty, c.done⟩) ∧
  (∀ k ∈ x.tr.kids, k.parent < x.tr.nOrders) ∧
  (∀ id, (x.st.parents id).cum = x.tr.exec id)

/-! ## Goals copied from failed attempts

Each goal is stated with the hypotheses of the error message it was copied from. The proof
with the automation comes first; the proof without it, where it is not the same single step,
follows as a second example. -/

/-- `results/knight-1/A2-2/events.jsonl`, line 475, case `h_3`: a projection of a structure instance
built from a pair. -/
example (x : Sys) (k q : Nat) :
    ({ st := (x.st, ([] : List Child)).fst,
       tr := (x.tr.observe (Event.fill k q)).record (x.st, ([] : List Child)).snd } : Sys).st.nParents =
      x.st.nParents := by
  struct_simp

example (x : Sys) (k q : Nat) :
    ({ st := (x.st, ([] : List Child)).fst,
       tr := (x.tr.observe (Event.fill k q)).record (x.st, ([] : List Child)).snd } : Sys).st.nParents =
      x.st.nParents :=
  rfl

/-- The same line, case `h_4`: the same projection through the condition
of the execution-report handler. -/
example (x : Sys) (k q k' q' : Nat) :
    ({ st :=
        (if k' < x.st.nChildren then
          have c := x.st.children k'
          have x_1 := min q' (c.qty - c.done)
          have p := x.st.parents c.parent
          ({ nParents := x.st.nParents,
             parents := upd x.st.parents c.parent { qty := p.qty, flag := p.flag, sent := p.sent, cum := p.cum + x_1 },
             nChildren := x.st.nChildren,
             children := upd x.st.children k' { parent := c.parent, qty := c.qty, done := c.done + x_1 } },
            ([] : List Child))
        else (x.st, [])).fst,
       tr := (x.tr.observe (Event.fill k q)).record [] } : Sys).st.nParents = x.st.nParents := by
  struct_simp

example (x : Sys) (k q k' q' : Nat) :
    ({ st :=
        (if k' < x.st.nChildren then
          have c := x.st.children k'
          have x_1 := min q' (c.qty - c.done)
          have p := x.st.parents c.parent
          ({ nParents := x.st.nParents,
             parents := upd x.st.parents c.parent { qty := p.qty, flag := p.flag, sent := p.sent, cum := p.cum + x_1 },
             nChildren := x.st.nChildren,
             children := upd x.st.children k' { parent := c.parent, qty := c.qty, done := c.done + x_1 } },
            ([] : List Child))
        else (x.st, [])).fst,
       tr := (x.tr.observe (Event.fill k q)).record [] } : Sys).st.nParents = x.st.nParents := by
  split <;> rfl

/-- The same line, case `h_2`: a projection of the routing helper. -/
example (x : Sys) (id liq : Nat) : (routeBySent x.st id liq).fst.nParents = x.st.nParents := by
  struct_simp [routeBySent]

example (x : Sys) (id liq : Nat) : (routeBySent x.st id liq).fst.nParents = x.st.nParents := by
  unfold routeBySent
  dsimp only
  split <;> rfl

/-- `results/knight-1/A2-2/events.jsonl`, line 486: an update read at another position, with the
inequation the other way round (`simp [upd_neq _ _ _ _ hj]` failed on it). -/
example (x : Sys) (k q id : Nat) (_h : k < x.st.nChildren) (hj : ¬(x.st.children k).parent = id) :
    (upd x.st.parents (x.st.children k).parent
        { qty := (x.st.parents (x.st.children k).parent).qty,
          flag := (x.st.parents (x.st.children k).parent).flag,
          sent := (x.st.parents (x.st.children k).parent).sent,
          cum := (x.st.parents (x.st.children k).parent).cum +
            min q ((x.st.children k).qty - (x.st.children k).done) }
        id).sent = (x.st.parents id).sent := by
  struct_simp [upd, hj]

example (x : Sys) (k q id : Nat) (_h : k < x.st.nChildren) (hj : ¬(x.st.children k).parent = id) :
    (upd x.st.parents (x.st.children k).parent
        { qty := (x.st.parents (x.st.children k).parent).qty,
          flag := (x.st.parents (x.st.children k).parent).flag,
          sent := (x.st.parents (x.st.children k).parent).sent,
          cum := (x.st.parents (x.st.children k).parent).cum +
            min q ((x.st.children k).qty - (x.st.children k).done) }
        id).sent = (x.st.parents id).sent := by
  have hj' : id ≠ (x.st.children k).parent := fun h => hj h.symm
  simp only [upd, hj', ite_false]

/-- `results/knight-1/A2-2/events.jsonl`, line 645: a decided condition left as `True ∧ True`. -/
example (x : Sys) (id liq : Nat) :
    [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent) : Child }] =
      if True ∧ True then [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent) }]
      else [] := by
  struct_simp

example (x : Sys) (id liq : Nat) :
    [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent) : Child }] =
      if True ∧ True then [{ parent := id, qty := min liq ((x.st.parents id).qty - (x.st.parents id).sent) }]
      else [] := by
  simp

/-- `results/knight-1/A2-2/events.jsonl`, line 636: an implication from a refuted equation. -/
example (x : Sys) (rid liq jj : Nat) (hjj : ¬jj = rid) :
    jj = rid →
      (x.st.parents jj).sent = (x.st.parents rid).sent + min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) := by
  struct_simp [hjj]

example (x : Sys) (rid liq jj : Nat) (hjj : ¬jj = rid) :
    jj = rid →
      (x.st.parents jj).sent = (x.st.parents rid).sent + min liq ((x.st.parents rid).qty - (x.st.parents rid).sent) := by
  intro h
  exact absurd h hjj

/-- `results/knight-1/A2-2/events.jsonl`, line 689: a condition refuted by its first conjunct, and an
invariant that closes the rest. -/
example (x : Sys) (id liq jj : Nat) (hLe : ∀ (jj : Nat), (x.st.parents jj).sent ≤ (x.st.parents jj).qty)
    (hjj : ¬jj = id) :
    (if jj = id ∧ id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent) then
        (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent)
      else (x.st.parents jj).sent) ≤ (x.st.parents jj).qty := by
  struct_simp [hjj, hLe]

example (x : Sys) (id liq jj : Nat) (hLe : ∀ (jj : Nat), (x.st.parents jj).sent ≤ (x.st.parents jj).qty)
    (hjj : ¬jj = id) :
    (if jj = id ∧ id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent) then
        (x.st.parents id).sent + min liq ((x.st.parents id).qty - (x.st.parents id).sent)
      else (x.st.parents jj).sent) ≤ (x.st.parents jj).qty := by
  have hc : ¬(jj = id ∧ id < x.st.nParents ∧ 0 < min liq ((x.st.parents id).qty - (x.st.parents id).sent)) :=
    fun h => hjj h.1
  simp only [hc, ite_false]
  exact hLe jj

/-- `results/knight-1/A2-1/events.jsonl`, line 1421: the last goal of REQ-FILL-ACCOUNTING in the run that
ran out of budget on it. -/
example (x : Sys) (q id : Nat) (c0 : Kid) (hold : (x.st.parents id).cum = x.tr.exec id)
    (heq : id = c0.parent) :
    (x.st.parents c0.parent).cum + min q (c0.qty - c0.done) = x.tr.exec id + min q (c0.qty - c0.done) := by
  struct_simp [← heq, hold]

example (x : Sys) (q id : Nat) (c0 : Kid) (hold : (x.st.parents id).cum = x.tr.exec id)
    (heq : id = c0.parent) :
    (x.st.parents c0.parent).cum + min q (c0.qty - c0.done) = x.tr.exec id + min q (c0.qty - c0.done) := by
  rw [← heq, hold]

/-! ## The invariants of the accepted repair over every sequence of events

`run_induction [run]` reads the task's `run` (a left fold) as `Seq.run` and leaves one goal per
event constructor, with the step function, the observation and the record unfolded and every
projection reduced; `step_cases` splits each on the conditions and the match of the venue model
that remain. What is left is the arithmetic of each event, which `grind` closes from the
invariant at the state before. The accepted repair proves the same two statements with 84
theorems and 753 lines of proof (`myWeak2_run_clean2`, `plan3_invFillAcc_run` and the lemmas
they use); here they take 4 theorems and 61 lines, `my_sentFor_ge` and `my_execFor_ge`
included. -/

/-- The router's count of parent orders is the number of parent orders, after every sequence
of events. -/
theorem nParents_run (b : Build) (evs : List Event) :
    (run step b evs).st.nParents = (run step b evs).tr.nOrders := by
  run_induction [run] with [advance, step, routeBySent, Truth.observe, Truth.record, upd]
  step_cases

/-- `InvWeak2` of the accepted repair (`myWeak2_run_clean2`) after every sequence of events. -/
theorem invWeak2_run (b : Build) (evs : List Event) : InvWeak2 (run step b evs) := by
  run_induction [run] with [advance, step, routeBySent, Truth.observe, Truth.record, upd, InvWeak2,
    Truth.sent, start, init, Truth.empty, sentFor]
  all_goals try step_cases
  case parent =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have h6 := fun id => my_sentFor_ge x.tr.kids x.tr.nOrders id h4
    grind
  case pos =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    simp only [sentFor_append, sentFor]
    grind
  case fill.some =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have hs := sentFor_set_done x.tr.kids child val (val.done + min q (val.qty - val.done)) hc
    have hm := List.mem_of_getElem? hc
    grind [List.mem_or_eq_of_mem_set]

/-- `InvFillAcc` of the accepted repair (`plan3_invFillAcc_run`) after every sequence of
events. -/
theorem invFillAcc_run (b : Build) (evs : List Event) : InvFillAcc (run step b evs) := by
  run_induction [run] with [advance, step, routeBySent, Truth.observe, Truth.record, upd, InvFillAcc,
    Truth.exec, start, init, Truth.empty, execFor]
  all_goals try step_cases
  case parent =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have h6 := fun id => my_execFor_ge x.tr.kids x.tr.nOrders id h4
    grind
  case pos =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    refine ⟨h1, by omega, fun k c hk => ?_, by grind, fun j => by simp [h5, execFor]⟩
    rw [List.getElem?_append] at hk
    by_cases hlt : k < x.tr.kids.length
    · grind
    · have : k - x.tr.kids.length = 0 := by grind
      grind
  case pos =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    grind
  case pos =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have he := execFor_set_done x.tr.kids child val (min q (val.qty - val.done)) hc
    have hm := List.mem_of_getElem? hc
    have hv := h3 child val hc
    grind [List.mem_or_eq_of_mem_set]
  case neg =>
    have := (List.getElem?_eq_some_iff.mp hc).1
    omega

/-! ## Two requirements of the task -/

/-- REQ-NEVER-OVERROUTE for the accepted repair. -/
theorem req_never_overroute : NeverOverroute step := by
  intro b evs id
  obtain ⟨_, h2, h3, h4, h5⟩ := invWeak2_run b evs
  by_cases hid : id < (run step b evs).tr.nOrders
  · have := h2 id; have := h3 id hid; have := h5 id; omega
  · have := my_sentFor_ge _ _ id h4 (by omega)
    simp only [Truth.sent] at *
    omega

/-- REQ-FILL-ACCOUNTING for the accepted repair: the requirement the run `A2-1` ran out of
budget on. -/
theorem req_fill_accounting : FillAccounting step :=
  fun b evs id _ => (invFillAcc_run b evs).2.2.2.2 id

end ProofForgeFinDemo.Router
