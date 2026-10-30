import ProofForgeFin.Trading.Book
/-!
# Demonstration: the six requirements of `queues-bounded-b3` with the order book library

The definitions in the first section are copied without change from
`tasks/queues-bounded-b3/spec/BoundedQueue/Spec.lean` (identical to `queues-bounded-b1` and
`queues-bounded-b2`). The task files are not imported or modified.

The reference solution (`reference/SolutionA.lean`) proves REQ-FIFO with a one-step flow lemma
and its own induction over the task's `run`. Here the task's `run` is `Book.runOut` and the
induction is `Book.flow_runOut` with the identity view, the same theorem that gives the
per-priority FIFO requirement of `queues-prio-b3`. The one-step facts about the implementation
remain task-specific.
-/

namespace ProofForgeFinDemo.Trading.BoundedQueue

open ProofForgeFin.Trading

/-! ## Copied from `spec/BoundedQueue/Spec.lean` -/

/-- Queue state: the capacity, the stored values from oldest (front) to newest (back), and
the number of values dequeued so far. -/
structure State where
  capacity : Nat
  items    : List Nat
  served   : Nat

inductive Op where
  | enqueue (x : Nat)
  | dequeue
  deriving DecidableEq, Repr

inductive Outcome where
  | ok
  | got (x : Nat)
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Op → Outcome × State

/-- The conditions under which an operation must succeed: enqueue needs a free place,
dequeue needs a stored value. -/
def Valid (s : State) : Op → Prop
  | .enqueue _ => s.items.length < s.capacity
  | .dequeue => s.items ≠ []

/-- Run a list of operations from a state; returns each operation with its outcome, and
the final state. -/
def run (step : Impl) : State → List Op → List (Op × Outcome) × State
  | s, [] => ([], s)
  | s, op :: ops =>
    ((op, (step s op).1) :: (run step (step s op).2 ops).1, (run step (step s op).2 ops).2)

/-- The value an operation added to the queue, if it was an accepted enqueue. -/
def inflowOf : Op × Outcome → List Nat
  | (.enqueue x, .ok) => [x]
  | _ => []

/-- The value an operation returned, if it was a dequeue that delivered one. -/
def outflowOf : Op × Outcome → List Nat
  | (_, .got x) => [x]
  | _ => []

/-- Values accepted into the queue during a trace, in order. -/
def inflow (t : List (Op × Outcome)) : List Nat := t.flatMap inflowOf

/-- Values delivered by the queue during a trace, in order. -/
def outflow (t : List (Op × Outcome)) : List Nat := t.flatMap outflowOf

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid operation succeeds, that is, it is not rejected. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s op, Valid s op → (step s op).1 ≠ .rejected

/-- REQ-INVALID-NOOP: every invalid operation is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s op, ¬ Valid s op → step s op = (.rejected, s)

/-- REQ-CAPACITY: if the queue holds at most `capacity` values, it still does after any
operation. -/
def CapacityBound (step : Impl) : Prop :=
  ∀ s op, s.items.length ≤ s.capacity →
    (step s op).2.items.length ≤ (step s op).2.capacity

/-- REQ-ENQUEUE-EFFECTS: a successful enqueue returns `ok`, appends the value at the back,
and leaves the capacity and the served count unchanged. -/
def EnqueueEffects (step : Impl) : Prop :=
  ∀ s x, (step s (.enqueue x)).1 ≠ .rejected →
    step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] })

/-- REQ-DEQUEUE-EFFECTS: a successful dequeue returns the front value, removes exactly that
value, increments the served count, and leaves the capacity unchanged. -/
def DequeueEffects (step : Impl) : Prop :=
  ∀ s, (step s .dequeue).1 ≠ .rejected →
    ∃ x rest, s.items = x :: rest ∧
      step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 })

/-- REQ-FIFO: over any sequence of operations, the starting values followed by the accepted
values equal the delivered values followed by the final contents. -/
def Fifo (step : Impl) : Prop :=
  ∀ s ops, s.items ++ inflow (run step s ops).1 = outflow (run step s ops).1 ++ (run step s ops).2.items

/-! ## Re-proved with the library -/

/-- The task's `run` is the library's `runOut`. -/
theorem run_eq (st : Impl) (s : State) (ops : List Op) : run st s ops = Book.runOut st s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [run, ih]; rfl

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid <;> infer_instance

/-- The implementation: decide validity, then append at the back or remove the front. -/
def step : Impl := fun s op =>
  if Valid s op then
    match op with
    | .enqueue x => (.ok, { s with items := s.items ++ [x] })
    | .dequeue => (.got (s.items.headD 0), { s with items := s.items.tail, served := s.served + 1 })
  else (.rejected, s)

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : step s op = (.rejected, s) := by
  simp [step, h]

theorem step_enqueue {s : State} {x : Nat} (h : s.items.length < s.capacity) :
    step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
  have : Valid s (.enqueue x) := h
  simp [step, this]

theorem step_dequeue {s : State} {x : Nat} {rest : List Nat} (h : s.items = x :: rest) :
    step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
  have : Valid s .dequeue := by simp [Valid, h]
  simp [step, this, h]

theorem ok_valid {s : State} {op : Op} (h : (step s op).1 ≠ .rejected) : Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · rw [step_invalid hv] at h; exact absurd rfl h

/-- A valid dequeue has a front value. -/
theorem dequeue_cons {s : State} (h : Valid s .dequeue) : ∃ x rest, s.items = x :: rest := by
  cases hs : s.items with
  | nil => simp [Valid, hs] at h
  | cons x rest => exact ⟨x, rest, rfl⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x => rw [step_enqueue h]; simp
  | dequeue => obtain ⟨x, rest, hs⟩ := dequeue_cons h; rw [step_dequeue hs]; simp

theorem req_invalid_noop : InvalidNoop step := fun _ _ h => step_invalid h

theorem req_enqueue_effects : EnqueueEffects step := fun _ _ h => step_enqueue (ok_valid h)

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  obtain ⟨x, rest, hs⟩ := dequeue_cons (ok_valid h)
  exact ⟨x, rest, hs, step_dequeue hs⟩

theorem req_capacity : CapacityBound step := by
  intro s op hle
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp only [List.length_append, List.length_singleton]; exact hv
    | dequeue =>
      obtain ⟨x, rest, hs⟩ := dequeue_cons hv
      rw [step_dequeue hs]; rw [hs] at hle; simp at hle ⊢; omega
  · rw [step_invalid hv]; exact hle

/-- One step moves values from the inflow into the queue and from the queue to the outflow. -/
theorem step_flow (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp [inflowOf, outflowOf]
    | dequeue =>
      obtain ⟨x, rest, hs⟩ := dequeue_cons hv
      rw [step_dequeue hs, hs]; simp [inflowOf, outflowOf]
  · rw [step_invalid hv]; cases op <;> simp [inflowOf, outflowOf]

theorem req_fifo : Fifo step := by
  intro s ops
  rw [run_eq]
  exact Book.flow_runOut State.items inflowOf outflowOf id (fun _ _ => rfl) step_flow s ops

end ProofForgeFinDemo.Trading.BoundedQueue
