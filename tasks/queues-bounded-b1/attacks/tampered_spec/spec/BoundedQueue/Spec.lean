/-!
# Bounded FIFO queue specification (protected)

A queue holds at most `capacity` values. Enqueue appends a value at the back and is
rejected when the queue is full; dequeue removes and returns the front value and is
rejected when the queue is empty. Every requirement is a predicate over an implementation
`step : Impl`; the locked challenge (`BoundedQueue/Challenge.lean`) applies each one to the
definition hole `BoundedQueue.step`.
-/

namespace BoundedQueue

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
  | .enqueue _ => s.items.length ≤ s.capacity
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
    (step s op).2.items.length ≤ (step s op).2.capacity + 1

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

end BoundedQueue
