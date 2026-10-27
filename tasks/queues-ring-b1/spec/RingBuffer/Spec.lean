/-!
# Ring buffer specification (protected)

A FIFO queue stored in a fixed array of `capacity` slots. The oldest value sits in slot
`head` and the `count` stored values occupy the slots that follow it, wrapping around
modulo `capacity`. Enqueue writes the slot after the newest value; dequeue reads slot
`head` and advances it. Every requirement is a predicate over an implementation
`step : Impl`; the locked challenge (`RingBuffer/Challenge.lean`) applies each one to the
definition hole `RingBuffer.step`.
-/

namespace RingBuffer

/-- Ring buffer state: the number of slots, the slot contents `buf 0` to
`buf (capacity - 1)`, the slot of the oldest value, and the number of stored values. -/
structure State where
  capacity : Nat
  buf      : Nat → Nat
  head     : Nat
  count    : Nat

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

/-- A state is well formed when it has a slot, `head` is a slot, and `count` fits. -/
def WellFormed (s : State) : Prop :=
  0 < s.capacity ∧ s.head < s.capacity ∧ s.count ≤ s.capacity

/-- The conditions under which an operation must succeed: the state is well formed, and
enqueue needs a free slot while dequeue needs a stored value. -/
def Valid (s : State) : Op → Prop
  | .enqueue _ => WellFormed s ∧ s.count < s.capacity
  | .dequeue => WellFormed s ∧ 0 < s.count

/-- The slot holding the value at position `i` counted from the oldest. -/
def slot (s : State) (i : Nat) : Nat := (s.head + i) % s.capacity

/-- The stored values from oldest to newest. -/
def contents (s : State) : List Nat := (List.range s.count).map (fun i => s.buf (slot s i))

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

/-- REQ-WELL-FORMED: every operation on a well-formed state yields a well-formed state. -/
def KeepsWellFormed (step : Impl) : Prop :=
  ∀ s op, WellFormed s → WellFormed (step s op).2

/-- REQ-ENQUEUE-EFFECTS: a successful enqueue returns `ok`, writes the value into slot
`slot s s.count` and no other slot, increments `count`, and keeps `capacity` and `head`. -/
def EnqueueEffects (step : Impl) : Prop :=
  ∀ s x, (step s (.enqueue x)).1 ≠ .rejected →
    step s (.enqueue x) = (.ok, { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 })

/-- REQ-DEQUEUE-EFFECTS: a successful dequeue returns the value in slot `head`, advances
`head` by one slot modulo `capacity`, decrements `count`, and keeps every slot. -/
def DequeueEffects (step : Impl) : Prop :=
  ∀ s, (step s .dequeue).1 ≠ .rejected →
    step s .dequeue = (.got (s.buf s.head), { s with
      head := (s.head + 1) % s.capacity,
      count := s.count - 1 })

/-- REQ-ENQUEUE-CONTENTS: a successful enqueue appends the value to the stored values. -/
def EnqueueContents (step : Impl) : Prop :=
  ∀ s x, (step s (.enqueue x)).1 ≠ .rejected →
    contents (step s (.enqueue x)).2 = contents s ++ [x]

/-- REQ-DEQUEUE-CONTENTS: a successful dequeue returns the oldest stored value and removes
exactly that value. -/
def DequeueContents (step : Impl) : Prop :=
  ∀ s, (step s .dequeue).1 ≠ .rejected →
    ∃ x, (step s .dequeue).1 = .got x ∧ contents s = x :: contents (step s .dequeue).2

/-- REQ-FIFO: over any sequence of operations, the starting values followed by the accepted
values equal the delivered values followed by the final stored values. -/
def Fifo (step : Impl) : Prop :=
  ∀ s ops, contents s ++ inflow (run step s ops).1
    = outflow (run step s ops).1 ++ contents (run step s ops).2

end RingBuffer
