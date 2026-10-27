/-!
# Stable priority queue specification (protected)

A bounded priority queue kept as a list in service order. A smaller priority number is
served first, and entries with equal priority are served in the order they were inserted.
Insert is rejected when the queue is full; pop removes and returns the next entry and is
rejected when the queue is empty. Both are rejected when the stored list is not in service
order. Every requirement is a predicate over an implementation `step : Impl`; the locked
challenge (`PrioQueue/Challenge.lean`) applies each one to the definition hole
`PrioQueue.step`.
-/

namespace PrioQueue

/-- A queued entry: its priority (smaller is served first) and its payload. -/
structure Entry where
  prio : Nat
  val  : Nat
  deriving DecidableEq, Repr

/-- Queue state: the capacity and the stored entries in service order. -/
structure State where
  capacity : Nat
  items    : List Entry

inductive Op where
  | insert (e : Entry)
  | pop
  deriving DecidableEq, Repr

inductive Outcome where
  | ok
  | got (e : Entry)
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Op → Outcome × State

/-- A list is in service order when priorities never decrease along it. -/
def Sorted (l : List Entry) : Prop := l.Pairwise (fun a b => a.prio ≤ b.prio)

/-- The conditions under which an operation must succeed: the stored list is in service
order, and insert needs a free place while pop needs a stored entry. -/
def Valid (s : State) : Op → Prop
  | .insert _ => Sorted s.items ∧ s.items.length < s.capacity
  | .pop => Sorted s.items ∧ s.items ≠ []

/-- The entries of priority `p` in a list, in list order. -/
def classOf (p : Nat) (l : List Entry) : List Entry := l.filter (fun x => x.prio == p)

/-- Run a list of operations from a state; returns each operation with its outcome, and
the final state. -/
def run (step : Impl) : State → List Op → List (Op × Outcome) × State
  | s, [] => ([], s)
  | s, op :: ops =>
    ((op, (step s op).1) :: (run step (step s op).2 ops).1, (run step (step s op).2 ops).2)

/-- The entry an operation added to the queue, if it was an accepted insert. -/
def inflowOf : Op × Outcome → List Entry
  | (.insert e, .ok) => [e]
  | _ => []

/-- The entry an operation returned, if it was a pop that delivered one. -/
def outflowOf : Op × Outcome → List Entry
  | (_, .got e) => [e]
  | _ => []

/-- Entries accepted into the queue during a trace, in order. -/
def inflow (t : List (Op × Outcome)) : List Entry := t.flatMap inflowOf

/-- Entries delivered by the queue during a trace, in order. -/
def outflow (t : List (Op × Outcome)) : List Entry := t.flatMap outflowOf

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid operation succeeds, that is, it is not rejected. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s op, Valid s op → (step s op).1 ≠ .rejected

/-- REQ-INVALID-NOOP: every invalid operation is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s op, ¬ Valid s op → step s op = (.rejected, s)

/-- REQ-CAPACITY: if the queue holds at most `capacity` entries, it still does after any
operation. -/
def CapacityBound (step : Impl) : Prop :=
  ∀ s op, s.items.length ≤ s.capacity →
    (step s op).2.items.length ≤ (step s op).2.capacity

/-- REQ-POP-MIN: a successful pop returns an entry whose priority is at most that of every
entry left in the queue. -/
def PopMin (step : Impl) : Prop :=
  ∀ s, (step s .pop).1 ≠ .rejected →
    ∃ e, (step s .pop).1 = .got e ∧ ∀ x ∈ (step s .pop).2.items, e.prio ≤ x.prio

/-- REQ-SORTED: every operation on a queue in service order leaves it in service order. -/
def KeepsSorted (step : Impl) : Prop :=
  ∀ s op, Sorted s.items → Sorted (step s op).2.items

/-- REQ-INSERT-EFFECTS: a successful insert returns `ok`, keeps the capacity, and places
the entry after every stored entry of smaller or equal priority and before every stored
entry of larger priority, keeping the order of the stored entries. -/
def InsertEffects (step : Impl) : Prop :=
  ∀ s e, (step s (.insert e)).1 ≠ .rejected →
    (step s (.insert e)).1 = .ok ∧ (step s (.insert e)).2.capacity = s.capacity ∧
    ∃ l₁ l₂, s.items = l₁ ++ l₂ ∧ (step s (.insert e)).2.items = l₁ ++ e :: l₂ ∧
      (∀ x ∈ l₁, x.prio ≤ e.prio) ∧ (∀ x ∈ l₂, e.prio < x.prio)

/-- REQ-POP-EFFECTS: a successful pop keeps the capacity and returns and removes the first
stored entry of smallest priority, keeping the order of the other entries. -/
def PopEffects (step : Impl) : Prop :=
  ∀ s, (step s .pop).1 ≠ .rejected →
    (step s .pop).2.capacity = s.capacity ∧
    ∃ l₁ e l₂, s.items = l₁ ++ e :: l₂ ∧ (step s .pop).1 = .got e ∧
      (step s .pop).2.items = l₁ ++ l₂ ∧
      (∀ x ∈ l₁, e.prio < x.prio) ∧ (∀ x ∈ l₂, e.prio ≤ x.prio)

/-- REQ-FIFO-TIES: over any sequence of operations and for every priority, the stored entries
of that priority followed by those accepted equal those delivered followed by those left,
so entries of equal priority leave in the order they arrived. -/
def FifoTies (step : Impl) : Prop :=
  ∀ s ops p, classOf p s.items ++ classOf p (inflow (run step s ops).1)
    = classOf p (outflow (run step s ops).1) ++ classOf p (run step s ops).2.items

end PrioQueue
