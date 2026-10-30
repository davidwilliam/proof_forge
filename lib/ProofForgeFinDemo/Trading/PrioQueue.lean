import ProofForgeFin.Trading.Book
/-!
# Demonstration: the eight requirements of `queues-prio-b3` with the order book library

The definitions in the first section are copied without change from
`tasks/queues-prio-b3/spec/PrioQueue/Spec.lean` (identical to `queues-prio-b1`). The task files
are not imported or modified.

A stable priority queue is one side of a limit order book: a smaller priority number is a better
price for the `sell` side, and entries of equal priority are served in arrival order (time
priority). The task's `Sorted` is `Book.Sorted .sell Entry.prio` and its `classOf p` is
`Book.level Entry.prio p`, both by `rfl`. The implementation below inserts with
`Book.insertBy`. The reference solution (`reference/SolutionA.lean`) proves its own insertion
split, length, sortedness, the per-priority bookkeeping of one insert and one pop, and the
induction over runs for REQ-FIFO-TIES; here they are `Book.insertBy_split`,
`Book.length_insertBy`, `Book.sorted_insertBy`, `Book.level_insertBy`, `Book.level_head` and
`Book.flow_runOut`.
-/

namespace ProofForgeFinDemo.Trading.PrioQueue

open ProofForgeFin.Trading

/-! ## Copied from `spec/PrioQueue/Spec.lean` -/

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

/-! ## Re-proved with the library -/

/-- The task's service order is the library's priority order for the `sell` side. -/
theorem sorted_iff (l : List Entry) : Sorted l ↔ Book.Sorted .sell Entry.prio l := Iff.rfl

/-- The task's priority class is the library's price level. -/
theorem classOf_eq (p : Nat) (l : List Entry) : classOf p l = Book.level Entry.prio p l := rfl

/-- The task's `run` is the library's `runOut`. -/
theorem run_eq (st : Impl) (s : State) (ops : List Op) : run st s ops = Book.runOut st s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [run, ih]; rfl

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid Sorted <;> infer_instance

/-- The implementation: insert with time priority, pop the head. -/
def step : Impl := fun s op =>
  if Valid s op then
    match op, s.items with
    | .insert e, _ => (.ok, { s with items := Book.insertBy .sell Entry.prio e s.items })
    | .pop, x :: xs => (.got x, { s with items := xs })
    | .pop, [] => (.rejected, s)
  else (.rejected, s)

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : step s op = (.rejected, s) := by
  simp [step, h]

theorem step_insert {s : State} {e : Entry} (h : Valid s (.insert e)) :
    step s (.insert e) = (.ok, { s with items := Book.insertBy .sell Entry.prio e s.items }) := by
  simp [step, h]

theorem step_pop {s : State} {x : Entry} {xs : List Entry} (hs : s.items = x :: xs)
    (h : Valid s .pop) : step s .pop = (.got x, { s with items := xs }) := by
  simp [step, h, hs]

theorem ok_valid {s : State} {op : Op} (h : (step s op).1 ≠ .rejected) : Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · rw [step_invalid hv] at h; exact absurd rfl h

/-- A valid pop has a head to return. -/
theorem pop_cons {s : State} (h : Valid s .pop) : ∃ x xs, s.items = x :: xs := by
  cases hs : s.items with
  | nil => exact absurd hs h.2
  | cons x xs => exact ⟨x, xs, rfl⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | insert e => rw [step_insert h]; simp
  | pop => obtain ⟨x, xs, hs⟩ := pop_cons h; rw [step_pop hs h]; simp

theorem req_invalid_noop : InvalidNoop step := fun _ _ h => step_invalid h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  by_cases hv : Valid s op
  · cases op with
    | insert e => rw [step_insert hv]; simp only [Book.length_insertBy]; exact hv.2
    | pop =>
      obtain ⟨x, xs, hs⟩ := pop_cons hv
      rw [step_pop hs hv]; rw [hs] at hle; simp at hle ⊢; omega
  · rw [step_invalid hv]; exact hle

theorem req_pop_min : PopMin step := by
  intro s h
  have hv := ok_valid h
  obtain ⟨x, xs, hs⟩ := pop_cons hv
  rw [step_pop hs hv]
  have hsort : Book.Sorted .sell Entry.prio (x :: xs) := hs ▸ hv.1
  exact ⟨x, rfl, hsort.head_le⟩

theorem req_sorted : KeepsSorted step := by
  intro s op hsort
  by_cases hv : Valid s op
  · cases op with
    | insert e => rw [step_insert hv]; exact Book.sorted_insertBy e ((sorted_iff _).1 hsort)
    | pop =>
      obtain ⟨x, xs, hs⟩ := pop_cons hv
      rw [step_pop hs hv]
      exact (show Book.Sorted .sell Entry.prio (x :: xs) from hs ▸ hsort).tail
  · rw [step_invalid hv]; exact hsort

theorem req_insert_effects : InsertEffects step := by
  intro s e h
  have hv := ok_valid h
  rw [step_insert hv]
  obtain ⟨l₁, l₂, h1, h2, h3, h4⟩ := Book.insertBy_split e ((sorted_iff _).1 hv.1)
  exact ⟨rfl, rfl, l₁, l₂, h1, h2, h3, h4⟩

theorem req_pop_effects : PopEffects step := by
  intro s h
  have hv := ok_valid h
  obtain ⟨x, xs, hs⟩ := pop_cons hv
  rw [step_pop hs hv]
  have hsort : Book.Sorted .sell Entry.prio (x :: xs) := hs ▸ hv.1
  exact ⟨rfl, [], x, xs, by simp [hs], rfl, rfl, by simp, hsort.head_le⟩

/-- One step keeps each priority class in order: the class before plus what was accepted equals
what was delivered plus the class after. -/
theorem step_flow (p : Nat) (s : State) (op : Op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by
  by_cases hv : Valid s op
  · cases op with
    | insert e =>
      rw [step_insert hv]
      simp only [classOf_eq, inflowOf, outflowOf, Book.level_insertBy p e ((sorted_iff _).1 hv.1)]; simp
    | pop =>
      obtain ⟨x, xs, hs⟩ := pop_cons hv
      rw [step_pop hs hv, hs]
      simp only [classOf_eq, inflowOf, outflowOf, Book.level_head p x xs]; simp
  · rw [step_invalid hv]; cases op <;> simp [inflowOf, outflowOf, classOf]

theorem req_fifo_ties : FifoTies step := by
  intro s ops p
  rw [run_eq]
  exact Book.flow_runOut State.items inflowOf outflowOf (classOf p)
    (fun _ _ => List.filter_append ..) (step_flow p) s ops

end ProofForgeFinDemo.Trading.PrioQueue
