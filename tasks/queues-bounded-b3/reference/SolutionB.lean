import BoundedQueue.Spec
/-!
# Reference solution B (hidden from agents)

Structural implementation: compare the free space with zero for enqueue and pattern match
the stored list for dequeue.
-/

namespace BoundedQueue

def enqueueImpl (s : State) (x : Nat) : Outcome × State :=
  if s.capacity - s.items.length = 0 then (.rejected, s)
  else (.ok, { s with items := s.items.concat x })

def dequeueImpl (s : State) : Outcome × State :=
  match s.items with
  | [] => (.rejected, s)
  | x :: rest => (.got x, { capacity := s.capacity, items := rest, served := s.served + 1 })

def step : Impl
  | s, .enqueue x => enqueueImpl s x
  | s, .dequeue => dequeueImpl s

theorem enqueue_full {s : State} {x : Nat} (h : ¬ s.items.length < s.capacity) :
    step s (.enqueue x) = (.rejected, s) := by
  have : s.capacity - s.items.length = 0 := by omega
  simp [step, enqueueImpl, this]

theorem enqueue_free {s : State} {x : Nat} (h : s.items.length < s.capacity) :
    step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
  have : s.capacity - s.items.length ≠ 0 := by omega
  simp [step, enqueueImpl, this]

theorem dequeue_nil {s : State} (h : s.items = []) : step s .dequeue = (.rejected, s) := by
  simp [step, dequeueImpl, h]

theorem dequeue_cons {s : State} {x : Nat} {rest : List Nat} (h : s.items = x :: rest) :
    step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
  simp [step, dequeueImpl, h]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x => rw [enqueue_free h]; simp
  | dequeue =>
    cases hs : s.items with
    | nil => simp [Valid, hs] at h
    | cons x rest => rw [dequeue_cons hs]; simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x => exact enqueue_full h
  | dequeue => exact dequeue_nil (by simpa [Valid] using h)

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  by_cases hv : s.items.length < s.capacity
  · exact enqueue_free hv
  · rw [enqueue_full hv] at h; exact absurd rfl h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases hs : s.items with
  | nil => rw [dequeue_nil hs] at h; exact absurd rfl h
  | cons x rest => exact ⟨x, rest, rfl, dequeue_cons hs⟩

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases hv : s.items.length < s.capacity
    · rw [enqueue_free hv]; simp; omega
    · rw [enqueue_full hv]; exact hle
  | dequeue =>
    cases hs : s.items with
    | nil => rw [dequeue_nil hs]; exact hle
    | cons x rest => rw [dequeue_cons hs]; rw [hs] at hle; simp at hle ⊢; omega

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run, inflow, outflow, List.flatMap_cons] at ih ⊢
    have hstep : s.items ++ inflowOf (op, (step s op).1)
        = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
      cases op with
      | enqueue x =>
        by_cases hv : s.items.length < s.capacity
        · rw [enqueue_free hv]; simp [inflowOf, outflowOf]
        · rw [enqueue_full hv]; simp [inflowOf, outflowOf]
      | dequeue =>
        cases hs : s.items with
        | nil => rw [dequeue_nil hs]; simp [inflowOf, outflowOf, hs]
        | cons x rest => rw [dequeue_cons hs]; simp [inflowOf, outflowOf]
    rw [← List.append_assoc, hstep, List.append_assoc, ih, List.append_assoc]

end BoundedQueue
