-- Tampered workspace: validity and the capacity bound are loosened in Spec.lean.
import BoundedQueue.Spec

namespace BoundedQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid <;> infer_instance

def step : Impl := fun s op =>
  if Valid s op then
    match op with
    | .enqueue x => (.ok, { s with items := s.items ++ [x] })
    | .dequeue => (.got (s.items.headD 0), { s with items := s.items.tail, served := s.served + 1 })
  else (.rejected, s)

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : step s op = (.rejected, s) := by
  simp [step, h]

theorem step_enqueue {s : State} {x : Nat} (h : s.items.length ≤ s.capacity) :
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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x => rw [step_enqueue h]; simp
  | dequeue =>
    cases hs : s.items with
    | nil => simp [Valid, hs] at h
    | cons x rest => rw [step_dequeue hs]; simp

theorem req_invalid_noop : InvalidNoop step := fun _ _ h => step_invalid h

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  exact step_enqueue (ok_valid h)

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  have hv : Valid s .dequeue := ok_valid h
  cases hs : s.items with
  | nil => simp [Valid, hs] at hv
  | cons x rest => exact ⟨x, rest, rfl, step_dequeue hs⟩

theorem req_capacity : CapacityBound step := by
  intro s op hle
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp only [List.length_append, List.length_singleton]; exact Nat.succ_le_succ hv
    | dequeue =>
      cases hs : s.items with
      | nil => simp [Valid, hs] at hv
      | cons x rest => rw [step_dequeue hs]; simp only; rw [hs] at hle; simp at hle; omega
  · rw [step_invalid hv]; exact Nat.le_succ_of_le hle

/-- One step moves values from the inflow into the queue and from the queue to the outflow. -/
theorem step_flow (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp [inflowOf, outflowOf]
    | dequeue =>
      cases hs : s.items with
      | nil => simp [Valid, hs] at hv
      | cons x rest => rw [step_dequeue hs]; simp [inflowOf, outflowOf]
  · rw [step_invalid hv]; simp [inflowOf, outflowOf]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run, inflow, outflow, List.flatMap_cons] at ih ⊢
    rw [← List.append_assoc, step_flow, List.append_assoc, ih, List.append_assoc]

end BoundedQueue
