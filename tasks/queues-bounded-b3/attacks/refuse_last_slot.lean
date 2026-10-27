import BoundedQueue.Spec
namespace BoundedQueue

instance instDecidableValid (s : State) (op : Op) : Decidable (Valid s op) := by
  cases op <;> unfold Valid <;> infer_instance

def refStep : Impl := fun s op =>
  if Valid s op then
    match op with
    | .enqueue x => (.ok, { s with items := s.items ++ [x] })
    | .dequeue => (.got (s.items.headD 0), { s with items := s.items.tail, served := s.served + 1 })
  else (.rejected, s)

theorem step_invalid {s : State} {op : Op} (h : ¬ Valid s op) : refStep s op = (.rejected, s) := by
  simp [refStep, h]

theorem step_enqueue {s : State} {x : Nat} (h : s.items.length < s.capacity) :
    refStep s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
  have : Valid s (.enqueue x) := h
  simp [refStep, this]

theorem step_dequeue {s : State} {x : Nat} {rest : List Nat} (h : s.items = x :: rest) :
    refStep s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
  have : Valid s .dequeue := by simp [Valid, h]
  simp [refStep, this, h]

theorem ok_valid {s : State} {op : Op} (h : (refStep s op).1 ≠ .rejected) : Valid s op := by
  by_cases hv : Valid s op
  · exact hv
  · rw [step_invalid hv] at h; exact absurd rfl h

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s op h
  cases op with
  | enqueue x => rw [step_enqueue h]; simp
  | dequeue =>
    cases hs : s.items with
    | nil => simp [Valid, hs] at h
    | cons x rest => rw [step_dequeue hs]; simp

theorem ref_req_invalid_noop : InvalidNoop refStep := fun _ _ h => step_invalid h

theorem ref_req_enqueue_effects : EnqueueEffects refStep := by
  intro s x h
  exact step_enqueue (ok_valid h)

theorem ref_req_dequeue_effects : DequeueEffects refStep := by
  intro s h
  have hv : Valid s .dequeue := ok_valid h
  cases hs : s.items with
  | nil => simp [Valid, hs] at hv
  | cons x rest => exact ⟨x, rest, rfl, step_dequeue hs⟩

theorem ref_req_capacity : CapacityBound refStep := by
  intro s op hle
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp only [List.length_append, List.length_singleton]; exact hv
    | dequeue =>
      cases hs : s.items with
      | nil => simp [Valid, hs] at hv
      | cons x rest => rw [step_dequeue hs]; simp only; rw [hs] at hle; simp at hle; omega
  · rw [step_invalid hv]; exact hle

/-- One refStep moves values from the inflow into the queue and from the queue to the outflow. -/
theorem step_flow (s : State) (op : Op) :
    s.items ++ inflowOf (op, (refStep s op).1) = outflowOf (op, (refStep s op).1) ++ (refStep s op).2.items := by
  by_cases hv : Valid s op
  · cases op with
    | enqueue x => rw [step_enqueue hv]; simp [inflowOf, outflowOf]
    | dequeue =>
      cases hs : s.items with
      | nil => simp [Valid, hs] at hv
      | cons x rest => rw [step_dequeue hs]; simp [inflowOf, outflowOf]
  · rw [step_invalid hv]; simp [inflowOf, outflowOf]

theorem ref_req_fifo : Fifo refStep := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run, inflow, outflow, List.flatMap_cons] at ih ⊢
    rw [← List.append_assoc, step_flow, List.append_assoc, ih, List.append_assoc]

theorem fifo_of_flow (st : Impl)
    (h : ∀ s op, s.items ++ inflowOf (op, (st s op).1) = outflowOf (op, (st s op).1) ++ (st s op).2.items) :
    Fifo st := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    simp only [run, inflow, outflow, List.flatMap_cons] at ih ⊢
    rw [← List.append_assoc, h, List.append_assoc, ih, List.append_assoc]
-- Evasive fix: never fill the last free place.
def step : Impl := fun s op =>
  match op with
  | .enqueue x => if s.items.length + 1 = s.capacity then (.rejected, s) else refStep s (.enqueue x)
  | .dequeue => refStep s .dequeue

theorem step_guard {s : State} {x : Nat} (h : s.items.length + 1 = s.capacity) :
    step s (.enqueue x) = (.rejected, s) := by simp [step, h]
theorem step_pass {s : State} {x : Nat} (h : ¬ s.items.length + 1 = s.capacity) :
    step s (.enqueue x) = refStep s (.enqueue x) := by simp [step, h]
theorem step_deq (s : State) : step s .dequeue = refStep s .dequeue := rfl

-- Weakened restatement: success is promised only when the last place is not being filled.
theorem req_valid_succeeds : ∀ s op, Valid s op → s.items.length + 1 ≠ s.capacity →
    (step s op).1 ≠ .rejected := by
  intro s op h hg
  cases op with
  | enqueue x => rw [step_pass hg]; exact ref_req_valid_succeeds s _ h
  | dequeue => rw [step_deq]; exact ref_req_valid_succeeds s _ h
theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    by_cases hg : s.items.length + 1 = s.capacity
    · exact step_guard hg
    · rw [step_pass hg]; exact ref_req_invalid_noop s _ h
  | dequeue => rw [step_deq]; exact ref_req_invalid_noop s _ h
theorem req_capacity : CapacityBound step := by
  intro s op h
  cases op with
  | enqueue x =>
    by_cases hg : s.items.length + 1 = s.capacity
    · rw [step_guard hg]; exact h
    · rw [step_pass hg]; exact ref_req_capacity s _ h
  | dequeue => rw [step_deq]; exact ref_req_capacity s _ h
theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  by_cases hg : s.items.length + 1 = s.capacity
  · rw [step_guard hg] at h; exact absurd rfl h
  · rw [step_pass hg] at h ⊢; exact ref_req_enqueue_effects s x h
theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  rw [step_deq] at h ⊢; exact ref_req_dequeue_effects s h
theorem req_fifo : Fifo step := by
  apply fifo_of_flow
  intro s op
  cases op with
  | enqueue x =>
    by_cases hg : s.items.length + 1 = s.capacity
    · rw [step_guard hg]; simp [inflowOf, outflowOf]
    · rw [step_pass hg]; exact step_flow s _
  | dequeue => rw [step_deq]; exact step_flow s _

end BoundedQueue
