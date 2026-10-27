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
def buggyStep : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if s.items.length < s.capacity then (.ok, { s with items := s.items ++ [x] })
    else (.rejected, s)
  | .dequeue =>
    match s.items.getLast? with
    | none => (.rejected, s)
    | some x => (.got x, { s with items := s.items.dropLast, served := s.served + 1 })

-- Code swap: the proofs are about refStep, the compiled code runs buggyStep.
@[implemented_by buggyStep] def step : Impl := refStep

theorem req_valid_succeeds : ValidSucceeds step := ref_req_valid_succeeds
theorem req_invalid_noop : InvalidNoop step := ref_req_invalid_noop
theorem req_capacity : CapacityBound step := ref_req_capacity
theorem req_enqueue_effects : EnqueueEffects step := ref_req_enqueue_effects
theorem req_dequeue_effects : DequeueEffects step := ref_req_dequeue_effects
theorem req_fifo : Fifo step := ref_req_fifo

end BoundedQueue
