import BoundedQueue.Spec
namespace BoundedQueue

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if s.items.length < s.capacity then (.ok, { s with items := s.items ++ [x] })
    else (.rejected, s)
  | .dequeue =>
    match s.items with
    | [] => (.rejected, s)
    | x :: rest => (.got x, { s with items := rest, served := s.served + 1 })

theorem my_lem1 : ValidSucceeds step := by
  intro s op h
  cases op
  · rename_i x
    simp [Valid] at h
    simp [step, h]
  · simp [Valid] at h
    cases e : s.items
    · simp [e] at h
    · simp [step, e]

theorem req_capacity_aux : CapacityBound step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · simp; omega
    · simp; exact h
  | dequeue =>
    have he : s.items = ([] : List Nat) ∨ ∃ x rest, s.items = x :: rest := by
      cases s.items with
      | nil => left; rfl
      | cons a b => right; exact ⟨a, b, rfl⟩
    cases he with
    | inl hl =>
      have e : s.items = ([] : List Nat) := hl
      simp [step, e]
    | inr hr =>
      obtain ⟨x, rest, e⟩ := hr
      simp [step, e]
      have h2 : s.items.length ≤ s.capacity := h
      rw [e] at h2
      simp at h2
      omega

def myTestFoo : Nat := 1

theorem myTestBar : 1 = 1 := rfl

theorem fifo_single_thm (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  cases op with
  | enqueue x =>
    by_cases hc : s.items.length < s.capacity
    · simp [step, hc, inflowOf, outflowOf]
    · simp [step, hc, inflowOf, outflowOf]
  | dequeue =>
    cases e : s.items with
    | nil =>
      simp [step, e, inflowOf, outflowOf]
    | cons x rest =>
      simp [step, e, inflowOf, outflowOf]

theorem inflow_cons_thm (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by
  simp [inflow]

theorem fifo_full_thm : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle := fifo_single_thm s op
    have hih := ih (step s op).2
    have hrun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp [run]
    have hrun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp [run]
    rw [hrun1, hrun2]
    have hin : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) =
      inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow]
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) =
      outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow]
    rw [hin, hout]
    rw [← List.append_assoc s.items _ _, hsingle, List.append_assoc, hih, ← List.append_assoc]

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s op h
  cases op
  · rename_i x
    simp [Valid] at h
    simp [step, h]
  · simp [Valid] at h
    cases e : s.items
    · simp [e] at h
    · simp [step, e]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    simp [step, h]

theorem req_capacity : CapacityBound step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · simp; omega
    · simp; exact h
  | dequeue =>
    have he : s.items = ([] : List Nat) ∨ ∃ x rest, s.items = x :: rest := by
      cases s.items with
      | nil => left; rfl
      | cons a b => right; exact ⟨a, b, rfl⟩
    cases he with
    | inl hl =>
      have e : s.items = ([] : List Nat) := hl
      simp [step, e]
    | inr hr =>
      obtain ⟨x, rest, e⟩ := hr
      simp [step, e]
      have h2 : s.items.length ≤ s.capacity := h
      rw [e] at h2
      simp at h2
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hNe
  by_cases hc : s.items.length < s.capacity
  · simp [step, hc]
  · simp [step, hc] at hNe

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hNe
  cases e : s.items with
  | nil =>
    simp [step, e] at hNe
  | cons x rest =>
    exact ⟨x, rest, rfl, by simp [step, e]⟩

theorem req_fifo : Fifo step := fifo_full_thm

end BoundedQueue
