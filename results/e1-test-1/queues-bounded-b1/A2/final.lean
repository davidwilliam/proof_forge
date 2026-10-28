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

private theorem fifo_single_aux4 (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) =
    outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  cases op with
  | enqueue x =>
    unfold step
    by_cases hlt : s.items.length < s.capacity
    · simp [hlt, inflowOf, outflowOf]
    · simp [hlt, inflowOf, outflowOf]
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have e : step s .dequeue = (.rejected, s) := by unfold step; simp [hitems]
      have h1 : (step s .dequeue).1 = .rejected := by rw [e]
      have h2 : (step s .dequeue).2 = s := by rw [e]
      rw [h1, h2]
      simp [inflowOf, outflowOf, hitems]
    | cons x rest =>
      have e : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
        unfold step; simp [hitems]
      have h1 : (step s .dequeue).1 = .got x := by rw [e]
      have h2 : (step s .dequeue).2.items = rest := by rw [e]
      rw [h1, h2]
      simp [inflowOf, outflowOf]

private theorem inflow_cons_rfl2 (a : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (a :: t) = inflowOf a ++ inflow t := rfl

private theorem outflow_cons_rfl2 (a : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (a :: t) = outflowOf a ++ outflow t := rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    simp only [step, h, ↓reduceIte]
    simp
  | dequeue =>
    simp only [Valid] at h
    cases hitems : s.items with
    | nil => contradiction
    | cons x rest =>
      simp only [step, hitems]
      simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    unfold step
    simp only [h, ↓reduceIte]
  | dequeue =>
    simp only [Valid] at h
    cases hitems : s.items with
    | nil =>
      simp only [step, hitems]
    | cons x rest =>
      rw [hitems] at h
      simp at h

theorem req_capacity : CapacityBound step := by
  intro s op h
  cases op with
  | enqueue x =>
    have h1 : (s.items ++ [x]).length = s.items.length + 1 := by simp
    by_cases hlt : s.items.length < s.capacity
    · have e : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
        unfold step
        simp [hlt]
      rw [e]
      simp only
      omega
    · have e : step s (.enqueue x) = (.rejected, s) := by
        unfold step
        simp [hlt]
      rw [e]
      simp only
      exact h
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have e : step s .dequeue = (.rejected, s) := by
        unfold step
        simp [hitems]
      rw [e]
      simp only
      exact h
    | cons x rest =>
      have e : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
        unfold step
        simp [hitems]
      rw [e]
      simp only
      rw [hitems] at h
      simp at h
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  by_cases hlt : s.items.length < s.capacity
  · simp [hlt]
  · simp [hlt] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases s with
  | mk cap items served =>
    cases items with
    | nil =>
      simp only [step] at h
      simp at h
    | cons x rest =>
      exact ⟨x, rest, rfl, by simp only [step]⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops IH =>
    have hsingle := fifo_single_aux4 s op
    have hIH := IH (step s op).2
    have hrun1 : (run step s (op :: ops)).1 =
        (op, (step s op).1) :: (run step (step s op).2 ops).1 := rfl
    have hrun2 : (run step s (op :: ops)).2 =
        (run step (step s op).2 ops).2 := rfl
    rw [hrun1, hrun2, inflow_cons_rfl2, outflow_cons_rfl2]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by
          rw [hsingle]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by
          rw [hIH]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by
          rw [List.append_assoc]

end BoundedQueue
