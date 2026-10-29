import BoundedQueue.Spec

namespace BoundedQueue

def step : Impl
  | s, .enqueue x =>
    if s.items.length < s.capacity then
      (.ok, { s with items := s.items ++ [x] })
    else
      (.rejected, s)
  | s, .dequeue =>
    match s.items with
    | [] => (.rejected, s)
    | x :: rest => (.got x, { s with items := rest, served := s.served + 1 })

theorem fifo_single_aux : ∀ (s : State) (op : Op),
    s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  intro s op
  cases op with
  | enqueue x =>
    by_cases h : s.items.length < s.capacity
    · simp [step, h, inflowOf, outflowOf]
    · simp [step, h, inflowOf, outflowOf]
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      simp [step, hitems, inflowOf, outflowOf]
    | cons x rest =>
      simp [step, hitems, inflowOf, outflowOf]

theorem run_cons_fst : ∀ (s : State) (op : Op) (ops : List Op),
    (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
  intro s op ops
  simp [run]

theorem run_cons_snd : ∀ (s : State) (op : Op) (ops : List Op),
    (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
  intro s op ops
  simp [run]

#check @fifo_single_aux
#check run
#check inflow
#check outflow

theorem inflow_cons_aux : ∀ (p : Op × Outcome) (t : List (Op × Outcome)),
    inflow (p :: t) = inflowOf p ++ inflow t := by
  intro p t
  simp [inflow]

theorem outflow_cons_aux : ∀ (p : Op × Outcome) (t : List (Op × Outcome)),
    outflow (p :: t) = outflowOf p ++ outflow t := by
  intro p t
  simp [outflow]

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil => contradiction
    | cons x rest =>
      simp [step, hitems]

theorem req_invalid_noop    : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil =>
      simp [step, hitems]
    | cons x rest =>
      simp [hitems] at h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases h : s.items.length < s.capacity
    · have e : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by simp [step, h]
      rw [e]
      simp
      omega
    · have e : step s (.enqueue x) = (.rejected, s) := by simp [step, h]
      rw [e]
      simp
      exact hle
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have e : step s .dequeue = (.rejected, s) := by simp [step, hitems]
      rw [e]
      simp
      exact hle
    | cons x rest =>
      have e : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by simp [step, hitems]
      rw [e]
      simp
      have hlen : (x :: rest).length ≤ s.capacity := by rw [← hitems]; exact hle
      simp at hlen
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases h : s.items.length < s.capacity
  · simp [step, h]
  · simp [step, h] at hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  cases hitems : s.items with
  | nil =>
    simp [step, hitems] at hne
  | cons x rest =>
    exact ⟨x, rest, rfl, by simp [step, hitems]⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have h1 := fifo_single_aux s op
    have h2 := ih (step s op).2
    have hc1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp [run]
    have hc2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp [run]
    rw [hc1, hc2]
    rw [inflow_cons_aux, outflow_cons_aux]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by simp [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by rw [h1]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by simp [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by rw [h2]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by simp [List.append_assoc]

end BoundedQueue
