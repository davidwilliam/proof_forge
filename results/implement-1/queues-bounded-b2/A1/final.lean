import BoundedQueue.Spec

namespace BoundedQueue

def step : Impl := fun s op =>
  match op with
  | .enqueue x => if s.items.length < s.capacity then (.ok, { s with items := s.items ++ [x] }) else (.rejected, s)
  | .dequeue =>
    match s.items with
    | [] => (.rejected, s)
    | x :: rest => (.got x, { s with items := rest, served := s.served + 1 })

theorem aux_single_fifo (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  cases op with
  | enqueue x =>
    by_cases h : s.items.length < s.capacity
    · simp [step, h, inflowOf, outflowOf]
    · simp [step, h, inflowOf, outflowOf]
  | dequeue =>
    cases h : s.items with
    | nil =>
      simp [step, h, inflowOf, outflowOf]
    | cons x rest =>
      simp [step, h, inflowOf, outflowOf]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil => simp [hitems] at h
    | cons x rest =>
      simp [step, hitems]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil => simp [step, hitems]
    | cons x rest =>
      simp [hitems] at h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases h : s.items.length < s.capacity
    · simp only [step, h, ↓reduceIte]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · simp only [step, h, ↓reduceIte]
      exact hle
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have hstep : step s .dequeue = (.rejected, s) := by simp [step, hitems]
      rw [hstep]
      exact hle
    | cons x rest =>
      have hstep : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by simp [step, hitems]
      rw [hstep]
      simp only
      have hlen : s.items.length = rest.length + 1 := by rw [hitems]; simp
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  simp only [step] at hne ⊢
  by_cases h : s.items.length < s.capacity
  · simp [h]
  · simp [h] at hne

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
    have hsingle : s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items :=
      aux_single_fifo s op
    have hih : (step s op).2.items ++ inflow (run step (step s op).2 ops).1 =
        outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items :=
      ih (step s op).2
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
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        _ = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
          rw [← List.append_assoc]
        _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by
          rw [hsingle]
        _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by
          rw [List.append_assoc]
        _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by
          rw [hih]
        _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by
          rw [← List.append_assoc]

end BoundedQueue
