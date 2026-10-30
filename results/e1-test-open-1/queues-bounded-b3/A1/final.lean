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

def dummyHelper : Nat := 42

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    unfold step
    simp [h]
  | dequeue =>
    unfold Valid at h
    unfold step
    revert h
    cases s.items with
    | nil => simp
    | cons y ys => simp

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    unfold step
    simp [h]
  | dequeue =>
    simp [Valid] at h
    unfold step
    simp [h]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    unfold step
    by_cases h : s.items.length < s.capacity
    · simp only [h, ↓reduceIte]
      simp only [List.length_append, List.length_singleton]
      omega
    · simp only [h, ↓reduceIte]
      exact hle
  | dequeue =>
    unfold step
    cases hitems : s.items with
    | nil => exact hle
    | cons y ys =>
      simp only [hitems]
      have heq : (y :: ys).length = ys.length + 1 := by simp
      have hle2 : (y :: ys).length ≤ s.capacity := by rw [← hitems]; exact hle
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : s.items.length < s.capacity
  · simp [hc]
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases s with
  | mk cap items served =>
    cases items with
    | nil =>
      simp [step] at h
    | cons x rest =>
      exact ⟨x, rest, rfl, rfl⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hfst : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by simp [run]
    have hsnd : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by simp [run]
    rw [hfst, hsnd]
    have h1 : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := by
      simp [inflow, List.flatMap_cons]
    have h2 : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1) = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := by
      simp [outflow, List.flatMap_cons]
    rw [h1, h2]
    have hstep : s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
      cases op with
      | enqueue x =>
        unfold step
        by_cases h : s.items.length < s.capacity
        · simp [h, inflowOf, outflowOf]
        · simp [h, inflowOf, outflowOf]
      | dequeue =>
        cases hitems : s.items with
        | nil =>
          have hstep : step s .dequeue = (.rejected, s) := by unfold step; simp [hitems]
          simp [hstep, inflowOf, outflowOf, hitems]
        | cons x rest =>
          have hstep : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by unfold step; simp [hitems]
          simp [hstep, inflowOf, outflowOf]
    have ih' := ih (step s op).2
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by simp [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by rw [hstep]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by simp [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by rw [ih']
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by simp [List.append_assoc]

end BoundedQueue
