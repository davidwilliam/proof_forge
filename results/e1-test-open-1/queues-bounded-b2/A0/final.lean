import BoundedQueue.Spec

namespace BoundedQueue

def step : Impl := fun s op =>
  match op with
  | .enqueue x =>
    if s.items.length < s.capacity then
      (.ok, { s with items := s.items ++ [x] })
    else
      (.rejected, s)
  | .dequeue =>
    match s.items with
    | [] => (.rejected, s)
    | y :: ys => (.got y, { s with items := ys, served := s.served + 1 })

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    unfold step
    simp [h]
  | dequeue =>
    simp only [Valid] at h
    cases hitems : s.items with
    | nil =>
      simp [hitems] at h
    | cons y ys =>
      unfold step
      simp [hitems]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    unfold step
    simp [h]
  | dequeue =>
    simp only [Valid] at h
    have hempty : s.items = [] := Classical.byContradiction fun hne => h hne
    cases hitems : s.items with
    | nil =>
      unfold step
      simp [hitems]
    | cons y ys =>
      simp [hitems] at hempty

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    unfold step
    by_cases hc : s.items.length < s.capacity
    · simp only [hc, ↓reduceIte]
      simp
      omega
    · simp only [hc, ↓reduceIte]
      exact hle
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have hstep : step s .dequeue = (Outcome.rejected, s) := by
        unfold step; simp [hitems]
      simp [hstep, hle]
    | cons y ys =>
      have hstep : (step s .dequeue).2 = { s with items := ys, served := s.served + 1 } := by
        unfold step; simp [hitems]
      simp [hstep]
      have hlen : s.items.length = ys.length + 1 := by simp [hitems]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  unfold step at hne
  unfold step
  by_cases hc : s.items.length < s.capacity
  · simp [hc]
  · simp [hc] at hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  cases s with
  | mk cap items served =>
    cases h : items with
    | nil =>
      simp [step, h] at hne
    | cons y ys =>
      exact ⟨y, ys, rfl, by simp [step, h]⟩

private theorem step_fifo_single (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  cases op with
  | enqueue x =>
    unfold step inflowOf outflowOf
    by_cases hc : s.items.length < s.capacity
    · simp [hc]
    · simp [hc]
  | dequeue =>
    cases s with
    | mk cap items served =>
      cases h : items with
      | nil =>
        simp [step, h, inflowOf, outflowOf]
      | cons y ys =>
        simp [step, h, inflowOf, outflowOf]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hrun : run step s (op :: ops) =
        ((op, (step s op).1) :: (run step (step s op).2 ops).1,
         (run step (step s op).2 ops).2) := by
      simp [run]
    have hinflow_cons : ∀ (a : Op × Outcome) (t : List (Op × Outcome)),
        inflow (a :: t) = inflowOf a ++ inflow t := by
      intro a t
      simp [inflow]
    have houtflow_cons : ∀ (a : Op × Outcome) (t : List (Op × Outcome)),
        outflow (a :: t) = outflowOf a ++ outflow t := by
      intro a t
      simp [outflow]
    have h1 := step_fifo_single s op
    have h2 := ih (s := (step s op).2)
    rw [hrun]
    simp only
    rw [hinflow_cons, houtflow_cons]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
          = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
              simp [List.append_assoc]
        _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by
              rw [h1]
        _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by
              simp [List.append_assoc]
        _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by
              rw [h2]
        _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by
              simp [List.append_assoc]

end BoundedQueue
