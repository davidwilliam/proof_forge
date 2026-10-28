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

theorem fifo_single_aux (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) =
      outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  cases op with
  | enqueue x =>
    unfold step
    by_cases hc : s.items.length < s.capacity
    · simp [hc, inflowOf, outflowOf]
    · simp [hc, inflowOf, outflowOf]
  | dequeue =>
    cases h : s.items with
    | nil =>
      unfold step
      simp [h, inflowOf, outflowOf]
    | cons hd tl =>
      unfold step
      simp [h, inflowOf, outflowOf]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    unfold step
    simp [h]
  | dequeue =>
    simp only [Valid] at h
    obtain ⟨hd, tl, e⟩ : ∃ hd tl, s.items = hd :: tl := by
      cases es : s.items with
      | nil => contradiction
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    unfold step
    simp [e]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    unfold step
    simp only [h, ↓reduceIte]
  | dequeue =>
    simp only [Valid] at h
    cases es : s.items with
    | nil => unfold step; simp [es]
    | cons hd tl =>
      have hne : s.items ≠ [] := by simp [es]
      exact absurd hne h

theorem req_capacity : CapacityBound step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold step
    by_cases hc : s.items.length < s.capacity
    · simp only [hc, ↓reduceIte]
      have hlen : (s.items ++ [x]).length = s.items.length + 1 := by simp
      omega
    · simp only [hc, ↓reduceIte]
      exact h
  | dequeue =>
    unfold step
    cases hitems : s.items with
    | nil => simp_all only
    | cons hd tl =>
      simp only
      have h2 : s.items.length = tl.length + 1 := by simp [hitems]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  by_cases hc : s.items.length < s.capacity
  · simp [hc] at h ⊢
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases hitems : s.items with
  | nil =>
    unfold step at h
    simp [hitems] at h
  | cons x rest =>
    refine ⟨x, rest, rfl, ?_⟩
    unfold step
    simp [hitems]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle := fifo_single_aux s op
    have hih := ih (step s op).2
    have hrun1 : (run step s (op :: ops)).1 =
        (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp only [run]
    have hrun2 : (run step s (op :: ops)).2 =
        (run step (step s op).2 ops).2 := by
      simp only [run]
    rw [hrun1, hrun2]
    simp only [inflow, outflow, List.flatMap_cons]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by
          rw [hsingle]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by
          rw [hih]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by
          rw [List.append_assoc]

end BoundedQueue
