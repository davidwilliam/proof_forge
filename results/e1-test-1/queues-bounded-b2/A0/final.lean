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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    have hc : s.items.length < s.capacity := hV
    simp [step, hc]
  | dequeue =>
    have hne : s.items ≠ [] := hV
    cases hm : s.items with
    | nil => exact False.elim (hne hm)
    | cons x rest => simp [step, hm]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hV
  cases op with
  | enqueue x =>
    have hc : ¬ s.items.length < s.capacity := hV
    simp [step, hc]
  | dequeue =>
    cases hm : s.items with
    | nil => simp [step, hm]
    | cons x rest =>
      have hvalid : Valid s Op.dequeue := by simp [Valid, hm]
      exact False.elim (hV hvalid)

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases hc : s.items.length < s.capacity
    · have hstep : step s (Op.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
        simp [step, hc]
      rw [hstep]
      simp only
      have hlen : (s.items ++ [x]).length = s.items.length + 1 := by simp
      omega
    · have hstep : step s (Op.enqueue x) = (.rejected, s) := by
        simp [step, hc]
      rw [hstep]
      simp only
      exact hle
  | dequeue =>
    cases hm : s.items with
    | nil =>
      have hstep : step s Op.dequeue = (.rejected, s) := by
        simp [step, hm]
      rw [hstep]
      simp only
      exact hle
    | cons x rest =>
      have hstep : step s Op.dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
        simp [step, hm]
      rw [hstep]
      simp only
      have heq : s.items.length = rest.length + 1 := by rw [hm]; simp
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases hc : s.items.length < s.capacity
  · simp [step, hc]
  · have hstep : step s (Op.enqueue x) = (.rejected, s) := by
      simp [step, hc]
    rw [hstep] at hne
    exact False.elim (hne rfl)

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  cases hm : s.items with
  | nil =>
    have hstep : step s Op.dequeue = (.rejected, s) := by
      simp [step, hm]
    rw [hstep] at hne
    exact False.elim (hne rfl)
  | cons x rest =>
    exact ⟨x, rest, rfl, by simp [step, hm]⟩

theorem req_fifo : Fifo step := by
  have hsingle : ∀ (s : State) (op : Op),
      s.items ++ inflowOf (op, (step s op).1) =
        outflowOf (op, (step s op).1) ++ (step s op).2.items := by
    intro s op
    cases op with
    | enqueue x =>
      by_cases hc : s.items.length < s.capacity
      · simp [step, hc, inflowOf, outflowOf]
      · simp [step, hc, inflowOf, outflowOf]
    | dequeue =>
      cases hm : s.items with
      | nil =>
        simp [step, hm, inflowOf, outflowOf]
      | cons x rest =>
        simp [step, hm, inflowOf, outflowOf]
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op rest ih =>
    have hs := hsingle s op
    have hi := ih (step s op).2
    have e1 : (run step s (op :: rest)).1 =
        (op, (step s op).1) :: (run step (step s op).2 rest).1 := rfl
    have e2 : (run step s (op :: rest)).2 =
        (run step (step s op).2 rest).2 := rfl
    rw [e1, e2]
    have c1 : inflow ((op, (step s op).1) :: (run step (step s op).2 rest).1) =
        inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1 := by
      simp [inflow]
    have c2 : outflow ((op, (step s op).1) :: (run step (step s op).2 rest).1) =
        outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1 := by
      simp [outflow]
    rw [c1, c2]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 rest).1)
        _ = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 rest).1 := by
          rw [List.append_assoc]
        _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 rest).1 := by
          rw [hs]
        _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 rest).1) := by
          rw [List.append_assoc]
        _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 rest).1 ++ (run step (step s op).2 rest).2.items) := by
          rw [hi]
        _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 rest).1) ++ (run step (step s op).2 rest).2.items := by
          rw [← List.append_assoc]

end BoundedQueue
