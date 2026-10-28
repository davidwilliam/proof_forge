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

theorem req_invalid_noop_aux : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    unfold step
    simp [h]
  | dequeue =>
    simp only [Valid] at h
    cases e : s.items with
    | nil =>
      unfold step
      simp [e]
    | cons x rest =>
      simp [e] at h

theorem req_valid_succeeds_aux : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    simp only [step, h, ↓reduceIte]
    decide
  | dequeue =>
    simp only [Valid] at h
    cases e : s.items with
    | nil => simp [e] at h
    | cons x rest =>
      unfold step
      simp [e]

theorem probe4 : True := by
  have h : CapacityBound step := by
    intro s op hlen
    cases op with
    | enqueue x =>
      unfold step
      by_cases hlt : s.items.length < s.capacity
      · simp [hlt]; omega
      · simp [hlt]; exact hlen
    | dequeue =>
      cases e : s.items with
      | nil =>
        have heq : step s .dequeue = (.rejected, s) := by unfold step; simp [e]
        rw [heq]; exact hlen
      | cons x rest =>
        have heq : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by unfold step; simp [e]
        rw [heq]
        simp
        simp [e] at hlen
        omega
  trivial

theorem req_dequeue_effects_tmp3 : DequeueEffects step := by
  intro s h
  obtain ⟨cap, items, served⟩ := s
  cases e : items with
  | nil =>
    subst e
    simp [step] at h
  | cons x rest =>
    exact ⟨x, rest, rfl, by simp [step]⟩

theorem fifo_single_test : True := trivial

def myTestDef : Nat := 1

theorem fifo_single_step2 : ∀ s op, s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  intro s op
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · simp [inflowOf, outflowOf]
    · simp [inflowOf, outflowOf]
  | dequeue =>
    cases e : s.items with
    | nil =>
      simp [step, e, inflowOf, outflowOf]
    | cons y rest =>
      simp [step, e, inflowOf, outflowOf]

theorem fifo_inflow_cons : ∀ (p : Op × Outcome) (t : List (Op × Outcome)), inflow (p :: t) = inflowOf p ++ inflow t := fun _ _ => rfl

theorem fifo_outflow_cons : ∀ (p : Op × Outcome) (t : List (Op × Outcome)), outflow (p :: t) = outflowOf p ++ outflow t := fun _ _ => rfl

theorem req_fifo_proof2 : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle := fifo_single_step2 s op
    have htail := ih (step s op).2
    have hrun1 : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by
      simp [run]
    have hrun2 : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by
      simp [run]
    rw [hrun1, hrun2]
    simp only [inflow, outflow, List.flatMap_cons]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by rw [hsingle]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by rw [htail]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by rw [← List.append_assoc]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    simp only [step, h, ↓reduceIte]
    decide
  | dequeue =>
    simp only [Valid] at h
    cases e : s.items with
    | nil => simp [e] at h
    | cons x rest =>
      unfold step
      simp [e]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    unfold step
    simp [h]
  | dequeue =>
    simp only [Valid] at h
    cases e : s.items with
    | nil =>
      unfold step
      simp [e]
    | cons x rest =>
      simp [e] at h

theorem req_capacity : CapacityBound step := by
  intro s op hlen
  cases op with
  | enqueue x =>
    unfold step
    by_cases hlt : s.items.length < s.capacity
    · simp [hlt]; omega
    · simp [hlt]; exact hlen
  | dequeue =>
    cases e : s.items with
    | nil =>
      have heq : step s .dequeue = (.rejected, s) := by unfold step; simp [e]
      rw [heq]; exact hlen
    | cons x rest =>
      have heq : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by unfold step; simp [e]
      rw [heq]
      simp
      simp [e] at hlen
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  by_cases hlt : s.items.length < s.capacity
  · simp [hlt]
  · simp [hlt] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  obtain ⟨cap, items, served⟩ := s
  cases e : items with
  | nil =>
    subst e
    simp [step] at h
  | cons x rest =>
    exact ⟨x, rest, rfl, by simp [step]⟩

theorem req_fifo : Fifo step := req_fifo_proof2

end BoundedQueue
