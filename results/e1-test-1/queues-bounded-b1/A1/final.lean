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

theorem testDeq2 : DequeueEffects step := by
  intro s hne
  obtain ⟨cap, items, served⟩ := s
  cases items with
  | nil =>
    simp [step] at hne
  | cons x rest =>
    refine ⟨x, rest, rfl, ?_⟩
    simp [step]

def fooTest123 : Nat := 5

theorem myHelper123 : 1 + 1 = 2 := by rfl

theorem fifo_single_aux456 (s : State) (op : Op) : s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  cases op with
  | enqueue x =>
    simp only [step]
    by_cases hlt : s.items.length < s.capacity
    · simp [hlt, inflowOf, outflowOf]
    · simp [hlt, inflowOf, outflowOf]
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      simp [step, hitems, inflowOf, outflowOf]
    | cons x rest =>
      simp [step, hitems, inflowOf, outflowOf]

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
    simp only [Valid] at h
    have hc : ¬ (s.items.length < s.capacity) := fun hlt => h hlt
    simp [step, hc]
  | dequeue =>
    simp only [Valid] at h
    have hempty : s.items = [] := by
      cases he : s.items with
      | nil => rfl
      | cons x rest => exfalso; apply h; simp [he]
    simp [step, hempty]

theorem req_capacity : CapacityBound step := by
  intro s op h
  cases op with
  | enqueue x =>
    by_cases hlt : s.items.length < s.capacity
    · have e : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
        simp [step, hlt]
      rw [e]
      simp only
      have hlen : (s.items ++ [x]).length = s.items.length + 1 := by simp
      rw [hlen]
      omega
    · have e : step s (.enqueue x) = (.rejected, s) := by
        simp [step, hlt]
      rw [e]
      simp only
      exact h
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have e : step s .dequeue = (.rejected, s) := by simp [step, hitems]
      rw [e]
      simp only
      exact h
    | cons x rest =>
      have e : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
        simp [step, hitems]
      rw [e]
      simp only
      have hlen : s.items.length ≤ s.capacity := h
      rw [hitems] at hlen
      simp at hlen
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  simp only [step] at h ⊢
  by_cases hlt : s.items.length < s.capacity
  · simp [hlt]
  · simp [hlt] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  obtain ⟨cap, items, served⟩ := s
  cases items with
  | nil =>
    simp [step] at hne
  | cons x rest =>
    refine ⟨x, rest, rfl, ?_⟩
    simp [step]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops IH =>
    have hsingle := fifo_single_aux456 s op
    have hIH := IH (s := (step s op).2)
    have hrun1 : (run step s (op :: ops)).1 =
        (op, (step s op).1) :: (run step (step s op).2 ops).1 := rfl
    have hrun2 : (run step s (op :: ops)).2 =
        (run step (step s op).2 ops).2 := rfl
    rw [hrun1, hrun2]
    simp only [inflow, outflow, List.flatMap_cons] at *
    rw [← List.append_assoc s.items _ _, hsingle, List.append_assoc, hIH, List.append_assoc]

end BoundedQueue
