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
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    simp [step, h]
  | dequeue =>
    obtain ⟨cap, items, served⟩ := s
    simp only [Valid] at h
    simp at h
    cases items with
    | nil =>
      simp at h
    | cons y rest =>
      simp [step]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp only [Valid] at h
    simp [step, h]
  | dequeue =>
    obtain ⟨cap, items, served⟩ := s
    simp only [Valid] at h
    cases items with
    | nil =>
      simp [step]
    | cons y rest =>
      simp at h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  obtain ⟨cap, items, served⟩ := s
  cases op with
  | enqueue x =>
    by_cases h : items.length < cap
    · have e : step ⟨cap, items, served⟩ (Op.enqueue x)
          = (.ok, ⟨cap, items ++ [x], served⟩) := by simp [step, h]
      rw [e]
      show (items ++ [x]).length ≤ cap
      have h2 : items.length + 1 ≤ cap := Nat.succ_le_of_lt h
      have h3 : (items ++ [x]).length = items.length + 1 := by simp
      omega
    · have e : step ⟨cap, items, served⟩ (Op.enqueue x)
          = (.rejected, ⟨cap, items, served⟩) := by simp [step, h]
      rw [e]
      exact hle
  | dequeue =>
    cases items with
    | nil =>
      have e : step ⟨cap, [], served⟩ Op.dequeue
          = (.rejected, ⟨cap, [], served⟩) := by simp [step]
      rw [e]
      exact hle
    | cons y rest =>
      have e : step ⟨cap, y :: rest, served⟩ Op.dequeue
          = (.got y, ⟨cap, rest, served + 1⟩) := by simp [step]
      rw [e]
      show rest.length ≤ cap
      have h2 : (y :: rest).length ≤ cap := hle
      simp at h2
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases h : s.items.length < s.capacity
  · simp [step, h]
  · exfalso
    apply hne
    simp [step, h]

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  obtain ⟨cap, items, served⟩ := s
  cases items with
  | nil =>
    exfalso
    apply hne
    simp [step]
  | cons x rest =>
    refine ⟨x, rest, rfl, ?_⟩
    simp [step]

theorem req_fifo : Fifo step := by
  have single : ∀ (s : State) (op : Op),
      s.items ++ inflowOf (op, (step s op).1)
        = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
    intro s op
    cases op with
    | enqueue x =>
      by_cases h : s.items.length < s.capacity
      · have e1 : (step s (.enqueue x)).1 = .ok := by simp [step, h]
        have e2 : (step s (.enqueue x)).2 = { s with items := s.items ++ [x] } := by simp [step, h]
        rw [e1, e2]
        show s.items ++ [x] = _ ++ _
        simp [inflowOf, outflowOf]
      · have e1 : (step s (.enqueue x)).1 = .rejected := by simp [step, h]
        have e2 : (step s (.enqueue x)).2 = s := by simp [step, h]
        rw [e1, e2]
        simp [inflowOf, outflowOf]
    | dequeue =>
      obtain ⟨cap, items, served⟩ := s
      cases items with
      | nil =>
        have e1 : (step ⟨cap, [], served⟩ .dequeue).1 = .rejected := by simp [step]
        have e2 : (step ⟨cap, [], served⟩ .dequeue).2 = ⟨cap, [], served⟩ := by simp [step]
        rw [e1, e2]
        simp [inflowOf, outflowOf]
      | cons y rest =>
        have e1 : (step ⟨cap, y :: rest, served⟩ .dequeue).1 = .got y := by simp [step]
        have e2 : (step ⟨cap, y :: rest, served⟩ .dequeue).2 = ⟨cap, rest, served + 1⟩ := by simp [step]
        rw [e1, e2]
        simp [inflowOf, outflowOf]
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops' ih =>
    have hrun1 : (run step s (op :: ops')).1
        = (op, (step s op).1) :: (run step (step s op).2 ops').1 := rfl
    have hrun2 : (run step s (op :: ops')).2
        = (run step (step s op).2 ops').2 := rfl
    rw [hrun1, hrun2]
    have hi : inflow ((op, (step s op).1) :: (run step (step s op).2 ops').1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops').1 := rfl
    have ho : outflow ((op, (step s op).1) :: (run step (step s op).2 ops').1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops').1 := rfl
    rw [hi, ho]
    have h1 := single s op
    have h2 := ih (step s op).2
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops').1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops').1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops').1 := by
          rw [h1]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops').1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops').1 ++ (run step (step s op).2 ops').2.items) := by
          rw [h2]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops').1) ++ (run step (step s op).2 ops').2.items := by
          rw [List.append_assoc]

end BoundedQueue
