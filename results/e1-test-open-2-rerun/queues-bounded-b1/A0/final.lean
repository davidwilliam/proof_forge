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
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil => simp [hitems] at h
    | cons hd tl => simp [step, hitems]

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
    | cons hd tl => simp [hitems] at h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases h : s.items.length < s.capacity
    · simp [step, h]
      have hle' : s.items.length + 1 ≤ s.capacity := Nat.succ_le_of_lt h
      simpa using hle'
    · simp [step, h]
      exact hle
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      simp [step, hitems]
    | cons hd tl =>
      simp [step, hitems]
      have : tl.length ≤ s.items.length := by simp [hitems]
      exact Nat.le_trans this hle

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  by_cases hh : s.items.length < s.capacity
  · simp [step, hh]
  · simp [step, hh] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases hitems : s.items with
  | nil =>
    simp [step, hitems] at h
  | cons x rest =>
    exact ⟨x, rest, rfl, by simp [step, hitems]⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases h : s.items.length < s.capacity
      · have hr : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1, (run step { s with items := s.items ++ [x] } ops).2) := by
          simp [run, step, h]
        have hinflow : inflow ((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1) = [x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [inflow, inflowOf]
        have houtflow : outflow ((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1) = outflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [outflow, outflowOf]
        have key : s.items ++ inflow (run step s (Op.enqueue x :: ops)).1 = s.items ++ ([x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1) := by
          rw [hr, hinflow]
        have key2 : outflow (run step s (Op.enqueue x :: ops)).1 ++ (run step s (Op.enqueue x :: ops)).2.items = outflow (run step { s with items := s.items ++ [x] } ops).1 ++ (run step { s with items := s.items ++ [x] } ops).2.items := by
          rw [hr, houtflow]
        rw [key, key2]
        have ih' := ih { s with items := s.items ++ [x] }
        have assoc : s.items ++ ([x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1) = (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          rw [List.append_assoc]
        rw [assoc]
        exact ih'
      · have hr : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, step, h]
        have hinflow : inflow ((Op.enqueue x, Outcome.rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have houtflow : outflow ((Op.enqueue x, Outcome.rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        have key : s.items ++ inflow (run step s (Op.enqueue x :: ops)).1 = s.items ++ inflow (run step s ops).1 := by
          rw [hr, hinflow]
        have key2 : outflow (run step s (Op.enqueue x :: ops)).1 ++ (run step s (Op.enqueue x :: ops)).2.items = outflow (run step s ops).1 ++ (run step s ops).2.items := by
          rw [hr, houtflow]
        rw [key, key2]
        exact ih s
    | dequeue =>
      cases hitems : s.items with
      | nil =>
        have hr : run step s (Op.dequeue :: ops) = ((Op.dequeue, .rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, step, hitems]
        have hinflow : inflow ((Op.dequeue, Outcome.rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have houtflow : outflow ((Op.dequeue, Outcome.rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        have ih0 := ih s
        simp [hitems] at ih0
        simp [hr, hinflow, houtflow]
        exact ih0
      | cons y ys =>
        have hr : run step s (Op.dequeue :: ops) = ((Op.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1, (run step { s with items := ys, served := s.served + 1 } ops).2) := by
          simp [run, step, hitems]
        have hinflow : inflow ((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) = inflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [inflow, inflowOf]
        have houtflow : outflow ((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) = y :: outflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [outflow, outflowOf]
        have ih' := ih { s with items := ys, served := s.served + 1 }
        simp [hr, hinflow, houtflow, hitems]
        exact ih'

end BoundedQueue
