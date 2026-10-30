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
    simp only [Valid] at hV
    simp [step, hV]
  | dequeue =>
    simp only [Valid] at hV
    simp only [step]
    cases h : s.items with
    | nil => simp [h] at hV
    | cons hd tl => simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hV
  cases op with
  | enqueue x =>
    simp only [Valid] at hV
    simp [step, hV]
  | dequeue =>
    simp only [Valid] at hV
    cases h : s.items with
    | nil =>
      simp [step, h]
    | cons hd tl =>
      have hne : s.items ≠ [] := by simp [h]
      exact absurd hne hV

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases hlt : s.items.length < s.capacity
    · simp [step, hlt]
      have h1 : s.items.length + 1 ≤ s.capacity := Nat.succ_le_of_lt hlt
      have h2 : (s.items ++ [x]).length = s.items.length + 1 := by simp
      omega
    · simp [step, hlt, hle]
  | dequeue =>
    match h : s.items with
    | [] => simp [step, h]
    | hd :: tl =>
      simp [step, h]
      have hlen : s.items.length = tl.length + 1 := by simp [h]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  simp only [step] at h ⊢
  by_cases hlt : s.items.length < s.capacity
  · simp [hlt]
  · simp [hlt] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  match hq : s.items with
  | [] =>
    simp [step, hq] at h
  | y :: ys =>
    refine ⟨y, ys, rfl, ?_⟩
    simp [step, hq]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hlt : s.items.length < s.capacity
      · have hs : step s (Op.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
          simp [step, hlt]
        have hrun : run step s (Op.enqueue x :: ops) =
            (((Op.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1),
             (run step { s with items := s.items ++ [x] } ops).2) := by
          simp [run, hs]
        rw [hrun]
        have h_in : inflow (((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1))
            = [x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [inflow, inflowOf]
        have h_out : outflow (((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1))
            = outflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [outflow, outflowOf]
        rw [h_in, h_out]
        have ih' := ih { s with items := s.items ++ [x] }
        simp only at ih' ⊢
        have heq : s.items ++ ([x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1) =
                   (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [List.append_assoc]
        rw [heq, ih']
      · have hs : step s (Op.enqueue x) = (.rejected, s) := by
          simp [step, hlt]
        have hrun : run step s (Op.enqueue x :: ops) =
            (((Op.enqueue x, .rejected) :: (run step s ops).1),
             (run step s ops).2) := by
          simp [run, hs]
        rw [hrun]
        have h_in : inflow (((Op.enqueue x, Outcome.rejected) :: (run step s ops).1))
            = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have h_out : outflow (((Op.enqueue x, Outcome.rejected) :: (run step s ops).1))
            = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        rw [h_in, h_out]
        exact ih s
    | dequeue =>
      cases hitems : s.items with
      | nil =>
        have hs : step s Op.dequeue = (.rejected, s) := by
          simp [step, hitems]
        have hrun : run step s (Op.dequeue :: ops) =
            (((Op.dequeue, .rejected) :: (run step s ops).1),
             (run step s ops).2) := by
          simp [run, hs]
        rw [hrun]
        have h_in : inflow (((Op.dequeue, Outcome.rejected) :: (run step s ops).1))
            = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have h_out : outflow (((Op.dequeue, Outcome.rejected) :: (run step s ops).1))
            = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        rw [h_in, h_out]
        have ih' := ih s
        simp [hitems] at ih' ⊢
        exact ih'
      | cons y ys =>
        have hs : step s Op.dequeue = (.got y, { s with items := ys, served := s.served + 1 }) := by
          simp [step, hitems]
        have hrun : run step s (Op.dequeue :: ops) =
            (((Op.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1),
             (run step { s with items := ys, served := s.served + 1 } ops).2) := by
          simp [run, hs]
        rw [hrun]
        have h_in : inflow (((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1))
            = inflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [inflow, inflowOf]
        have h_out : outflow (((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1))
            = [y] ++ outflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [outflow, outflowOf]
        rw [h_in, h_out]
        have ih' := ih { s with items := ys, served := s.served + 1 }
        simp only at ih' ⊢
        show (y :: ys) ++ inflow (run step { capacity := s.capacity, items := ys, served := s.served + 1 } ops).1 =
             ([y] ++ outflow (run step { capacity := s.capacity, items := ys, served := s.served + 1 } ops).1) ++
             (run step { capacity := s.capacity, items := ys, served := s.served + 1 } ops).2.items
        have heq1 : (y :: ys) ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1 =
                   y :: (ys ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1) := rfl
        have heq2 : ([y] ++ outflow (run step { s with items := ys, served := s.served + 1 } ops).1) ++
                     (run step { s with items := ys, served := s.served + 1 } ops).2.items =
                     y :: (outflow (run step { s with items := ys, served := s.served + 1 } ops).1 ++
                     (run step { s with items := ys, served := s.served + 1 } ops).2.items) := rfl
        rw [heq1, heq2, ih']

end BoundedQueue
