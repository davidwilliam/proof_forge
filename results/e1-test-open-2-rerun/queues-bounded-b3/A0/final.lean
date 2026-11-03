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
    | x :: rest => (.got x, { s with items := rest, served := s.served + 1 })

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hV
  cases op with
  | enqueue x =>
    unfold Valid at hV
    unfold step
    simp [hV]
  | dequeue =>
    unfold Valid at hV
    unfold step
    cases hs : s.items with
    | nil => simp [hs] at hV
    | cons _ _ => simp [hs]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hN
  cases op with
  | enqueue x =>
    unfold Valid at hN
    unfold step
    simp [hN]
  | dequeue =>
    unfold Valid at hN
    unfold step
    cases hs : s.items with
    | nil => simp [hs]
    | cons _ _ => simp [hs] at hN

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    unfold step
    by_cases hlt : s.items.length < s.capacity
    · simp only [hlt, ↓reduceIte]
      simp
      omega
    · simp only [hlt, ↓reduceIte]
      exact hle
  | dequeue =>
    cases hm : s.items with
    | nil =>
      unfold step
      simp [hm, hle]
    | cons hd tl =>
      unfold step
      simp [hm]
      have hle' : (hd :: tl).length ≤ s.capacity := by rw [← hm]; exact hle
      simp at hle' ⊢
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  by_cases hlt : s.items.length < s.capacity
  · simp [hlt]
  · simp [hlt] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  rcases s with ⟨cap, items, served⟩
  cases items with
  | nil =>
    unfold step at h
    simp at h
  | cons hd tl =>
    exact ⟨hd, tl, rfl, by unfold step; rfl⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hlt : s.items.length < s.capacity
      · have hstep : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
          unfold step; simp [hlt]
        have hrun : run step s (.enqueue x :: ops) = ((.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1, (run step { s with items := s.items ++ [x] } ops).2) := by
          simp [run, hstep]
        have hin : inflow (run step s (.enqueue x :: ops)).1 = x :: inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [hrun, inflow, inflowOf]
        have hout : outflow (run step s (.enqueue x :: ops)).1 = outflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [hrun, outflow, outflowOf]
        have hfinal : (run step s (.enqueue x :: ops)).2 = (run step { s with items := s.items ++ [x] } ops).2 := by
          simp [hrun]
        rw [hin, hout, hfinal]
        have ih' := ih { s with items := s.items ++ [x] }
        have hleft : s.items ++ (x :: inflow (run step { s with items := s.items ++ [x] } ops).1) = (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [List.append_assoc]
        rw [hleft]
        exact ih'
      · have hstep : step s (.enqueue x) = (.rejected, s) := by
          unfold step; simp [hlt]
        have hrun : run step s (.enqueue x :: ops) = ((.enqueue x, .rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, hstep]
        have hin : inflow (run step s (.enqueue x :: ops)).1 = inflow (run step s ops).1 := by
          simp [hrun, inflow, inflowOf]
        have hout : outflow (run step s (.enqueue x :: ops)).1 = outflow (run step s ops).1 := by
          simp [hrun, outflow, outflowOf]
        have hfinal : (run step s (.enqueue x :: ops)).2 = (run step s ops).2 := by
          simp [hrun]
        rw [hin, hout, hfinal]
        exact ih s
    | dequeue =>
      cases hm : s.items with
      | nil =>
        have hstep : step s .dequeue = (.rejected, s) := by unfold step; simp [hm]
        have hrun : run step s (.dequeue :: ops) = ((.dequeue, .rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, hstep]
        have hin : inflow (run step s (.dequeue :: ops)).1 = inflow (run step s ops).1 := by
          simp [hrun, inflow, inflowOf]
        have hout : outflow (run step s (.dequeue :: ops)).1 = outflow (run step s ops).1 := by
          simp [hrun, outflow, outflowOf]
        have hfinal : (run step s (.dequeue :: ops)).2 = (run step s ops).2 := by
          simp [hrun]
        rw [hin, hout, hfinal]
        have ih' := ih s
        simp [hm] at ih' ⊢
        exact ih'
      | cons hd tl =>
        have hstep : step s .dequeue = (.got hd, { s with items := tl, served := s.served + 1 }) := by
          unfold step; simp [hm]
        have hrun : run step s (.dequeue :: ops) = ((.dequeue, .got hd) :: (run step { s with items := tl, served := s.served + 1 } ops).1, (run step { s with items := tl, served := s.served + 1 } ops).2) := by
          simp [run, hstep]
        have hin : inflow (run step s (.dequeue :: ops)).1 = inflow (run step { s with items := tl, served := s.served + 1 } ops).1 := by
          simp [hrun, inflow, inflowOf]
        have hout : outflow (run step s (.dequeue :: ops)).1 = hd :: outflow (run step { s with items := tl, served := s.served + 1 } ops).1 := by
          simp [hrun, outflow, outflowOf]
        have hfinal : (run step s (.dequeue :: ops)).2 = (run step { s with items := tl, served := s.served + 1 } ops).2 := by
          simp [hrun]
        rw [hin, hout, hfinal]
        have ih' := ih { s with items := tl, served := s.served + 1 }
        calc hd :: tl ++ inflow (run step { s with items := tl, served := s.served + 1 } ops).1
            = hd :: (tl ++ inflow (run step { s with items := tl, served := s.served + 1 } ops).1) := rfl
          _ = hd :: (outflow (run step { s with items := tl, served := s.served + 1 } ops).1 ++ (run step { s with items := tl, served := s.served + 1 } ops).2.items) := by
              rw [ih']
          _ = hd :: outflow (run step { s with items := tl, served := s.served + 1 } ops).1 ++ (run step { s with items := tl, served := s.served + 1 } ops).2.items := rfl

end BoundedQueue
