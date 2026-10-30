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
  intro s op hvalid
  cases op with
  | enqueue x =>
    simp [Valid] at hvalid
    unfold step
    simp [hvalid]
  | dequeue =>
    simp [Valid] at hvalid
    unfold step
    cases h : s.items with
    | nil => contradiction
    | cons hd tl =>
      simp

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
    by_cases hc : s.items.length < s.capacity
    · simp only [hc, ↓reduceIte]
      have h1 : (s.items ++ [x]).length = s.items.length + 1 := by simp
      omega
    · simp only [hc, ↓reduceIte]
      exact hle
  | dequeue =>
    cases h : s.items with
    | nil => unfold step; simp [h]
    | cons hd tl =>
      unfold step; simp [h]
      have hlen : s.items.length = tl.length + 1 := by rw [h]; simp
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  by_cases hc : s.items.length < s.capacity
  · simp [hc]
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  unfold step at h
  cases hitems : s.items with
  | nil =>
    simp [hitems] at h
  | cons x rest =>
    refine ⟨x, rest, rfl, ?_⟩
    unfold step
    simp [hitems]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hc : s.items.length < s.capacity
      · have hstep : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
          unfold step; simp [hc]
        have h_run1 : (run step s (.enqueue x :: ops)).1 = ((.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1) := by
          simp [run, hstep]
        have h_run2 : (run step s (.enqueue x :: ops)).2 = (run step { s with items := s.items ++ [x] } ops).2 := by
          simp [run, hstep]
        have hin : inflow (((.enqueue x : Op), .ok) :: (run step { s with items := s.items ++ [x] } ops).1) = [x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [inflow, inflowOf]
        have hout : outflow (((.enqueue x : Op), .ok) :: (run step { s with items := s.items ++ [x] } ops).1) = outflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [outflow, outflowOf]
        have ih' := ih { s with items := s.items ++ [x] }
        rw [h_run1, h_run2, hin, hout]
        have h_assoc : s.items ++ ([x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1) = (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          rw [List.append_assoc]
        rw [h_assoc]
        exact ih'
      · have hstep : step s (.enqueue x) = (.rejected, s) := by
          unfold step; simp [hc]
        have h_run1 : (run step s (.enqueue x :: ops)).1 = ((.enqueue x, .rejected) :: (run step s ops).1) := by
          simp [run, hstep]
        have h_run2 : (run step s (.enqueue x :: ops)).2 = (run step s ops).2 := by
          simp [run, hstep]
        have hin : inflow (((.enqueue x : Op), .rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have hout : outflow (((.enqueue x : Op), .rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        rw [h_run1, h_run2, hin, hout]
        exact ih s
    | dequeue =>
      by_cases hnil : s.items = []
      · have hstep : step s .dequeue = (.rejected, s) := by
          unfold step; simp [hnil]
        have h_run1 : (run step s (.dequeue :: ops)).1 = ((.dequeue, .rejected) :: (run step s ops).1) := by
          simp [run, hstep]
        have h_run2 : (run step s (.dequeue :: ops)).2 = (run step s ops).2 := by
          simp [run, hstep]
        have hin : inflow (((.dequeue : Op), .rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have hout : outflow (((.dequeue : Op), .rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        rw [h_run1, h_run2, hin, hout]
        exact ih s
      · have hne : s.items ≠ [] := hnil
        obtain ⟨y, ys, hcons⟩ : ∃ y ys, s.items = y :: ys := by
          match hm : s.items with
          | [] => contradiction
          | y :: ys => exact ⟨y, ys, rfl⟩
        have hstep : step s .dequeue = (.got y, { s with items := ys, served := s.served + 1 }) := by
          unfold step; simp [hcons]
        have h_run1 : (run step s (.dequeue :: ops)).1 = ((.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) := by
          simp [run, hstep]
        have h_run2 : (run step s (.dequeue :: ops)).2 = (run step { s with items := ys, served := s.served + 1 } ops).2 := by
          simp [run, hstep]
        have hin : inflow (((.dequeue : Op), .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) = inflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [inflow, inflowOf]
        have hout : outflow (((.dequeue : Op), .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) = [y] ++ outflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [outflow, outflowOf]
        have ih' := ih { s with items := ys, served := s.served + 1 }
        rw [h_run1, h_run2, hin, hout, hcons]
        have h1 : (y :: ys) ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1 = y :: (ys ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1) := rfl
        have h2 : ([y] ++ outflow (run step { s with items := ys, served := s.served + 1 } ops).1) ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items = y :: (outflow (run step { s with items := ys, served := s.served + 1 } ops).1 ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items) := rfl
        rw [h1, h2, ih']

end BoundedQueue
