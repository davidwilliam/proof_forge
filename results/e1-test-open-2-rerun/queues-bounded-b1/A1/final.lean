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
  intro s op hValid
  unfold Valid at hValid
  cases op with
  | enqueue x =>
    unfold step
    simp only [hValid]
    intro h
    contradiction
  | dequeue =>
    unfold step
    cases hItems : s.items with
    | nil =>
      simp [hItems] at hValid
    | cons hd tl =>
      simp only [hItems]
      intro h
      contradiction

theorem req_invalid_noop    : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have h1 : ¬ s.items.length < s.capacity := by
      intro hc
      exact h (show Valid s (Op.enqueue x) from hc)
    simp [step, h1]
  | dequeue =>
    cases hc : s.items with
    | nil =>
      simp [step, hc]
    | cons hd tl =>
      exfalso
      apply h
      unfold Valid
      intro heq
      rw [hc] at heq
      contradiction

theorem req_capacity : CapacityBound step := by
  intro s op hcap
  cases op with
  | enqueue x =>
    unfold step
    by_cases h : s.items.length < s.capacity
    · simp only [h, ↓reduceIte]
      simp
      omega
    · simp only [h, ↓reduceIte]
      exact hcap
  | dequeue =>
    unfold step
    cases hitems : s.items with
    | nil =>
      simp only [hitems] at hcap ⊢
      exact hcap
    | cons hd tl =>
      simp only [hitems]
      have h1 : tl.length + 1 = s.items.length := by rw [hitems]; simp
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  by_cases hc : s.items.length < s.capacity
  · simp only [hc, ↓reduceIte] at h ⊢
  · simp only [hc, ↓reduceIte] at h
    contradiction

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  unfold step at h
  cases hitems : s.items with
  | nil =>
    simp [hitems] at h
  | cons hd tl =>
    refine ⟨hd, tl, rfl, ?_⟩
    unfold step; simp [hitems]

theorem req_fifo : Fifo step := by
  unfold Fifo
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases h : s.items.length < s.capacity
      · have hstep : step s (Op.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by simp [step, h]
        have heq : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1, (run step { s with items := s.items ++ [x] } ops).2) := by simp [run, hstep]
        have h1 : s.items ++ inflow (run step s (Op.enqueue x :: ops)).1 = s.items ++ x :: inflow (run step { s with items := s.items ++ [x] } ops).1 := by rw [heq]; simp [inflow, inflowOf]
        have h2 : outflow (run step s (Op.enqueue x :: ops)).1 ++ (run step s (Op.enqueue x :: ops)).2.items = outflow (run step { s with items := s.items ++ [x] } ops).1 ++ (run step { s with items := s.items ++ [x] } ops).2.items := by rw [heq]; simp [outflow, outflowOf]
        have h3 : s.items ++ x :: inflow (run step { s with items := s.items ++ [x] } ops).1 = (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by simp
        calc s.items ++ inflow (run step s (Op.enqueue x :: ops)).1 = s.items ++ x :: inflow (run step { s with items := s.items ++ [x] } ops).1 := h1
          _ = (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := h3
          _ = outflow (run step { s with items := s.items ++ [x] } ops).1 ++ (run step { s with items := s.items ++ [x] } ops).2.items := ih { s with items := s.items ++ [x] }
          _ = outflow (run step s (Op.enqueue x :: ops)).1 ++ (run step s (Op.enqueue x :: ops)).2.items := h2.symm
      · have hstep : step s (Op.enqueue x) = (.rejected, s) := by simp [step, h]
        have heq : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, Outcome.rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hstep]
        have h1 : s.items ++ inflow (run step s (Op.enqueue x :: ops)).1 = s.items ++ inflow (run step s ops).1 := by rw [heq]; simp [inflow, inflowOf]
        have h2 : outflow (run step s (Op.enqueue x :: ops)).1 ++ (run step s (Op.enqueue x :: ops)).2.items = outflow (run step s ops).1 ++ (run step s ops).2.items := by rw [heq]; simp [outflow, outflowOf]
        calc s.items ++ inflow (run step s (Op.enqueue x :: ops)).1 = s.items ++ inflow (run step s ops).1 := h1
          _ = outflow (run step s ops).1 ++ (run step s ops).2.items := ih s
          _ = outflow (run step s (Op.enqueue x :: ops)).1 ++ (run step s (Op.enqueue x :: ops)).2.items := h2.symm
    | dequeue =>
      cases hitems : s.items with
      | nil =>
        have hstep : step s Op.dequeue = (.rejected, s) := by simp [step, hitems]
        have heq : run step s (Op.dequeue :: ops) = ((Op.dequeue, Outcome.rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hstep]
        have h1 : inflow (run step s (Op.dequeue :: ops)).1 = inflow (run step s ops).1 := by rw [heq]; simp [inflow, inflowOf]
        have h2 : outflow (run step s (Op.dequeue :: ops)).1 ++ (run step s (Op.dequeue :: ops)).2.items = outflow (run step s ops).1 ++ (run step s ops).2.items := by rw [heq]; simp [outflow, outflowOf]
        have ih' : ([] : List Nat) ++ inflow (run step s ops).1 = outflow (run step s ops).1 ++ (run step s ops).2.items := by have := ih s; rw [hitems] at this; exact this
        calc ([] : List Nat) ++ inflow (run step s (Op.dequeue :: ops)).1 = ([] : List Nat) ++ inflow (run step s ops).1 := by rw [h1]
          _ = outflow (run step s ops).1 ++ (run step s ops).2.items := by simp [ih']
          _ = outflow (run step s (Op.dequeue :: ops)).1 ++ (run step s (Op.dequeue :: ops)).2.items := h2.symm
      | cons y ys =>
        have hstep : step s Op.dequeue = (.got y, { s with items := ys, served := s.served + 1 }) := by simp [step, hitems]
        have heq : run step s (Op.dequeue :: ops) = ((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1, (run step { s with items := ys, served := s.served + 1 } ops).2) := by simp [run, hstep]
        have h1 : (y :: ys) ++ inflow (run step s (Op.dequeue :: ops)).1 = y :: (ys ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1) := by rw [heq]; simp [inflow, inflowOf]
        have h2 : outflow (run step s (Op.dequeue :: ops)).1 ++ (run step s (Op.dequeue :: ops)).2.items = y :: (outflow (run step { s with items := ys, served := s.served + 1 } ops).1 ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items) := by rw [heq]; simp [outflow, outflowOf]
        have h3 : ys ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1 = outflow (run step { s with items := ys, served := s.served + 1 } ops).1 ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items := ih { s with items := ys, served := s.served + 1 }
        calc (y :: ys) ++ inflow (run step s (Op.dequeue :: ops)).1 = y :: (ys ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1) := h1
          _ = y :: (outflow (run step { s with items := ys, served := s.served + 1 } ops).1 ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items) := by rw [h3]
          _ = outflow (run step s (Op.dequeue :: ops)).1 ++ (run step s (Op.dequeue :: ops)).2.items := h2.symm

end BoundedQueue
