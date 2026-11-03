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
  cases op with
  | enqueue x =>
    unfold Valid at hValid
    unfold step
    simp [hValid]
  | dequeue =>
    unfold Valid at hValid
    unfold step
    cases h : s.items with
    | nil => simp [h] at hValid
    | cons x rest => simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold Valid at h
    unfold step
    simp [h]
  | dequeue =>
    unfold Valid at h
    unfold step
    cases hitems : s.items with
    | nil => simp [hitems]
    | cons y ys =>
      have hValid : s.items ≠ [] := by simp [hitems]
      exact False.elim (h hValid)

theorem req_capacity : CapacityBound step := by
  intro s op hle
  unfold step
  cases op with
  | enqueue x =>
    simp only
    by_cases hc : s.items.length < s.capacity
    · simp [hc]; omega
    · simp [hc]; exact hle
  | dequeue =>
    simp only
    cases h : s.items with
    | nil => simp [h]
    | cons y ys =>
      simp [h]
      have hlen : (y :: ys).length = ys.length + 1 := by simp
      have hitems_len : s.items.length = (y :: ys).length := by rw [h]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : s.items.length < s.capacity
  · simp [hc]
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases s with
  | mk cap items served =>
    cases items with
    | nil =>
      unfold step at h
      simp at h
    | cons hd tl =>
      simp at h ⊢
      exists hd
      exists tl

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hc : s.items.length < s.capacity
      · have h1 : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1, (run step { s with items := s.items ++ [x] } ops).2) := by
          simp [run, step, hc]
        have h1fst : (run step s (Op.enqueue x :: ops)).1 = (Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1 := by rw [h1]
        have h2snd : (run step s (Op.enqueue x :: ops)).2 = (run step { s with items := s.items ++ [x] } ops).2 := by rw [h1]
        rw [h1fst, h2snd]
        have hexpI : inflow ((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1) = [x] ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [inflow, inflowOf]
        have hexpO : outflow ((Op.enqueue x, Outcome.ok) :: (run step { s with items := s.items ++ [x] } ops).1) = outflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [outflow, outflowOf]
        rw [hexpI, hexpO]
        have ih' := ih { s with items := s.items ++ [x] }
        simp at ih'
        simp [List.append_assoc, ih']
      · have h1 : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, Outcome.rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, step, hc]
        have h1fst : (run step s (Op.enqueue x :: ops)).1 = (Op.enqueue x, Outcome.rejected) :: (run step s ops).1 := by rw [h1]
        have h2snd : (run step s (Op.enqueue x :: ops)).2 = (run step s ops).2 := by rw [h1]
        rw [h1fst, h2snd]
        have hexpI : inflow ((Op.enqueue x, Outcome.rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have hexpO : outflow ((Op.enqueue x, Outcome.rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        rw [hexpI, hexpO]
        exact ih s
    | dequeue =>
      by_cases hnil : s.items = []
      · have h1 : run step s (Op.dequeue :: ops) = ((Op.dequeue, Outcome.rejected) :: (run step s ops).1, (run step s ops).2) := by
          simp [run, step, hnil]
        have h1fst : (run step s (Op.dequeue :: ops)).1 = (Op.dequeue, Outcome.rejected) :: (run step s ops).1 := by rw [h1]
        have h2snd : (run step s (Op.dequeue :: ops)).2 = (run step s ops).2 := by rw [h1]
        rw [h1fst, h2snd]
        have hexpI : inflow ((Op.dequeue, Outcome.rejected) :: (run step s ops).1) = inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have hexpO : outflow ((Op.dequeue, Outcome.rejected) :: (run step s ops).1) = outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        rw [hexpI, hexpO, hnil]
        have ihs := ih s
        rw [hnil] at ihs
        exact ihs
      · have hcons : ∃ y ys, s.items = y :: ys := by
          cases hs : s.items with
          | nil => exact False.elim (hnil hs)
          | cons y ys => exact ⟨y, ys, rfl⟩
        obtain ⟨y, ys, h⟩ := hcons
        have h1 : run step s (Op.dequeue :: ops) = ((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1, (run step { s with items := ys, served := s.served + 1 } ops).2) := by
          simp [run, step, h]
        have h1fst : (run step s (Op.dequeue :: ops)).1 = (Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1 := by rw [h1]
        have h2snd : (run step s (Op.dequeue :: ops)).2 = (run step { s with items := ys, served := s.served + 1 } ops).2 := by rw [h1]
        rw [h1fst, h2snd]
        have hexpI : inflow ((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) = inflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [inflow, inflowOf]
        have hexpO : outflow ((Op.dequeue, Outcome.got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) = [y] ++ outflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [outflow, outflowOf]
        rw [hexpI, hexpO, h]
        have ih' := ih { s with items := ys, served := s.served + 1 }
        simp at ih'
        simp [ih']

end BoundedQueue
