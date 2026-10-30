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
    unfold Valid at hV
    simp [step, hV]
  | dequeue =>
    unfold Valid at hV
    cases h : s.items with
    | nil =>
      simp [h] at hV
    | cons hd tl =>
      simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op hInv
  cases op with
  | enqueue x =>
    unfold Valid at hInv
    simp [step, hInv]
  | dequeue =>
    unfold Valid at hInv
    cases h : s.items with
    | nil =>
      simp [step, h]
    | cons hd tl =>
      exfalso
      apply hInv
      simp [h]

theorem req_capacity : CapacityBound step := by
  intro s op hLe
  cases op with
  | enqueue x =>
    by_cases h : s.items.length < s.capacity
    · simp [step, h]
      have : (s.items ++ [x]).length = s.items.length + 1 := by simp
      omega
    · simp [step, h, hLe]
  | dequeue =>
    cases hItems : s.items with
    | nil =>
      simp [step, hItems, hLe]
    | cons hd tl =>
      simp [step, hItems]
      have h1 : s.items.length = tl.length + 1 := by simp [hItems]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hNe
  by_cases h : s.items.length < s.capacity
  · simp [step, h]
  · simp [step, h] at hNe

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hNe
  cases h : s.items with
  | nil =>
    simp [step, h] at hNe
  | cons hd tl =>
    exact ⟨hd, tl, rfl, by simp [step, h]⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    cases op with
    | enqueue x =>
      by_cases hlt : s.items.length < s.capacity
      · have hStep : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
          simp [step, hlt]
        have hRun : run step s (.enqueue x :: ops) =
            ((.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1,
             (run step { s with items := s.items ++ [x] } ops).2) := by
          have hrw : run step s (.enqueue x :: ops) =
            ((.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1,
             (run step (step s (.enqueue x)).2 ops).2) := rfl
          rw [hStep] at hrw
          exact hrw
        have ih' := ih { s with items := s.items ++ [x] }
        have hInflow : inflow ((.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1) =
            x :: inflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [inflow, inflowOf]
        have hOutflow : outflow ((.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1) =
            outflow (run step { s with items := s.items ++ [x] } ops).1 := by
          simp [outflow, outflowOf]
        calc s.items ++ inflow (run step s (.enqueue x :: ops)).1
            = s.items ++ inflow ((.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1) := by
                rw [hRun]
          _ = s.items ++ (x :: inflow (run step { s with items := s.items ++ [x] } ops).1) := by
                rw [hInflow]
          _ = (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by
                simp
          _ = outflow (run step { s with items := s.items ++ [x] } ops).1 ++ (run step { s with items := s.items ++ [x] } ops).2.items := ih'
          _ = outflow ((.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1) ++ (run step { s with items := s.items ++ [x] } ops).2.items := by
                rw [hOutflow]
          _ = outflow (run step s (.enqueue x :: ops)).1 ++ (run step s (.enqueue x :: ops)).2.items := by
                rw [hRun]
      · have hStep : step s (.enqueue x) = (.rejected, s) := by
          simp [step, hlt]
        have hRun : run step s (.enqueue x :: ops) =
            ((.enqueue x, .rejected) :: (run step s ops).1,
             (run step s ops).2) := by
          have hrw : run step s (.enqueue x :: ops) =
            ((.enqueue x, (step s (.enqueue x)).1) :: (run step (step s (.enqueue x)).2 ops).1,
             (run step (step s (.enqueue x)).2 ops).2) := rfl
          rw [hStep] at hrw
          exact hrw
        have hInflow : inflow ((.enqueue x, .rejected) :: (run step s ops).1) =
            inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have hOutflow : outflow ((.enqueue x, .rejected) :: (run step s ops).1) =
            outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        calc s.items ++ inflow (run step s (.enqueue x :: ops)).1
            = s.items ++ inflow ((.enqueue x, .rejected) :: (run step s ops).1) := by rw [hRun]
          _ = s.items ++ inflow (run step s ops).1 := by rw [hInflow]
          _ = outflow (run step s ops).1 ++ (run step s ops).2.items := ih s
          _ = outflow ((.enqueue x, .rejected) :: (run step s ops).1) ++ (run step s ops).2.items := by rw [hOutflow]
          _ = outflow (run step s (.enqueue x :: ops)).1 ++ (run step s (.enqueue x :: ops)).2.items := by rw [hRun]
    | dequeue =>
      by_cases hNil : s.items = []
      · have hStep : step s .dequeue = (.rejected, s) := by
          simp [step, hNil]
        have hRun : run step s (.dequeue :: ops) =
            ((.dequeue, .rejected) :: (run step s ops).1,
             (run step s ops).2) := by
          have hrw : run step s (.dequeue :: ops) =
            ((.dequeue, (step s .dequeue).1) :: (run step (step s .dequeue).2 ops).1,
             (run step (step s .dequeue).2 ops).2) := rfl
          rw [hStep] at hrw
          exact hrw
        have hInflow : inflow ((.dequeue, .rejected) :: (run step s ops).1) =
            inflow (run step s ops).1 := by
          simp [inflow, inflowOf]
        have hOutflow : outflow ((.dequeue, .rejected) :: (run step s ops).1) =
            outflow (run step s ops).1 := by
          simp [outflow, outflowOf]
        calc s.items ++ inflow (run step s (.dequeue :: ops)).1
            = s.items ++ inflow ((.dequeue, .rejected) :: (run step s ops).1) := by rw [hRun]
          _ = s.items ++ inflow (run step s ops).1 := by rw [hInflow]
          _ = outflow (run step s ops).1 ++ (run step s ops).2.items := ih s
          _ = outflow ((.dequeue, .rejected) :: (run step s ops).1) ++ (run step s ops).2.items := by rw [hOutflow]
          _ = outflow (run step s (.dequeue :: ops)).1 ++ (run step s (.dequeue :: ops)).2.items := by rw [hRun]
      · have hDecomp : ∃ y ys, s.items = y :: ys := by
          cases hc : s.items with
          | nil => exact False.elim (hNil hc)
          | cons y ys => exact ⟨y, ⟨ys, rfl⟩⟩
        obtain ⟨y, ys, hItems⟩ := hDecomp
        have hStep : step s .dequeue = (.got y, { s with items := ys, served := s.served + 1 }) := by
          simp [step, hItems]
        have hRun : run step s (.dequeue :: ops) =
            ((.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1,
             (run step { s with items := ys, served := s.served + 1 } ops).2) := by
          have hrw : run step s (.dequeue :: ops) =
            ((.dequeue, (step s .dequeue).1) :: (run step (step s .dequeue).2 ops).1,
             (run step (step s .dequeue).2 ops).2) := rfl
          rw [hStep] at hrw
          exact hrw
        have ih' := ih { s with items := ys, served := s.served + 1 }
        have hInflow : inflow ((.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) =
            inflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [inflow, inflowOf]
        have hOutflow : outflow ((.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) =
            y :: outflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by
          simp [outflow, outflowOf]
        calc s.items ++ inflow (run step s (.dequeue :: ops)).1
            = (y :: ys) ++ inflow (run step s (.dequeue :: ops)).1 := by rw [hItems]
          _ = (y :: ys) ++ inflow ((.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) := by rw [hRun]
          _ = (y :: ys) ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1 := by rw [hInflow]
          _ = y :: (ys ++ inflow (run step { s with items := ys, served := s.served + 1 } ops).1) := by simp
          _ = y :: (outflow (run step { s with items := ys, served := s.served + 1 } ops).1 ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items) := by
                rw [ih']
          _ = (y :: outflow (run step { s with items := ys, served := s.served + 1 } ops).1) ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items := by simp
          _ = outflow ((.dequeue, .got y) :: (run step { s with items := ys, served := s.served + 1 } ops).1) ++ (run step { s with items := ys, served := s.served + 1 } ops).2.items := by rw [hOutflow]
          _ = outflow (run step s (.dequeue :: ops)).1 ++ (run step s (.dequeue :: ops)).2.items := by rw [hRun]

end BoundedQueue
