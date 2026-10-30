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
    simp [step]
    intro heq
    cases s with
    | mk capacity items served =>
      simp at heq
      cases items with
      | nil => simp at h
      | cons y ys => simp at heq

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    simp [step, h]

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    simp only [step]
    by_cases hc : s.items.length < s.capacity
    · simp only [hc, ↓reduceIte]
      simp
      omega
    · simp only [hc, ↓reduceIte]
      exact hle
  | dequeue =>
    cases h : s.items with
    | nil =>
      have : step s .dequeue = (.rejected, s) := by simp [step, h]
      simp [this, hle]
    | cons y ys =>
      have hstep : step s .dequeue = (.got y, { s with items := ys, served := s.served + 1 }) := by simp [step, h]
      simp [hstep]
      have heq : s.items.length = ys.length + 1 := by simp [h]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  simp [step] at h ⊢
  by_cases hc : s.items.length < s.capacity
  · simp [hc]
  · simp [hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases hmem : s.items with
  | nil => simp [step, hmem] at h
  | cons a b =>
    exists a
    exists b
    constructor
    · rfl
    · simp [step, hmem]

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    -- expose s components to avoid s.items vs [] mismatch
    obtain ⟨cap, items, served⟩ := s
    cases op with
    | enqueue x =>
      by_cases hc : items.length < cap
      · have hstep : step ⟨cap, items, served⟩ (Op.enqueue x) = (.ok, { capacity := cap, items := items ++ [x], served := served }) := by
          simp [step, hc]
        have hrun : run step ⟨cap, items, served⟩ (Op.enqueue x :: ops) =
            ((Op.enqueue x, (.ok : Outcome)) :: (run step { capacity := cap, items := items ++ [x], served := served } ops).1,
             (run step { capacity := cap, items := items ++ [x], served := served } ops).2) := by
          simp [run, hstep]
        have h_in_ok : inflowOf (Op.enqueue x, (.ok : Outcome)) = [x] := by simp [inflowOf]
        have h_out_ok : outflowOf (Op.enqueue x, (.ok : Outcome)) = ([] : List Nat) := by simp [outflowOf]
        have ih' := ih (s := { capacity := cap, items := items ++ [x], served := served })
        have h1 : items ++ inflow (run step ⟨cap, items, served⟩ (Op.enqueue x :: ops)).1 =
            items ++ [x] ++ inflow (run step { capacity := cap, items := items ++ [x], served := served } ops).1 := by
          rw [hrun]
          simp [inflow, h_in_ok]
        have h2 : outflow (run step ⟨cap, items, served⟩ (Op.enqueue x :: ops)).1 ++
            (run step ⟨cap, items, served⟩ (Op.enqueue x :: ops)).2.items =
            outflow (run step { capacity := cap, items := items ++ [x], served := served } ops).1 ++
            (run step { capacity := cap, items := items ++ [x], served := served } ops).2.items := by
          rw [hrun]
          simp [outflow, h_out_ok]
        rw [h1, h2]
        have hassoc : items ++ [x] ++ inflow (run step { capacity := cap, items := items ++ [x], served := served } ops).1 =
            (items ++ [x]) ++ inflow (run step { capacity := cap, items := items ++ [x], served := served } ops).1 := by
          simp [List.append_assoc]
        rw [hassoc]
        exact ih'
      · have hstep : step ⟨cap, items, served⟩ (Op.enqueue x) = ((.rejected : Outcome), ⟨cap, items, served⟩) := by
          simp [step, hc]
        have hrun : run step ⟨cap, items, served⟩ (Op.enqueue x :: ops) =
            ((Op.enqueue x, (.rejected : Outcome)) :: (run step ⟨cap, items, served⟩ ops).1,
             (run step ⟨cap, items, served⟩ ops).2) := by
          simp [run, hstep]
        have h_in_rej : inflowOf (Op.enqueue x, (.rejected : Outcome)) = ([] : List Nat) := by simp [inflowOf]
        have h_out_rej : outflowOf (Op.enqueue x, (.rejected : Outcome)) = ([] : List Nat) := by simp [outflowOf]
        have h1 : items ++ inflow (run step ⟨cap, items, served⟩ (Op.enqueue x :: ops)).1 =
            items ++ inflow (run step ⟨cap, items, served⟩ ops).1 := by
          rw [hrun]
          simp [inflow, h_in_rej]
        have h2 : outflow (run step ⟨cap, items, served⟩ (Op.enqueue x :: ops)).1 ++
            (run step ⟨cap, items, served⟩ (Op.enqueue x :: ops)).2.items =
            outflow (run step ⟨cap, items, served⟩ ops).1 ++ (run step ⟨cap, items, served⟩ ops).2.items := by
          rw [hrun]
          simp [outflow, h_out_rej]
        rw [h1, h2]
        exact ih (s := ⟨cap, items, served⟩)
    | dequeue =>
      cases items with
      | nil =>
        have hstep : step ⟨cap, [], served⟩ Op.dequeue = ((.rejected : Outcome), ⟨cap, [], served⟩) := by
          simp [step]
        have hrun : run step ⟨cap, [], served⟩ (Op.dequeue :: ops) =
            ((Op.dequeue, (.rejected : Outcome)) :: (run step ⟨cap, [], served⟩ ops).1,
             (run step ⟨cap, [], served⟩ ops).2) := by
          simp [run, hstep]
        have h_in : inflowOf (Op.dequeue, (.rejected : Outcome)) = ([] : List Nat) := by simp [inflowOf]
        have h_out : outflowOf (Op.dequeue, (.rejected : Outcome)) = ([] : List Nat) := by simp [outflowOf]
        have h1 : ([] : List Nat) ++ inflow (run step ⟨cap, [], served⟩ (Op.dequeue :: ops)).1 =
            ([] : List Nat) ++ inflow (run step ⟨cap, [], served⟩ ops).1 := by
          rw [hrun]
          simp [inflow, h_in]
        have h2 : outflow (run step ⟨cap, [], served⟩ (Op.dequeue :: ops)).1 ++
            (run step ⟨cap, [], served⟩ (Op.dequeue :: ops)).2.items =
            outflow (run step ⟨cap, [], served⟩ ops).1 ++ (run step ⟨cap, [], served⟩ ops).2.items := by
          rw [hrun]
          simp [outflow, h_out]
        rw [h1, h2]
        exact ih (s := ⟨cap, [], served⟩)
      | cons y ys =>
        have hstep : step ⟨cap, y :: ys, served⟩ Op.dequeue =
            ((.got y : Outcome), { capacity := cap, items := ys, served := served + 1 }) := by
          simp [step]
        have hrun : run step ⟨cap, y :: ys, served⟩ (Op.dequeue :: ops) =
            ((Op.dequeue, (.got y : Outcome)) :: (run step { capacity := cap, items := ys, served := served + 1 } ops).1,
             (run step { capacity := cap, items := ys, served := served + 1 } ops).2) := by
          simp [run, hstep]
        have h_in : inflowOf (Op.dequeue, (.got y : Outcome)) = ([] : List Nat) := by simp [inflowOf]
        have h_out : outflowOf (Op.dequeue, (.got y : Outcome)) = [y] := by simp [outflowOf]
        have ih' := ih (s := { capacity := cap, items := ys, served := served + 1 })
        have h1 : (y :: ys) ++ inflow (run step ⟨cap, y :: ys, served⟩ (Op.dequeue :: ops)).1 =
            (y :: ys) ++ inflow (run step { capacity := cap, items := ys, served := served + 1 } ops).1 := by
          rw [hrun]
          simp [inflow, h_in]
        have h2 : outflow (run step ⟨cap, y :: ys, served⟩ (Op.dequeue :: ops)).1 ++
            (run step ⟨cap, y :: ys, served⟩ (Op.dequeue :: ops)).2.items =
            ([y] ++ outflow (run step { capacity := cap, items := ys, served := served + 1 } ops).1) ++
            (run step { capacity := cap, items := ys, served := served + 1 } ops).2.items := by
          rw [hrun]
          simp [outflow, h_out]
        rw [h1, h2]
        have h3 : (y :: ys) ++ inflow (run step { capacity := cap, items := ys, served := served + 1 } ops).1 =
            [y] ++ (ys ++ inflow (run step { capacity := cap, items := ys, served := served + 1 } ops).1) := by
          simp
        rw [h3, ih']
        simp [List.append_assoc]

end BoundedQueue
