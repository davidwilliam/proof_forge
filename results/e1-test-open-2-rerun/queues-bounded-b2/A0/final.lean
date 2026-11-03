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
    unfold step
    simp [hV]
  | dequeue =>
    unfold Valid at hV
    cases h : s.items with
    | nil => simp [h] at hV
    | cons hd tl =>
      unfold step
      simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hc : ¬ s.items.length < s.capacity := by
      intro hc
      apply h
      exact hc
    unfold step
    simp [hc]
  | dequeue =>
    cases heq : s.items with
    | nil =>
      unfold step
      simp [heq]
    | cons hd tl =>
      have hv : Valid s .dequeue := by simp [Valid, heq]
      exact absurd hv h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases hc : s.items.length < s.capacity
    · have hstep : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by unfold step; simp [hc]
      have : (step s (.enqueue x)).2.items.length ≤ (step s (.enqueue x)).2.capacity := by
        rw [hstep]
        simp
        have : (s.items ++ [x]).length = s.items.length + 1 := by simp
        omega
      exact this
    · have hstep : step s (.enqueue x) = (.rejected, s) := by unfold step; simp [hc]
      rw [hstep]
      exact hle
  | dequeue =>
    cases h : s.items with
    | nil =>
      have hstep : step s .dequeue = (.rejected, s) := by unfold step; simp [h]
      rw [hstep]
      exact hle
    | cons hd tl =>
      have hstep : step s .dequeue = (.got hd, { s with items := tl, served := s.served + 1 }) := by unfold step; simp [h]
      rw [hstep]
      simp
      have hlen : s.items.length = tl.length + 1 := by simp [h]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  by_cases hc : s.items.length < s.capacity
  · unfold step
    simp [hc]
  · exfalso
    apply h
    unfold step
    simp [hc]

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases heq : s.items with
  | nil =>
    unfold step at h
    simp [heq] at h
  | cons hd tl =>
    exact ⟨hd, tl, rfl, by unfold step; simp [heq]⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    rcases s with ⟨cap, items, served⟩
    cases op with
    | enqueue x =>
      by_cases hc : items.length < cap
      · have h1 : (step ⟨cap, items, served⟩ (.enqueue x)).1 = .ok := by unfold step; simp [hc]
        have h2 : (step ⟨cap, items, served⟩ (.enqueue x)).2 = (⟨cap, items ++ [x], served⟩ : State) := by unfold step; simp [hc]
        have hrun : run step ⟨cap, items, served⟩ (.enqueue x :: ops) =
            ((.enqueue x, .ok) :: (run step ⟨cap, items ++ [x], served⟩ ops).1,
             (run step ⟨cap, items ++ [x], served⟩ ops).2) := by
          simp [run, h1, h2]
        rw [hrun]
        have hin_ok : inflowOf (.enqueue x, .ok) = [x] := rfl
        have hout_ok : outflowOf (.enqueue x, .ok) = ([] : List Nat) := rfl
        simp only [inflow, outflow, List.flatMap_cons, hin_ok, hout_ok, List.nil_append]
        have ih' := ih ⟨cap, items ++ [x], served⟩
        simp only at ih'
        calc items ++ ([x] ++ inflow (run step ⟨cap, items ++ [x], served⟩ ops).1)
            = items ++ [x] ++ inflow (run step ⟨cap, items ++ [x], served⟩ ops).1 := by
              rw [List.append_assoc]
          _ = outflow (run step ⟨cap, items ++ [x], served⟩ ops).1 ++ (run step ⟨cap, items ++ [x], served⟩ ops).2.items := ih'
      · have h1 : (step ⟨cap, items, served⟩ (.enqueue x)).1 = .rejected := by unfold step; simp [hc]
        have h2 : (step ⟨cap, items, served⟩ (.enqueue x)).2 = (⟨cap, items, served⟩ : State) := by unfold step; simp [hc]
        have hrun : run step ⟨cap, items, served⟩ (.enqueue x :: ops) =
            ((.enqueue x, .rejected) :: (run step ⟨cap, items, served⟩ ops).1,
             (run step ⟨cap, items, served⟩ ops).2) := by
          simp [run, h1, h2]
        rw [hrun]
        have hin_rej : inflowOf (.enqueue x, .rejected) = ([] : List Nat) := rfl
        have hout_rej : outflowOf (.enqueue x, .rejected) = ([] : List Nat) := rfl
        simp only [inflow, outflow, List.flatMap_cons, hin_rej, hout_rej, List.nil_append]
        exact ih ⟨cap, items, served⟩
    | dequeue =>
      cases items with
      | nil =>
        have h1 : (step ⟨cap, [], served⟩ .dequeue).1 = .rejected := by unfold step; rfl
        have h2 : (step ⟨cap, [], served⟩ .dequeue).2 = (⟨cap, [], served⟩ : State) := by unfold step; rfl
        have hrun : run step ⟨cap, [], served⟩ (.dequeue :: ops) =
            ((.dequeue, .rejected) :: (run step ⟨cap, [], served⟩ ops).1,
             (run step ⟨cap, [], served⟩ ops).2) := by
          simp [run, h1, h2]
        rw [hrun]
        have hin_rej : inflowOf (.dequeue, .rejected) = ([] : List Nat) := rfl
        have hout_rej : outflowOf (.dequeue, .rejected) = ([] : List Nat) := rfl
        simp only [inflow, outflow, List.flatMap_cons, hin_rej, hout_rej, List.nil_append]
        exact ih ⟨cap, [], served⟩
      | cons hd tl =>
        have h1 : (step ⟨cap, hd :: tl, served⟩ .dequeue).1 = .got hd := by unfold step; rfl
        have h2 : (step ⟨cap, hd :: tl, served⟩ .dequeue).2 = (⟨cap, tl, served + 1⟩ : State) := by unfold step; rfl
        have hrun : run step ⟨cap, hd :: tl, served⟩ (.dequeue :: ops) =
            ((.dequeue, .got hd) :: (run step ⟨cap, tl, served + 1⟩ ops).1,
             (run step ⟨cap, tl, served + 1⟩ ops).2) := by
          simp [run, h1, h2]
        rw [hrun]
        have hin_got : inflowOf (.dequeue, .got hd) = ([] : List Nat) := rfl
        have hout_got : outflowOf (.dequeue, .got hd) = [hd] := rfl
        simp only [inflow, outflow, List.flatMap_cons, hin_got, hout_got, List.nil_append]
        have ih' := ih ⟨cap, tl, served + 1⟩
        simp only at ih'
        calc (hd :: tl) ++ inflow (run step ⟨cap, tl, served + 1⟩ ops).1
            = hd :: (tl ++ inflow (run step ⟨cap, tl, served + 1⟩ ops).1) := rfl
          _ = hd :: (outflow (run step ⟨cap, tl, served + 1⟩ ops).1 ++ (run step ⟨cap, tl, served + 1⟩ ops).2.items) := by rw [ih']
          _ = ([hd] ++ outflow (run step ⟨cap, tl, served + 1⟩ ops).1) ++ (run step ⟨cap, tl, served + 1⟩ ops).2.items := rfl

end BoundedQueue
