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

theorem req_fifo_aux : ∀ (s : State) (ops : List Op), s.items ++ inflow (run step s ops).1 = outflow (run step s ops).1 ++ (run step s ops).2.items := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops IH =>
    cases op with
    | enqueue x =>
      by_cases hc : s.items.length < s.capacity
      · have hstep : step s (Op.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by unfold step; simp [hc]
        have hrun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .ok) :: (run step { s with items := s.items ++ [x] } ops).1, (run step { s with items := s.items ++ [x] } ops).2) := by simp [run, hstep]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        simp
        calc s.items ++ x :: inflow (run step { s with items := s.items ++ [x] } ops).1
            = (s.items ++ [x]) ++ inflow (run step { s with items := s.items ++ [x] } ops).1 := by simp
          _ = outflow (run step { s with items := s.items ++ [x] } ops).1 ++ (run step { s with items := s.items ++ [x] } ops).2.items := IH { s with items := s.items ++ [x] }
      · have hstep : step s (Op.enqueue x) = (.rejected, s) := by unfold step; simp [hc]
        have hrun : run step s (Op.enqueue x :: ops) = ((Op.enqueue x, .rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hstep]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        simp
        exact IH s
    | dequeue =>
      cases hitems : s.items with
      | nil =>
        have hstep : step s Op.dequeue = (.rejected, s) := by unfold step; simp [hitems]
        have hrun : run step s (Op.dequeue :: ops) = ((Op.dequeue, .rejected) :: (run step s ops).1, (run step s ops).2) := by simp [run, hstep]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        simp
        have ih := IH s
        simp [hitems] at ih ⊢
        exact ih
      | cons y rest =>
        have hstep : step s Op.dequeue = (.got y, { s with items := rest, served := s.served + 1 }) := by unfold step; simp [hitems]
        have hrun : run step s (Op.dequeue :: ops) = ((Op.dequeue, .got y) :: (run step { s with items := rest, served := s.served + 1 } ops).1, (run step { s with items := rest, served := s.served + 1 } ops).2) := by simp [run, hstep]
        rw [hrun]
        simp only [inflow, outflow, List.flatMap_cons, inflowOf, outflowOf]
        simp [hitems]
        exact IH { s with items := rest, served := s.served + 1 }

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  unfold Valid at h
  unfold step
  cases op with
  | enqueue x =>
    simp [h]
  | dequeue =>
    cases hitems : s.items with
    | nil => simp [hitems] at h
    | cons hd tl => simp [hitems]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  unfold Valid at h
  unfold step
  cases op with
  | enqueue x =>
    simp only [decide_eq_true_iff] at *
    -- need to show not Valid => condition false
    have hnot : ¬ (s.items.length < s.capacity) := h
    simp [hnot]
  | dequeue =>
    cases hitems : s.items with
    | nil => simp [hitems]
    | cons hd tl =>
      simp [hitems] at h

theorem req_capacity : CapacityBound step := by
  intro s op hcap
  unfold step
  cases op with
  | enqueue x =>
    simp only
    split
    · simp
      omega
    · simp
      exact hcap
  | dequeue =>
    cases hitems : s.items with
    | nil => simp [hitems, hcap]
    | cons hd tl =>
      simp
      have hlen : s.items.length = tl.length + 1 := by rw [hitems]; simp
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
  have hne : s.items ≠ [] := by
    intro heq
    have : (step s .dequeue).1 = .rejected := by unfold step; simp [heq]
    rw [this] at h
    simp at h
  obtain ⟨x, rest, heq⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨x, rest, heq, ?_⟩
  show step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 })
  unfold step
  rw [heq]

theorem req_fifo : Fifo step := req_fifo_aux

end BoundedQueue
