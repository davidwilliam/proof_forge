import BoundedQueue.Spec

namespace BoundedQueue

def step : Impl := fun s op =>
  match op with
  | .enqueue x => if s.items.length < s.capacity then (.ok, { s with items := s.items ++ [x] }) else (.rejected, s)
  | .dequeue =>
    match s.items with
    | [] => (.rejected, s)
    | y :: rest => (.got y, { s with items := rest, served := s.served + 1 })

theorem req_enqueue_effects_myhelper : EnqueueEffects step := by
  intro s x h
  by_cases hc : s.items.length < s.capacity
  · simp [step, hc]
  · simp [step, hc] at h

theorem req_dequeue_effects_aux2 : DequeueEffects step := by
  intro s h
  cases s with
  | mk cap items served =>
    cases items with
    | nil =>
      simp [step] at h
    | cons y rest =>
      refine ⟨y, rest, rfl, ?_⟩
      simp [step]

theorem inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    inflow (p :: t) = inflowOf p ++ inflow t := by
  simp [inflow]

theorem outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) :
    outflow (p :: t) = outflowOf p ++ outflow t := by
  simp [outflow]

theorem run_cons_eq (s : State) (op : Op) (ops : List Op) :
    run step s (op :: ops) =
      ((op, (step s op).1) :: (run step (step s op).2 ops).1,
       (run step (step s op).2 ops).2) := by
  simp [run]

theorem step_single_fifo_clean (s : State) (op : Op) :
    s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
  cases op with
  | enqueue x =>
    by_cases hc : s.items.length < s.capacity
    · have hstep : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by simp [step, hc]
      rw [hstep]
      simp [inflowOf, outflowOf]
    · have hstep : step s (.enqueue x) = (.rejected, s) := by simp [step, hc]
      rw [hstep]
      simp [inflowOf, outflowOf]
  | dequeue =>
    cases h : s.items with
    | nil =>
      have hstep : step s .dequeue = (.rejected, s) := by simp [step, h]
      rw [hstep]
      simp [inflowOf, outflowOf, h]
    | cons y rest =>
      have hstep : step s .dequeue = (.got y, { s with items := rest, served := s.served + 1 }) := by simp [step, h]
      rw [hstep]
      simp [inflowOf, outflowOf]

theorem req_valid_succeeds  : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil => simp [hitems] at h
    | cons y rest =>
      simp [step, hitems]

theorem req_invalid_noop    : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    simp [step, h]

theorem req_capacity : CapacityBound step := by
  intro s op h
  cases op with
  | enqueue x =>
    unfold step
    simp only
    split
    · next hlt =>
      simp
      have : (s.items ++ [x]).length = s.items.length + 1 := by simp
      omega
    · simp; exact h
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have : (step s .dequeue).2 = s := by simp [step, hitems]
      rw [this]; exact h
    | cons y rest =>
      have hstep : step s .dequeue = (.got y, { s with items := rest, served := s.served + 1 }) := by simp [step, hitems]
      have hlen : (step s .dequeue).2.items.length ≤ (step s .dequeue).2.capacity := by
        rw [hstep]; simp
        have : s.items.length = rest.length + 1 := by rw [hitems]; simp
        omega
      exact hlen

theorem req_enqueue_effects : EnqueueEffects step := req_enqueue_effects_myhelper

theorem req_dequeue_effects : DequeueEffects step := req_dequeue_effects_aux2

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops' ih =>
    have hsingle := step_single_fifo_clean s op
    have hih := ih (step s op).2
    have hrun : run step s (op :: ops') =
      ((op, (step s op).1) :: (run step (step s op).2 ops').1,
       (run step (step s op).2 ops').2) := run_cons_eq s op ops'
    have h1 : (run step s (op :: ops')).1 =
      (op, (step s op).1) :: (run step (step s op).2 ops').1 := by rw [hrun]
    have h2 : (run step s (op :: ops')).2 =
      (run step (step s op).2 ops').2 := by rw [hrun]
    rw [h1, h2]
    rw [inflow_cons, outflow_cons]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops').1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops').1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops').1 := by
          rw [hsingle]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops').1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops').1 ++ (run step (step s op).2 ops').2.items) := by
          rw [hih]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops').1) ++ (run step (step s op).2 ops').2.items := by
          rw [List.append_assoc]

end BoundedQueue
