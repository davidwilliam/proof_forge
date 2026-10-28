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

theorem req_valid_succeeds_test : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil => contradiction
    | cons x rest =>
      simp [step, hitems]

theorem req_capacity_aux : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · next h =>
      simp
      omega
    · next h =>
      simpa using hle
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      simp [step, hitems]
    | cons x rest =>
      simp [step, hitems]
      simp [hitems] at hle
      omega

theorem my_deq_lemma2 : DequeueEffects step := by
  intro s h
  cases s with
  | mk cap items served =>
    cases items with
    | nil => simp [step] at h
    | cons x rest => exact ⟨x, rest, rfl, by simp [step]⟩

def myTestFoo : Nat := 1

theorem my_inflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) : inflow (p :: t) = inflowOf p ++ inflow t := by simp [inflow]

theorem my_outflow_cons (p : Op × Outcome) (t : List (Op × Outcome)) : outflow (p :: t) = outflowOf p ++ outflow t := by simp [outflow]

theorem my_single_step (s : State) (op : Op) : s.items ++ inflowOf (op, (step s op).1) = outflowOf (op, (step s op).1) ++ (step s op).2.items := by cases op with | enqueue x => by_cases hc : s.items.length < s.capacity <;> simp [step, hc, inflowOf, outflowOf] | dequeue => cases h : s.items with | nil => simp [step, h, inflowOf, outflowOf] | cons x rest => simp [step, h, inflowOf, outflowOf]

theorem my_run_nil (s : State) : run step s [] = ([], s) := by rfl

theorem my_run_cons_eq (s : State) (op : Op) (ops : List Op) : run step s (op :: ops) = ((op, (step s op).1) :: (run step (step s op).2 ops).1, (run step (step s op).2 ops).2) := by simp [run]

theorem my_run_cons_fst (s : State) (op : Op) (ops : List Op) : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by rfl

theorem my_run_cons_snd (s : State) (op : Op) (ops : List Op) : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    simp [Valid] at h
    cases hitems : s.items with
    | nil => contradiction
    | cons x rest =>
      simp [step, hitems]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    simp [Valid] at h
    simp [step, h]
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      simp [step, hitems]
    | cons x rest =>
      have hv : Valid s .dequeue := by simp [Valid, hitems]
      exact absurd hv h

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    simp only [step]
    split
    · next h =>
      simp
      omega
    · next h =>
      simpa using hle
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      simp [step, hitems]
    | cons x rest =>
      simp [step, hitems]
      simp [hitems] at hle
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x h
  by_cases hc : s.items.length < s.capacity
  · simp [step, hc]
  · simp [step, hc] at h

theorem req_dequeue_effects : DequeueEffects step := by
  intro s h
  cases s with
  | mk cap items served =>
    cases items with
    | nil => simp [step] at h
    | cons x rest => exact ⟨x, rest, rfl, by simp [step]⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil => simp [run, inflow, outflow]
  | cons op ops ih =>
    have hsingle := my_single_step s op
    have hih := ih (step s op).2
    have hfst : (run step s (op :: ops)).1 = (op, (step s op).1) :: (run step (step s op).2 ops).1 := by rfl
    have hsnd : (run step s (op :: ops)).2 = (run step (step s op).2 ops).2 := by rfl
    rw [hfst, hsnd]
    rw [my_inflow_cons, my_outflow_cons]
    rw [← List.append_assoc s.items _ _, hsingle, List.append_assoc, hih, ← List.append_assoc]

end BoundedQueue
