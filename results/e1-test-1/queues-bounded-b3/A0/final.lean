import BoundedQueue.Spec
import Init.Data.List.Lemmas
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

private theorem cons_of_ne_nil : ∀ (l : List Nat), l ≠ [] → ∃ x rest, l = x :: rest := by
  intro l h
  cases l with
  | nil => exact False.elim (h rfl)
  | cons x rest => exact ⟨x, rest, rfl⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s op hvalid
  cases op with
  | enqueue x =>
    have hc : s.items.length < s.capacity := hvalid
    simp [step, hc]
  | dequeue =>
    have hne : s.items ≠ [] := hvalid
    obtain ⟨x, rest, heq⟩ := cons_of_ne_nil s.items hne
    simp [step, heq]

theorem req_invalid_noop : InvalidNoop step := by
  intro s op h
  cases op with
  | enqueue x =>
    have hc : ¬ s.items.length < s.capacity := h
    simp [step, hc]
  | dequeue =>
    have hn : ¬ s.items ≠ [] := h
    by_cases hitems : s.items = []
    · simp [step, hitems]
    · exact False.elim (hn hitems)

theorem req_capacity : CapacityBound step := by
  intro s op hle
  cases op with
  | enqueue x =>
    by_cases hc : s.items.length < s.capacity
    · have hst : step s (.enqueue x) = (.ok, { s with items := s.items ++ [x] }) := by
        simp [step, hc]
      rw [hst]
      simp
      omega
    · have hst : step s (.enqueue x) = (.rejected, s) := by
        simp [step, hc]
      rw [hst]
      simpa using hle
  | dequeue =>
    cases hitems : s.items with
    | nil =>
      have hst : step s .dequeue = (.rejected, s) := by simp [step, hitems]
      rw [hst]
      simpa using hle
    | cons x rest =>
      have hst : step s .dequeue = (.got x, { s with items := rest, served := s.served + 1 }) := by
        simp [step, hitems]
      rw [hst]
      simp
      have hlen : s.items.length = rest.length + 1 := by simp [hitems]
      omega

theorem req_enqueue_effects : EnqueueEffects step := by
  intro s x hne
  by_cases hc : s.items.length < s.capacity
  · simp [step, hc]
  · have hrej : (step s (.enqueue x)).1 = .rejected := by simp [step, hc]
    exact absurd hrej hne

theorem req_dequeue_effects : DequeueEffects step := by
  intro s hne
  have hnnil : s.items ≠ [] := by
    intro hcon
    apply hne
    simp [step, hcon]
  obtain ⟨x, rest, hitems⟩ := cons_of_ne_nil s.items hnnil
  exact ⟨x, rest, hitems, by simp [step, hitems]⟩

theorem req_fifo : Fifo step := by
  intro s ops
  induction ops generalizing s with
  | nil =>
    simp [run, inflow, outflow]
  | cons op ops ih =>
    have hstep : s.items ++ inflowOf (op, (step s op).1)
        = outflowOf (op, (step s op).1) ++ (step s op).2.items := by
      cases op with
      | enqueue x =>
        by_cases hc : s.items.length < s.capacity
        · have h1 : (step s (.enqueue x)).1 = .ok := by simp [step, hc]
          have h2 : (step s (.enqueue x)).2 = { s with items := s.items ++ [x] } := by simp [step, hc]
          rw [h1, h2]
          have hi : inflowOf ((.enqueue x), (.ok : Outcome)) = [x] := rfl
          have ho : outflowOf ((.enqueue x), (.ok : Outcome)) = ([] : List Nat) := rfl
          rw [hi, ho]
          simp
        · have h1 : (step s (.enqueue x)).1 = .rejected := by simp [step, hc]
          have h2 : (step s (.enqueue x)).2 = s := by simp [step, hc]
          rw [h1, h2]
          have hi : inflowOf ((.enqueue x), (.rejected : Outcome)) = ([] : List Nat) := rfl
          have ho : outflowOf ((.enqueue x), (.rejected : Outcome)) = ([] : List Nat) := rfl
          rw [hi, ho]
          simp
      | dequeue =>
        cases hitems : s.items with
        | nil =>
          have h1 : (step s .dequeue).1 = .rejected := by simp [step, hitems]
          have h2 : (step s .dequeue).2 = s := by simp [step, hitems]
          rw [h1, h2]
          have hi : inflowOf ((.dequeue : Op), (.rejected : Outcome)) = ([] : List Nat) := rfl
          have ho : outflowOf ((.dequeue : Op), (.rejected : Outcome)) = ([] : List Nat) := rfl
          rw [hi, ho]
          simp [hitems]
        | cons x rest =>
          have h1 : (step s .dequeue).1 = (.got x) := by simp [step, hitems]
          have h2 : (step s .dequeue).2 = { s with items := rest, served := s.served + 1 } := by simp [step, hitems]
          rw [h1, h2]
          have hi : inflowOf ((.dequeue : Op), (Outcome.got x)) = ([] : List Nat) := rfl
          have ho : outflowOf ((.dequeue : Op), (Outcome.got x)) = [x] := rfl
          rw [hi, ho]
          simp [hitems]
    have htail := ih ((step s op).2)
    have hrun1 : (run step s (op :: ops)).1
        = (op, (step s op).1) :: (run step (step s op).2 ops).1 := rfl
    have hrun2 : (run step s (op :: ops)).2
        = (run step (step s op).2 ops).2 := rfl
    have hin : inflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1 := rfl
    have hout : outflow ((op, (step s op).1) :: (run step (step s op).2 ops).1)
        = outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1 := rfl
    rw [hrun1, hrun2, hin, hout]
    calc s.items ++ (inflowOf (op, (step s op).1) ++ inflow (run step (step s op).2 ops).1)
        = (s.items ++ inflowOf (op, (step s op).1)) ++ inflow (run step (step s op).2 ops).1 := by
          rw [List.append_assoc]
      _ = (outflowOf (op, (step s op).1) ++ (step s op).2.items) ++ inflow (run step (step s op).2 ops).1 := by
          rw [hstep]
      _ = outflowOf (op, (step s op).1) ++ ((step s op).2.items ++ inflow (run step (step s op).2 ops).1) := by
          rw [List.append_assoc]
      _ = outflowOf (op, (step s op).1) ++ (outflow (run step (step s op).2 ops).1 ++ (run step (step s op).2 ops).2.items) := by
          rw [htail]
      _ = (outflowOf (op, (step s op).1) ++ outflow (run step (step s op).2 ops).1) ++ (run step (step s op).2 ops).2.items := by
          rw [← List.append_assoc]

end BoundedQueue
