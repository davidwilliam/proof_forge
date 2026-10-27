import TokenBucket.Spec
/-!
# Reference solution B (hidden from agents)

Staged checks with an explicit clamp instead of `min`, building the next state field by field.
-/

namespace TokenBucket

/-- Refilled level computed with a comparison instead of `min`. -/
def level (s : State) (t : Nat) : Nat :=
  let raw := s.tokens + s.rate * (t - s.last)
  if raw ≤ s.capacity then raw else s.capacity

def step : Impl := fun s r =>
  if r.time < s.last then (.rejected, s)
  else if r.cost = 0 then (.rejected, s)
  else
    let lv := level s r.time
    if r.cost ≤ lv then (.ok, ⟨s.capacity, s.rate, lv - r.cost, r.time⟩)
    else (.rejected, s)

theorem level_eq (s : State) (t : Nat) : level s t = refilled s t := by
  simp only [level, refilled]
  split <;> omega

theorem step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    step s r = (.ok, ⟨s.capacity, s.rate, refilled s r.time - r.cost, r.time⟩) := by
  obtain ⟨h1, h2, h3⟩ := h
  have n1 : ¬ r.time < s.last := by omega
  have n2 : r.cost ≠ 0 := by omega
  simp only [step, n1, n2, level_eq, h3, ite_false, ite_true]

theorem step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by
  unfold Admissible at h
  unfold step
  by_cases h1 : r.time < s.last
  · simp [h1]
  · by_cases h2 : r.cost = 0
    · simp [h2]
    · have h3 : ¬ r.cost ≤ level s r.time := by rw [level_eq]; omega
      simp [h1, h2, h3]

theorem adm_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : Admissible s r := by
  by_cases hv : Admissible s r
  · exact hv
  · rw [step_of_not hv] at h; cases h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_adm h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_not h

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r ht hc
  refine ⟨fun h => (adm_of_ok h).2.2, fun h => ?_⟩
  rw [step_of_adm ⟨ht, hc, h⟩]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases hv : Admissible s r
  · rw [step_of_adm hv]; exact ⟨hv.1, fun _ => rfl⟩
  · rw [step_of_not hv]; exact ⟨Nat.le_refl _, fun h => by cases h⟩

theorem req_remaining : Remaining step := by
  intro s r h
  have hv := adm_of_ok h
  rw [step_of_adm hv]
  have := hv.2.2
  show refilled s r.time - r.cost + r.cost = refilled s r.time
  omega

theorem req_effects : Effects step := by
  intro s r h
  rw [step_of_adm (adm_of_ok h)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem req_capacity : CapacityBound step := by
  intro s r hs
  by_cases hv : Admissible s r
  · rw [step_of_adm hv]
    show refilled s r.time - r.cost ≤ s.capacity
    have : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    omega
  · rw [step_of_not hv]; exact hs

end TokenBucket
