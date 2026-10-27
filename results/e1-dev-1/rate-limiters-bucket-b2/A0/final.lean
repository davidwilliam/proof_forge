import TokenBucket.Spec
namespace TokenBucket

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  have hiff : Admissible s r ↔ r.cost ≤ refilled s r.time := by
    constructor
    · intro h
      exact h.2.2
    · intro h
      exact ⟨hle, hpos, h⟩
  have hstep : (step s r).1 = .ok ↔ Admissible s r := by
    by_cases h : Admissible s r
    · simp [step, h]
    · simp [step, h]
  rw [hstep, hiff]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have hs : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    constructor
    · rw [hs]
      exact h.1
    · intro _
      rw [hs]
  · have hs : step s r = (.rejected, s) := by
      simp [step, h]
    constructor
    · rw [hs]
      exact Nat.le_refl _
    · intro hok
      have h1 : (step s r).1 = .rejected := by
        simp [step, h]
      rw [h1] at hok
      cases hok

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · have hs : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    rw [hs]
    exact Nat.sub_add_cancel h.2.2
  · have h1 : (step s r).1 = .rejected := by
      simp [step, h]
    rw [h1] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · have hs : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    rw [hs]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have h1 : (step s r).1 = .rejected := by
      simp [step, h]
    rw [h1] at hok
    cases hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  by_cases h : Admissible s r
  · have hs : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    rw [hs]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · have hs : step s r = (.rejected, s) := by
      simp [step, h]
    rw [hs]
    exact hcap

end TokenBucket
