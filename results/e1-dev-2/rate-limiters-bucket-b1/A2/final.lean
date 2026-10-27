import TokenBucket.Spec
namespace TokenBucket
def step : Impl := fun s r =>
  let level := refilled s r.time
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ level then
    (.ok, { s with tokens := level - r.cost, last := r.time })
  else (.rejected, s)

theorem req_valid_succeeds_test1 : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  unfold step
  simp_all

theorem req_invalid_noop_aux : InvalidNoop step := by
  intro s r h
  unfold Admissible at h
  unfold step
  simp_all

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  unfold step
  simp_all

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold Admissible at h
  unfold step
  simp_all

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  unfold step
  simp only [hle, hpos, true_and]
  by_cases h : r.cost ≤ refilled s r.time <;> simp [h]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [h]
    constructor
    · exact h.1
    · intro _; rfl
  · simp only [h]
    constructor
    · exact Nat.le_refl _
    · intro hok; contradiction

theorem req_remaining : Remaining step := by
  intro s r h
  unfold step at h ⊢
  simp only at h ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [hc] at h ⊢
    simp at ⊢
    omega
  · simp only [hc] at h
    contradiction

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [hc] at h ⊢
    simp at h ⊢
  · simp only [hc] at h
    simp at h

theorem req_capacity : CapacityBound step := by
  intro s r hle
  by_cases hadm : Admissible s r
  · have hok : (step s r).1 = .ok := req_valid_succeeds s r hadm
    obtain ⟨hcap, _, htok, _⟩ := req_effects s r hok
    rw [hcap, htok]
    calc refilled s r.time - r.cost ≤ refilled s r.time := Nat.sub_le _ _
      _ ≤ s.capacity := Nat.min_le_left _ _
  · have hnoop : step s r = (.rejected, s) := req_invalid_noop s r hadm
    rw [hnoop]
    exact hle

end TokenBucket
