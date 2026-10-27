import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_remaining_aux : Remaining step := by
  unfold Remaining step
  intro s r h
  by_cases hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hcond]
  · simp [hcond] at h

theorem req_effects_aux : Effects step := by
  unfold Effects step
  intro s r h
  by_cases hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hcond]
  · simp [hcond] at h

theorem my_allow_clean : AllowIffSufficient step := by
  unfold AllowIffSufficient step
  intro s r hle hpos
  by_cases h : r.cost ≤ refilled s r.time
  · have hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := ⟨hle, hpos, h⟩
    simp [hcond]
  · simp [h]

theorem my_time_aux : TimeMonotone step := by
  unfold TimeMonotone step
  intro s r
  by_cases hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hcond]
  · simp [hcond]

theorem my_time_final_proof : TimeMonotone step := my_time_aux

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  unfold step
  have hcond : s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time := h
  simp [hcond]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  unfold step
  have hcond : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := by
    intro hc
    apply h
    unfold Admissible
    exact hc
  simp [hcond]

theorem req_allow_iff_sufficient : AllowIffSufficient step := my_allow_clean

theorem req_time_monotone : TimeMonotone step := my_time_aux

theorem req_remaining : Remaining step := req_remaining_aux

theorem req_effects : Effects step := req_effects_aux

theorem req_capacity : CapacityBound step := by
  unfold CapacityBound step
  intro s r hcap
  by_cases hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [hcond]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp [hcond, hcap]

end TokenBucket
