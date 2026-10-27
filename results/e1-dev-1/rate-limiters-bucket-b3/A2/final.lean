import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_time_monotone_aux : TimeMonotone step := by
  unfold TimeMonotone step
  intro s r
  by_cases h : Admissible s r
  · simp [h, h.1]
  · simp [h]

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  unfold step
  simp [h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  unfold AllowIffSufficient
  intro s r hle hpos
  unfold step
  by_cases h : Admissible s r
  · simp [h, h.2.2]
  · simp [h]
    have hc : ¬ r.cost ≤ refilled s r.time := fun hc => h ⟨hle, hpos, hc⟩
    omega

theorem req_time_monotone : TimeMonotone step := by
  unfold TimeMonotone step
  intro s r
  by_cases h : Admissible s r
  · simp [h, h.1]
  · simp [h]

theorem req_remaining : Remaining step := by
  unfold Remaining step
  intro s r h
  by_cases hA : Admissible s r
  · simp [hA, Nat.sub_add_cancel hA.2.2]
  · simp [hA] at h

theorem req_effects : Effects step := by
  unfold Effects step
  intro s r h
  by_cases hA : Admissible s r
  · simp [hA]
  · simp [hA] at h

theorem req_capacity : CapacityBound step := by
  unfold CapacityBound step
  intro s r hcap
  by_cases h : Admissible s r
  · simp only [h, if_true]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp only [h, if_false]
    exact hcap

end TokenBucket
