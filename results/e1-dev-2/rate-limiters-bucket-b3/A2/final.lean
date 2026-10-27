import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_capacity_aux_test : True := trivial
#check @Nat.sub_le
#check @Nat.min_le_left

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  unfold step
  by_cases h : Admissible s r
  · simp [h]
    unfold Admissible at h
    exact h.2.2
  · simp [h]
    have hc : ¬ r.cost ≤ refilled s r.time := fun hc => h ⟨hle, hpos, hc⟩
    exact Nat.lt_of_not_le hc

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have hle : s.last ≤ r.time := h.1
    unfold step
    simp [h, hle]
  · unfold step
    simp [h]

theorem req_remaining : Remaining step := by
  intro s r hOk
  by_cases h : Admissible s r
  · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step; simp [h]
    rw [hstep]
    simp only
    exact Nat.sub_add_cancel h.2.2
  · have hstep : step s r = (.rejected, s) := by
      unfold step; simp [h]
    rw [hstep] at hOk
    contradiction

theorem req_effects : Effects step := by
  intro s r hOk
  by_cases h : Admissible s r
  · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step; simp [h]
    rw [hstep]
    simp
  · have hstep : step s r = (.rejected, s) := by
      unfold step; simp [h]
    rw [hstep] at hOk
    contradiction

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  by_cases h : Admissible s r
  · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step; simp [h]
    rw [hstep]
    simp only
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · have hstep : step s r = (.rejected, s) := by
      unfold step; simp [h]
    rw [hstep]
    simp only
    exact hcap

end TokenBucket
