import TokenBucket.Spec
namespace TokenBucket

def step : Impl := fun s r =>
  if s.last ≤ r.time then
    if 0 < r.cost then
      if r.cost ≤ refilled s r.time then
        (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
      else (.rejected, s)
    else (.rejected, s)
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  unfold Admissible at h
  obtain ⟨hle, hpos, hcost⟩ := h
  unfold step
  simp [hle, hpos, hcost]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  unfold Admissible at h
  unfold step
  by_cases hle : s.last ≤ r.time
  · by_cases hpos : 0 < r.cost
    · by_cases hcost : r.cost ≤ refilled s r.time
      · exact absurd ⟨hle, hpos, hcost⟩ h
      · simp [hle, hpos, hcost]
    · simp [hle, hpos]
  · simp [hle]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  unfold AllowIffSufficient
  intro s r hle hpos
  by_cases hcost : r.cost ≤ refilled s r.time
  · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step
      simp [hle, hpos, hcost]
    rw [hstep]
    simp [hcost]
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hle, hpos, hcost]
    rw [hstep]
    simp [hcost]

theorem req_time_monotone : TimeMonotone step := by
  unfold TimeMonotone
  intro s r
  by_cases hle : s.last ≤ r.time
  · by_cases hpos : 0 < r.cost
    · by_cases hcost : r.cost ≤ refilled s r.time
      · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep]
        exact ⟨hle, fun _ => rfl⟩
      · have hstep : step s r = (.rejected, s) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep]
        simp
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [hle, hpos]
      rw [hstep]
      simp
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hle]
    rw [hstep]
    simp

theorem req_remaining : Remaining step := by
  unfold Remaining
  intro s r hok
  by_cases hle : s.last ≤ r.time
  · by_cases hpos : 0 < r.cost
    · by_cases hcost : r.cost ≤ refilled s r.time
      · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep] at hok ⊢
        exact Nat.sub_add_cancel hcost
      · have hstep : step s r = (.rejected, s) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep] at hok
        simp at hok
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [hle, hpos]
      rw [hstep] at hok
      simp at hok
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hle]
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  by_cases hle : s.last ≤ r.time
  · by_cases hpos : 0 < r.cost
    · by_cases hcost : r.cost ≤ refilled s r.time
      · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep] at hok ⊢
        exact ⟨rfl, rfl, rfl, rfl⟩
      · have hstep : step s r = (.rejected, s) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep] at hok
        simp at hok
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [hle, hpos]
      rw [hstep] at hok
      simp at hok
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hle]
    rw [hstep] at hok
    simp at hok

theorem req_capacity : CapacityBound step := by
  unfold CapacityBound
  intro s r hcap
  by_cases hle : s.last ≤ r.time
  · by_cases hpos : 0 < r.cost
    · by_cases hcost : r.cost ≤ refilled s r.time
      · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep]
        exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
      · have hstep : step s r = (.rejected, s) := by
          unfold step
          simp [hle, hpos, hcost]
        rw [hstep]
        exact hcap
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        simp [hle, hpos]
      rw [hstep]
      exact hcap
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hle]
    rw [hstep]
    exact hcap

end TokenBucket
