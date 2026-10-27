import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if _h : Admissible s r then
    (.ok, { capacity := s.capacity, rate := s.rate, tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_capacity_aux_test : True := trivial

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
  have hiff : Admissible s r ↔ r.cost ≤ refilled s r.time := by
    unfold Admissible
    simp [hle, hpos]
  by_cases h : Admissible s r
  · have hc : r.cost ≤ refilled s r.time := hiff.mp h
    unfold step
    simp [h, hc]
  · have hcost : ¬ r.cost ≤ refilled s r.time := fun hc => h (hiff.mpr hc)
    unfold step
    simp [h, hcost]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : Admissible s r
  · simp [h, h.1]
  · simp [h]

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · have e : step s r = (.ok, { capacity := s.capacity, rate := s.rate, tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step; simp [h]
    have hc : r.cost ≤ refilled s r.time := h.2.2
    have ht : (step s r).2.tokens = refilled s r.time - r.cost := by rw [e]
    rw [ht]
    exact Nat.sub_add_cancel hc
  · have e : step s r = (.rejected, s) := by unfold step; simp [h]
    rw [e] at hok
    simp at hok

theorem req_effects              : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · have e : step s r = (.ok, { capacity := s.capacity, rate := s.rate, tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step; simp [h]
    rw [e]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have e : step s r = (.rejected, s) := by unfold step; simp [h]
    rw [e] at hok
    simp at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : Admissible s r
  · simp only [h, dite_true]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp [h, hcap]

end TokenBucket
