import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_allow_iff_sufficient_aux2 : AllowIffSufficient step := by
  intro s r hle hpos
  unfold step
  by_cases h : Admissible s r
  · simp [h, h.2.2]
  · simp [h]
    have h2 : ¬ r.cost ≤ refilled s r.time := fun hle2 => h ⟨hle, hpos, hle2⟩
    omega

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
  · simp [h, h.2.2]
  · simp [h]
    have h2 : ¬ r.cost ≤ refilled s r.time := fun hle2 => h ⟨hle, hpos, hle2⟩
    omega

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : Admissible s r
  · simp [h, h.1]
  · simp [h]

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · simp [step, h]
    exact Nat.sub_add_cancel h.2.2
  · simp [step, h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · simp [step, h]
  · simp [step, h] at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : Admissible s r
  · simp [h]
    have hmin : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    omega
  · simp [h, hcap]

end TokenBucket
