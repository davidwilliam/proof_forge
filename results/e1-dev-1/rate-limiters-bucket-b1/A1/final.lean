import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if h : Admissible s r then
    (.ok, { capacity := s.capacity, rate := s.rate, tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem my_effects_test : Effects step := by
  intro s r hOk
  unfold step at hOk ⊢
  by_cases hA : Admissible s r
  · simp [hA] at hOk ⊢
  · simp [hA] at hOk

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
  by_cases hA : Admissible s r
  · simp [hA, hA.2.2]
  · simp only [dif_neg hA]
    have hne : ¬ (Outcome.rejected = Outcome.ok) := by simp
    constructor
    · intro h; exfalso; exact hne h
    · intro hle2; exfalso; apply hA; exact ⟨hle, hpos, hle2⟩

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases hA : Admissible s r
  · simp [hA, hA.1]
  · simp [hA]

theorem req_remaining : Remaining step := by
  intro s r hOk
  unfold step at hOk ⊢
  by_cases hA : Admissible s r
  · simp only [dif_pos hA] at hOk ⊢
    exact Nat.sub_add_cancel hA.2.2
  · simp only [dif_neg hA] at hOk
    simp at hOk

theorem req_effects : Effects step := by
  intro s r hOk
  unfold step at hOk ⊢
  by_cases hA : Admissible s r
  · simp [hA] at hOk ⊢
  · simp [hA] at hOk

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases hA : Admissible s r
  · simp only [dif_pos hA]
    show refilled s r.time - r.cost ≤ s.capacity
    calc refilled s r.time - r.cost ≤ refilled s r.time := Nat.sub_le _ _
      _ ≤ s.capacity := Nat.min_le_left _ _
  · simp only [dif_neg hA]
    exact hcap

end TokenBucket
