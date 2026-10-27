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
  have hstep : ((step s r).1 = .ok) ↔ Admissible s r := by
    unfold step
    by_cases h : Admissible s r <;> simp [h]
  rw [hstep]
  unfold Admissible
  constructor
  · intro hh; exact hh.2.2
  · intro hh; exact ⟨hle, hpos, hh⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  have hstep : ((step s r).1 = .ok) ↔ Admissible s r := by
    unfold step
    by_cases h : Admissible s r <;> simp [h]
  rw [hstep]
  unfold Admissible
  constructor
  · intro hh; exact hh.2.2
  · intro hh; exact ⟨hle, hpos, hh⟩

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have hs : step s r = (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step; simp [h]
    rw [hs]
    obtain ⟨hle, _, _⟩ := h
    exact ⟨hle, fun _ => rfl⟩
  · have hs : step s r = (Outcome.rejected, s) := by
      unfold step; simp [h]
    rw [hs]
    exact ⟨Nat.le_refl _, fun hh => by simp at hh⟩

theorem req_remaining : Remaining step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : Admissible s r
  · simp [h] at hok ⊢
    obtain ⟨hle, hpos, hle2⟩ := h
    have : r.cost ≤ refilled s r.time := hle2
    simp [Nat.sub_add_cancel this]
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : Admissible s r
  · simp [h] at hok ⊢
  · simp [h] at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp [h, hcap]

end TokenBucket
