import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have h' : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := h
  unfold step
  simp [h']

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  have h' : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := h
  simp [h']

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  show (step s r).1 = .ok ↔ r.cost ≤ refilled s r.time
  unfold step
  by_cases hc : r.cost ≤ refilled s r.time
  · have hp : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := ⟨hle, hpos, hc⟩
    simp [hp]
  · simp [hc]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos h]
    exact ⟨h.1, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨Nat.le_refl _, fun hc => by simp at hc⟩

theorem req_remaining : Remaining step := by
  intro s r h
  unfold step at h ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos hc] at h ⊢
    simp only at h ⊢
    exact Nat.sub_add_cancel hc.2.2
  · rw [if_neg hc] at h
    simp at h

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos hc] at h ⊢
    simp
  · rw [if_neg hc] at h
    simp at h

theorem req_capacity             : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos h]
    simp only
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · rw [if_neg h]
    simpa using hcap

end TokenBucket
