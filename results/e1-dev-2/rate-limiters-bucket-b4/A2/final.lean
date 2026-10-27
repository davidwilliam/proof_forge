import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  let level := refilled s r.time
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ level then
    (.ok, { s with tokens := level - r.cost, last := r.time })
  else (.rejected, s)

theorem req_valid_succeeds_aux2 : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  show (step s r).1 = .ok
  unfold step
  simp only
  have hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := h
  rw [if_pos hcond]

theorem req_effects_aux_tmp : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  simp only at hok ⊢
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos h] at hok ⊢
    simp at hok ⊢
  · rw [if_neg h] at hok
    simp at hok

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  show (step s r).1 = .ok
  unfold step
  simp only
  have hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := h
  rw [if_pos hcond]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  show step s r = (.rejected, s)
  unfold step
  simp only
  have h' : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := by
    unfold Admissible at h
    exact h
  rw [if_neg h']

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  show ((step s r).1 = .ok ↔ r.cost ≤ refilled s r.time)
  unfold step
  simp only
  by_cases h : r.cost ≤ refilled s r.time
  · have hcond : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := ⟨hle, hpos, h⟩
    rw [if_pos hcond]
    simp [h]
  · have hcond : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := by
      intro ⟨_, _, hle2⟩
      exact h hle2
    rw [if_neg hcond]
    simp [h]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos h]
    exact ⟨h.1, fun _ => rfl⟩
  · rw [if_neg h]
    refine ⟨Nat.le_refl _, fun hok => ?_⟩
    simp at hok

theorem req_remaining : Remaining step := by
  intro s r hok
  unfold step at hok ⊢
  simp only at hok ⊢
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos h] at hok ⊢
    simp at hok ⊢
    omega
  · rw [if_neg h] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  simp only at hok ⊢
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos h] at hok ⊢
    simp at hok ⊢
  · rw [if_neg h] at hok
    simp at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  simp only
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · rw [if_pos h]
    simp only
    have hlev : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    omega
  · rw [if_neg h]
    simp only
    exact hcap

end TokenBucket
