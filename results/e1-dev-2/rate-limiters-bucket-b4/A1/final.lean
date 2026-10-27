import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  let level := refilled s r.time
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ level then
    (.ok, { s with tokens := level - r.cost, last := r.time })
  else (.rejected, s)

theorem test_valid : ValidSucceeds step := by
  intro s r h
  obtain ⟨h1,h2,h3⟩ := h
  unfold step
  simp [h1,h2,h3]

theorem req_invalid_noop_aux2 : InvalidNoop step := by
  intro s r h
  unfold step
  simp only
  have h' : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := by
    intro hc
    exact h ⟨hc.1, hc.2.1, hc.2.2⟩
  simp [h']

theorem req_time_monotone_aux : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [h]
  · simp [h]

theorem req_effects_pf : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [h] at hok ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp [h] at hok

theorem req_valid_succeeds       : ValidSucceeds step := by
  intro s r h
  obtain ⟨h1,h2,h3⟩ := h
  unfold step
  simp [h1,h2,h3]

theorem req_invalid_noop : InvalidNoop step := req_invalid_noop_aux2

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  unfold step
  simp only
  by_cases hcost : r.cost ≤ refilled s r.time
  · simp [hle, hpos, hcost]
  · simp [hle, hpos, hcost]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [h]
  · simp [h]

theorem req_remaining : Remaining step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [h] at hok ⊢
  · simp [h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [h] at hok ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp [h] at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [h]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp only [h]
    exact hcap

end TokenBucket
