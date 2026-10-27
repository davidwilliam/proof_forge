import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  let level := refilled s r.time
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ level then
    (.ok, { s with tokens := level - r.cost, last := r.time })
  else (.rejected, s)

theorem req_valid_succeeds_tmp : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold step
  simp only [h1, h2, h3, and_self, reduceIte]

theorem req_time_monotone_aux : TimeMonotone step := by
  intro s r
  unfold step
  simp only
  split
  · next h =>
    obtain ⟨h1, -, -⟩ := h
    exact ⟨h1, fun _ => rfl⟩
  · next h =>
    exact ⟨Nat.le_refl _, fun hok => by contradiction⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold Admissible at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold step
  simp only [h1, h2, h3, and_self, reduceIte]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp only
  have hcond : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := by
    intro hc
    apply h
    unfold Admissible
    exact hc
  simp [hcond]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  unfold step
  simp only
  by_cases h : r.cost ≤ refilled s r.time
  · simp [hle, hpos, h]
  · simp [hle, hpos, h]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  simp only
  split
  · next h =>
    obtain ⟨h1, -, -⟩ := h
    exact ⟨h1, fun _ => rfl⟩
  · next h =>
    exact ⟨Nat.le_refl _, fun hok => by contradiction⟩

theorem req_remaining : Remaining step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [if_pos hc] at hok ⊢
    obtain ⟨-, -, hle⟩ := hc
    -- goal should be (refilled - cost) + cost = refilled
    exact Nat.sub_add_cancel hle
  · simp only [if_neg hc] at hok
    contradiction

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp only [if_pos hc] at hok ⊢
    exact ⟨trivial, trivial, trivial, trivial⟩
  · simp only [if_neg hc] at hok
    contradiction

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  simp only
  split
  · next h =>
    simp only
    have hle : refilled s r.time - r.cost ≤ refilled s r.time := Nat.sub_le _ _
    have hcap2 : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    exact Nat.le_trans hle hcap2
  · next h =>
    simp only
    exact hcap

end TokenBucket
