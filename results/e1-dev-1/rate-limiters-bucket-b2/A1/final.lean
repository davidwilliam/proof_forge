import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_valid_succeeds_aux : ValidSucceeds step := by
  intro s r h
  have hc : s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time := h
  have hstep : step s r = (.ok, ({ s with tokens := refilled s r.time - r.cost, last := r.time } : State)) := by
    unfold step
    simp [hc]
  rw [hstep]

theorem req_time_monotone_helper_test : True := by trivial
#check @TimeMonotone

theorem req_remaining_test4 : Remaining step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hc, Nat.sub_add_cancel] at hok ⊢
  · simp [hc] at hok

theorem my_cap_lemma_test : True := by trivial
#check (Nat.sub_le : ∀ (n m : Nat), n - m ≤ n)
#check (Nat.min_le_left : ∀ (a b : Nat), min a b ≤ a)

theorem my_cap_final2 : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hc]
    exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _)
  · simp [hc, hcap]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hc : s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time := h
  unfold step
  simp [hc]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold Admissible at h
  unfold step
  simp [h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  unfold step
  by_cases h : r.cost ≤ refilled s r.time
  · simp [hle, hpos, h]
  · simp [hle, hpos, h]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  unfold step
  by_cases h : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) <;> simp [h]

theorem req_remaining : Remaining step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hc, Nat.sub_add_cancel] at hok ⊢
  · simp [hc] at hok

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok ⊢
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hc] at hok ⊢
  · simp [hc] at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · simp [hc]
    exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _)
  · simp [hc, hcap]

end TokenBucket
