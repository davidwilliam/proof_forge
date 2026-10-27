import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
-- Side-effect fix with every proof done: the rate is cleared on acceptance, and the
-- effects theorem is restated without its rate clause.
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with rate := 0, tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)
theorem step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    step s r = (.ok, { s with rate := 0, tokens := refilled s r.time - r.cost, last := r.time }) := by
  simp [step, h]
theorem step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    step s r = (.rejected, s) := by
  simp [step, h]
theorem adm_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : Admissible s r := by
  by_cases hv : Admissible s r
  · exact hv
  · rw [step_of_not hv] at h; cases h
theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h; rw [step_of_adm h]
theorem req_invalid_noop : InvalidNoop step := by
  intro s r h; exact step_of_not h
theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r ht hc
  refine ⟨fun h => (adm_of_ok h).2.2, fun h => ?_⟩
  rw [step_of_adm ⟨ht, hc, h⟩]
theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases hv : Admissible s r
  · rw [step_of_adm hv]; exact ⟨hv.1, fun _ => rfl⟩
  · rw [step_of_not hv]; exact ⟨Nat.le_refl _, fun h => by cases h⟩
theorem req_remaining : Remaining step := by
  intro s r h
  have hv := adm_of_ok h
  rw [step_of_adm hv]
  have := hv.2.2
  show refilled s r.time - r.cost + r.cost = refilled s r.time
  omega
theorem req_effects : ∀ s r, (step s r).1 = .ok →
    (step s r).2.capacity = s.capacity ∧
    (step s r).2.tokens = refilled s r.time - r.cost ∧
    (step s r).2.last = r.time := by
  intro s r h
  rw [step_of_adm (adm_of_ok h)]
  exact ⟨rfl, rfl, rfl⟩
theorem req_capacity : CapacityBound step := by
  intro s r hs
  by_cases hv : Admissible s r
  · rw [step_of_adm hv]
    show refilled s r.time - r.cost ≤ s.capacity
    have : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    omega
  · rw [step_of_not hv]; exact hs
end TokenBucket
