import TokenBucket.Spec
namespace TokenBucket

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else
    (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  unfold InvalidNoop
  intro s r h
  unfold step
  simp [h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  unfold AllowIffSufficient
  intro s r hle hpos
  by_cases h : Admissible s r
  · have hcost : r.cost ≤ refilled s r.time := by
      unfold Admissible at h
      exact h.2.2
    have eok : (step s r).1 = .ok := by
      unfold step
      simp [h]
    simp [eok, hcost]
  · have erej : (step s r).1 = .rejected := by
      unfold step
      simp [h]
    have hncost : ¬ r.cost ≤ refilled s r.time := by
      intro hle2
      apply h
      unfold Admissible
      exact ⟨hle, hpos, hle2⟩
    simp [erej, hncost]

theorem req_time_monotone : TimeMonotone step := by
  unfold TimeMonotone
  intro s r
  by_cases h : Admissible s r
  · have hle : s.last ≤ r.time := by
      unfold Admissible at h
      exact h.1
    have e_last : (step s r).2.last = r.time := by
      unfold step
      simp [h]
    constructor
    · rw [e_last]
      exact hle
    · intro _
      exact e_last
  · have e : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    constructor
    · rw [e]
      exact Nat.le_refl _
    · intro hok
      have hcon : (step s r).1 = .rejected := by
        rw [e]
      rw [hcon] at hok
      simp at hok

theorem req_remaining : Remaining step := by
  unfold Remaining
  intro s r hok
  by_cases h : Admissible s r
  · have hcost : r.cost ≤ refilled s r.time := by
      unfold Admissible at h
      exact h.2.2
    have etok : (step s r).2.tokens = refilled s r.time - r.cost := by
      unfold step
      simp [h]
    rw [etok]
    exact Nat.sub_add_cancel hcost
  · have e : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    unfold step at hok
    simp [h] at hok

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  by_cases h : Admissible s r
  · have e : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step
      simp [h]
    rw [e]
    simp
  · have e : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    unfold step at hok
    simp [h] at hok

theorem req_capacity : CapacityBound step := by
  unfold CapacityBound
  intro s r hcap
  by_cases h : Admissible s r
  · have e1 : (step s r).2.tokens = refilled s r.time - r.cost := by
      unfold step
      simp [h]
    have e2 : (step s r).2.capacity = s.capacity := by
      unfold step
      simp [h]
    rw [e1, e2]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · have e : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    rw [e]
    simpa using hcap

end TokenBucket
