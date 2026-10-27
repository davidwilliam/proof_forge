import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_allow_iff_sufficient_aux3 : AllowIffSufficient step := by
  intro s r hle hpos
  have hiff : Admissible s r ↔ r.cost ≤ refilled s r.time := by
    unfold Admissible
    constructor
    · intro h; exact h.2.2
    · intro h; exact ⟨hle, hpos, h⟩
  by_cases h : Admissible s r
  · have hc : r.cost ≤ refilled s r.time := hiff.mp h
    simp [step, h, hc]
  · have hc : ¬ r.cost ≤ refilled s r.time := fun hh => h (hiff.mpr hh)
    simp [step, h, hc]

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
  have hiff : Admissible s r ↔ r.cost ≤ refilled s r.time := by
    unfold Admissible
    constructor
    · intro h; exact h.2.2
    · intro h; exact ⟨hle, hpos, h⟩
  by_cases h : Admissible s r
  · have hc : r.cost ≤ refilled s r.time := hiff.mp h
    simp [step, h, hc]
  · have hc : ¬ r.cost ≤ refilled s r.time := fun hh => h (hiff.mpr hh)
    simp [step, h, hc]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have hle : s.last ≤ r.time := h.1
    simp [step, h, hle]
  · simp [step, h]

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · have hle : r.cost ≤ refilled s r.time := h.2.2
    have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := by
      simp [hstep]
    rw [htok]
    exact Nat.sub_add_cancel hle
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · simp [step, h]
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [h1] at hok
    simp at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  by_cases h : Admissible s r
  · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := by simp [hstep]
    have hcap2 : (step s r).2.capacity = s.capacity := by simp [hstep]
    rw [htok, hcap2]
    calc refilled s r.time - r.cost ≤ refilled s r.time := Nat.sub_le _ _
      _ ≤ s.capacity := Nat.min_le_left _ _
  · have hstep : step s r = (.rejected, s) := by simp [step, h]
    have htok : (step s r).2.tokens = s.tokens := by simp [hstep]
    have hcap2 : (step s r).2.capacity = s.capacity := by simp [hstep]
    rw [htok, hcap2]
    exact hcap

end TokenBucket
