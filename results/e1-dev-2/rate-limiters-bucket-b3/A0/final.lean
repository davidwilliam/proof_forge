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
  intro s r h
  unfold step
  simp [h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  simp [h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  have hadm : Admissible s r ↔ r.cost ≤ refilled s r.time := by
    constructor
    · intro h
      exact h.2.2
    · intro h
      exact ⟨hle, hpos, h⟩
  have hstep : ((step s r).1 = .ok ↔ Admissible s r) := by
    constructor
    · intro hok
      by_cases h : Admissible s r
      · exact h
      · have e2 := req_invalid_noop s r h
        have hr : (step s r).1 = .rejected := by rw [e2]
        rw [hr] at hok
        cases hok
    · intro h
      exact req_valid_succeeds s r h
  exact Iff.trans hstep hadm

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have e : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step
      simp [h]
    constructor
    · have hlast : (step s r).2.last = r.time := by rw [e]
      rw [hlast]
      exact h.1
    · intro hok
      have hlast : (step s r).2.last = r.time := by rw [e]
      exact hlast
  · have e2 : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    constructor
    · have h2 : (step s r).2 = s := by rw [e2]
      rw [h2]
      exact Nat.le_refl s.last
    · intro hok
      have hr : (step s r).1 = .rejected := by rw [e2]
      rw [hr] at hok
      cases hok

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · have e : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step
      simp [h]
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := by rw [e]
    rw [htok]
    have hcost : r.cost ≤ refilled s r.time := h.2.2
    omega
  · have e2 : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    have hr : (step s r).1 = .rejected := by rw [e2]
    rw [hr] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · have e : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step
      simp [h]
    rw [e]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have e2 : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    have hr : (step s r).1 = .rejected := by rw [e2]
    rw [hr] at hok
    cases hok

theorem req_capacity : CapacityBound step := by
  intro s r hle
  by_cases h : Admissible s r
  · have e : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step
      simp [h]
    have hcap : (step s r).2.capacity = s.capacity := by rw [e]
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := by rw [e]
    rw [hcap, htok]
    have href : refilled s r.time ≤ s.capacity := by
      unfold refilled
      omega
    omega
  · have e2 : step s r = (.rejected, s) := by
      unfold step
      simp [h]
    have h2 : (step s r).2 = s := by rw [e2]
    rw [h2]
    exact hle

end TokenBucket
