import TokenBucket.Spec
namespace TokenBucket

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { capacity := s.capacity, rate := s.rate, tokens := refilled s r.time - r.cost, last := r.time })
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
  constructor
  · intro hok
    by_cases hc : r.cost ≤ refilled s r.time
    · exact hc
    · have hna : ¬ Admissible s r := by
        unfold Admissible
        intro hcon
        exact hc hcon.2.2
      have hstep := req_invalid_noop s r hna
      have hfst : (step s r).1 = .rejected := by rw [hstep]
      rw [hfst] at hok
      cases hok
  · intro hle2
    have hadm : Admissible s r := by
      unfold Admissible
      exact ⟨hle, hpos, hle2⟩
    exact req_valid_succeeds s r hadm

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have hle : s.last ≤ r.time := by
      unfold Admissible at h
      exact h.1
    have hlast : (step s r).2.last = r.time := by
      unfold step
      simp [h]
    have hle2 : s.last ≤ (step s r).2.last := by
      rw [hlast]
      exact hle
    constructor
    · exact hle2
    · intro _
      exact hlast
  · have hstep := req_invalid_noop s r h
    have hlast : (step s r).2.last = s.last := by
      rw [hstep]
    have hle2 : s.last ≤ (step s r).2.last := by
      rw [hlast]
      exact Nat.le_refl _
    constructor
    · exact hle2
    · intro hok
      have hfst : (step s r).1 = .rejected := by rw [hstep]
      rw [hfst] at hok
      cases hok

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · have htok : (step s r).2.tokens = refilled s r.time - r.cost := by
      unfold step
      simp [h]
    rw [htok]
    have hle : r.cost ≤ refilled s r.time := by
      unfold Admissible at h
      exact h.2.2
    exact Nat.sub_add_cancel hle
  · have hstep := req_invalid_noop s r h
    have hfst : (step s r).1 = .rejected := by rw [hstep]
    rw [hfst] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · have hcap : (step s r).2.capacity = s.capacity := by
      unfold step
      simp [h]
    have hrate : (step s r).2.rate = s.rate := by
      unfold step
      simp [h]
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := by
      unfold step
      simp [h]
    have hlast : (step s r).2.last = r.time := by
      unfold step
      simp [h]
    exact ⟨hcap, hrate, htok, hlast⟩
  · have hstep := req_invalid_noop s r h
    have hfst : (step s r).1 = .rejected := by rw [hstep]
    rw [hfst] at hok
    cases hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap_le
  by_cases h : Admissible s r
  · have htok : (step s r).2.tokens = refilled s r.time - r.cost := by
      unfold step
      simp [h]
    have hcap : (step s r).2.capacity = s.capacity := by
      unfold step
      simp [h]
    rw [htok, hcap]
    have hle_sub : refilled s r.time - r.cost ≤ refilled s r.time := Nat.sub_le _ _
    have hle_min : refilled s r.time ≤ s.capacity := by
      unfold refilled
      exact Nat.min_le_left _ _
    exact Nat.le_trans hle_sub hle_min
  · have hstep := req_invalid_noop s r h
    have htok : (step s r).2.tokens = s.tokens := by rw [hstep]
    have hcap : (step s r).2.capacity = s.capacity := by rw [hstep]
    rw [htok, hcap]
    exact hcap_le

end TokenBucket
