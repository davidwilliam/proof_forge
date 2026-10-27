import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { capacity := s.capacity, rate := s.rate, tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem req_capacity_debug : True := trivial
#check @Nat.le_trans
#check @Nat.sub_le
#check @Nat.min_le_left

theorem req_capacity2 : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    show min s.capacity (s.tokens + s.rate * (r.time - s.last)) - r.cost ≤ s.capacity
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp only [h, ↓reduceIte]
    exact hcap

theorem req_capacity_aux_clean : True := trivial

theorem req_capacity3 : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    show min s.capacity (s.tokens + s.rate * (r.time - s.last)) - r.cost ≤ s.capacity
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp only [h, ↓reduceIte]
    exact hcap

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
    · intro h; exact h.2.2
    · intro h; exact ⟨hle, hpos, h⟩
  by_cases h : Admissible s r
  · have hc : r.cost ≤ refilled s r.time := hadm.mp h
    unfold step
    simp [h, hc]
  · have hc : ¬ r.cost ≤ refilled s r.time := fun hc => h (hadm.mpr hc)
    unfold step
    simp [h, hc]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have hle : s.last ≤ r.time := h.1
    unfold step
    simp [h, hle]
  · unfold step
    simp [h]

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · have hle : r.cost ≤ refilled s r.time := h.2.2
    unfold step
    simp [h]
    exact Nat.sub_add_cancel hle
  · unfold step at hok
    simp [h] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · unfold step
    simp [h]
  · unfold step at hok
    simp [h] at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  unfold step
  by_cases h : Admissible s r
  · simp only [h, ↓reduceIte]
    show min s.capacity (s.tokens + s.rate * (r.time - s.last)) - r.cost ≤ s.capacity
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · simp only [h, ↓reduceIte]
    exact hcap

end TokenBucket
