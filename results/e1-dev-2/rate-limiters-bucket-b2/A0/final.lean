import TokenBucket.Spec
namespace TokenBucket

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

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
  by_cases hadm : Admissible s r
  · have hok : (step s r).1 = .ok := by
      unfold step
      simp [hadm]
    have hcost : r.cost ≤ refilled s r.time := hadm.2.2
    simp [hok, hcost]
  · have hrej : (step s r).1 = .rejected := by
      unfold step
      simp [hadm]
    have hnot : ¬ r.cost ≤ refilled s r.time := fun hcost => hadm ⟨hle, hpos, hcost⟩
    simp [hrej, hnot]

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases hadm : Admissible s r
  · have hfst : (step s r).2.last = r.time := by
      unfold step
      simp [hadm]
    have hle : s.last ≤ r.time := hadm.1
    constructor
    · rw [hfst]
      exact hle
    · intro _
      exact hfst
  · have h1 : (step s r).1 = .rejected := by
      unfold step
      simp [hadm]
    have h2 : (step s r).2 = s := by
      unfold step
      simp [hadm]
    constructor
    · rw [h2]
      exact Nat.le_refl _
    · intro hok
      rw [h1] at hok
      cases hok

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases hadm : Admissible s r
  · have htok : (step s r).2.tokens = refilled s r.time - r.cost := by
      unfold step
      simp [hadm]
    rw [htok]
    exact Nat.sub_add_cancel hadm.2.2
  · have h1 : (step s r).1 = .rejected := by
      unfold step
      simp [hadm]
    rw [h1] at hok
    cases hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hadm : Admissible s r
  · have hstep : step s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      unfold step
      simp [hadm]
    rw [hstep]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have h1 : (step s r).1 = .rejected := by
      unfold step
      simp [hadm]
    rw [h1] at hok
    cases hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  by_cases hadm : Admissible s r
  · have htok : (step s r).2.tokens = refilled s r.time - r.cost := by
      unfold step
      simp [hadm]
    have hcap2 : (step s r).2.capacity = s.capacity := by
      unfold step
      simp [hadm]
    rw [htok, hcap2]
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
  · have h2 : (step s r).2 = s := by
      unfold step
      simp [hadm]
    rw [h2]
    exact hcap

end TokenBucket
