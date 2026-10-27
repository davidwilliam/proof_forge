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
  simp [step, h]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  simp [step, h]

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  have hstep : ((step s r).1 = Outcome.ok) ↔ Admissible s r := by
    by_cases hadm : Admissible s r
    · simp [step, hadm]
    · simp [step, hadm]
  rw [hstep]
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨hle, hpos, h⟩

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  constructor
  · by_cases hadm : Admissible s r
    · simp [step, hadm, hadm.1]
    · simp [step, hadm]
  · intro hok
    by_cases hadm : Admissible s r
    · have h1 : (step s r).2.last = r.time := by simp [step, hadm]
      exact h1
    · simp [step, hadm] at hok

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases hadm : Admissible s r
  · have heq : (step s r).2.tokens = refilled s r.time - r.cost := by
      simp [step, hadm]
    rw [heq]
    exact Nat.sub_add_cancel hadm.2.2
  · simp [step, hadm] at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hadm : Admissible s r
  · have he1 : (step s r).2.capacity = s.capacity := by simp [step, hadm]
    have he2 : (step s r).2.rate = s.rate := by simp [step, hadm]
    have he3 : (step s r).2.tokens = refilled s r.time - r.cost := by simp [step, hadm]
    have he4 : (step s r).2.last = r.time := by simp [step, hadm]
    exact ⟨he1, he2, he3, he4⟩
  · simp [step, hadm] at hok

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  by_cases hadm : Admissible s r
  · have hle : refilled s r.time - r.cost ≤ s.capacity :=
      Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_left _ _)
    have heq1 : (step s r).2.tokens = refilled s r.time - r.cost := by
      simp [step, hadm]
    have heq2 : (step s r).2.capacity = s.capacity := by
      simp [step, hadm]
    rw [heq1, heq2]
    exact hle
  · have heq1 : (step s r).2.tokens = s.tokens := by simp [step, hadm]
    have heq2 : (step s r).2.capacity = s.capacity := by simp [step, hadm]
    rw [heq1, heq2]
    exact hcap

end TokenBucket
