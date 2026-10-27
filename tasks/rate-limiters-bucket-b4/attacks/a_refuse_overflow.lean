import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance

def refStep : Impl := fun s r =>
  if Admissible s r then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem ref_step_of_adm {s : State} {r : Request} (h : Admissible s r) :
    refStep s r = (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
  simp [refStep, h]

theorem ref_step_of_not {s : State} {r : Request} (h : ¬ Admissible s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem ref_adm_of_ok {s : State} {r : Request} (h : (refStep s r).1 = .ok) : Admissible s r := by
  by_cases hv : Admissible s r
  · exact hv
  · rw [ref_step_of_not hv] at h; cases h

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [ref_step_of_adm h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact ref_step_of_not h

theorem ref_req_allow_iff_sufficient : AllowIffSufficient refStep := by
  intro s r ht hc
  constructor
  · intro h; exact (ref_adm_of_ok h).2.2
  · intro h; rw [ref_step_of_adm ⟨ht, hc, h⟩]

theorem ref_req_time_monotone : TimeMonotone refStep := by
  intro s r
  by_cases hv : Admissible s r
  · rw [ref_step_of_adm hv]; exact ⟨hv.1, fun _ => rfl⟩
  · rw [ref_step_of_not hv]; exact ⟨Nat.le_refl _, fun h => by cases h⟩

theorem ref_req_remaining : Remaining refStep := by
  intro s r h
  have hv := ref_adm_of_ok h
  rw [ref_step_of_adm hv]
  show refilled s r.time - r.cost + r.cost = refilled s r.time
  have := hv.2.2
  omega

theorem ref_req_effects : Effects refStep := by
  intro s r h
  have hv := ref_adm_of_ok h
  rw [ref_step_of_adm hv]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ref_req_capacity : CapacityBound refStep := by
  intro s r hs
  by_cases hv : Admissible s r
  · rw [ref_step_of_adm hv]
    show refilled s r.time - r.cost ≤ s.capacity
    have : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    omega
  · rw [ref_step_of_not hv]; exact hs

-- Evasive fix: only accept requests whose refill stays within capacity.
def step : Impl := fun s r =>
  if s.tokens + s.rate * (r.time - s.last) ≤ s.capacity then refStep s r else (.rejected, s)

theorem step_eq (s : State) (r : Request) : step s r = refStep s r ∨ step s r = (.rejected, s) := by
  unfold step; split
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem ok_eq {s : State} {r : Request} (h : (step s r).1 = .ok) : step s r = refStep s r := by
  rcases step_eq s r with e | e
  · exact e
  · rw [e] at h; cases h
-- Weakened restatements: success is only promised when the refill does not overflow.
theorem req_valid_succeeds : ∀ s r, Admissible s r →
    s.tokens + s.rate * (r.time - s.last) ≤ s.capacity → (step s r).1 = .ok := by
  intro s r h hc
  simp only [step, hc, ite_true]
  exact ref_req_valid_succeeds s r h
theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  rcases step_eq s r with e | e
  · rw [e]; exact ref_req_invalid_noop s r h
  · exact e
theorem req_allow_iff_sufficient : ∀ s r, s.last ≤ r.time → 0 < r.cost →
    s.tokens + s.rate * (r.time - s.last) ≤ s.capacity →
    ((step s r).1 = .ok ↔ r.cost ≤ refilled s r.time) := by
  intro s r ht hc hcap
  simp only [step, hcap, ite_true]
  exact ref_req_allow_iff_sufficient s r ht hc
theorem req_time_monotone : TimeMonotone step := by
  intro s r
  rcases step_eq s r with e | e
  · rw [e]; exact ref_req_time_monotone s r
  · rw [e]; exact ⟨Nat.le_refl _, fun h => by cases h⟩
theorem req_remaining : Remaining step := by
  intro s r h
  have e := ok_eq h
  rw [e] at h ⊢; exact ref_req_remaining s r h
theorem req_effects : Effects step := by
  intro s r h
  have e := ok_eq h
  rw [e] at h ⊢; exact ref_req_effects s r h
theorem req_capacity : CapacityBound step := by
  intro s r hs
  rcases step_eq s r with e | e
  · rw [e]; exact ref_req_capacity s r hs
  · rw [e]; exact hs
end TokenBucket
