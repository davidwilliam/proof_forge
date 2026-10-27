import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)

theorem mytest_em (p : Prop) [Decidable p] : p ∨ ¬ p := Decidable.em p
#check Outcome.noConfusion
#check @Decidable.em
#check False.elim

theorem mytest_by_cases : ∀ (s : State) (r : Request), s.last ≤ r.time → 0 < r.cost → ((step s r).1 = .ok → r.cost ≤ refilled s r.time) := by
  intro s r hle hpos hok
  by_cases h : r.cost ≤ refilled s r.time
  · exact h
  · have hc : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := by
      intro hh
      exact h hh.2.2
    have hstep : step s r = ((.rejected : Outcome), s) := if_neg hc
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [hok] at h1
    exact False.elim (Outcome.noConfusion h1)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := h
  show (step s r).1 = _
  have hstep : step s r = ((.ok : Outcome), ({ s with tokens := refilled s r.time - r.cost, last := r.time } : State)) := if_pos hc
  rw [hstep]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hc : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := h
  have hstep : step s r = ((.rejected : Outcome), s) := if_neg hc
  exact hstep

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  constructor
  · intro hok
    by_cases h : r.cost ≤ refilled s r.time
    · exact h
    · have hc : ¬ (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := by
        intro hh
        exact h hh.2.2
      have hstep : step s r = ((.rejected : Outcome), s) := if_neg hc
      have h1 : (step s r).1 = .rejected := by rw [hstep]
      rw [hok] at h1
      exact False.elim (Outcome.noConfusion h1)
  · intro hle2
    have hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time) := ⟨hle, hpos, hle2⟩
    have hstep : step s r = ((.ok : Outcome), ({ s with tokens := refilled s r.time - r.cost, last := r.time } : State)) := if_pos hc
    have h1 : (step s r).1 = .ok := by rw [hstep]
    exact h1

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · have hstep : step s r = ((.ok : Outcome), ({ s with tokens := refilled s r.time - r.cost, last := r.time } : State)) := if_pos hc
    constructor
    · rw [hstep]
      exact hc.1
    · intro _hok
      rw [hstep]
  · have hstep : step s r = ((.rejected : Outcome), s) := if_neg hc
    constructor
    · rw [hstep]
      exact Nat.le_refl _
    · intro hok
      have h1 : (step s r).1 = .rejected := by rw [hstep]
      rw [hok] at h1
      exact False.elim (Outcome.noConfusion h1)

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · have hstep : step s r = ((.ok : Outcome), ({ s with tokens := refilled s r.time - r.cost, last := r.time } : State)) := if_pos hc
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := by rw [hstep]
    rw [htok]
    exact Nat.sub_add_cancel hc.2.2
  · have hstep : step s r = ((.rejected : Outcome), s) := if_neg hc
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [hok] at h1
    exact False.elim (Outcome.noConfusion h1)

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · have hstep : step s r = ((.ok : Outcome), ({ s with tokens := refilled s r.time - r.cost, last := r.time } : State)) := if_pos hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : (step s r).2.capacity = s.capacity := by rw [hstep]
      exact h
    · have h : (step s r).2.rate = s.rate := by rw [hstep]
      exact h
    · have h : (step s r).2.tokens = refilled s r.time - r.cost := by rw [hstep]
      exact h
    · have h : (step s r).2.last = r.time := by rw [hstep]
      exact h
  · have hstep : step s r = ((.rejected : Outcome), s) := if_neg hc
    have h1 : (step s r).1 = .rejected := by rw [hstep]
    rw [hok] at h1
    exact False.elim (Outcome.noConfusion h1)

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  by_cases hc : (s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time)
  · have hstep : step s r = ((.ok : Outcome), ({ s with tokens := refilled s r.time - r.cost, last := r.time } : State)) := if_pos hc
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := by rw [hstep]
    have hcap2 : (step s r).2.capacity = s.capacity := by rw [hstep]
    rw [htok, hcap2]
    calc refilled s r.time - r.cost ≤ refilled s r.time := Nat.sub_le _ _
      _ ≤ s.capacity := Nat.min_le_left _ _
  · have hstep : step s r = ((.rejected : Outcome), s) := if_neg hc
    have htok : (step s r).2.tokens = s.tokens := by rw [hstep]
    have hcap2 : (step s r).2.capacity = s.capacity := by rw [hstep]
    rw [htok, hcap2]
    exact hcap

end TokenBucket
