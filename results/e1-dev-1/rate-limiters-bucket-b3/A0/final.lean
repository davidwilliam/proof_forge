import TokenBucket.Spec
namespace TokenBucket

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible
  infer_instance

def step : Impl := fun s r =>
  if Admissible s r then
    (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have he : step s r = (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
    simp [step, h]
  exact congrArg Prod.fst he

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have he : step s r = (Outcome.rejected, s) := by
    simp [step, h]
  exact he

theorem req_allow_iff_sufficient : AllowIffSufficient step := by
  intro s r hle hpos
  by_cases h : Admissible s r
  · have he : step s r = (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    have hfst : (step s r).1 = Outcome.ok := congrArg Prod.fst he
    have hconj : s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time := h
    have hcost : r.cost ≤ refilled s r.time := hconj.2.2
    exact Iff.intro (fun _ => hcost) (fun _ => hfst)
  · have he : step s r = (Outcome.rejected, s) := by
      simp [step, h]
    have hfst : (step s r).1 = Outcome.rejected := congrArg Prod.fst he
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    have hncost : ¬ r.cost ≤ refilled s r.time := by
      intro hc
      have hconj : s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time := ⟨hle, hpos, hc⟩
      have hadm : Admissible s r := hconj
      exact h hadm
    constructor
    · intro hok
      have hcontra : Outcome.rejected = Outcome.ok := Eq.trans hfst.symm hok
      exact False.elim (hne hcontra)
    · intro hcost
      exact False.elim (hncost hcost)

theorem req_time_monotone : TimeMonotone step := by
  intro s r
  by_cases h : Admissible s r
  · have he : step s r = (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    have hlast : (step s r).2.last = r.time := congrArg (fun p : Outcome × State => p.2.last) he
    have hconj : s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time := h
    have hle : s.last ≤ r.time := hconj.1
    constructor
    · rw [hlast]
      exact hle
    · intro _
      exact hlast
  · have he : step s r = (Outcome.rejected, s) := by
      simp [step, h]
    have hlast : (step s r).2.last = s.last := congrArg (fun p : Outcome × State => p.2.last) he
    have hfst : (step s r).1 = Outcome.rejected := congrArg Prod.fst he
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    constructor
    · rw [hlast]
      exact Nat.le_refl _
    · intro hok
      have hcontra : Outcome.rejected = Outcome.ok := Eq.trans hfst.symm hok
      exact False.elim (hne hcontra)

theorem req_remaining : Remaining step := by
  intro s r hok
  by_cases h : Admissible s r
  · have he : step s r = (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := congrArg (fun p : Outcome × State => p.2.tokens) he
    have hconj : s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost ≤ refilled s r.time := h
    have hcost : r.cost ≤ refilled s r.time := hconj.2.2
    have hsub : refilled s r.time - r.cost + r.cost = refilled s r.time := Nat.sub_add_cancel hcost
    rw [htok]
    exact hsub
  · have he : step s r = (Outcome.rejected, s) := by
      simp [step, h]
    have hfst : (step s r).1 = Outcome.rejected := congrArg Prod.fst he
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    have hcontra : Outcome.rejected = Outcome.ok := Eq.trans hfst.symm hok
    exact False.elim (hne hcontra)

theorem req_effects : Effects step := by
  intro s r hok
  by_cases h : Admissible s r
  · have he : step s r = (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    have hcap : (step s r).2.capacity = s.capacity := congrArg (fun p : Outcome × State => p.2.capacity) he
    have hrate : (step s r).2.rate = s.rate := congrArg (fun p : Outcome × State => p.2.rate) he
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := congrArg (fun p : Outcome × State => p.2.tokens) he
    have hlast : (step s r).2.last = r.time := congrArg (fun p : Outcome × State => p.2.last) he
    exact ⟨hcap, hrate, htok, hlast⟩
  · have he : step s r = (Outcome.rejected, s) := by
      simp [step, h]
    have hfst : (step s r).1 = Outcome.rejected := congrArg Prod.fst he
    have hne : Outcome.rejected ≠ Outcome.ok := by decide
    have hcontra : Outcome.rejected = Outcome.ok := Eq.trans hfst.symm hok
    exact False.elim (hne hcontra)

theorem req_capacity : CapacityBound step := by
  intro s r hcap
  by_cases h : Admissible s r
  · have he : step s r = (Outcome.ok, { s with tokens := refilled s r.time - r.cost, last := r.time }) := by
      simp [step, h]
    have htok : (step s r).2.tokens = refilled s r.time - r.cost := congrArg (fun p : Outcome × State => p.2.tokens) he
    have hcap2 : (step s r).2.capacity = s.capacity := congrArg (fun p : Outcome × State => p.2.capacity) he
    rw [htok, hcap2]
    have h1 : refilled s r.time - r.cost ≤ refilled s r.time := Nat.sub_le _ _
    have h2 : refilled s r.time ≤ s.capacity := Nat.min_le_left _ _
    exact Nat.le_trans h1 h2
  · have he : step s r = (Outcome.rejected, s) := by
      simp [step, h]
    have htok : (step s r).2.tokens = s.tokens := congrArg (fun p : Outcome × State => p.2.tokens) he
    have hcap2 : (step s r).2.capacity = s.capacity := congrArg (fun p : Outcome × State => p.2.capacity) he
    rw [htok, hcap2]
    exact hcap

end TokenBucket
