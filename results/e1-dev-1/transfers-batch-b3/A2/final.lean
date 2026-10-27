import Batch.Spec
import Batch.Lemmas
namespace Batch
/-- Admission check of one leg against the running balances. -/
def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && l.source != l.target &&
  s.accounts.contains l.source &&
  s.accounts.contains l.target &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - l.amount)

/-- Move one leg's amount between the running balances. -/
def post (bal : AccountId → Int) (l : Leg) : AccountId → Int :=
  fun a => bal a - (if a = l.source then (l.amount : Int) else 0)
    + (if a = l.target then (l.amount : Int) else 0)

/-- Final balances after the legs in order, or `none` if a leg is not allowed. -/
def applyAllAux (s : State) (bal : AccountId → Int) : List Leg → Option (AccountId → Int)
  | [] => some bal
  | l :: ls => if legAllowed s bal l then applyAllAux s (post bal l) ls else none

def applyAll (s : State) (legs : List Leg) : Option (AccountId → Int) :=
  applyAllAux s s.balance legs

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied then
    match applyAll s r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

theorem t2a (a b : Nat) : ((a != b) = true) ↔ a ≠ b := by
  simp

theorem t2b (a b : Nat) (h : ((a != b) = true)) : a ≠ b := by
  simpa using h

theorem t2c (a b : Nat) (h : a ≠ b) : ((a != b) = true) := by
  simpa using h

theorem legAllowed_iff2 (s : State) (bal : AccountId → Int) (l : Leg) :
    (legAllowed s bal l = true) ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem]
  constructor
  · intro h
    obtain ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩ := h
    refine ⟨h1, ?_, h3, h4, h5⟩
    intro heq; rw [heq] at h2; simp at h2
  · intro h
    obtain ⟨h1,h2,h3,h4,h5⟩ := h
    refine ⟨⟨⟨⟨h1,?_⟩,h3⟩,h4⟩,h5⟩
    simp [h2]

theorem post_eq_shift (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem applyAllAux_of_LegsOk (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int), LegsOk s bal legs → applyAllAux s bal legs = some (applyLegs bal legs) := by
  induction legs with
  | nil => intro bal h; rfl
  | cons l ls ih =>
    intro bal h
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    have hall : legAllowed s bal l = true := (legAllowed_iff2 s bal l).mpr hok
    -- unfold one step
    have hstep : applyAllAux s bal (l :: ls) = applyAllAux s (post bal l) ls := by
      simp [applyAllAux, hall]
    have happ : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [hstep, happ]
    have : post bal l = shift bal l := rfl
    rw [this]
    exact ih _ hrest

theorem req_valid_succeeds_aux2 : ValidSucceeds step := by
  intro s r h
  obtain ⟨hnodup, hne, hnotapp, hlegsok⟩ := h
  have hcond : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) := ⟨hnodup, hne, hnotapp⟩
  have happly : applyAll s r.legs = some (applyLegs s.balance r.legs) := by
    unfold applyAll
    exact applyAllAux_of_LegsOk s r.legs s.balance hlegsok
  unfold step
  rw [if_pos hcond, happly]

theorem applyAllAux_none_of_not_LegsOk2 (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int), ¬ LegsOk s bal legs → applyAllAux s bal legs = none := by
  induction legs with
  | nil =>
    intro bal h
    simp only [LegsOk] at h
    exact absurd True.intro h
  | cons l ls ih =>
    intro bal h
    simp only [LegsOk] at h
    by_cases he : legAllowed s bal l = true
    · have hok : LegOk s bal l := (legAllowed_iff2 s bal l).mp he
      have hrest : ¬ LegsOk s (shift bal l) ls := fun hr => h ⟨hok, hr⟩
      have hpost : post bal l = shift bal l := rfl
      have haux : applyAllAux s bal (l :: ls) = applyAllAux s (post bal l) ls := by
        simp [applyAllAux, he]
      rw [haux, hpost]
      exact ih _ hrest
    · have heF : legAllowed s bal l = false := by
        cases hh : legAllowed s bal l with
        | true => simp [hh] at he
        | false => rfl
      have haux : applyAllAux s bal (l :: ls) = none := by
        simp [applyAllAux, heF]
      exact haux

theorem applyAllAux_some_eq (s : State) (legs : List Leg) :
    ∀ (bal bal' : AccountId → Int), applyAllAux s bal legs = some bal' → bal' = applyLegs bal legs := by
  induction legs with
  | nil =>
    intro bal bal' h
    simp [applyAllAux] at h
    rw [h]; rfl
  | cons l ls ih =>
    intro bal bal' h
    simp only [applyAllAux] at h
    by_cases he : legAllowed s bal l = true
    · simp [he] at h
      have hrec := ih (post bal l) bal' h
      have hpost : post bal l = shift bal l := rfl
      rw [hpost] at hrec
      -- applyLegs (bal) (l::ls) = applyLegs (shift bal l) ls
      have happ : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
      rw [happ]
      exact hrec
    · have heF : legAllowed s bal l = false := by
        cases hh : legAllowed s bal l with
        | true => simp [hh] at he
        | false => rfl
      simp [heF] at h

theorem req_valid_succeeds   : ValidSucceeds step := by
  intro s r h
  obtain ⟨hnodup, hne, hnotapp, hlegsok⟩ := h
  have hcond : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) := ⟨hnodup, hne, hnotapp⟩
  have happly : applyAll s r.legs = some (applyLegs s.balance r.legs) := by
    unfold applyAll
    exact applyAllAux_of_LegsOk s r.legs s.balance hlegsok
  unfold step
  rw [if_pos hcond, happly]

theorem req_atomicity : Atomicity step := by
  intro s r h
  simp only [ValidBatch] at h
  unfold step
  by_cases hcond : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · rw [if_pos hcond]
    obtain ⟨hc1, hc2, hc3⟩ := hcond
    have hlegs : ¬ LegsOk s s.balance r.legs := by
      intro hleg
      exact h ⟨hc1, hc2, hc3, hleg⟩
    have hnone : applyAll s r.legs = none := by
      unfold applyAll
      exact applyAllAux_none_of_not_LegsOk2 s r.legs s.balance hlegs
    rw [hnone]
  · rw [if_neg hcond]

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  case pos =>
    cases hA : applyAll s r.legs with
    | none =>
      have hstep2 : step s r = (Outcome.rejected, s) := by unfold step; rw [if_pos hc, hA]
      rw [hstep2] at hok
      simp at hok
    | some bal =>
      have hst2 : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by unfold step; rw [if_pos hc, hA]
      have hbalLegs : applyAllAux s s.balance [l] = some bal := by
        have h1 : applyAll s r.legs = applyAllAux s s.balance [l] := by unfold applyAll; rw [hlegs]
        rw [h1] at hA
        exact hA
      have haux : applyAllAux s s.balance [l] = if legAllowed s s.balance l then some (post s.balance l) else none := by simp [applyAllAux]
      rw [haux] at hbalLegs
      have hallow : legAllowed s s.balance l = true := by
        cases hh : legAllowed s s.balance l with
        | false => simp [hh] at hbalLegs
        | true => rfl
      rw [hallow] at hbalLegs
      simp at hbalLegs
      have hLegOk : LegOk s s.balance l := (legAllowed_iff2 s s.balance l).mp hallow
      obtain ⟨_, hne, _, _, _⟩ := hLegOk
      rw [hst2]
      simp only
      rw [← hbalLegs]
      constructor
      · show post s.balance l l.source = _
        unfold post
        simp only [ite_true]
        have ht : ¬ (l.source = l.target) := hne
        simp [ht]
      · show post s.balance l l.target = _
        unfold post
        by_cases hts : l.target = l.source
        · exact absurd hts (fun he => hne he.symm)
        · simp [hts]
  case neg =>
    have hstep2 : step s r = (Outcome.rejected, s) := by unfold step; rw [if_neg hc]
    rw [hstep2] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  unfold step at hok
  by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · rw [if_pos hc] at hok
    cases hA : applyAll s r.legs with
    | none =>
      simp [hA] at hok
    | some bal =>
      simp [hA] at hok
      have hbal_eq : bal = applyLegs s.balance r.legs := by
        unfold applyAll at hA
        exact applyAllAux_some_eq s r.legs s.balance bal hA
      -- now describe step second component
      have hstep2 : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
        unfold step; rw [if_pos hc, hA]
      rw [hstep2]
      refine ⟨rfl, rfl, ?_⟩
      intro a
      simp only
      rw [hbal_eq]
  · rw [if_neg hc] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · cases hA : applyAll s r.legs with
    | none =>
      have hstep : step s r = (Outcome.rejected, s) := by unfold step; rw [if_pos hc, hA]
      have h1 : (step s r).1 = Outcome.rejected := by rw [hstep]
      rw [h1] at hok
      simp at hok
    | some bal =>
      have hstep : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by unfold step; rw [if_pos hc, hA]
      have h2eq : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by rw [hstep]
      constructor
      · intro x
        rw [h2eq]
        simp only
        simp
      · have hmem : r.batchId ∈ (({ s with balance := bal, applied := r.batchId :: s.applied } : State)).applied := by simp
        have hmem2 : r.batchId ∈ (step s r).2.applied := by rw [h2eq]; exact hmem
        have hcond2 : ¬ (((step s r).2).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ (step s r).2.applied) := by
          intro h
          obtain ⟨_, _, hnotin⟩ := h
          exact hnotin hmem2
        have hstep2 : step (step s r).2 r = (Outcome.rejected, (step s r).2) := by unfold step; rw [if_neg hcond2]
        exact hstep2
  · have hstep : step s r = (Outcome.rejected, s) := by unfold step; rw [if_neg hc]
    have h1 : (step s r).1 = Outcome.rejected := by rw [hstep]
    rw [h1] at hok
    simp at hok

theorem req_conservation     : Conserves step := sorry

theorem req_limit_every_step : LimitEveryStep step := sorry

end Batch
