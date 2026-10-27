import Batch.Spec
import Batch.Lemmas
namespace Batch
/-- Admission check of one leg against the running balances. -/
def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && decide (l.source ≠ l.target) &&
  decide (l.source ∈ s.accounts) &&
  decide (l.target ∈ s.accounts) &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - l.amount)

/-- Final balances after the legs in order, or `none` if a leg is not allowed. -/
def go (s : State) : (AccountId → Int) → List Leg → Option (AccountId → Int)
  | bal, [] => some bal
  | bal, l :: ls =>
    if legAllowed s bal l then go s (shift bal l) ls else none

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied then
    match go s s.balance r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

def fooTest : Nat := 1

theorem fooThm : 1 = 1 := rfl

theorem legAllowed_correct5 (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  simp only [legAllowed, LegOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem go_some_of_LegsOk (s : State) (bal : AccountId → Int) (ls : List Leg) :
    LegsOk s bal ls → go s bal ls = some (applyLegs bal ls) := by
  intro h
  induction ls generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    simp only [LegsOk] at h
    simp only [go, applyLegs]
    rw [if_pos (legAllowed_correct5 s bal l |>.mpr h.1)]
    rw [ih _ h.2]

theorem go_none_of_not_LegsOk_aux (s : State) (bal : AccountId → Int) (ls : List Leg) :
    ¬ LegsOk s bal ls → go s bal ls = none := by
  induction ls generalizing bal with
  | nil =>
    intro h
    simp only [LegsOk] at h
    exact absurd True.intro h
  | cons l ls ih =>
    intro h
    simp only [LegsOk] at h
    simp only [go]
    by_cases hleg : legAllowed s bal l = true
    · rw [if_pos hleg]
      have hLegOk : LegOk s bal l := (legAllowed_correct5 s bal l).mp hleg
      have htail : ¬ LegsOk s (shift bal l) ls := fun ht => h ⟨hLegOk, ht⟩
      exact ih _ htail
    · rw [if_neg hleg]

theorem req_single_leg_aux2 : True := trivial

theorem single_leg_helper1 (s : State) (r : Request) (h : (step s r).1 = Outcome.ok) :
    s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied := by
  by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · exact hc
  · exfalso
    have hre : (step s r).1 = Outcome.rejected := by
      unfold step
      rw [if_neg hc]
    rw [hre] at h
    exact Outcome.noConfusion h

theorem single_leg_helper2 (s : State) (r : Request) (l : Leg) (hlegs : r.legs = [l])
    (hok : (step s r).1 = Outcome.ok) :
    legAllowed s s.balance l = true ∧
    (step s r).2 = { s with balance := shift s.balance l, applied := r.batchId :: s.applied } := by
  have hcond := single_leg_helper1 s r hok
  have hcond2 : s.accounts.Nodup ∧ ([l] : List Leg) ≠ [] ∧ r.batchId ∉ s.applied := by
    rw [← hlegs]; exact hcond
  have hgo_ne : go s s.balance [l] ≠ none := by
    rw [← hlegs]
    intro hnone
    have hre : (step s r).1 = Outcome.rejected := by
      unfold step
      rw [if_pos hcond, hnone]
    rw [hre] at hok
    exact Outcome.noConfusion hok
  simp only [go] at hgo_ne
  have hallow : legAllowed s s.balance l = true := by
    cases he : legAllowed s s.balance l with
    | true => rfl
    | false =>
      simp [he] at hgo_ne
  refine ⟨hallow, ?_⟩
  have hgo_eq : go s s.balance [l] = some (shift s.balance l) := by
    simp only [go, if_pos hallow]
  have hgo_eq2 : go s s.balance r.legs = some (shift s.balance l) := by
    rw [hlegs]; exact hgo_eq
  have hstep : step s r = (Outcome.ok, { s with balance := shift s.balance l, applied := r.batchId :: s.applied }) := by
    unfold step
    rw [if_pos hcond, hgo_eq2]
  rw [hstep]

theorem single_leg_check (s : State) (l : Leg) (hNe : l.source ≠ l.target) :
    shift s.balance l l.source = s.balance l.source - (l.amount : Int) := by
  unfold shift
  simp [hNe]

theorem go_some_apply3 (s : State) (bal bal' : AccountId → Int) (ls : List Leg) :
    go s bal ls = some bal' → bal' = applyLegs bal ls := by
  induction ls generalizing bal bal' with
  | nil =>
    intro h
    simp only [go] at h
    have h2 : bal = bal' := Option.some_inj.mp h
    simp only [applyLegs]
    exact h2.symm
  | cons l ls ih =>
    intro h
    simp only [go] at h
    by_cases hallow : legAllowed s bal l = true
    · rw [if_pos hallow] at h
      have ihr := ih _ _ h
      simp only [applyLegs]
      exact ihr
    · rw [if_neg hallow] at h
      simp at h

theorem idem_helper_ok (s : State) (r : Request) (hok : (step s r).1 = Outcome.ok) :
    ∃ bal', go s s.balance r.legs = some bal' ∧
      (step s r).2 = { s with balance := bal', applied := r.batchId :: s.applied } := by
  have hcond := single_leg_helper1 s r hok
  unfold step at hok ⊢
  rw [if_pos hcond] at hok ⊢
  match hgo : go s s.balance r.legs with
  | none =>
    simp [hgo] at hok
  | some bal' =>
    exact ⟨bal', rfl, by simp [hgo]⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hnd, hne, hbid, hlegs⟩ := h
  show (step s r).1 = .ok
  unfold step
  rw [if_pos ⟨hnd, hne, hbid⟩]
  rw [go_some_of_LegsOk s s.balance r.legs hlegs]

theorem req_atomicity : Atomicity step := by
  intro s r hNot
  simp only [ValidBatch] at hNot
  unfold step
  by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hLegsNot : ¬ LegsOk s s.balance r.legs := fun hlegs => hNot ⟨hcond.1, hcond.2.1, hcond.2.2, hlegs⟩
    rw [if_pos hcond, go_none_of_not_LegsOk_aux s s.balance r.legs hLegsNot]
  · rw [if_neg hcond]

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  obtain ⟨hallow, hstate⟩ := single_leg_helper2 s r l hlegs hok
  have hLegOk : LegOk s s.balance l := (legAllowed_correct5 s s.balance l).mp hallow
  have hNe : l.source ≠ l.target := hLegOk.2.1
  have hTneS : l.target ≠ l.source := fun h => hNe h.symm
  constructor
  · rw [hstate]
    show shift s.balance l l.source = s.balance l.source - (l.amount : Int)
    unfold shift
    simp [hNe]
  · rw [hstate]
    show shift s.balance l l.target = s.balance l.target + (l.amount : Int)
    unfold shift
    simp [hTneS]

theorem req_effects : Effects step := by
  intro s r hok
  obtain ⟨bal', hgo, hbal, hstate⟩ := effects_helper2 s r hok
  refine ⟨?_, ?_, ?_⟩
  · rw [hstate]
  · rw [hstate]
  · intro a
    rw [hstate, hbal]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  obtain ⟨bal', hgo, hstate⟩ := idem_helper_ok s r hok
  constructor
  · intro x
    rw [hstate]
    simp
  · have hmem : r.batchId ∈ ({ s with balance := bal', applied := r.batchId :: s.applied } : State).applied := by
      simp
    have hstate2 : (step s r).2 = ({ s with balance := bal', applied := r.batchId :: s.applied } : State) := hstate
    have hnotmem : ¬ (r.batchId ∉ ((step s r).2).applied) := by
      rw [hstate2]
      simp [hmem]
    have hcond_false : ¬ (((step s r).2).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ ((step s r).2).applied) := by
      intro hc
      exact hnotmem hc.2.2
    have hstep2 : step ((step s r).2) r = (Outcome.rejected, ((step s r).2)) := by
      unfold step
      rw [if_neg hcond_false]
    exact hstep2

theorem req_conservation : Conserves step := by
  intro s r hok
  obtain ⟨bal', hgo, hstate⟩ := idem_helper_ok s r hok
  have hcond := single_leg_helper1 s r hok
  have hNodup : s.accounts.Nodup := hcond.1
  have hLegsOk : LegsOk s s.balance r.legs := consGoSomeLegsOkC s s.balance bal' r.legs hgo
  have hbalEq : bal' = applyLegs s.balance r.legs := go_some_apply3 s s.balance bal' r.legs hgo
  have hsum : sumOver s.accounts bal' = sumOver s.accounts s.balance := by
    rw [hbalEq]
    exact consApplyPreserveC s s.balance r.legs hNodup hLegsOk
  have htotal2 : total (step s r).2 = sumOver s.accounts bal' := by
    rw [hstate]
    rfl
  have htotal1 : total s = sumOver s.accounts s.balance := rfl
  rw [htotal2, htotal1]
  exact hsum

theorem req_limit_every_step : LimitEveryStep step := sorry

end Batch
