import Batch.Spec
import Batch.Lemmas
namespace Batch

def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && (decide (l.source ≠ l.target) && (decide (l.source ∈ s.accounts) && (decide (l.target ∈ s.accounts) && decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int)))))

def checkLegs (s : State) (bal : AccountId → Int) : List Leg → Bool
  | [] => true
  | l :: ls => (legAllowed s bal l) && checkLegs s (shift bal l) ls

def validBool (s : State) (r : Request) : Bool :=
  decide (s.accounts.Nodup) && (decide (r.legs ≠ []) && (decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs))

def step : Impl := fun s r =>
  if validBool s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else (.rejected, s)

theorem legAllowed_correct (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  simp [legAllowed, LegOk]

theorem checkLegs_correct (s : State) (bal : AccountId → Int) (legs : List Leg) :
    checkLegs s bal legs = true ↔ LegsOk s bal legs := by
  induction legs generalizing bal with
  | nil => simp [checkLegs, LegsOk]
  | cons l ls ih => simp [checkLegs, legAllowed_correct, ih, LegsOk]

theorem validBool_correct (s : State) (r : Request) :
    validBool s r = true ↔ ValidBatch s r := by
  simp [validBool, ValidBatch, checkLegs_correct]

theorem step_ok_eq (s : State) (r : Request) (h : validBool s r = true) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  simp [step, h]

theorem step_rej_eq (s : State) (r : Request) (h : validBool s r = false) :
    step s r = (.rejected, s) := by
  simp [step, h]

theorem step_valid_true (s : State) (r : Request) (hok : (step s r).1 = .ok) :
    validBool s r = true := by
  by_cases hb : validBool s r = true
  · exact hb
  · have hbF : validBool s r = false := Bool.eq_false_iff.mpr hb
    have heq := step_rej_eq s r hbF
    have h1 : (step s r).1 = .rejected := by simp [heq]
    rw [h1] at hok
    cases hok

theorem step_ok_iff (s : State) (r : Request) : (step s r).1 = .ok ↔ ValidBatch s r := by
  constructor
  · intro h
    exact (validBool_correct s r).mp (step_valid_true s r h)
  · intro h
    have hb : validBool s r = true := (validBool_correct s r).mpr h
    have heq := step_ok_eq s r hb
    simp [heq]

theorem shift_apply_single (bal : AccountId → Int) (l : Leg) (hst : l.source ≠ l.target) :
    shift bal l l.source = bal l.source - (l.amount : Int) ∧
    shift bal l l.target = bal l.target + (l.amount : Int) := by
  have hns : l.target ≠ l.source := fun h => hst h.symm
  constructor
  · simp [shift, hst]
  · simp [shift, hns]

theorem total_shift (s : State) (bal : AccountId → Int) (l : Leg)
    (hN : s.accounts.Nodup) (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have heq : sumOver s.accounts (shift bal l)
      = sumOver s.accounts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0))
        + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [heq, sumOver_add, sumOver_sub]
  have h1 : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0)
      = (l.amount : Int) := by
    rw [sumOver_ite_eq hN]
    simp [hs]
  have h2 : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0)
      = (l.amount : Int) := by
    rw [sumOver_ite_eq hN]
    simp [ht]
  omega

theorem total_applyLegs_of_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hN : s.accounts.Nodup) (hOk : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hok, htail⟩ := hOk
    unfold LegOk at hok
    obtain ⟨_, hne, hsm, htm, _⟩ := hok
    show sumOver s.accounts (applyLegs (shift bal l) ls) = _
    rw [ih (shift bal l) htail, total_shift s bal l hN hsm htm]

theorem within_shift (s : State) (bal : AccountId → Int) (l : Leg)
    (hw : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hok : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  unfold LegOk at hok
  obtain ⟨hpos, hne, hsm, htm, hlim⟩ := hok
  intro a ha
  show -(s.limit a : Int) ≤ bal a - (if a = l.source then (l.amount : Int) else 0)
    + (if a = l.target then (l.amount : Int) else 0)
  by_cases hs : a = l.source
  · subst hs
    simp [hne]
    omega
  · by_cases ht : a = l.target
    · subst ht
      have hbase := hw l.target htm
      simp [hs]
      omega
    · have hbase := hw a ha
      simp [hs, ht]
      omega

theorem within_applyLegs (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hw : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegsOk s bal legs) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal legs a := by
  induction legs generalizing bal with
  | nil =>
    intro a ha
    show -(s.limit a : Int) ≤ bal a
    exact hw a ha
  | cons l ls ih =>
    obtain ⟨hok, htail⟩ := hOk
    show ∀ a ∈ s.accounts, _ ≤ applyLegs (shift bal l) ls a
    exact ih (shift bal l) (within_shift s bal l hw hok) htail

theorem LegsOk_take (s : State) (bal : AccountId → Int) (legs : List Leg) :
    ∀ (k : Nat), LegsOk s bal legs → LegsOk s bal (legs.take k) := by
  induction legs generalizing bal with
  | nil =>
    intro k _
    cases k with
    | zero => trivial
    | succ n => trivial
  | cons l ls ih =>
    intro k hOk
    cases k with
    | zero => trivial
    | succ n =>
      obtain ⟨hok, htail⟩ := hOk
      exact ⟨hok, ih (shift bal l) n htail⟩

theorem within_prefix (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hw : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegsOk s bal legs) :
    ∀ k, ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  intro k a ha
  have hOkTake := LegsOk_take s bal legs k hOk
  exact within_applyLegs s bal (legs.take k) hw hOkTake a ha

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hb : validBool s r = true := (validBool_correct s r).mpr h
  have heq := step_ok_eq s r hb
  simp [heq]

theorem req_atomicity : Atomicity step := by
  intro s r h
  by_cases hb : validBool s r = true
  · exact absurd ((validBool_correct s r).mp hb) h
  · have hbF : validBool s r = false := Bool.eq_false_iff.mpr hb
    exact step_rej_eq s r hbF

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  have hVb : ValidBatch s r := (step_ok_iff s r).mp hok
  have hb : validBool s r = true := (validBool_correct s r).mpr hVb
  have heq := step_ok_eq s r hb
  have hbal : (step s r).2.balance = applyLegs s.balance r.legs := by simp [heq]
  have hLegs : LegsOk s s.balance r.legs := hVb.2.2.2
  rw [hlegs] at hLegs
  obtain ⟨hok1, _⟩ := hLegs
  unfold LegOk at hok1
  obtain ⟨_, hne, _, _, _⟩ := hok1
  have hs := (shift_apply_single s.balance l hne).1
  have ht := (shift_apply_single s.balance l hne).2
  constructor
  · rw [hbal, hlegs]; exact hs
  · rw [hbal, hlegs]; exact ht

theorem req_effects : Effects step := by
  intro s r hok
  have hb := step_valid_true s r hok
  have heq := step_ok_eq s r hb
  have h1 : (step s r).2.accounts = s.accounts := by simp [heq]
  have h2 : (step s r).2.limit = s.limit := by simp [heq]
  have h3 : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by intro a; simp [heq]
  exact ⟨h1, h2, h3⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hb := step_valid_true s r hok
  have heq := step_ok_eq s r hb
  constructor
  · intro x
    simp [heq]
  · have hmem : r.batchId ∈ (step s r).2.applied := by simp [heq]
    have hdec : decide (r.batchId ∉ (step s r).2.applied) = false := by simp [hmem]
    have hb2 : validBool (step s r).2 r = false := by simp [validBool, hdec]
    exact step_rej_eq (step s r).2 r hb2

theorem req_conservation : Conserves step := by
  intro s r hok
  have hVb : ValidBatch s r := (step_ok_iff s r).mp hok
  have hN : s.accounts.Nodup := hVb.1
  have hLegs : LegsOk s s.balance r.legs := hVb.2.2.2
  have hb : validBool s r = true := (validBool_correct s r).mpr hVb
  have heq := step_ok_eq s r hb
  unfold total
  have hacc : (step s r).2.accounts = s.accounts := by simp [heq]
  have hbal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by intro a; simp [heq]
  have hsum : sumOver (step s r).2.accounts (step s r).2.balance
      = sumOver s.accounts (applyLegs s.balance r.legs) := by
    rw [hacc]
    exact sumOver_congr s.accounts _ _ (fun a _ => hbal a)
  rw [hsum]
  exact total_applyLegs_of_LegsOk s s.balance r.legs hN hLegs

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hw
  constructor
  · by_cases hb : validBool s r = true
    · have heq := step_ok_eq s r hb
      have hVb : ValidBatch s r := (validBool_correct s r).mp hb
      have hLegs : LegsOk s s.balance r.legs := hVb.2.2.2
      intro a ha
      have ha2 : a ∈ s.accounts := by simp [heq] at ha; exact ha
      have hle := within_applyLegs s s.balance r.legs (fun a ha => hw a ha) hLegs a ha2
      have hlim : (step s r).2.limit a = s.limit a := by simp [heq]
      have hbal : (step s r).2.balance a = applyLegs s.balance r.legs a := by simp [heq]
      rw [hlim, hbal]
      exact hle
    · have hbF : validBool s r = false := Bool.eq_false_iff.mpr hb
      have heq := step_rej_eq s r hbF
      intro a ha
      have ha2 : a ∈ s.accounts := by simp [heq] at ha; exact ha
      have hbal : (step s r).2.balance a = s.balance a := by simp [heq]
      have hlim : (step s r).2.limit a = s.limit a := by simp [heq]
      rw [hbal, hlim]
      exact hw a ha2
  · intro hok k a ha
    have hVb : ValidBatch s r := (step_ok_iff s r).mp hok
    have hLegs : LegsOk s s.balance r.legs := hVb.2.2.2
    exact within_prefix s s.balance r.legs (fun a ha => hw a ha) hLegs k a ha

end Batch
