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

/-- Sequential check of legs against running balances. -/
def checkLegs (s : State) (bal : AccountId → Int) : List Leg → Bool
  | [] => true
  | l :: ls => legAllowed s bal l && checkLegs s (shift bal l) ls

def step : Impl := fun s r =>
  if decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else (.rejected, s)

theorem probe_contain (s : State) (x : Nat) : (s.accounts.contains x = true) ↔ x ∈ s.accounts := by
  simp [List.contains_eq_mem]

theorem legAllowed_true_iff2 (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, by simpa using h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, by simpa using h2⟩, h3⟩, h4⟩, h5⟩

theorem checkLegs_true_iff (s : State) (bal : AccountId → Int) (ls : List Leg) :
    checkLegs s bal ls = true ↔ LegsOk s bal ls := by
  induction ls generalizing bal with
  | nil => simp [checkLegs, LegsOk]
  | cons l ls ih =>
    simp only [checkLegs, Bool.and_eq_true, LegsOk]
    rw [legAllowed_true_iff2, ih]

theorem step_ok_of (s : State) (r : Request)
    (hN : s.accounts.Nodup) (hne : r.legs ≠ []) (hni : r.batchId ∉ s.applied)
    (hLegs : LegsOk s s.balance r.legs) : (step s r).1 = .ok := by
  have h1 : decide s.accounts.Nodup = true := decide_eq_true hN
  have h2 : decide (r.legs ≠ []) = true := decide_eq_true hne
  have h3 : decide (r.batchId ∉ s.applied) = true := decide_eq_true hni
  have h4 : checkLegs s s.balance r.legs = true := (checkLegs_true_iff s s.balance r.legs).mpr hLegs
  have hcond : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true := by
    simp [h1, h2, h3, h4]
  unfold step
  simp only [hcond]
  rfl

theorem tmp_explore2 (s : State) (r : Request)
    (h : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  unfold step
  rw [h]
  simp

theorem tmp_explore3 (s : State) (r : Request)
    (h : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = false) :
    step s r = (.rejected, s) := by
  unfold step
  rw [h]
  simp

theorem shift_sum_eq2 (s : State) (bal : AccountId → Int) (l : Leg)
    (hN : s.accounts.Nodup)
    (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have hCong : sumOver s.accounts (shift bal l) = sumOver s.accounts (fun a => ((bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0))) :=
    sumOver_congr s.accounts _ _ (fun a _ => rfl)
  rw [hCong]
  have hAdd := sumOver_add s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) (fun a => (if a = l.target then (l.amount : Int) else 0))
  have hSub := sumOver_sub s.accounts (fun a => bal a) (fun a => (if a = l.source then (l.amount : Int) else 0))
  rw [hAdd, hSub]
  have hS : sumOver s.accounts (fun a => (if a = l.source then (l.amount : Int) else 0)) = (l.amount : Int) := by
    have h := sumOver_ite_eq hN l.source (l.amount : Int)
    simpa [hs] using h
  have hT : sumOver s.accounts (fun a => (if a = l.target then (l.amount : Int) else 0)) = (l.amount : Int) := by
    have h := sumOver_ite_eq hN l.target (l.amount : Int)
    simpa [ht] using h
  rw [hS, hT]
  have hEta : (sumOver s.accounts fun a => bal a) = sumOver s.accounts bal := rfl
  omega

theorem applyLegs_sum_eq2 (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hN : s.accounts.Nodup) : LegsOk s bal ls → sumOver s.accounts (applyLegs bal ls) = sumOver s.accounts bal := by
  induction ls generalizing bal with
  | nil => intro _; rfl
  | cons l ls ih =>
    intro h
    simp only [LegsOk] at h
    obtain ⟨hOk, hRest⟩ := h
    simp only [applyLegs]
    rw [ih (shift bal l) hRest, shift_sum_eq2 s bal l hN hOk.2.2.1 hOk.2.2.2.1]

theorem my_test_aux : True := trivial

theorem foo_test2 (n : Nat) : n = n := by rfl

theorem bar_helper (a : Nat) (h : a = 1) : a = 1 := by exact h

theorem rwTest (a b : Nat) (c : Int) (h : a = b) : (if a = b then c else 0) = c := by rw [if_pos h]

theorem my_extra_lemma123 : True := trivial

theorem shift_preserves_aux (s : State) (bal : AccountId → Int) (l : Leg)
    (hBal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  intro a ha
  obtain ⟨_, hne, _, _, hFloor⟩ := hOk
  unfold shift
  by_cases hs : a = l.source
  · subst hs
    have ht : ¬ (l.source = l.target) := hne
    simp only [if_true, ht, if_false]
    have h1 : bal l.source - (l.amount : Int) + 0 = bal l.source - (l.amount : Int) := by omega
    rw [h1]
    exact hFloor
  · by_cases ht : a = l.target
    · subst ht
      simp only [hs, if_false, if_true]
      have hle := hBal l.target ha
      omega
    · simp only [hs, if_false, ht, if_false]
      have hle := hBal a ha
      omega

theorem final_within_aux (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hBal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegsOk s bal ls) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal ls a := by
  induction ls generalizing bal with
  | nil =>
    simpa [applyLegs] using hBal
  | cons l ls ih =>
    simp only [LegsOk] at hOk
    obtain ⟨hHead, hTail⟩ := hOk
    simp only [applyLegs]
    exact ih (shift bal l) (shift_preserves_aux s bal l hBal hHead) hTail

theorem legsOk_take_aux (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hOk : LegsOk s bal ls) (k : Nat) : LegsOk s bal (ls.take k) := by
  induction ls generalizing bal k with
  | nil =>
    simp only [List.take_nil, LegsOk]
  | cons l ls ih =>
    simp only [LegsOk] at hOk
    obtain ⟨hHead, hTail⟩ := hOk
    cases k with
    | zero => simp only [List.take_zero, LegsOk]
    | succ n =>
      simp only [List.take_succ_cons]
      simp only [LegsOk]
      exact ⟨hHead, ih (shift bal l) hTail n⟩

theorem req_valid_succeeds   : ValidSucceeds step := by
  intro s r h
  obtain ⟨hN, hne, hni, hLegs⟩ := h
  exact step_ok_of s r hN hne hni hLegs

theorem req_atomicity : Atomicity step := by
  intro s r hInvalid
  unfold step
  cases hcond : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
  | true =>
    exfalso
    apply hInvalid
    have hAnd : decide s.accounts.Nodup = true ∧ decide (r.legs ≠ []) = true ∧ decide (r.batchId ∉ s.applied) = true ∧ checkLegs s s.balance r.legs = true := by
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcond
      exact ⟨h1, h2, h3, h4⟩
    obtain ⟨h1, h2, h3, h4⟩ := hAnd
    have hN : s.accounts.Nodup := of_decide_eq_true h1
    have hne : r.legs ≠ [] := of_decide_eq_true h2
    have hni : r.batchId ∉ s.applied := of_decide_eq_true h3
    have hLegs : LegsOk s s.balance r.legs := (checkLegs_true_iff s s.balance r.legs).mp h4
    exact ⟨hN, hne, hni, hLegs⟩
  | false => simp

theorem req_single_leg : SingleLeg step := by
  intro s r l hr hok
  cases hcc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
  | false =>
    have hstep := tmp_explore3 s r hcc
    rw [hstep] at hok
    simp at hok
  | true =>
    have hstep := tmp_explore2 s r hcc
    have h4 : checkLegs s s.balance r.legs = true := by
      simp only [Bool.and_eq_true] at hcc
      obtain ⟨⟨⟨_, _⟩, _⟩, h4⟩ := hcc
      exact h4
    have hLegs : LegsOk s s.balance r.legs :=
      (checkLegs_true_iff s s.balance r.legs).mp h4
    rw [hstep]
    simp only
    rw [hr] at hLegs
    simp only [LegsOk] at hLegs
    obtain ⟨hLegOk, _⟩ := hLegs
    obtain ⟨_, hne, _, _, _⟩ := hLegOk
    rw [hr]
    constructor
    · simp only [applyLegs, shift]
      simp [hne]
    · simp only [applyLegs, shift]
      have hts : ¬ (l.target = l.source) := fun h => hne h.symm
      simp [hts]

theorem req_effects : Effects step := by
  intro s r hok
  have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
    cases hcc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | false =>
      have hs := tmp_explore3 s r hcc
      rw [hs] at hok
      simp at hok
    | true => exact tmp_explore2 s r hcc
  rw [hstep]
  exact ⟨rfl, rfl, fun a => rfl⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hccT : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true := by
    cases hcc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | true => rfl
    | false =>
      have hs := tmp_explore3 s r hcc
      rw [hs] at hok
      simp at hok
  have hstep := tmp_explore2 s r hccT
  constructor
  · intro x
    rw [hstep]
    simp
  · have hrewrite : (step s r).2 = ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State) := by
      rw [hstep]
    rw [hrewrite]
    have hcondF : (decide ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State).accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State).applied) && checkLegs ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State) ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State).balance r.legs) = false := by
      simp
    have hstep2 := tmp_explore3 ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State) r hcondF
    exact hstep2

theorem req_conservation     : Conserves step := by
  intro s r hok
  have hccT : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) = true := by
    cases hcc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | true => rfl
    | false =>
      have hs := tmp_explore3 s r hcc
      rw [hs] at hok
      simp at hok
  have hstep := tmp_explore2 s r hccT
  have hAnd : decide s.accounts.Nodup = true ∧ decide (r.legs ≠ []) = true ∧ decide (r.batchId ∉ s.applied) = true ∧ checkLegs s s.balance r.legs = true := by
    simp only [Bool.and_eq_true] at hccT
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hccT
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨h1, h2, h3, h4⟩ := hAnd
  have hN : s.accounts.Nodup := of_decide_eq_true h1
  have hLegs : LegsOk s s.balance r.legs := (checkLegs_true_iff s s.balance r.legs).mp h4
  have hSum := applyLegs_sum_eq2 s s.balance r.legs hN hLegs
  unfold total
  rw [hstep]
  simp only
  exact hSum

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hW
  constructor
  · cases hcc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | false =>
      have hs := tmp_explore3 s r hcc
      rw [hs]
      simpa using hW
    | true =>
      have hs := tmp_explore2 s r hcc
      rw [hs]
      simp only
      have h4 : checkLegs s s.balance r.legs = true := by
        simp only [Bool.and_eq_true] at hcc
        obtain ⟨⟨⟨_, _⟩, _⟩, h4⟩ := hcc
        exact h4
      have hLegs : LegsOk s s.balance r.legs :=
        (checkLegs_true_iff s s.balance r.legs).mp h4
      have hBal : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ s.balance b := hW
      have hfin := final_within_aux s s.balance r.legs hBal hLegs
      exact hfin
  · intro hok k a ha
    cases hcc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs) with
    | false =>
      have hs := tmp_explore3 s r hcc
      rw [hs] at hok
      simp at hok
    | true =>
      have h4 : checkLegs s s.balance r.legs = true := by
        simp only [Bool.and_eq_true] at hcc
        obtain ⟨⟨⟨_, _⟩, _⟩, h4⟩ := hcc
        exact h4
      have hLegs : LegsOk s s.balance r.legs :=
        (checkLegs_true_iff s s.balance r.legs).mp h4
      have hBal : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ s.balance b := hW
      have hTake : LegsOk s s.balance (r.legs.take k) :=
        legsOk_take_aux s s.balance r.legs hLegs k
      have hfin := final_within_aux s s.balance (r.legs.take k) hBal hTake
      exact hfin a ha

end Batch
