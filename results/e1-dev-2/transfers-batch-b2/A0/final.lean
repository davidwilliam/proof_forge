import Batch.Spec
import Batch.Lemmas
namespace Batch

def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && (decide (l.source ≠ l.target) && (decide (l.source ∈ s.accounts) && (decide (l.target ∈ s.accounts) && decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int)))))

def checkLegs (s : State) (bal : AccountId → Int) : List Leg → Bool
  | [] => true
  | l :: rest => legAllowed s bal l && checkLegs s (shift bal l) rest

def validBatchBool (s : State) (r : Request) : Bool :=
  decide s.accounts.Nodup && (decide (r.legs ≠ []) && (decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs))

def step : Impl := fun s r =>
  if validBatchBool s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else (.rejected, s)

theorem legAllowed_iff (s : State) (bal : AccountId → Int) (l : Leg) :
    (legAllowed s bal l = true) ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp

theorem checkLegs_iff (s : State) (bal : AccountId → Int) (ls : List Leg) :
    checkLegs s bal ls = true ↔ LegsOk s bal ls := by
  induction ls generalizing bal with
  | nil =>
    simp only [checkLegs, LegsOk]
  | cons l ls ih =>
    have eC : checkLegs s bal (l :: ls) = (legAllowed s bal l && checkLegs s (shift bal l) ls) := rfl
    have eL : (LegsOk s bal (l :: ls) : Prop) = (LegOk s bal l ∧ LegsOk s (shift bal l) ls) := rfl
    rw [eC, eL, Bool.and_eq_true, legAllowed_iff, ih]

theorem validBatchBool_iff (s : State) (r : Request) :
    (validBatchBool s r = true) ↔ ValidBatch s r := by
  unfold validBatchBool ValidBatch
  simp [checkLegs_iff s s.balance r.legs]

theorem step_ok_eq (s : State) (r : Request) (h : ValidBatch s r) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  unfold step
  have hT : validBatchBool s r = true := (validBatchBool_iff s r).mpr h
  rw [if_pos hT]

theorem step_rej_eq (s : State) (r : Request) (h : ¬ ValidBatch s r) :
    step s r = (.rejected, s) := by
  unfold step
  have hN : ¬ (validBatchBool s r = true) := fun he => h ((validBatchBool_iff s r).mp he)
  rw [if_neg hN]

theorem of_ok_valid (s : State) (r : Request) (hOk : (step s r).1 = .ok) : ValidBatch s r := by
  cases hc : validBatchBool s r with
  | true => exact (validBatchBool_iff s r).mp hc
  | false =>
    have hN : ¬ (validBatchBool s r = true) := by simp [hc]
    have hRej : step s r = (.rejected, s) := by unfold step; rw [if_neg hN]
    have h1 : (step s r).1 = .rejected := by rw [hRej]
    rw [h1] at hOk
    cases hOk

theorem shift_sum_eq (s : State) (bal : AccountId → Int) (l : Leg)
    (hNodup : s.accounts.Nodup) (hSrc : l.source ∈ s.accounts) (hTgt : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have h1 : (shift bal l) = (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [h1, sumOver_add, sumOver_sub,
    sumOver_ite_eq hNodup l.source ((l.amount : Int)),
    sumOver_ite_eq hNodup l.target ((l.amount : Int))]
  simp [hSrc, hTgt]

theorem total_applyLegs_eq (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hNodup : s.accounts.Nodup) (hOk : LegsOk s bal ls) :
    sumOver s.accounts (applyLegs bal ls) = sumOver s.accounts bal := by
  induction ls generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    have hHead : LegOk s bal l := hOk.1
    have hTail : LegsOk s (shift bal l) ls := hOk.2
    obtain ⟨_, _, hSrc, hTgt, _⟩ := hHead
    have hEq : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [hEq, ih (shift bal l) hTail]
    exact shift_sum_eq s bal l hNodup hSrc hTgt

theorem shift_preserves (s : State) (bal : AccountId → Int) (l : Leg)
    (hBal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ (shift bal l) a := by
  obtain ⟨_, hNe, _, _, hLim⟩ := hOk
  intro a ha
  have hEq : (shift bal l) a = bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0) := rfl
  rw [hEq]
  by_cases hAS : a = l.source
  · subst hAS
    rw [if_pos rfl, if_neg hNe]
    omega
  · have hBase := hBal a ha
    by_cases hAT : a = l.target
    · subst hAT
      rw [if_neg hAS, if_pos rfl]
      omega
    · rw [if_neg hAS, if_neg hAT]
      omega

theorem apply_take_within (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hBal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegsOk s bal ls) :
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts → -(s.limit a : Int) ≤ applyLegs bal (ls.take k) a := by
  induction ls generalizing bal with
  | nil =>
    intro k a ha
    have hT : List.take k ([] : List Leg) = [] := by cases k <;> rfl
    rw [hT]
    exact hBal a ha
  | cons l ls ih =>
    intro k a ha
    have hHead : LegOk s bal l := hOk.1
    have hTail : LegsOk s (shift bal l) ls := hOk.2
    have hBal' : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ (shift bal l) b :=
      shift_preserves s bal l hBal hHead
    cases k with
    | zero => exact hBal a ha
    | succ n =>
      have hA : applyLegs bal (List.take (Nat.succ n) (l :: ls)) = applyLegs (shift bal l) (List.take n ls) := rfl
      rw [hA]
      exact ih (shift bal l) hBal' hTail n a ha

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  have hEq := step_ok_eq s r hV
  rw [hEq]

theorem req_atomicity : Atomicity step := by
  intro s r hN
  exact step_rej_eq s r hN

theorem req_single_leg : SingleLeg step := by
  intro s r l hLegs hOk
  have hV : ValidBatch s r := of_ok_valid s r hOk
  have hEq := step_ok_eq s r hV
  have hBal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := fun a => by rw [hEq]
  have hLegsOk : LegsOk s s.balance r.legs := hV.2.2.2
  rw [hLegs] at hLegsOk
  have hNe : l.source ≠ l.target := hLegsOk.1.2.1
  constructor
  · have h1 := hBal l.source
    rw [hLegs] at h1
    have hS : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := by
      show (shift s.balance l) l.source = _
      simp [shift, hNe]
    rw [hS] at h1
    exact h1
  · have h2 := hBal l.target
    rw [hLegs] at h2
    have hNS : l.target ≠ l.source := Ne.symm hNe
    have hT : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := by
      show (shift s.balance l) l.target = _
      simp [shift, hNS]
    rw [hT] at h2
    exact h2

theorem req_effects : Effects step := by
  intro s r hOk
  have hV := of_ok_valid s r hOk
  have hEq := step_ok_eq s r hV
  refine ⟨by rw [hEq], by rw [hEq], fun a => by rw [hEq]⟩

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hV := of_ok_valid s r hOk
  have hEq := step_ok_eq s r hV
  have hApp : (step s r).2.applied = r.batchId :: s.applied := by rw [hEq]
  constructor
  · intro x
    rw [hApp]
    simp
  · have hMem : r.batchId ∈ (step s r).2.applied := by rw [hApp]; simp
    have hNotValid : ¬ ValidBatch (step s r).2 r := fun hC => hC.2.2.1 hMem
    exact step_rej_eq _ _ hNotValid

theorem req_conservation : Conserves step := by
  intro s r hOk
  have hV := of_ok_valid s r hOk
  have hEq := step_ok_eq s r hV
  have hNodup : s.accounts.Nodup := hV.1
  have hLegsOk : LegsOk s s.balance r.legs := hV.2.2.2
  have hAcc : (step s r).2.accounts = s.accounts := by rw [hEq]
  have hBal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := fun a => by rw [hEq]
  have hTot : total (step s r).2 = sumOver s.accounts (applyLegs s.balance r.legs) := by
    unfold total
    rw [hAcc]
    exact sumOver_congr s.accounts _ _ (fun a _ => hBal a)
  rw [hTot]
  exact total_applyLegs_eq s s.balance r.legs hNodup hLegsOk

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hWL
  constructor
  · cases hc : validBatchBool s r with
    | true =>
      have hV : ValidBatch s r := (validBatchBool_iff s r).mp hc
      have hEq := step_ok_eq s r hV
      have hAcc : (step s r).2.accounts = s.accounts := by rw [hEq]
      have hLimEq : (step s r).2.limit = s.limit := by rw [hEq]
      have hBalEq : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := fun a => by rw [hEq]
      have hLegsOk : LegsOk s s.balance r.legs := hV.2.2.2
      have hPref := apply_take_within s s.balance r.legs (fun a ha => hWL a ha) hLegsOk
      intro a ha
      rw [hAcc] at ha
      have hTakeLen : r.legs.take r.legs.length = r.legs := by simp
      have hLe := hPref r.legs.length a ha
      rw [hTakeLen] at hLe
      rw [hLimEq, hBalEq]
      exact hLe
    | false =>
      have hN : ¬ (validBatchBool s r = true) := by simp [hc]
      have hRej : step s r = (.rejected, s) := by unfold step; rw [if_neg hN]
      have h2 : (step s r).2 = s := by rw [hRej]
      rw [h2]
      exact hWL
  · intro hOk k a ha
    have hV := of_ok_valid s r hOk
    have hLegsOk : LegsOk s s.balance r.legs := hV.2.2.2
    exact apply_take_within s s.balance r.legs (fun b hb => hWL b hb) hLegsOk k a ha

end Batch
