import Batch.Spec
import Batch.Lemmas
namespace Batch

def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && decide (l.source ≠ l.target) &&
  decide (l.source ∈ s.accounts) &&
  decide (l.target ∈ s.accounts) &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int))

theorem legAllowed_true (s : State) (bal : AccountId → Int) (l : Leg) :
    (legAllowed s bal l = true) ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

def applyAll (s : State) : (AccountId → Int) → List Leg → Option (AccountId → Int)
  | bal, [] => some bal
  | bal, l :: ls =>
    if legAllowed s bal l then applyAll s (shift bal l) ls else none

theorem applyAll_of_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : LegsOk s bal legs) : applyAll s bal legs = some (applyLegs bal legs) := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hHead, hTail⟩ := h
    have hAllow : legAllowed s bal l = true := (legAllowed_true s bal l).mpr hHead
    have eA : applyAll s bal (l :: ls) = applyAll s (shift bal l) ls := by
      simp [applyAll, hAllow]
    have eL : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [eA, eL, ih _ hTail]

theorem LegsOk_of_applyAll_some (s : State) (bal : AccountId → Int) (legs : List Leg)
    (bal' : AccountId → Int) (h : applyAll s bal legs = some bal') :
    LegsOk s bal legs ∧ bal' = applyLegs bal legs := by
  induction legs generalizing bal bal' with
  | nil =>
    simp [applyAll] at h
    subst h
    constructor
    · trivial
    · rfl
  | cons l ls ih =>
    have eA : applyAll s bal (l :: ls) =
        (if legAllowed s bal l then applyAll s (shift bal l) ls else none) := by
      simp [applyAll]
    rw [eA] at h
    cases hB : legAllowed s bal l with
    | true =>
      simp [hB] at h
      obtain ⟨hTail, hBal⟩ := ih _ _ h
      have hHead : LegOk s bal l := (legAllowed_true s bal l).mp hB
      constructor
      · exact ⟨hHead, hTail⟩
      · have eL : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
        rw [eL, ← hBal]
    | false =>
      simp [hB] at h

theorem applyAll_eq_none_of_not_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : ¬ LegsOk s bal legs) : applyAll s bal legs = none := by
  cases he : applyAll s bal legs with
  | some bal' =>
    have hOk := (LegsOk_of_applyAll_some s bal legs bal' he).1
    exact absurd hOk h
  | none => rfl

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied then
    match applyAll s s.balance r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

theorem step_of_valid (s : State) (r : Request) (h : ValidBatch s r) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  obtain ⟨hNodup, hNe, hNotMem, hLegs⟩ := h
  have hOuter : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    ⟨hNodup, hNe, hNotMem⟩
  have hApply : applyAll s s.balance r.legs = some (applyLegs s.balance r.legs) :=
    applyAll_of_LegsOk s _ _ hLegs
  unfold step
  simp [hOuter, hApply]

theorem step_of_invalid (s : State) (r : Request) (h : ¬ ValidBatch s r) :
    step s r = (.rejected, s) := by
  by_cases hOuter : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hLegs : ¬ LegsOk s s.balance r.legs := by
      intro hL
      exact h ⟨hOuter.1, hOuter.2.1, hOuter.2.2, hL⟩
    have hNone : applyAll s s.balance r.legs = none :=
      applyAll_eq_none_of_not_LegsOk _ _ _ hLegs
    unfold step
    simp [hOuter, hNone]
  · unfold step
    simp [hOuter]

theorem valid_of_ok (s : State) (r : Request) (hOk : (step s r).1 = .ok) :
    ValidBatch s r := by
  by_cases hOuter : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · cases he : applyAll s s.balance r.legs with
    | none =>
      have hStep : step s r = (.rejected, s) := by
        unfold step
        simp [hOuter, he]
      have hFst : (step s r).1 = .rejected := by rw [hStep]
      rw [hFst] at hOk
      contradiction
    | some bal' =>
      have hRes := LegsOk_of_applyAll_some s s.balance r.legs bal' he
      exact ⟨hOuter.1, hOuter.2.1, hOuter.2.2, hRes.1⟩
  · have hStep : step s r = (.rejected, s) := by
      unfold step
      simp [hOuter]
    have hFst : (step s r).1 = .rejected := by rw [hStep]
    rw [hFst] at hOk
    contradiction

theorem shift_sum (s : State) (bal : AccountId → Int) (l : Leg)
    (hNodup : s.accounts.Nodup) (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have hAdd := sumOver_add s.accounts
    (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
    (fun a => if a = l.target then (l.amount : Int) else 0)
  have hSub := sumOver_sub s.accounts bal
    (fun a => if a = l.source then (l.amount : Int) else 0)
  have hSrc := sumOver_ite_eq hNodup l.source (l.amount : Int)
  have hTgt := sumOver_ite_eq hNodup l.target (l.amount : Int)
  have eShift : sumOver s.accounts (shift bal l) =
      (sumOver s.accounts bal - sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0))
      + sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) := by
    have h1 : sumOver s.accounts (shift bal l) =
        sumOver s.accounts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0))
          + (if a = l.target then (l.amount : Int) else 0)) := rfl
    rw [h1, hAdd, hSub]
  have hsEq : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by
    rw [hSrc]
    simp [hs]
  have htEq : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by
    rw [hTgt]
    simp [ht]
  rw [eShift, hsEq, htEq]
  omega

theorem applyLegs_sum (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hNodup : s.accounts.Nodup) (hOk : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hHead, hTail⟩ := hOk
    have hs : l.source ∈ s.accounts := hHead.2.2.1
    have ht : l.target ∈ s.accounts := hHead.2.2.2.1
    have e : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [e, ih _ hTail, shift_sum s bal l hNodup hs ht]

theorem shift_within (s : State) (bal : AccountId → Int) (l : Leg)
    (hW : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) (hOk : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  obtain ⟨_, hNe, _, _, hFloor⟩ := hOk
  intro a ha
  have hWa : -(s.limit a : Int) ≤ bal a := hW a ha
  have hAmt : (0 : Int) ≤ (l.amount : Int) := by omega
  by_cases hAS : a = l.source
  · subst hAS
    have e2 : (if l.source = l.target then (l.amount : Int) else 0) = 0 :=
      if_neg hNe
    have hShift : shift bal l l.source = bal l.source - (l.amount : Int) := by
      unfold shift
      simp [e2]
    rw [hShift]
    exact hFloor
  · have e1 : (if a = l.source then (l.amount : Int) else 0) = 0 := if_neg hAS
    have hPos : (0 : Int) ≤ (if a = l.target then (l.amount : Int) else 0) := by
      by_cases hAT : a = l.target
      · rw [if_pos hAT]
        exact hAmt
      · rw [if_neg hAT]
        omega
    have hShift : shift bal l a = bal a - 0 + (if a = l.target then (l.amount : Int) else 0) := by
      unfold shift
      rw [e1]
    rw [hShift]
    omega

theorem applyLegs_within (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hW : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) (hOk : LegsOk s bal legs) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal legs a := by
  induction legs generalizing bal with
  | nil =>
    intro a ha
    show -(s.limit a : Int) ≤ bal a
    exact hW a ha
  | cons l ls ih =>
    obtain ⟨hHead, hTail⟩ := hOk
    have hW' := shift_within s bal l hW hHead
    have e : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    intro a ha
    rw [e]
    exact ih _ hW' hTail a ha

theorem legs_within_take_aux (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hW : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) (hOk : LegsOk s bal legs) :
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts →
    -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    simp only [List.take_nil]
    show -(s.limit a : Int) ≤ bal a
    exact hW a ha
  | cons l ls ih =>
    obtain ⟨hHead, hTail⟩ := hOk
    intro k
    cases k with
    | zero =>
      intro a ha
      simp only [List.take_zero]
      show -(s.limit a : Int) ≤ bal a
      exact hW a ha
    | succ n =>
      intro a ha
      have eTake : (l :: ls).take (n + 1) = l :: (ls.take n) := rfl
      rw [eTake]
      have eApp : applyLegs bal (l :: (ls.take n)) = applyLegs (shift bal l) (ls.take n) := rfl
      rw [eApp]
      have hW' := shift_within s bal l hW hHead
      exact ih _ hW' hTail n a ha

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hV
  have hStep := step_of_valid s r hV
  rw [hStep]

theorem req_atomicity : Atomicity step := by
  intro s r hN
  exact step_of_invalid s r hN

theorem req_single_leg : SingleLeg step := by
  intro s r l hLegs hOk
  have hV := valid_of_ok s r hOk
  have hStep := step_of_valid s r hV
  have hBal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    rw [hStep]
  have hLegsOk : LegsOk s s.balance [l] := hLegs ▸ hV.2.2.2
  have hBalL : ∀ a, (step s r).2.balance a = applyLegs s.balance [l] a := hLegs ▸ hBal
  have hLegOk : LegOk s s.balance l := hLegsOk.1
  obtain ⟨_, hNe, _, _, _⟩ := hLegOk
  have hNe' : l.target ≠ l.source := fun h => hNe h.symm
  have hS := hBalL l.source
  have hT := hBalL l.target
  have eS : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := by
    have hSh : shift s.balance l l.source = s.balance l.source - (l.amount : Int) := by
      unfold shift
      simp [hNe]
    exact hSh
  have eT : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := by
    have hSh : shift s.balance l l.target = s.balance l.target + (l.amount : Int) := by
      unfold shift
      simp [hNe']
    exact hSh
  rw [eS] at hS
  rw [eT] at hT
  exact ⟨hS, hT⟩

theorem req_effects : Effects step := by
  intro s r hOk
  have hV := valid_of_ok s r hOk
  have hStep := step_of_valid s r hV
  refine ⟨?_, ?_, ?_⟩
  · rw [hStep]
  · rw [hStep]
  · intro a
    rw [hStep]

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  have hV := valid_of_ok s r hOk
  have hStep := step_of_valid s r hV
  have h2eq : (step s r).2 =
      { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
    rw [hStep]
  constructor
  · intro x
    rw [h2eq]
    simp
  · have hMem : r.batchId ∈ (step s r).2.applied := by
      rw [h2eq]
      simp
    have hNotValid : ¬ ValidBatch (step s r).2 r := fun hC => hC.2.2.1 hMem
    have hRej := step_of_invalid _ _ hNotValid
    exact hRej

theorem req_conservation : Conserves step := by
  intro s r hOk
  have hV := valid_of_ok s r hOk
  have hStep := step_of_valid s r hV
  have hNodup : s.accounts.Nodup := hV.1
  have hLegs : LegsOk s s.balance r.legs := hV.2.2.2
  have hSum := applyLegs_sum s s.balance r.legs hNodup hLegs
  have hAcc : (step s r).2.accounts = s.accounts := by rw [hStep]
  have hBal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    rw [hStep]
  have hTot2 : total (step s r).2 = sumOver s.accounts (applyLegs s.balance r.legs) := by
    unfold total
    rw [hAcc]
    exact sumOver_congr _ _ _ (fun a _ => hBal a)
  have hTot : total s = sumOver s.accounts s.balance := rfl
  rw [hTot2, hTot, hSum]

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hW
  by_cases hOuter : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · cases he : applyAll s s.balance r.legs with
    | none =>
      have hStep : step s r = (.rejected, s) := by
        unfold step
        simp [hOuter, he]
      constructor
      · rw [hStep]
        exact hW
      · intro hOk
        have hFst : (step s r).1 = .rejected := by rw [hStep]
        rw [hFst] at hOk
        contradiction
    | some bal' =>
      have hRes := LegsOk_of_applyAll_some s s.balance r.legs bal' he
      have hLegs : LegsOk s s.balance r.legs := hRes.1
      have hBalEq : bal' = applyLegs s.balance r.legs := hRes.2
      have hStep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
        unfold step
        simp [hOuter, he, hBalEq]
      constructor
      · rw [hStep]
        intro a ha
        exact applyLegs_within s s.balance r.legs hW hLegs a ha
      · intro _ k a ha
        exact legs_within_take_aux s s.balance r.legs hW hLegs k a ha
  · have hStep : step s r = (.rejected, s) := by
      unfold step
      simp [hOuter]
    constructor
    · rw [hStep]
      exact hW
    · intro hOk
      have hFst : (step s r).1 = .rejected := by rw [hStep]
      rw [hFst] at hOk
      contradiction

end Batch
