import Batch.Spec
import Batch.Lemmas

namespace Batch

def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && (decide (l.source ≠ l.target) && (decide (l.source ∈ s.accounts) && (decide (l.target ∈ s.accounts) && decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int)))))

def legsNonempty : List Leg → Bool
  | [] => false
  | _ :: _ => true

def checkLegs (s : State) (bal : AccountId → Int) : List Leg → Bool
  | [] => true
  | l :: ls => legAllowed s bal l && checkLegs s (shift bal l) ls

def validBool (s : State) (r : Request) : Bool :=
  decide s.accounts.Nodup && (legsNonempty r.legs && (decide (r.batchId ∉ s.applied) && checkLegs s s.balance r.legs))

def step : Impl := fun s r =>
  if validBool s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else
    (.rejected, s)

theorem legAllowed_correct (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp

theorem legsNonempty_correct (legs : List Leg) :
    legsNonempty legs = true ↔ legs ≠ [] := by
  cases legs with
  | nil => simp [legsNonempty]
  | cons hd tl => simp [legsNonempty]

theorem checkLegs_correct (s : State) (bal : AccountId → Int) (legs : List Leg) :
    checkLegs s bal legs = true ↔ LegsOk s bal legs := by
  induction legs generalizing bal with
  | nil => simp [checkLegs, LegsOk]
  | cons l ls ih => simp [checkLegs, LegsOk, legAllowed_correct, ih, Bool.and_eq_true]

theorem validBool_correct (s : State) (r : Request) :
    validBool s r = true ↔ ValidBatch s r := by
  unfold validBool ValidBatch
  simp only [Bool.and_eq_true, decide_eq_true_eq, legsNonempty_correct, checkLegs_correct]

theorem validBool_of_ok (s : State) (r : Request) (h : (step s r).1 = .ok) :
    validBool s r = true := by
  cases hB : validBool s r
  · have hStep : (step s r).1 = .rejected := by
      unfold step
      simp [hB]
    rw [hStep] at h
    cases h
  · rfl

theorem sum_shift (s : State) (bal : AccountId → Int) (l : Leg)
    (hnodup : s.accounts.Nodup) (hsrc : l.source ∈ s.accounts)
    (htgt : l.target ∈ s.accounts) (hneq : l.source ≠ l.target) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have hcongr : ∀ (a : AccountId), a ∈ s.accounts → shift bal l a = (bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0)) :=
    fun a _ => rfl
  rw [sumOver_congr _ _ _ hcongr]
  have hadd : sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0)) = sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) + sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) :=
    sumOver_add _ _ _
  rw [hadd]
  have hsub : sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) = sumOver s.accounts bal - sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) :=
    sumOver_sub _ _ _
  rw [hsub]
  have hs : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by
    rw [sumOver_ite_eq hnodup l.source (l.amount : Int)]
    simp [hsrc]
  have ht : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by
    rw [sumOver_ite_eq hnodup l.target (l.amount : Int)]
    simp [htgt]
  rw [hs, ht]
  omega

theorem applyLegs_sum (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hnodup : s.accounts.Nodup) (hoks : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    have hhead : LegOk s bal l := hoks.1
    have htail : LegsOk s (shift bal l) ls := hoks.2
    obtain ⟨_, hneq, hsrc, htgt, _⟩ := hhead
    have hstep : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [hstep]
    rw [ih _ htail]
    exact sum_shift s bal l hnodup hsrc htgt hneq

theorem shift_within (s : State) (bal : AccountId → Int) (l : Leg) (a : AccountId)
    (hmem : a ∈ s.accounts)
    (hbal : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ bal b)
    (hok : LegOk s bal l) :
    -(s.limit a : Int) ≤ shift bal l a := by
  obtain ⟨hpos, hneq, _, _, hle⟩ := hok
  unfold shift
  by_cases h1 : a = l.source
  · subst h1
    simp [hneq]
    simpa using hle
  · by_cases h2 : a = l.target
    · subst h2
      simp [h1]
      have hle2 := hbal l.target hmem
      have hc : (0 : Int) ≤ (l.amount : Int) := by omega
      omega
    · simp [h1, h2]
      exact hbal a hmem

theorem applyLegs_take_within_aux (s : State) (bal : AccountId → Int) (legs : List Leg) :
    (∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ bal b) →
    LegsOk s bal legs →
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts → -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro hbal hoks k a ha
    cases k with
    | zero => exact hbal a ha
    | succ n => exact hbal a ha
  | cons l ls ih =>
    intro hbal hoks k a ha
    cases k with
    | zero => exact hbal a ha
    | succ n =>
      have hhead : LegOk s bal l := hoks.1
      have htail : LegsOk s (shift bal l) ls := hoks.2
      have htake : (l :: ls).take (n + 1) = l :: (ls.take n) := rfl
      rw [htake]
      have happly : applyLegs bal (l :: ls.take n) = applyLegs (shift bal l) (ls.take n) := rfl
      rw [happly]
      have hshift : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ shift bal l b :=
        fun b hb => shift_within s bal l b hb hbal hhead
      exact ih (shift bal l) hshift htail n a ha

theorem take_length_eq_self (l : List Leg) : l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h1 : (x :: xs).take ((x :: xs).length) = x :: (xs.take xs.length) := rfl
    rw [h1, ih]

theorem step_ok_fst (s : State) (r : Request) (hb : validBool s r = true) :
    (step s r).1 = .ok := by
  unfold step
  simp [hb]

theorem step_ok_snd (s : State) (r : Request) (hb : validBool s r = true) :
    (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
  unfold step
  simp [hb]

theorem step_rej (s : State) (r : Request) (hb : validBool s r = false) :
    step s r = (.rejected, s) := by
  unfold step
  simp [hb]

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hb : validBool s r = true := (validBool_correct s r).mpr h
  exact step_ok_fst s r hb

theorem req_atomicity : Atomicity step := by
  intro s r h
  have hb : validBool s r = false := by
    cases hB : validBool s r
    · rfl
    · have hV := (validBool_correct s r).mp hB
      exact absurd hV h
  exact step_rej s r hb

theorem req_single_leg : SingleLeg step := by
  intro s r l hrlegs hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hV : ValidBatch s r := (validBool_correct s r).mp hb
  have hLegs : LegsOk s s.balance r.legs := hV.2.2.2
  rw [hrlegs] at hLegs
  have hLegOk : LegOk s s.balance l := hLegs.1
  obtain ⟨_, hneq, _, _, _⟩ := hLegOk
  have hSnd := step_ok_snd s r hb
  have hBal : ∀ (a : AccountId), (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    rw [hSnd]
  have hBal2 : ∀ (a : AccountId), (step s r).2.balance a = applyLegs s.balance [l] a := by
    intro a
    rw [hBal a, hrlegs]
  have hsrc_eq : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := by
    show shift s.balance l l.source = _
    unfold shift
    simp [hneq]
  have htgt_eq : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := by
    show shift s.balance l l.target = _
    simp [shift, Ne.symm hneq]
  constructor
  · rw [hBal2 l.source, hsrc_eq]
  · rw [hBal2 l.target, htgt_eq]

theorem req_effects : Effects step := by
  intro s r hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hSnd := step_ok_snd s r hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hSnd]
  · rw [hSnd]
  · intro a
    rw [hSnd]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hSnd := step_ok_snd s r hb
  have hApp : (step s r).2.applied = r.batchId :: s.applied := by
    rw [hSnd]
  constructor
  · intro x
    rw [hApp]
    simp
  · have hMem : r.batchId ∈ (step s r).2.applied := by
      rw [hApp]
      simp
    have hNotValid : ¬ ValidBatch (step s r).2 r := by
      intro hV
      have hNotIn : r.batchId ∉ (step s r).2.applied := hV.2.2.1
      exact hNotIn hMem
    have hB2_false : validBool (step s r).2 r = false := by
      cases hB2 : validBool (step s r).2 r
      · rfl
      · have hV := (validBool_correct (step s r).2 r).mp hB2
        exact absurd hV hNotValid
    exact step_rej (step s r).2 r hB2_false

theorem req_conservation : Conserves step := by
  intro s r hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hV : ValidBatch s r := (validBool_correct s r).mp hb
  obtain ⟨hnodup, _, _, hoks⟩ := hV
  have hSnd := step_ok_snd s r hb
  have hAcc : (step s r).2.accounts = s.accounts := by
    rw [hSnd]
  have hBal : ∀ (a : AccountId), (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    rw [hSnd]
  unfold total
  rw [hAcc]
  have hcongr : ∀ (a : AccountId), a ∈ s.accounts → (step s r).2.balance a = applyLegs s.balance r.legs a :=
    fun a _ => hBal a
  rw [sumOver_congr _ _ _ hcongr]
  exact applyLegs_sum s s.balance r.legs hnodup hoks

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hW
  constructor
  · cases hB : validBool s r
    · have hEq : (step s r).2 = s := by
        have hR := step_rej s r hB
        rw [hR]
      rw [hEq]
      exact hW
    · have hV : ValidBatch s r := (validBool_correct s r).mp hB
      obtain ⟨_, _, _, hoks⟩ := hV
      have hSnd := step_ok_snd s r hB
      have hAcc : (step s r).2.accounts = s.accounts := by
        rw [hSnd]
      have hLim : (step s r).2.limit = s.limit := by
        rw [hSnd]
      have hBal : ∀ (a : AccountId), (step s r).2.balance a = applyLegs s.balance r.legs a := by
        intro a
        rw [hSnd]
      intro a ha
      rw [hAcc] at ha
      rw [hLim, hBal]
      have hbase : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ s.balance b :=
        fun b hb => hW b hb
      have hPref := applyLegs_take_within_aux s s.balance r.legs hbase hoks r.legs.length a ha
      rw [take_length_eq_self] at hPref
      exact hPref
  · intro hok k a ha
    have hb : validBool s r = true := validBool_of_ok s r hok
    have hV : ValidBatch s r := (validBool_correct s r).mp hb
    obtain ⟨_, _, _, hoks⟩ := hV
    have hbase : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ s.balance b :=
      fun b hb2 => hW b hb2
    exact applyLegs_take_within_aux s s.balance r.legs hbase hoks k a ha

end Batch
