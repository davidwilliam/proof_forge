import Batch.Spec
import Batch.Lemmas
namespace Batch

instance decLegOk (s : State) (bal : AccountId → Int) (l : Leg) : Decidable (LegOk s bal l) := by
  unfold LegOk
  infer_instance

def decLegsOkAux (s : State) (bal : AccountId → Int) (ls : List Leg) : Decidable (LegsOk s bal ls) :=
  match ls with
  | [] => isTrue True.intro
  | l :: ls' =>
    match decLegOk s bal l with
    | isTrue h1 =>
      match decLegsOkAux s (shift bal l) ls' with
      | isTrue h2 => isTrue ⟨h1, h2⟩
      | isFalse h2 => isFalse (fun h => h2 h.2)
    | isFalse h1 => isFalse (fun h => h1 h.1)

instance decLegsOk (s : State) (bal : AccountId → Int) (ls : List Leg) : Decidable (LegsOk s bal ls) :=
  decLegsOkAux s bal ls

instance decValidBatch (s : State) (r : Request) : Decidable (ValidBatch s r) := by
  unfold ValidBatch
  infer_instance

def step : Impl := fun s r =>
  if ValidBatch s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else
    (.rejected, s)

theorem step_eq_ok {s : State} {r : Request} (h : ValidBatch s r) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  unfold step
  rw [if_pos h]

theorem step_eq_rej {s : State} {r : Request} (h : ¬ ValidBatch s r) :
    step s r = (.rejected, s) := by
  unfold step
  rw [if_neg h]

theorem valid_of_ok {s : State} {r : Request} (h : (step s r).1 = .ok) : ValidBatch s r := by
  have hem : ValidBatch s r ∨ ¬ ValidBatch s r :=
    if hv : ValidBatch s r then Or.inl hv else Or.inr hv
  cases hem with
  | inl hv => exact hv
  | inr hn =>
    have hstep : step s r = (.rejected, s) := step_eq_rej hn
    rw [hstep] at h
    simp at h

theorem shift_sum (s : State) (bal : AccountId → Int) (l : Leg)
    (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts)
    (hn : s.accounts.Nodup) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have h1 : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by
    rw [sumOver_ite_eq hn]
    simp [hs]
  have h2 : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by
    rw [sumOver_ite_eq hn]
    simp [ht]
  have hcongr : ∀ a ∈ s.accounts, shift bal l a =
      (bal a - (if a = l.source then (l.amount : Int) else 0)) +
      (if a = l.target then (l.amount : Int) else 0) := by
    intro a _
    rfl
  have h3 := sumOver_congr s.accounts (shift bal l)
    (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) hcongr
  have h4 : sumOver s.accounts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0))
      = sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
        + sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) := by
    rw [sumOver_add]
  have h5 : sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
      = sumOver s.accounts bal - sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) := by
    rw [sumOver_sub]
  rw [h3, h4, h5, h1, h2]
  omega

theorem applyLegs_sum (s : State) (legs : List Leg) : ∀ (bal : AccountId → Int),
    LegsOk s bal legs → s.accounts.Nodup → sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs with
  | nil =>
    intro bal hlegs hn
    rfl
  | cons l ls ih =>
    intro bal hlegs hn
    have hhead : LegOk s bal l := hlegs.1
    have htail : LegsOk s (shift bal l) ls := hlegs.2
    have hhs : l.source ∈ s.accounts := hhead.2.2.1
    have hht : l.target ∈ s.accounts := hhead.2.2.2.1
    have hih : sumOver s.accounts (applyLegs (shift bal l) ls) = sumOver s.accounts (shift bal l) :=
      ih (shift bal l) htail hn
    have hsh : sumOver s.accounts (shift bal l) = sumOver s.accounts bal :=
      shift_sum s bal l hhs hht hn
    have heq : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [heq, hih]
    exact hsh

theorem shift_within (s : State) (bal : AccountId → Int) (l : Leg)
    (hok : LegOk s bal l)
    (hw : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  intro a ha
  have hne : l.source ≠ l.target := hok.2.1
  have hsrc_le : -(s.limit l.source : Int) ≤ bal l.source - l.amount := hok.2.2.2.2
  have hle_a : -(s.limit a : Int) ≤ bal a := hw a ha
  by_cases heq : a = l.source
  · subst heq
    have hifT : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) :=
      if_pos rfl
    have hifF : (if l.source = l.target then (l.amount : Int) else 0) = 0 :=
      if_neg hne
    have hsh : shift bal l l.source = bal l.source - (l.amount : Int) := by
      unfold shift
      rw [hifT, hifF]
      omega
    rw [hsh]
    exact hsrc_le
  · have hifF1 : (if a = l.source then (l.amount : Int) else 0) = 0 :=
      if_neg heq
    by_cases ht : a = l.target
    · have hifT2 : (if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) :=
        if_pos ht
      have hsh : shift bal l a = bal a + (l.amount : Int) := by
        unfold shift
        rw [hifF1, hifT2]
        omega
      rw [hsh]
      omega
    · have hifF2 : (if a = l.target then (l.amount : Int) else 0) = 0 :=
        if_neg ht
      have hsh : shift bal l a = bal a := by
        unfold shift
        rw [hifF1, hifF2]
        omega
      rw [hsh]
      exact hle_a

theorem applyLegs_within (s : State) (legs : List Leg) : ∀ (bal : AccountId → Int),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) → LegsOk s bal legs →
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal legs a := by
  induction legs with
  | nil =>
    intro bal hw hlegs a ha
    exact hw a ha
  | cons l ls ih =>
    intro bal hw hlegs a ha
    have hhead : LegOk s bal l := hlegs.1
    have htail : LegsOk s (shift bal l) ls := hlegs.2
    have hw' : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ shift bal l b :=
      shift_within s bal l hhead hw
    have heq : applyLegs bal (l :: ls) a = applyLegs (shift bal l) ls a := rfl
    rw [heq]
    exact ih (shift bal l) hw' htail a ha

theorem legsOk_take (s : State) (legs : List Leg) : ∀ (bal : AccountId → Int) (k : Nat),
    LegsOk s bal legs → LegsOk s bal (legs.take k) := by
  induction legs with
  | nil =>
    intro bal k h
    cases k with
    | zero => exact True.intro
    | succ n => exact True.intro
  | cons l ls ih =>
    intro bal k h
    cases k with
    | zero => exact True.intro
    | succ n =>
      have heq : (l :: ls).take (Nat.succ n) = l :: (ls.take n) := rfl
      rw [heq]
      exact ⟨h.1, ih (shift bal l) n h.2⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hstep := step_eq_ok h
  rw [hstep]

theorem req_atomicity : Atomicity step := by
  intro s r h
  exact step_eq_rej h

theorem req_single_leg : SingleLeg step := by
  intro s r l hrleg hok
  have hvalid : ValidBatch s r := valid_of_ok hok
  have hlegs : LegsOk s s.balance r.legs := hvalid.2.2.2
  rw [hrleg] at hlegs
  have hleg : LegOk s s.balance l := hlegs.1
  have hne : l.source ≠ l.target := hleg.2.1
  have hstep := step_eq_ok hvalid
  have h2eq : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
    rw [hstep]
  have hbal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    rw [h2eq]
  have hne' : l.target ≠ l.source := fun hh => hne hh.symm
  have hsrc_shift : shift s.balance l l.source = s.balance l.source - (l.amount : Int) := by
    unfold shift
    have h1 : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
    have h2 : (if l.source = l.target then (l.amount : Int) else 0) = 0 := if_neg hne
    rw [h1, h2]
    omega
  have htgt_shift : shift s.balance l l.target = s.balance l.target + (l.amount : Int) := by
    unfold shift
    have h1 : (if l.target = l.source then (l.amount : Int) else 0) = 0 := if_neg hne'
    have h2 : (if l.target = l.target then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
    rw [h1, h2]
    omega
  have hsrc_app : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := hsrc_shift
  have htgt_app : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := htgt_shift
  constructor
  · have e := hbal l.source
    rw [hrleg] at e
    rw [hsrc_app] at e
    exact e
  · have e := hbal l.target
    rw [hrleg] at e
    rw [htgt_app] at e
    exact e

theorem req_effects : Effects step := by
  intro s r hok
  have hvalid : ValidBatch s r := valid_of_ok hok
  have hstep := step_eq_ok hvalid
  refine ⟨?_, ?_, ?_⟩
  · rw [hstep]
  · rw [hstep]
  · intro a
    rw [hstep]

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hvalid : ValidBatch s r := valid_of_ok hok
  have hstep := step_eq_ok hvalid
  have h2eq : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
    rw [hstep]
  constructor
  · intro x
    rw [h2eq]
    simp
  · have hmem : r.batchId ∈ (step s r).2.applied := by
      rw [h2eq]
      simp
    have hneg : ¬ ValidBatch (step s r).2 r := fun hh => hh.2.2.1 hmem
    exact step_eq_rej hneg

theorem req_conservation : Conserves step := by
  intro s r hok
  have hvalid : ValidBatch s r := valid_of_ok hok
  have hnodup : s.accounts.Nodup := hvalid.1
  have hlegs : LegsOk s s.balance r.legs := hvalid.2.2.2
  have hstep := step_eq_ok hvalid
  have h2eq : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
    rw [hstep]
  have hacc : (step s r).2.accounts = s.accounts := by
    rw [hstep]
  have hbal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    rw [h2eq]
  show total (step s r).2 = total s
  unfold total
  rw [hacc]
  have hcon : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (applyLegs s.balance r.legs) :=
    sumOver_congr s.accounts (step s r).2.balance (applyLegs s.balance r.legs) (fun a _ => hbal a)
  rw [hcon]
  exact applyLegs_sum s r.legs s.balance hlegs hnodup

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hw
  constructor
  · have hem : ValidBatch s r ∨ ¬ ValidBatch s r :=
      if hv : ValidBatch s r then Or.inl hv else Or.inr hv
    cases hem with
    | inl hvalid =>
      have hstep := step_eq_ok hvalid
      have h2eq : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
        rw [hstep]
      have hlegs : LegsOk s s.balance r.legs := hvalid.2.2.2
      have hfin := applyLegs_within s r.legs s.balance hw hlegs
      rw [h2eq]
      exact hfin
    | inr hn =>
      have hstep := step_eq_rej hn
      have h2eq : (step s r).2 = s := by
        rw [hstep]
      rw [h2eq]
      exact hw
  · intro hok k a ha
    have hvalid : ValidBatch s r := valid_of_ok hok
    have hlegs : LegsOk s s.balance r.legs := hvalid.2.2.2
    have ht : LegsOk s s.balance (r.legs.take k) := legsOk_take s r.legs s.balance k hlegs
    have hfin := applyLegs_within s (r.legs.take k) s.balance hw ht
    exact hfin a ha

end Batch
