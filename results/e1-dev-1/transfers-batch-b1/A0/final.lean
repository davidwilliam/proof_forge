import Batch.Spec
import Batch.Lemmas

namespace Batch

def legOkBool (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && decide (l.source ≠ l.target) &&
    decide (l.source ∈ s.accounts) && decide (l.target ∈ s.accounts) &&
    decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int))

def legsOkBool (s : State) (bal : AccountId → Int) : List Leg → Bool
  | [] => true
  | l :: ls => legOkBool s bal l && legsOkBool s (shift bal l) ls

def nonemptyBool : List Leg → Bool
  | [] => false
  | _ :: _ => true

def validBool (s : State) (r : Request) : Bool :=
  decide (s.accounts.Nodup) && nonemptyBool r.legs &&
    decide (r.batchId ∉ s.applied) && legsOkBool s s.balance r.legs

def step : Impl := fun s r =>
  if validBool s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else
    (.rejected, s)

/-! Boolean reflection helpers -/

theorem nonempty_true_iff (l : List Leg) : nonemptyBool l = true ↔ l ≠ [] := by
  cases l with
  | nil => simp [nonemptyBool]
  | cons hd tl => simp [nonemptyBool]

theorem legOkBool_true_iff (s : State) (bal : AccountId → Int) (l : Leg) :
    legOkBool s bal l = true ↔ LegOk s bal l := by
  unfold legOkBool LegOk
  constructor
  · intro h
    have e1 : decide (0 < l.amount) = true := by
      cases h1 : decide (0 < l.amount) with
      | true => rfl
      | false => simp [h1] at h
    have e2 : decide (l.source ≠ l.target) = true := by
      cases h2 : decide (l.source ≠ l.target) with
      | true => rfl
      | false => simp [h2] at h
    have e3 : decide (l.source ∈ s.accounts) = true := by
      cases h3 : decide (l.source ∈ s.accounts) with
      | true => rfl
      | false => simp [h3] at h
    have e4 : decide (l.target ∈ s.accounts) = true := by
      cases h4 : decide (l.target ∈ s.accounts) with
      | true => rfl
      | false => simp [h4] at h
    have e5 : decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int)) = true := by
      cases h5 : decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int)) with
      | true => rfl
      | false => simp [h5] at h
    exact ⟨of_decide_eq_true e1, of_decide_eq_true e2, of_decide_eq_true e3,
      of_decide_eq_true e4, of_decide_eq_true e5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have e1 : decide (0 < l.amount) = true := by simp [h1]
    have e2 : decide (l.source ≠ l.target) = true := by simp [h2]
    have e3 : decide (l.source ∈ s.accounts) = true := by simp [h3]
    have e4 : decide (l.target ∈ s.accounts) = true := by simp [h4]
    have e5 : decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int)) = true := by simp [h5]
    simp [e1, e2, e3, e4, e5]

theorem legsOkBool_true_iff (s : State) (bal : AccountId → Int) (legs : List Leg) :
    legsOkBool s bal legs = true ↔ LegsOk s bal legs := by
  induction legs generalizing bal with
  | nil => simp [legsOkBool, LegsOk]
  | cons l ls ih =>
    simp only [legsOkBool, LegsOk]
    constructor
    · intro h
      have e1 : legOkBool s bal l = true := by
        cases h1 : legOkBool s bal l with
        | true => rfl
        | false => simp [h1] at h
      have e2 : legsOkBool s (shift bal l) ls = true := by
        cases h2 : legsOkBool s (shift bal l) ls with
        | true => rfl
        | false => simp [h2] at h
      exact ⟨(legOkBool_true_iff s bal l).mp e1, (ih _).mp e2⟩
    · rintro ⟨h1, h2⟩
      have e1 : legOkBool s bal l = true := (legOkBool_true_iff s bal l).mpr h1
      have e2 : legsOkBool s (shift bal l) ls = true := (ih _).mpr h2
      simp [e1, e2]

theorem validBool_true_iff (s : State) (r : Request) :
    validBool s r = true ↔ ValidBatch s r := by
  unfold validBool ValidBatch
  constructor
  · intro h
    have e1 : decide (s.accounts.Nodup) = true := by
      cases h1 : decide (s.accounts.Nodup) with
      | true => rfl
      | false => simp [h1] at h
    have e2 : nonemptyBool r.legs = true := by
      cases h2 : nonemptyBool r.legs with
      | true => rfl
      | false => simp [h2] at h
    have e3 : decide (r.batchId ∉ s.applied) = true := by
      cases h3 : decide (r.batchId ∉ s.applied) with
      | true => rfl
      | false => simp [h3] at h
    have e4 : legsOkBool s s.balance r.legs = true := by
      cases h4 : legsOkBool s s.balance r.legs with
      | true => rfl
      | false => simp [h4] at h
    exact ⟨of_decide_eq_true e1, (nonempty_true_iff _).mp e2,
      of_decide_eq_true e3, (legsOkBool_true_iff _ _ _).mp e4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have e1 : decide (s.accounts.Nodup) = true := by simp [h1]
    have e2 : nonemptyBool r.legs = true := (nonempty_true_iff _).mpr h2
    have e3 : decide (r.batchId ∉ s.applied) = true := by simp [h3]
    have e4 : legsOkBool s s.balance r.legs = true := (legsOkBool_true_iff _ _ _).mpr h4
    simp [e1, e2, e3, e4]

theorem validBool_false_of_not_valid (s : State) (r : Request) (h : ¬ ValidBatch s r) :
    validBool s r = false := by
  cases hvb : validBool s r with
  | true =>
    have hval := (validBool_true_iff s r).mp hvb
    have hcon : False := h hval
    cases hcon
  | false => rfl

theorem validBool_true_of_ok (s : State) (r : Request) (hok : (step s r).1 = .ok) :
    validBool s r = true := by
  cases hvb : validBool s r with
  | true => rfl
  | false =>
    have hstep : (step s r).1 = .rejected := by simp [step, hvb]
    rw [hstep] at hok
    simp at hok

theorem step_ok_eq (s : State) (r : Request) (hv : validBool s r = true) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  simp [step, hv]

theorem step_rej_eq (s : State) (r : Request) (hv : validBool s r = false) :
    step s r = (.rejected, s) := by
  simp [step, hv]

/-! Conservation helpers -/

theorem shift_sum (accts : List AccountId) (hnd : accts.Nodup) (bal : AccountId → Int)
    (l : Leg) (hs : l.source ∈ accts) (ht : l.target ∈ accts) :
    sumOver accts (shift bal l) = sumOver accts bal := by
  have h1 : sumOver accts (fun a => if a = l.source then (l.amount : Int) else 0)
      = if l.source ∈ accts then (l.amount : Int) else 0 :=
    sumOver_ite_eq hnd _ _
  have h2 : sumOver accts (fun a => if a = l.target then (l.amount : Int) else 0)
      = if l.target ∈ accts then (l.amount : Int) else 0 :=
    sumOver_ite_eq hnd _ _
  have hsub : sumOver accts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
      = sumOver accts bal - sumOver accts (fun a => if a = l.source then (l.amount : Int) else 0) :=
    sumOver_sub _ _ _
  have hadd : sumOver accts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0))
      + (if a = l.target then (l.amount : Int) else 0))
      = sumOver accts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
        + sumOver accts (fun a => if a = l.target then (l.amount : Int) else 0) :=
    sumOver_add _ _ _
  have heq : sumOver accts (shift bal l)
      = sumOver accts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0))
        + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [heq, hadd, hsub, h1, h2, if_pos hs, if_pos ht]
  omega

theorem applyLegs_sum (s : State) (hnd : s.accounts.Nodup) (bal : AccountId → Int)
    (legs : List Leg) (h : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    have hhead : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [hhead]
    simp only [LegsOk] at h
    obtain ⟨hl, htl⟩ := h
    have hs : l.source ∈ s.accounts := hl.2.2.1
    have ht : l.target ∈ s.accounts := hl.2.2.2.1
    have hsh := shift_sum s.accounts hnd bal l hs ht
    have hiht := ih (shift bal l) htl
    omega

/-! Limit helpers -/

theorem shift_preserves (s : State) (bal : AccountId → Int) (l : Leg)
    (hbal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hl : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  intro a ha
  have hne : l.source ≠ l.target := hl.2.1
  have hlim : -(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int) := hl.2.2.2.2
  have hbal_a : -(s.limit a : Int) ≤ bal a := hbal a ha
  by_cases hs : a = l.source
  · by_cases ht : a = l.target
    · have hcontra : l.source = l.target := hs.symm.trans ht
      have hfalse : False := hne hcontra
      cases hfalse
    · have eS : (if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) :=
        if_pos hs
      have eT : (if a = l.target then (l.amount : Int) else 0) = 0 :=
        if_neg ht
      have hshift : shift bal l a = bal a - (l.amount : Int) := by
        unfold shift
        rw [eS, eT]
        omega
      rw [hshift, hs]
      exact hlim
  · by_cases ht : a = l.target
    · have eS : (if a = l.source then (l.amount : Int) else 0) = 0 :=
        if_neg hs
      have eT : (if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) :=
        if_pos ht
      have hshift : shift bal l a = bal a + (l.amount : Int) := by
        unfold shift
        rw [eS, eT]
        omega
      rw [hshift]
      have hpos : (0 : Int) ≤ (l.amount : Int) := by omega
      omega
    · have eS : (if a = l.source then (l.amount : Int) else 0) = 0 :=
        if_neg hs
      have eT : (if a = l.target then (l.amount : Int) else 0) = 0 :=
        if_neg ht
      have hshift : shift bal l a = bal a := by
        unfold shift
        rw [eS, eT]
        omega
      rw [hshift]
      exact hbal_a

theorem take_length_eq (l : List Leg) : l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp [ih]

theorem prefix_bound (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hbal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hlegs : LegsOk s bal legs) :
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts →
      -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    have htake : (List.nil : List Leg).take k = [] := by cases k <;> rfl
    rw [htake]
    show -(s.limit a : Int) ≤ applyLegs bal [] a
    exact hbal a ha
  | cons l ls ih =>
    intro k a ha
    simp only [LegsOk] at hlegs
    obtain ⟨hl, htl⟩ := hlegs
    have hbal' := shift_preserves s bal l hbal hl
    cases k with
    | zero =>
      show -(s.limit a : Int) ≤ applyLegs bal ((l :: ls).take 0) a
      simp
      exact hbal a ha
    | succ k =>
      have htake : (l :: ls).take (Nat.succ k) = l :: (ls.take k) := rfl
      rw [htake]
      have happ : applyLegs bal (l :: ls.take k) = applyLegs (shift bal l) (ls.take k) := rfl
      rw [happ]
      exact ih (shift bal l) hbal' htl k a ha

/-! Required theorems -/

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hv : validBool s r = true := (validBool_true_iff s r).mpr h
  have hstep := step_ok_eq s r hv
  rw [hstep]

theorem req_atomicity : Atomicity step := by
  intro s r h
  have hv : validBool s r = false := validBool_false_of_not_valid s r h
  exact step_rej_eq s r hv

theorem req_single_leg : SingleLeg step := by
  intro s r l hrleg hok
  have hv : validBool s r = true := validBool_true_of_ok s r hok
  have hvalid := (validBool_true_iff s r).mp hv
  obtain ⟨hnd, hne, hnap, hlegs⟩ := hvalid
  rw [hrleg] at hlegs
  simp only [LegsOk] at hlegs
  obtain ⟨hl, htail⟩ := hlegs
  have hne2 : l.source ≠ l.target := hl.2.1
  have hne2s : l.target ≠ l.source := fun h => hne2 h.symm
  have h2 : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
    rw [step_ok_eq s r hv]
  have hrw : applyLegs s.balance r.legs = shift s.balance l := by
    rw [hrleg]
    rfl
  have hbal : ∀ a, (step s r).2.balance a = shift s.balance l a := by
    intro a
    rw [h2, hrw]
  constructor
  · rw [hbal l.source]
    simp [shift, hne2]
  · rw [hbal l.target]
    simp [shift, hne2s]

theorem req_effects : Effects step := by
  intro s r hok
  have hv : validBool s r = true := validBool_true_of_ok s r hok
  have hstep := step_ok_eq s r hv
  have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
  have hlim : (step s r).2.limit = s.limit := by rw [hstep]
  have hbal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    rw [hstep]
  exact ⟨hacc, hlim, hbal⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hv : validBool s r = true := validBool_true_of_ok s r hok
  have hstep := step_ok_eq s r hv
  have h2 : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
    rw [hstep]
  constructor
  · intro x
    rw [h2]
    simp
  · have hmem : r.batchId ∈ (step s r).2.applied := by
      rw [h2]
      simp
    have hdec : decide (r.batchId ∉ (step s r).2.applied) = false := by simp [hmem]
    have hv2 : validBool (step s r).2 r = false := by
      unfold validBool
      simp [hdec]
    have hrej := step_rej_eq (step s r).2 r hv2
    exact hrej

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv : validBool s r = true := validBool_true_of_ok s r hok
  have hvalid := (validBool_true_iff s r).mp hv
  obtain ⟨hnd, hne, hnap, hlegs⟩ := hvalid
  have hstep := step_ok_eq s r hv
  have hsum := applyLegs_sum s hnd s.balance r.legs hlegs
  have htot : total (step s r).2 = total s := by
    rw [hstep]
    unfold total
    simp only
    exact hsum
  exact htot

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hwl
  constructor
  · cases hvb : validBool s r with
    | false =>
      have hstep := step_rej_eq s r hvb
      rw [hstep]
      exact hwl
    | true =>
      have hvalid := (validBool_true_iff s r).mp hvb
      obtain ⟨hnd, hne, hnap, hlegs⟩ := hvalid
      have hstep := step_ok_eq s r hvb
      have h2 : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
        rw [hstep]
      have hacc : (step s r).2.accounts = s.accounts := by rw [h2]
      have hlim_eq : (step s r).2.limit = s.limit := by rw [h2]
      have hbal_eq : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
        intro a
        rw [h2]
      intro a ha
      have ha' : a ∈ s.accounts := hacc ▸ ha
      have hpre := prefix_bound s s.balance r.legs (fun a ha => hwl a ha) hlegs r.legs.length a ha'
      have htake : r.legs.take r.legs.length = r.legs := take_length_eq r.legs
      rw [htake] at hpre
      have hlim_a : (step s r).2.limit a = s.limit a := by rw [hlim_eq]
      rw [hlim_a, hbal_eq]
      exact hpre
  · intro hok k a ha
    have hv : validBool s r = true := validBool_true_of_ok s r hok
    have hvalid := (validBool_true_iff s r).mp hv
    obtain ⟨hnd, hne, hnap, hlegs⟩ := hvalid
    exact prefix_bound s s.balance r.legs (fun a ha => hwl a ha) hlegs k a ha

end Batch
