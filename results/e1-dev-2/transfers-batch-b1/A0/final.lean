import Batch.Spec
import Batch.Lemmas
namespace Batch

def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && decide (l.source ≠ l.target) &&
  decide (l.source ∈ s.accounts) && decide (l.target ∈ s.accounts) &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int))

def legsOk (s : State) (bal : AccountId → Int) : List Leg → Bool
  | [] => true
  | l :: ls => legAllowed s bal l && legsOk s (shift bal l) ls

def validBool (s : State) (r : Request) : Bool :=
  decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) && legsOk s s.balance r.legs

def step : Impl := fun s r =>
  if validBool s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else
    (.rejected, s)

theorem bool_and_true (a b : Bool) : (((a && b) = true) ↔ (a = true ∧ b = true)) := by
  cases a <;> cases b <;> simp

theorem decide_is_true (P : Prop) [Decidable P] : ((decide P = true) ↔ P) := by
  simp

theorem legAllowed_correct (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [bool_and_true, decide_is_true, and_assoc]

theorem legsOk_correct (s : State) (bal : AccountId → Int) (ls : List Leg) :
    legsOk s bal ls = true ↔ LegsOk s bal ls := by
  induction ls generalizing bal with
  | nil =>
    simp [legsOk, LegsOk]
  | cons l ls ih =>
    have hiff : (((legAllowed s bal l && legsOk s (shift bal l) ls) = true) ↔
        (legAllowed s bal l = true ∧ legsOk s (shift bal l) ls = true)) :=
      bool_and_true _ _
    have hLeg : ((LegsOk s bal (l :: ls)) ↔ (LegOk s bal l ∧ LegsOk s (shift bal l) ls)) := by
      simp [LegsOk]
    have h1 : legsOk s bal (l :: ls) = (legAllowed s bal l && legsOk s (shift bal l) ls) := rfl
    rw [h1, hiff, legAllowed_correct, ih, hLeg]

theorem validBool_correct (s : State) (r : Request) :
    validBool s r = true ↔ ValidBatch s r := by
  unfold validBool ValidBatch
  rw [bool_and_true, decide_is_true, legsOk_correct]
  constructor
  · rintro ⟨⟨a, b, c⟩, d⟩
    exact ⟨a, b, c, d⟩
  · rintro ⟨a, b, c, d⟩
    exact ⟨⟨a, b, c⟩, d⟩

theorem step_ok_iff (s : State) (r : Request) :
    (step s r).1 = .ok ↔ validBool s r = true := by
  unfold step
  cases h : validBool s r <;> simp [h]

theorem step_valid_of_ok (s : State) (r : Request) (h : (step s r).1 = .ok) :
    ValidBatch s r := by
  have hb := (step_ok_iff s r).mp h
  exact (validBool_correct s r).mp hb

theorem step_true_eq (s : State) (r : Request) (h : validBool s r = true) :
    step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
  unfold step
  simp [h]

theorem step_false_eq (s : State) (r : Request) (h : validBool s r = false) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem step_snd_of_true (s : State) (r : Request) (h : validBool s r = true) :
    (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
  have he := step_true_eq s r h
  simp [he]

theorem step_snd_of_false (s : State) (r : Request) (h : validBool s r = false) :
    (step s r).2 = s := by
  have he := step_false_eq s r h
  simp [he]

theorem validBool_of_ok (s : State) (r : Request) (h : (step s r).1 = .ok) :
    validBool s r = true := (step_ok_iff s r).mp h

theorem validBool_of_not_valid (s : State) (r : Request) (h : ¬ ValidBatch s r) :
    validBool s r = false := by
  cases hb : validBool s r with
  | true =>
    have hv := (validBool_correct s r).mp hb
    exact absurd hv h
  | false => rfl

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hb : validBool s r = true := (validBool_correct s r).mpr h
  have he := step_true_eq s r hb
  simp [he]

theorem req_atomicity : Atomicity step := by
  intro s r h
  have hb : validBool s r = false := validBool_of_not_valid s r h
  exact step_false_eq s r hb

theorem req_effects : Effects step := by
  intro s r hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hsnd := step_snd_of_true s r hb
  constructor
  · simp [hsnd]
  · constructor
    · simp [hsnd]
    · intro a
      simp [hsnd]

theorem shift_single_eq (bal : AccountId → Int) (l : Leg) :
    applyLegs bal [l] = shift bal l := rfl

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hv : ValidBatch s r := (validBool_correct s r).mp hb
  have hsnd := step_snd_of_true s r hb
  have hBal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    simp [hsnd]
  have hLegsOk : LegsOk s s.balance r.legs := by
    obtain ⟨_, _, _, hlegsok⟩ := hv
    exact hlegsok
  rw [hlegs] at hLegsOk
  have hOk : LegOk s s.balance l := by
    have hpair : LegOk s s.balance l ∧ LegsOk s (shift s.balance l) [] := hLegsOk
    exact hpair.1
  have hne : l.source ≠ l.target := hOk.2.1
  have hne' : l.target ≠ l.source := fun h => hne h.symm
  have e1 := hBal l.source
  have e2 := hBal l.target
  rw [hlegs] at e1 e2
  have s1 : applyLegs s.balance [l] l.source = shift s.balance l l.source := rfl
  have s2 : applyLegs s.balance [l] l.target = shift s.balance l l.target := rfl
  rw [s1] at e1
  rw [s2] at e2
  have hsh1 : shift s.balance l l.source = s.balance l.source - (l.amount : Int) := by
    unfold shift
    rw [if_pos rfl, if_neg hne]
    simp
  have hsh2 : shift s.balance l l.target = s.balance l.target + (l.amount : Int) := by
    unfold shift
    rw [if_neg hne', if_pos rfl]
    omega
  rw [hsh1] at e1
  rw [hsh2] at e2
  exact ⟨e1, e2⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hsnd := step_snd_of_true s r hb
  have happlied : (step s r).2.applied = r.batchId :: s.applied := by
    simp [hsnd]
  constructor
  · intro x
    rw [happlied]
    simp
  · have hmem : r.batchId ∈ (step s r).2.applied := by
      rw [happlied]
      simp
    have hnotvalid : ¬ ValidBatch (step s r).2 r := by
      intro hv
      obtain ⟨_, _, hni, _⟩ := hv
      exact hni hmem
    have hb2 : validBool (step s r).2 r = false := validBool_of_not_valid _ _ hnotvalid
    exact step_false_eq _ _ hb2

theorem shift_total (s : State) (bal : AccountId → Int) (l : Leg)
    (hnodup : s.accounts.Nodup) (hsrc : l.source ∈ s.accounts)
    (htgt : l.target ∈ s.accounts) (_hne : l.source ≠ l.target) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have h_ite_s := sumOver_ite_eq hnodup l.source ((l.amount : Int))
  have h_ite_t := sumOver_ite_eq hnodup l.target ((l.amount : Int))
  rw [if_pos hsrc] at h_ite_s
  rw [if_pos htgt] at h_ite_t
  have h_add := sumOver_add s.accounts
    (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
    (fun a => if a = l.target then (l.amount : Int) else 0)
  have h_sub := sumOver_sub s.accounts bal
    (fun a => if a = l.source then (l.amount : Int) else 0)
  have h_eq : sumOver s.accounts (shift bal l) =
      sumOver s.accounts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [h_eq, h_add, h_sub, h_ite_s, h_ite_t]
  omega

theorem applyLegs_total (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hnodup : s.accounts.Nodup) (hok : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    have hpair : LegOk s bal l ∧ LegsOk s (shift bal l) ls := hok
    have hhead := hpair.1
    have htail := hpair.2
    have hsrc : l.source ∈ s.accounts := hhead.2.2.1
    have htgt : l.target ∈ s.accounts := hhead.2.2.2.1
    have hne : l.source ≠ l.target := hhead.2.1
    have h_shift := shift_total s bal l hnodup hsrc htgt hne
    have h_ih := ih (shift bal l) htail
    have h_def : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [h_def, h_ih, h_shift]

theorem req_conservation : Conserves step := by
  intro s r hok
  have hb : validBool s r = true := validBool_of_ok s r hok
  have hv : ValidBatch s r := (validBool_correct s r).mp hb
  obtain ⟨hnodup, _, _, hlegsok⟩ := hv
  have hsnd := step_snd_of_true s r hb
  unfold total
  have hacc : (step s r).2.accounts = s.accounts := by simp [hsnd]
  have hbal : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
    intro a
    simp [hsnd]
  have hcongr : sumOver (step s r).2.accounts (step s r).2.balance =
      sumOver s.accounts (applyLegs s.balance r.legs) := by
    rw [hacc]
    exact sumOver_congr s.accounts _ _ (fun a _ => hbal a)
  rw [hcongr]
  exact applyLegs_total s s.balance r.legs hnodup hlegsok

theorem shift_within (s : State) (bal : AccountId → Int) (l : Leg) (a : AccountId)
    (hmem : a ∈ s.accounts)
    (hbal : ∀ x ∈ s.accounts, -(s.limit x : Int) ≤ bal x)
    (hok : LegOk s bal l) : -(s.limit a : Int) ≤ shift bal l a := by
  have hne : l.source ≠ l.target := hok.2.1
  have hfloor_src : -(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int) := hok.2.2.2.2
  have hbal_a : -(s.limit a : Int) ≤ bal a := hbal a hmem
  by_cases hs : a = l.source
  · subst hs
    have h1 : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
    have h2 : (if l.source = l.target then (l.amount : Int) else 0) = 0 := if_neg hne
    have heq : shift bal l l.source = bal l.source - (l.amount : Int) := by
      unfold shift
      rw [h1, h2]
      simp
    rw [heq]
    exact hfloor_src
  · have h1 : (if a = l.source then (l.amount : Int) else 0) = 0 := if_neg hs
    by_cases ht : a = l.target
    · subst ht
      have hne' : l.target ≠ l.source := fun h => hne h.symm
      have h1' : (if l.target = l.source then (l.amount : Int) else 0) = 0 := if_neg hne'
      have h2' : (if l.target = l.target then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
      have heq : shift bal l l.target = bal l.target + (l.amount : Int) := by
        unfold shift
        rw [h1', h2']
        omega
      rw [heq]
      have hpos' : (0 : Int) ≤ (l.amount : Int) := by omega
      omega
    · have h2 : (if a = l.target then (l.amount : Int) else 0) = 0 := if_neg ht
      have heq : shift bal l a = bal a := by
        unfold shift
        rw [h1, h2]
        simp
      rw [heq]
      exact hbal_a

theorem applyLegs_within (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) →
    LegsOk s bal legs →
    ∀ (a : AccountId), a ∈ s.accounts →
    -(s.limit a : Int) ≤ applyLegs bal legs a := by
  induction legs with
  | nil =>
    intro bal hbal _ a hmem
    exact hbal a hmem
  | cons l ls ih =>
    intro bal hbal hok a hmem
    have hpair : LegOk s bal l ∧ LegsOk s (shift bal l) ls := hok
    have hbal' : ∀ x ∈ s.accounts, -(s.limit x : Int) ≤ shift bal l x :=
      fun x hx => shift_within s bal l x hx hbal hpair.1
    have hres := ih (shift bal l) hbal' hpair.2 a hmem
    have hdef : applyLegs bal (l :: ls) a = applyLegs (shift bal l) ls a := rfl
    rw [hdef]
    exact hres

theorem prefix_within (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) →
    LegsOk s bal legs →
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts →
    -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs with
  | nil =>
    intro bal hbal _ k a hmem
    simp
    exact hbal a hmem
  | cons l ls ih =>
    intro bal hbal hok k a hmem
    have hpair : LegOk s bal l ∧ LegsOk s (shift bal l) ls := hok
    have hbal' : ∀ x ∈ s.accounts, -(s.limit x : Int) ≤ shift bal l x :=
      fun x hx => shift_within s bal l x hx hbal hpair.1
    cases k with
    | zero => exact hbal a hmem
    | succ n =>
      have htake : ((l :: ls).take (n + 1)) = l :: (ls.take n) := rfl
      rw [htake]
      have hdef : applyLegs bal (l :: ls.take n) a = applyLegs (shift bal l) (ls.take n) a := rfl
      rw [hdef]
      exact ih (shift bal l) hbal' hpair.2 n a hmem

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hwl
  constructor
  · cases hb : validBool s r with
    | false =>
      have he : (step s r).2 = s := step_snd_of_false s r hb
      rw [he]
      exact hwl
    | true =>
      have hv : ValidBatch s r := (validBool_correct s r).mp hb
      obtain ⟨_, _, _, hlegsok⟩ := hv
      have hsnd := step_snd_of_true s r hb
      intro a ha
      have ha' : a ∈ s.accounts := by simp [hsnd] at ha; exact ha
      have hbal_eq : (step s r).2.balance a = applyLegs s.balance r.legs a := by simp [hsnd]
      have hlim_eq : (step s r).2.limit a = s.limit a := by simp [hsnd]
      rw [hbal_eq, hlim_eq]
      exact applyLegs_within s r.legs s.balance hwl hlegsok a ha'
  · intro hok k a ha
    have hb : validBool s r = true := validBool_of_ok s r hok
    have hv : ValidBatch s r := (validBool_correct s r).mp hb
    obtain ⟨_, _, _, hlegsok⟩ := hv
    exact prefix_within s r.legs s.balance hwl hlegsok k a ha

end Batch
