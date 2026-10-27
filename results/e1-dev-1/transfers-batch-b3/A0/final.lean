import Batch.Spec
import Batch.Lemmas
namespace Batch

def legOkB (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && decide (l.source ≠ l.target) &&
  decide (l.source ∈ s.accounts) && decide (l.target ∈ s.accounts) &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - (l.amount : Int))

def legsOkB (s : State) : (AccountId → Int) → List Leg → Bool
  | _, [] => true
  | bal, l :: ls => legOkB s bal l && legsOkB s (shift bal l) ls

def validB (s : State) (r : Request) : Bool :=
  decide s.accounts.Nodup && (!r.legs.isEmpty) &&
  decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs

def step : Impl := fun s r =>
  if validB s r then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else
    (.rejected, s)

theorem decide_true_iff {P : Prop} [Decidable P] : (decide P = true) ↔ P := by
  simp

theorem legOkB_eq (s : State) (bal : AccountId → Int) (l : Leg) :
    (legOkB s bal l = true) ↔ LegOk s bal l := by
  unfold legOkB LegOk
  simp only [Bool.and_eq_true, decide_true_iff, and_assoc]

theorem legsOkB_eq (s : State) (bal : AccountId → Int) (ls : List Leg) :
    (legsOkB s bal ls = true) ↔ LegsOk s bal ls := by
  induction ls generalizing bal with
  | nil => simp [legsOkB, LegsOk]
  | cons l ls ih =>
    simp [legsOkB, LegsOk, Bool.and_eq_true, legOkB_eq, ih]

theorem notEmpty_iff (legs : List Leg) : ((!legs.isEmpty) = true) ↔ (legs ≠ []) := by
  cases legs with
  | nil => simp
  | cons a l => simp

theorem validB_eq (s : State) (r : Request) : (validB s r = true) ↔ ValidBatch s r := by
  unfold validB ValidBatch
  obtain ⟨bid, legs⟩ := r
  simp only [Bool.and_eq_true, decide_true_iff, and_assoc]
  rw [notEmpty_iff]
  simp only [legsOkB_eq]

theorem bool_ne_true_eq_false (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

theorem if_ok_eq (b : Bool) (h : (if b then Outcome.ok else Outcome.rejected) = Outcome.ok) :
    b = true := by
  cases b with
  | true => rfl
  | false => simp at h

theorem step_fst (s : State) (r : Request) :
    (step s r).1 = (if validB s r then Outcome.ok else Outcome.rejected) := by
  unfold step
  cases h : validB s r <;> rfl

theorem step_valid_true (s : State) (r : Request) (h : ValidBatch s r) :
    validB s r = true := (validB_eq s r).mpr h

theorem step_ok_state (s : State) (r : Request) (h : (step s r).1 = .ok) :
    validB s r = true := by
  have hf := step_fst s r
  have h2 : (if validB s r then Outcome.ok else Outcome.rejected) = Outcome.ok := by
    rw [← hf]
    exact h
  exact if_ok_eq _ h2

theorem step_valid_false (s : State) (r : Request) (h : ¬ ValidBatch s r) :
    validB s r = false := by
  apply bool_ne_true_eq_false
  intro ht
  exact h ((validB_eq s r).mp ht)

theorem step_rej_state (s : State) (r : Request) (h : validB s r = false) :
    step s r = (.rejected, s) := by
  unfold step
  simp [h]

theorem step_ok_full (s : State) (r : Request) (h : (step s r).1 = .ok) :
    (step s r).2.accounts = s.accounts ∧
    (step s r).2.limit = s.limit ∧
    (∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a) ∧
    (∀ x, x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied) := by
  have hv : validB s r = true := step_ok_state s r h
  unfold step
  simp [hv]

theorem shift_source_of_ne (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.source = bal l.source - (l.amount : Int) := by
  unfold shift
  have h1 : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by simp
  have h2 : (if l.source = l.target then (l.amount : Int) else 0) = 0 := if_neg hne
  rw [h1, h2]
  omega

theorem shift_target_of_ne (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.target = bal l.target + (l.amount : Int) := by
  unfold shift
  have hns : ¬ (l.target = l.source) := fun he => hne he.symm
  have h1 : (if l.target = l.source then (l.amount : Int) else 0) = 0 := if_neg hns
  have h2 : (if l.target = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by simp
  rw [h1, h2]
  omega

theorem applyLegs_single_source (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    applyLegs bal [l] l.source = bal l.source - (l.amount : Int) := by
  simp only [applyLegs, shift_source_of_ne _ _ hne]

theorem applyLegs_single_target (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    applyLegs bal [l] l.target = bal l.target + (l.amount : Int) := by
  simp only [applyLegs, shift_target_of_ne _ _ hne]

theorem sum_shift_eq (s : State) (bal : AccountId → Int) (l : Leg)
    (hnodup : s.accounts.Nodup) (hsrc : l.source ∈ s.accounts)
    (htgt : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have h1 : ∀ a : AccountId, shift bal l a = (bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0)) := by
    intro a
    unfold shift
    omega
  have h2 : sumOver s.accounts (shift bal l)
      = sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0)) := by
    exact sumOver_congr s.accounts _ _ (fun a _ => h1 a)
  rw [h2]
  have h3 : (fun a : AccountId => bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0))
      = (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [h3, sumOver_add]
  have h4 : sumOver s.accounts (fun a : AccountId => bal a - (if a = l.source then (l.amount : Int) else 0))
      = sumOver s.accounts bal - sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) := by
    exact sumOver_sub s.accounts bal (fun a => if a = l.source then (l.amount : Int) else 0)
  rw [h4]
  rw [sumOver_ite_eq hnodup l.source (l.amount : Int)]
  rw [sumOver_ite_eq hnodup l.target (l.amount : Int)]
  simp [hsrc, htgt]

theorem sum_applyLegs_eq (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hnodup : s.accounts.Nodup) (hok : LegsOk s bal ls) :
    sumOver s.accounts (applyLegs bal ls) = sumOver s.accounts bal := by
  induction ls generalizing bal with
  | nil => simp [applyLegs]
  | cons l ls ih =>
    have hhead : LegOk s bal l := hok.1
    have htail : LegsOk s (shift bal l) ls := hok.2
    simp only [applyLegs]
    rw [ih (shift bal l) htail]
    exact sum_shift_eq s bal l hnodup hhead.2.2.1 hhead.2.2.2.1

theorem shift_within (s : State) (bal : AccountId → Int) (l : Leg) (a : AccountId)
    (ha : a ∈ s.accounts)
    (hbal : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ bal b)
    (hok : LegOk s bal l) :
    -(s.limit a : Int) ≤ shift bal l a := by
  obtain ⟨_, hne, _, _, hlim⟩ := hok
  unfold shift
  by_cases h1 : a = l.source
  · by_cases h2 : a = l.target
    · exfalso
      exact hne (h1.symm.trans h2)
    · have e1 : (if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by simp [h1]
      have e2 : (if a = l.target then (l.amount : Int) else 0) = 0 := by simp [h2]
      rw [e1, e2]
      have heq : s.limit a = s.limit l.source := by rw [h1]
      have heq2 : bal a = bal l.source := by rw [h1]
      rw [heq, heq2]
      omega
  · by_cases h2 : a = l.target
    · have e1 : (if a = l.source then (l.amount : Int) else 0) = 0 := by simp [h1]
      have e2 : (if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by simp [h2]
      rw [e1, e2]
      have hle := hbal a ha
      omega
    · have e1 : (if a = l.source then (l.amount : Int) else 0) = 0 := by simp [h1]
      have e2 : (if a = l.target then (l.amount : Int) else 0) = 0 := by simp [h2]
      rw [e1, e2]
      have hle := hbal a ha
      omega

theorem shift_within_all (s : State) (bal : AccountId → Int) (l : Leg)
    (hbal : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ bal b)
    (hok : LegOk s bal l) :
    ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ shift bal l b := by
  intro b hb
  exact shift_within s bal l b hb hbal hok

theorem applyLegs_within_all (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hbal : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ bal b)
    (hok : LegsOk s bal ls) :
    ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ applyLegs bal ls b := by
  induction ls generalizing bal with
  | nil =>
    intro b hb
    simp [applyLegs]
    exact hbal b hb
  | cons l ls ih =>
    have hhead : LegOk s bal l := hok.1
    have htail : LegsOk s (shift bal l) ls := hok.2
    intro b hb
    simp only [applyLegs]
    exact ih (shift bal l) (shift_within_all s bal l hbal hhead) htail b hb

theorem legsOk_take (s : State) (bal : AccountId → Int) (ls : List Leg) (k : Nat) :
    LegsOk s bal ls → LegsOk s bal (ls.take k) := by
  induction ls generalizing bal k with
  | nil =>
    intro _
    cases k with
    | zero => trivial
    | succ n => trivial
  | cons l ls ih =>
    intro hok
    have hhead : LegOk s bal l := hok.1
    have htail : LegsOk s (shift bal l) ls := hok.2
    cases k with
    | zero => trivial
    | succ n =>
      simp [List.take]
      exact ⟨hhead, ih (shift bal l) n htail⟩

theorem prefix_within (s : State) (bal : AccountId → Int) (ls : List Leg)
    (hbal : ∀ (b : AccountId), b ∈ s.accounts → -(s.limit b : Int) ≤ bal b)
    (hok : LegsOk s bal ls) (k : Nat) (a : AccountId) (ha : a ∈ s.accounts) :
    -(s.limit a : Int) ≤ applyLegs bal (ls.take k) a := by
  have htake : LegsOk s bal (ls.take k) := legsOk_take s bal ls k hok
  exact applyLegs_within_all s bal (ls.take k) hbal htake a ha

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hv : validB s r = true := step_valid_true s r h
  unfold step
  simp [hv]

theorem req_atomicity : Atomicity step := by
  intro s r h
  have hv : validB s r = false := step_valid_false s r h
  exact step_rej_state s r hv

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  have hv : validB s r = true := step_ok_state s r hok
  have hvalid : ValidBatch s r := (validB_eq s r).mp hv
  have hlegsok : LegsOk s s.balance r.legs := hvalid.2.2.2
  rw [hlegs] at hlegsok
  have hhead : LegOk s s.balance l := hlegsok.1
  have hne : l.source ≠ l.target := hhead.2.1
  have hfull := step_ok_full s r hok
  have hbalf : ∀ (a : AccountId), (step s r).2.balance a = applyLegs s.balance r.legs a := hfull.2.2.1
  rw [hlegs] at hbalf
  constructor
  · have e := hbalf l.source
    rw [applyLegs_single_source s.balance l hne] at e
    exact e
  · have e := hbalf l.target
    rw [applyLegs_single_target s.balance l hne] at e
    exact e

theorem req_effects : Effects step := by
  intro s r hok
  have hfull := step_ok_full s r hok
  exact ⟨hfull.1, hfull.2.1, hfull.2.2.1⟩

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hfull := step_ok_full s r hok
  have happ : ∀ (x : BatchId), x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied := hfull.2.2.2
  constructor
  · exact happ
  · have hmem : r.batchId ∈ (step s r).2.applied := (happ r.batchId).mpr (Or.inl rfl)
    have hnotvalid : ¬ ValidBatch (step s r).2 r := by
      intro hv2
      exact hv2.2.2.1 hmem
    have hv2 : validB (step s r).2 r = false := step_valid_false _ _ hnotvalid
    exact step_rej_state _ _ hv2

theorem req_conservation : Conserves step := by
  intro s r hok
  have hv : validB s r = true := step_ok_state s r hok
  have hvalid : ValidBatch s r := (validB_eq s r).mp hv
  have hnodup : s.accounts.Nodup := hvalid.1
  have hlegsok : LegsOk s s.balance r.legs := hvalid.2.2.2
  have hfull := step_ok_full s r hok
  have hacc : (step s r).2.accounts = s.accounts := hfull.1
  have hbalf : ∀ (a : AccountId), (step s r).2.balance a = applyLegs s.balance r.legs a := hfull.2.2.1
  have hsum : sumOver s.accounts (applyLegs s.balance r.legs) = sumOver s.accounts s.balance :=
    sum_applyLegs_eq s s.balance r.legs hnodup hlegsok
  have hcongr : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (applyLegs s.balance r.legs) := by
    exact sumOver_congr s.accounts _ _ (fun a _ => hbalf a)
  unfold total
  rw [hacc, hcongr, hsum]

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hwithin
  constructor
  · intro a ha
    by_cases hv : validB s r = true
    · have hok : (step s r).1 = .ok := by
        unfold step
        simp [hv]
      have hfull := step_ok_full s r hok
      have hacc : (step s r).2.accounts = s.accounts := hfull.1
      have hlim : (step s r).2.limit = s.limit := hfull.2.1
      have hbalf : ∀ (x : AccountId), (step s r).2.balance x = applyLegs s.balance r.legs x := hfull.2.2.1
      have hvalid : ValidBatch s r := (validB_eq s r).mp hv
      have hlegsok : LegsOk s s.balance r.legs := hvalid.2.2.2
      have ha_old : a ∈ s.accounts := by
        have hmem := ha
        rw [hacc] at hmem
        exact hmem
      have hle : -(s.limit a : Int) ≤ applyLegs s.balance r.legs a :=
        applyLegs_within_all s s.balance r.legs (fun b hb => hwithin b hb) hlegsok a ha_old
      have hlim_eq : (step s r).2.limit a = s.limit a := by rw [hlim]
      have e : (step s r).2.balance a = applyLegs s.balance r.legs a := hbalf a
      rw [hlim_eq, e]
      exact hle
    · have hvf : validB s r = false := bool_ne_true_eq_false _ hv
      have heq := step_rej_state s r hvf
      have h2 : (step s r).2 = s := by rw [heq]
      have ha_old : a ∈ s.accounts := by
        have hmem := ha
        rw [h2] at hmem
        exact hmem
      have hle := hwithin a ha_old
      have hlim_eq : (step s r).2.limit a = s.limit a := by rw [h2]
      have e : (step s r).2.balance a = s.balance a := by rw [h2]
      rw [hlim_eq, e]
      exact hle
  · intro hok k a ha
    have hv : validB s r = true := step_ok_state s r hok
    have hvalid : ValidBatch s r := (validB_eq s r).mp hv
    have hlegsok : LegsOk s s.balance r.legs := hvalid.2.2.2
    exact prefix_within s s.balance r.legs (fun b hb => hwithin b hb) hlegsok k a ha

end Batch
