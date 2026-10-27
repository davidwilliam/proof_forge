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

/-- Apply the legs in order; `none` if a leg is not allowed when it is reached. -/
def applyAll (s : State) : (AccountId → Int) → List Leg → Option (AccountId → Int)
  | bal, [] => some bal
  | bal, l :: ls => if legAllowed s bal l then applyAll s (post bal l) ls else none

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied then
    match applyAll s s.balance r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

theorem legAllowed_correct_aux (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.contains_eq_mem]
  constructor
  · intro h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem post_eq_shift (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem applyAll_of_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : LegsOk s bal legs) : applyAll s bal legs = some (applyLegs bal legs) := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    have hall : legAllowed s bal l = true := (legAllowed_correct_aux s bal l).mpr hok
    simp only [applyAll, hall, ↓reduceIte]
    have hshift : post bal l = shift bal l := rfl
    rw [hshift]
    exact ih _ hrest

theorem applyAll_eq_none_of_not_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : ¬ LegsOk s bal legs) : applyAll s bal legs = none := by
  induction legs generalizing bal with
  | nil =>
    simp only [LegsOk] at h
    exact absurd True.intro h
  | cons l ls ih =>
    unfold applyAll
    by_cases hall : legAllowed s bal l
    · have hok : LegOk s bal l := (legAllowed_correct_aux s bal l).mp hall
      simp only [hall, ↓reduceIte]
      have hrest : ¬ LegsOk s (shift bal l) ls := by
        intro hr
        apply h
        exact ⟨hok, hr⟩
      have hpost : ¬ LegsOk s (post bal l) ls := by
        rw [post_eq_shift]
        exact hrest
      rw [ih _ hpost]
    · simp [hall]

theorem step_ok_iff_aux (s : State) (r : Request) (bal : AccountId → Int)
    (h : applyAll s s.balance r.legs = some bal)
    (hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) :
    step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
  unfold step
  rw [if_pos hpre, h]

theorem step_snd_balance_aux (s : State) (r : Request) (bal : AccountId → Int)
    (hE : applyAll s s.balance r.legs = some bal)
    (hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) :
    (step s r).2.balance = bal := by
  unfold step
  rw [if_pos hpre, hE]

theorem single_pre_ok (s : State) (r : Request) (hok : (step s r).1 = Outcome.ok) :
    s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied := by
  unfold step at hok
  by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · exact hpre
  · rw [if_neg hpre] at hok
    simp at hok

theorem applyAll_some_eq_applyLegs2 (s : State) (bal : AccountId → Int) (legs : List Leg)
    (bal' : AccountId → Int) (h : applyAll s bal legs = some bal') :
    bal' = applyLegs bal legs := by
  induction legs generalizing bal bal' with
  | nil =>
    simp only [applyAll] at h
    simp only [applyLegs]
    cases h
    rfl
  | cons l ls ih =>
    unfold applyAll at h
    by_cases hLB : legAllowed s bal l = true
    · simp only [hLB, ↓reduceIte] at h
      have hpost : post bal l = shift bal l := rfl
      have hres := ih _ _ h
      rw [hpost] at hres
      simp only [applyLegs]
      exact hres
    · have hLBf : ¬ (legAllowed s bal l = true) := hLB
      simp only [hLBf] at h
      simp at h

theorem dummy_garbage2 : True := trivial

theorem foo_test : True := trivial

theorem shift_total_aux (s : State) (bal : AccountId → Int) (l : Leg)
    (hN : s.accounts.Nodup) (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have h1 : ∀ a : AccountId, shift bal l a = (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0) := by
    intro a
    rfl
  have heq : sumOver s.accounts (shift bal l) = sumOver s.accounts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := by
    apply sumOver_congr
    intro a ha
    exact h1 a
  rw [heq, sumOver_add, sumOver_sub]
  have hs2 : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hN l.source (l.amount : Int)
    rw [h]
    simp [hs]
  have ht2 : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hN l.target (l.amount : Int)
    rw [h]
    simp [ht]
  rw [hs2, ht2]
  omega

theorem applyLegs_total_aux (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hN : s.accounts.Nodup) (h : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    simp only [applyLegs]
    rw [ih (shift bal l) hrest]
    exact shift_total_aux s bal l hN hok.2.2.1 hok.2.2.2.1

theorem mytest_thm (p : Prop) (h : p) : p := by exact h

theorem check_by_contra_available (h : ¬ ¬ True) : True := by
  exact Decidable.byContradiction h

theorem check_by_contra2 : ¬ ¬ True → True := by intro h; exact Decidable.byContradiction h

theorem limit_shift_preserves_aux (s : State) (bal : AccountId → Int) (l : Leg)
    (hBal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  intro a ha
  obtain ⟨hpos, hne, hsmem, htmem, hfloor⟩ := hOk
  by_cases hs : a = l.source
  · subst hs
    show -(s.limit l.source : Int) ≤ shift bal l l.source
    unfold shift
    simp only [ite_true, hne, ite_false]
    omega
  · have hs' : ¬ (a = l.source) := hs
    show -(s.limit a : Int) ≤ shift bal l a
    unfold shift
    simp only [hs', ite_false]
    by_cases ht : a = l.target
    · subst ht
      simp only [ite_true]
      have h := hBal _ ha
      omega
    · simp only [ht, ite_false]
      have h := hBal _ ha
      omega

theorem legs_prefix_within_aux2 (s : State) (bal : AccountId → Int) (legs : List Leg)
    : (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) → LegsOk s bal legs →
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts →
      -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro hBal hOk k a ha
    have ht : (([] : List Leg).take k) = [] := by simp
    rw [ht]
    show -(s.limit a : Int) ≤ bal a
    exact hBal a ha
  | cons l ls ih =>
    intro hBal hOk k a ha
    simp only [LegsOk] at hOk
    obtain ⟨hok, hrest⟩ := hOk
    have hBal' : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a :=
      limit_shift_preserves_aux s bal l hBal hok
    cases k with
    | zero =>
      have ht0 : ((l :: ls).take 0) = [] := rfl
      rw [ht0]
      show -(s.limit a : Int) ≤ bal a
      exact hBal a ha
    | succ n =>
      have hts : ((l :: ls).take (n+1)) = l :: ((ls).take n) := rfl
      rw [hts]
      have heq : applyLegs bal (l :: List.take n ls) a = applyLegs (shift bal l) (List.take n ls) a := rfl
      rw [heq]
      exact ih _ hBal' hrest _ _ ha

theorem req_single_leg_helper_use : True := trivial


theorem req_single_leg_aux2 : SingleLeg step := by
  intro s r l hlegs hok
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    single_pre_ok s r hok
  have hne : l.source ≠ l.target := by
    intro heq
    have hbeq : (l.source != l.target) = false := by simp [heq]
    have hallow_false : legAllowed s s.balance l = false := by
      unfold legAllowed
      rw [hbeq]
      simp
    have hnone : applyAll s s.balance r.legs = none := by
      rw [hlegs]
      unfold applyAll
      simp [hallow_false]
    unfold step at hok
    rw [if_pos hpre, hnone] at hok
    simp at hok
  cases hA : applyAll s s.balance r.legs with
  | none =>
    unfold step at hok
    rw [if_pos hpre, hA] at hok
    simp at hok
  | some bal =>
    have hbal_eq : bal = applyLegs s.balance r.legs :=
      applyAll_some_eq_applyLegs2 s s.balance r.legs bal hA
    have hstep2 : (step s r).2.balance = bal := by
      unfold step
      rw [if_pos hpre, hA]
    rw [hstep2, hbal_eq, hlegs]
    have e1 : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := by
      show shift s.balance l l.source = _
      unfold shift
      simp [hne]
    have e2 : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := by
      show shift s.balance l l.target = _
      unfold shift
      have hnsym : ¬ (l.target = l.source) := fun h => hne h.symm
      simp [hnsym]
    exact ⟨e1, e2⟩

theorem req_single_leg_aux1 : True := trivial

theorem applyAll_some_implies_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (bal' : AccountId → Int) (h : applyAll s bal legs = some bal') :
    LegsOk s bal legs := by
  induction legs generalizing bal bal' with
  | nil => trivial
  | cons l ls ih =>
    unfold applyAll at h
    by_cases hLB : legAllowed s bal l = true
    · simp only [hLB, ↓reduceIte] at h
      have hok : LegOk s bal l := (legAllowed_correct_aux s bal l).mp hLB
      have hpost : post bal l = shift bal l := rfl
      -- h : applyAll s (post bal l) ls = some bal'
      have hrest : LegsOk s (shift bal l) ls := by
        have := ih (post bal l) bal' h
        rw [hpost] at this
        exact this
      exact ⟨hok, hrest⟩
    · have hLBf : ¬ (legAllowed s bal l = true) := hLB
      simp only [hLBf] at h
      simp at h

theorem req_limit_every_step_aux_test : True := trivial

theorem req_limit_every_step_try1 : LimitEveryStep step := by
  intro s r hWL
  constructor
  · by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · cases hA : applyAll s s.balance r.legs with
      | none =>
        have hstep2 : (step s r).2 = s := by unfold step; rw [if_pos hpre, hA]
        rw [hstep2]
        exact hWL
      | some bal =>
        have hLegs : LegsOk s s.balance r.legs :=
          applyAll_some_implies_LegsOk s s.balance r.legs bal hA
        have hbal_eq : bal = applyLegs s.balance r.legs :=
          applyAll_some_eq_applyLegs2 s s.balance r.legs bal hA
        have hstep : step s r = (.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
          unfold step; rw [if_pos hpre, hA]
        have hstep2 : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
          rw [hstep]
        rw [hstep2]
        intro a ha
        simp only at ha ⊢
        rw [hbal_eq]
        have hpr := legs_prefix_within_aux2 s s.balance r.legs hWL hLegs (r.legs.length) a ha
        simp at hpr
        exact hpr
    · have hstep2 : (step s r).2 = s := by unfold step; rw [if_neg hpre]
      rw [hstep2]
      exact hWL
  · intro hok k a ha
    have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
      single_pre_ok s r hok
    have hA : ∃ bal, applyAll s s.balance r.legs = some bal := by
      unfold step at hok
      rw [if_pos hpre] at hok
      match hEq : applyAll s s.balance r.legs with
      | none => rw [hEq] at hok; simp at hok
      | some bal => exact ⟨bal, rfl⟩
    obtain ⟨bal, hEq⟩ := hA
    have hLegs : LegsOk s s.balance r.legs :=
      applyAll_some_implies_LegsOk s s.balance r.legs bal hEq
    exact legs_prefix_within_aux2 s s.balance r.legs hWL hLegs k a ha

theorem req_valid_succeeds   : ValidSucceeds step := by
  intro s r h
  obtain ⟨hNodup, hNe, hNotMem, hLegs⟩ := h
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    ⟨hNodup, hNe, hNotMem⟩
  have hSome : applyAll s s.balance r.legs = some (applyLegs s.balance r.legs) :=
    applyAll_of_LegsOk s s.balance r.legs hLegs
  unfold step
  rw [if_pos hpre, hSome]

theorem req_atomicity : Atomicity step := by
  intro s r hneg
  have hneg' : ¬ (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ LegsOk s s.balance r.legs) := hneg
  unfold step
  by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hLegs : ¬ LegsOk s s.balance r.legs := by
      intro hlegs
      apply hneg'
      obtain ⟨h1, h2, h3⟩ := hpre
      exact ⟨h1, h2, h3, hlegs⟩
    have hnone : applyAll s s.balance r.legs = none :=
      applyAll_eq_none_of_not_LegsOk s s.balance r.legs hLegs
    rw [if_pos hpre, hnone]
  · rw [if_neg hpre]

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    single_pre_ok s r hok
  have hne : l.source ≠ l.target := by
    intro heq
    have hbeq : (l.source != l.target) = false := by simp [heq]
    have hallow_false : legAllowed s s.balance l = false := by
      unfold legAllowed
      rw [hbeq]
      simp
    have hnone : applyAll s s.balance r.legs = none := by
      rw [hlegs]
      unfold applyAll
      simp [hallow_false]
    unfold step at hok
    rw [if_pos hpre, hnone] at hok
    simp at hok
  cases hA : applyAll s s.balance r.legs with
  | none =>
    unfold step at hok
    rw [if_pos hpre, hA] at hok
    simp at hok
  | some bal =>
    have hbal_eq : bal = applyLegs s.balance r.legs :=
      applyAll_some_eq_applyLegs2 s s.balance r.legs bal hA
    have hstep2 : (step s r).2.balance = bal := by
      unfold step
      rw [if_pos hpre, hA]
    rw [hstep2, hbal_eq, hlegs]
    have e1 : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := by
      show shift s.balance l l.source = _
      unfold shift
      simp [hne]
    have e2 : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := by
      show shift s.balance l l.target = _
      unfold shift
      have hnsym : ¬ (l.target = l.source) := fun h => hne h.symm
      simp [hnsym]
    exact ⟨e1, e2⟩

theorem req_effects : Effects step := by
  intro s r hok
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    single_pre_ok s r hok
  unfold step at hok
  rw [if_pos hpre] at hok
  match hEq : applyAll s s.balance r.legs with
  | none =>
    rw [hEq] at hok
    simp at hok
  | some bal =>
    rw [hEq] at hok
    simp at hok
    have hbal_eq : bal = applyLegs s.balance r.legs :=
      applyAll_some_eq_applyLegs2 s s.balance r.legs bal hEq
    unfold step
    rw [if_pos hpre, hEq]
    refine ⟨rfl, rfl, ?_⟩
    intro a
    rw [hbal_eq]

theorem req_idempotency      : Idempotent step := by
  intro s r hok
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    single_pre_ok s r hok
  unfold step at hok
  rw [if_pos hpre] at hok
  match hEq : applyAll s s.balance r.legs with
  | none =>
    rw [hEq] at hok
    simp at hok
  | some bal =>
    rw [hEq] at hok
    simp at hok
    have hstep : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
      unfold step
      rw [if_pos hpre, hEq]
    rw [hstep]
    constructor
    · intro x
      simp
    · have hmem : r.batchId ∈ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied) := by
        simp
      have hpre2neg : ¬ ((({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied)) := by
        intro h
        exact h.2.2 hmem
      have hstep2 : step { s with balance := bal, applied := r.batchId :: s.applied } r = (.rejected, { s with balance := bal, applied := r.batchId :: s.applied }) := by
        unfold step
        rw [if_neg hpre2neg]
      exact hstep2

theorem req_conservation : Conserves step := by
  intro s r hok
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
    single_pre_ok s r hok
  unfold step at hok
  rw [if_pos hpre] at hok
  match hEq : applyAll s s.balance r.legs with
  | none =>
    rw [hEq] at hok
    simp at hok
  | some bal =>
    rw [hEq] at hok
    simp at hok
    have hLegs : LegsOk s s.balance r.legs :=
      applyAll_some_implies_LegsOk s s.balance r.legs bal hEq
    have htot : sumOver s.accounts (applyLegs s.balance r.legs) = sumOver s.accounts s.balance :=
      applyLegs_total_aux s s.balance r.legs hpre.1 hLegs
    have hbal_eq : bal = applyLegs s.balance r.legs :=
      applyAll_some_eq_applyLegs2 s s.balance r.legs bal hEq
    -- compute totals
    unfold total step
    rw [if_pos hpre, hEq]
    simp only
    rw [hbal_eq, htot]

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hWL
  constructor
  · by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · cases hA : applyAll s s.balance r.legs with
      | none =>
        have hstep2 : (step s r).2 = s := by unfold step; rw [if_pos hpre, hA]
        rw [hstep2]
        exact hWL
      | some bal =>
        have hLegs : LegsOk s s.balance r.legs :=
          applyAll_some_implies_LegsOk s s.balance r.legs bal hA
        have hbal_eq : bal = applyLegs s.balance r.legs :=
          applyAll_some_eq_applyLegs2 s s.balance r.legs bal hA
        have hstep : step s r = (.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
          unfold step; rw [if_pos hpre, hA]
        have hstep2 : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
          rw [hstep]
        rw [hstep2]
        intro a ha
        simp only at ha ⊢
        rw [hbal_eq]
        have hpr := legs_prefix_within_aux2 s s.balance r.legs hWL hLegs (r.legs.length) a ha
        simp at hpr
        exact hpr
    · have hstep2 : (step s r).2 = s := by unfold step; rw [if_neg hpre]
      rw [hstep2]
      exact hWL
  · intro hok k a ha
    have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied :=
      single_pre_ok s r hok
    have hA : ∃ bal, applyAll s s.balance r.legs = some bal := by
      unfold step at hok
      rw [if_pos hpre] at hok
      match hEq : applyAll s s.balance r.legs with
      | none => rw [hEq] at hok; simp at hok
      | some bal => exact ⟨bal, rfl⟩
    obtain ⟨bal, hEq⟩ := hA
    have hLegs : LegsOk s s.balance r.legs :=
      applyAll_some_implies_LegsOk s s.balance r.legs bal hEq
    exact legs_prefix_within_aux2 s s.balance r.legs hWL hLegs k a ha

end Batch
