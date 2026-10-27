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

theorem contains_mem_test (l : List Nat) (x : Nat) : (l.contains x = true) ↔ x ∈ l := by
  simp

theorem legAllowed_correct_aux (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.contains_eq_mem]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem post_eq_shift_aux2 (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem applyAll_some_of_LegsOk_aux2 (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int), LegsOk s bal legs → applyAll s bal legs = some (applyLegs bal legs) := by
  induction legs with
  | nil => intro bal _; rfl
  | cons l ls ih =>
    intro bal h
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    have hallow : legAllowed s bal l = true := (legAllowed_correct_aux s bal l).mpr hok
    simp only [applyAll, hallow]
    have hpost : post bal l = shift bal l := rfl
    rw [hpost]
    have := ih (shift bal l) hrest
    -- applyLegs (l::ls) unfolds
    simp only [applyLegs] at *
    -- need to adjust? applyLegs def: applyLegs bal (l::ls) = applyLegs (shift bal l) ls, by rfl
    exact this

theorem applyAll_none_of_not_LegsOk_aux2 (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int), ¬ LegsOk s bal legs → applyAll s bal legs = none := by
  induction legs with
  | nil =>
    intro bal h
    simp only [LegsOk] at h
    exact absurd True.intro h
  | cons l ls ih =>
    intro bal h
    simp only [LegsOk] at h
    have hEq : applyAll s bal (l :: ls) =
      (if legAllowed s bal l then applyAll s (post bal l) ls else none) := rfl
    rw [hEq]
    cases hb : legAllowed s bal l
    · simp
    · simp
      have hok : LegOk s bal l := (legAllowed_correct_aux s bal l).mp hb
      have hrest : ¬ LegsOk s (shift bal l) ls := fun hr => h ⟨hok, hr⟩
      have hpost : post bal l = shift bal l := rfl
      rw [hpost]
      exact ih (shift bal l) hrest

theorem applyAll_some_eq_aux4 (s : State) (legs : List Leg) :
    ∀ (bal bal' : AccountId → Int), applyAll s bal legs = some bal' → bal' = applyLegs bal legs := by
  induction legs with
  | nil =>
    intro bal bal' h
    simp only [applyAll] at h
    simp only [applyLegs]
    cases h
    rfl
  | cons l ls ih =>
    intro bal bal' h
    have hEq : applyAll s bal (l :: ls) =
      (if legAllowed s bal l then applyAll s (post bal l) ls else none) := rfl
    rw [hEq] at h
    cases hb : legAllowed s bal l
    · simp [hb] at h
    · simp [hb] at h
      have hpost : post bal l = shift bal l := rfl
      rw [hpost] at h
      have ihr := ih (shift bal l) bal' h
      have heq : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
      rw [heq]
      exact ihr

theorem test_by_cases (s : State) (r : Request) : True := by
  by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · trivial
  · trivial

theorem myEffects : Effects step := by
  intro s r hOk
  by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hstep_eq : step s r =
      (match applyAll s s.balance r.legs with
       | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
       | none => (Outcome.rejected, s)) := by
      unfold step
      simp [hcond]
    cases hmatch : applyAll s s.balance r.legs with
    | none =>
      have hstep_none : step s r = (Outcome.rejected, s) := by
        rw [hstep_eq, hmatch]
      have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_none]
      rw [h1] at hOk
      exact absurd hOk (by decide)
    | some bal =>
      have hstep_some : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
        rw [hstep_eq, hmatch]
      have hbal : bal = applyLegs s.balance r.legs :=
        applyAll_some_eq_aux4 s r.legs s.balance bal hmatch
      rw [hstep_some]
      refine ⟨rfl, rfl, ?_⟩
      intro a
      simp [hbal]
  · have hstep_eq : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hcond]
    have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_eq]
    rw [h1] at hOk
    exact absurd hOk (by decide)

def fooTest := 1

theorem fooLem : 1 = 1 := rfl

theorem shift_sum_aux2 (_s : State) : 1 = 1 := rfl

theorem shift_sum_aux (s : State) (bal : AccountId → Int) (l : Leg) (hnd : s.accounts.Nodup) (_hne : l.source ≠ l.target) (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts) : sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have hcongr : sumOver s.accounts (shift bal l) = sumOver s.accounts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := by
    apply sumOver_congr
    intro a ha
    rfl
  rw [hcongr]
  rw [sumOver_add]
  rw [sumOver_sub]
  have hs2 : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hnd l.source (l.amount : Int)
    rw [h]
    simp [hs]
  have ht2 : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hnd l.target (l.amount : Int)
    rw [h]
    simp [ht]
  rw [hs2, ht2]
  omega

theorem applyAll_some_implies_LegsOk2 (s : State) (legs : List Leg) : ∀ (bal bal' : AccountId → Int), applyAll s bal legs = some bal' → LegsOk s bal legs := by
  induction legs with
  | nil =>
    intro bal bal' h
    trivial
  | cons l ls ih =>
    intro bal bal' h
    have hEq : applyAll s bal (l :: ls) = (if legAllowed s bal l then applyAll s (post bal l) ls else none) := rfl
    rw [hEq] at h
    cases hb : legAllowed s bal l with
    | false =>
      simp [hb] at h
    | true =>
      simp [hb] at h
      have hok : LegOk s bal l := (legAllowed_correct_aux s bal l).mp hb
      have hpost : post bal l = shift bal l := rfl
      rw [hpost] at h
      have hrest : LegsOk s (shift bal l) ls := ih (shift bal l) bal' h
      show LegOk s bal l ∧ LegsOk s (shift bal l) ls
      exact ⟨hok, hrest⟩

theorem shift_preserves_lim (s : State) (bal : AccountId → Int) (l : Leg)
    (hBal : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hok : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  intro a ha
  obtain ⟨hpos, hne, hs, ht, hlim⟩ := hok
  unfold shift
  by_cases h1 : a = l.source
  · subst h1
    have e1 : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
    have e2 : (if l.source = l.target then (l.amount : Int) else 0) = 0 := if_neg hne
    rw [e1, e2]
    simp at hlim ⊢
    omega
  · by_cases h2 : a = l.target
    · subst h2
      have e1 : (if l.target = l.source then (l.amount : Int) else 0) = 0 := if_neg h1
      have e2 : (if l.target = l.target then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
      rw [e1, e2]
      have hba := hBal l.target ha
      simp
      omega
    · have e1 : (if a = l.source then (l.amount : Int) else 0) = 0 := if_neg h1
      have e2 : (if a = l.target then (l.amount : Int) else 0) = 0 := if_neg h2
      rw [e1, e2]
      simp
      exact hBal a ha

theorem legs_prefix_within (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) →
    LegsOk s bal legs →
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts →
      -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs with
  | nil =>
    intro bal hbal hok k a ha
    have htk : List.take k ([] : List Leg) = [] := by simp
    rw [htk]
    simp only [applyLegs]
    exact hbal a ha
  | cons l ls ih =>
    intro bal hbal hok k a ha
    simp only [LegsOk] at hok
    obtain ⟨hokHead, hokTail⟩ := hok
    have hbal' : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ shift bal l b :=
      shift_preserves_lim s bal l hbal hokHead
    cases k with
    | zero =>
      simp [applyLegs]
      exact hbal a ha
    | succ n =>
      simp only [List.take_succ_cons]
      have heq : applyLegs bal (l :: List.take n ls) = applyLegs (shift bal l) (List.take n ls) := rfl
      rw [heq]
      exact ih (shift bal l) hbal' hokTail n a ha

theorem applyLegs_sum_preserve (s : State) (legs : List Leg) :
    ∀ (bal : AccountId → Int),
    LegsOk s bal legs →
    s.accounts.Nodup →
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs with
  | nil => intro bal _ _; rfl
  | cons l ls ih =>
    intro bal hok hnd
    simp only [LegsOk] at hok
    obtain ⟨hhead, htail⟩ := hok
    obtain ⟨hpos, hne, hs, ht, hlim⟩ := hhead
    have hshift : sumOver s.accounts (shift bal l) = sumOver s.accounts bal :=
      shift_sum_aux s bal l hnd hne hs ht
    have heq : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [heq]
    rw [ih (shift bal l) htail hnd]
    exact hshift

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hnd, hne, hbid, hlegs⟩ := h
  have hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied := ⟨hnd, hne, hbid⟩
  unfold step
  simp only [if_pos hcond]
  have hsome : applyAll s s.balance r.legs = some (applyLegs s.balance r.legs) :=
    applyAll_some_of_LegsOk_aux2 s r.legs s.balance hlegs
  rw [hsome]

theorem req_atomicity : Atomicity step := by
  intro s r h
  unfold ValidBatch at h
  unfold step
  by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · simp only [if_pos hcond]
    have hlegs : ¬ LegsOk s s.balance r.legs := by
      intro hlegs
      exact h ⟨hcond.1, hcond.2.1, hcond.2.2, hlegs⟩
    have hnone : applyAll s s.balance r.legs = none :=
      applyAll_none_of_not_LegsOk_aux2 s r.legs s.balance hlegs
    rw [hnone]
  · simp only [if_neg hcond]

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hOk
  have hEff := myEffects s r hOk
  obtain ⟨hacc, hlim, hbal⟩ := hEff
  have hsrc : (step s r).2.balance l.source = applyLegs s.balance r.legs l.source := hbal l.source
  have htgt : (step s r).2.balance l.target = applyLegs s.balance r.legs l.target := hbal l.target
  rw [hlegs] at hsrc htgt
  have hne : l.source ≠ l.target := by
    by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · have hstep_eq : step s r =
        (match applyAll s s.balance r.legs with
         | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
         | none => (Outcome.rejected, s)) := by
        unfold step
        simp [hcond]
      cases hmatch : applyAll s s.balance r.legs with
      | none =>
        have hstep_none : step s r = (Outcome.rejected, s) := by rw [hstep_eq, hmatch]
        have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_none]
        rw [h1] at hOk
        exact absurd hOk (by decide)
      | some bal =>
        have hLegs : LegsOk s s.balance r.legs :=
          applyAll_some_implies_LegsOk2 s r.legs s.balance bal hmatch
        rw [hlegs] at hLegs
        simp only [LegsOk] at hLegs
        exact hLegs.1.2.1
    · have hstep_eq : step s r = (Outcome.rejected, s) := by
        unfold step
        simp [hcond]
      have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_eq]
      rw [h1] at hOk
      exact absurd hOk (by decide)
  have hsrc_eq : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := by
    show shift s.balance l l.source = _
    unfold shift
    have e1 : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
    have e2 : (if l.source = l.target then (l.amount : Int) else 0) = 0 := if_neg hne
    rw [e1, e2]
    omega
  have htgt_eq : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := by
    show shift s.balance l l.target = _
    unfold shift
    have hns : l.target ≠ l.source := fun h => hne h.symm
    have e1 : (if l.target = l.source then (l.amount : Int) else 0) = 0 := if_neg hns
    have e2 : (if l.target = l.target then (l.amount : Int) else 0) = (l.amount : Int) := if_pos rfl
    rw [e1, e2]
    omega
  rw [hsrc_eq] at hsrc
  rw [htgt_eq] at htgt
  exact ⟨hsrc, htgt⟩

theorem req_effects : Effects step := myEffects

theorem req_idempotency : Idempotent step := by
  intro s r hOk
  by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hstep_eq : step s r =
      (match applyAll s s.balance r.legs with
       | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
       | none => (Outcome.rejected, s)) := by
      unfold step
      simp [hcond]
    cases hmatch : applyAll s s.balance r.legs with
    | none =>
      have hstep_none : step s r = (Outcome.rejected, s) := by
        rw [hstep_eq, hmatch]
      have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_none]
      rw [h1] at hOk
      exact absurd hOk (by decide)
    | some bal =>
      have hstep_some : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
        rw [hstep_eq, hmatch]
      have h2eq : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
        rw [hstep_some]
      have hfirst : ∀ x, x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied := by
        intro x
        rw [h2eq]
        simp
      have hstep2 : step ({ s with balance := bal, applied := r.batchId :: s.applied } : State) r = (Outcome.rejected, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
        unfold step
        simp
      have hsecond : step (step s r).2 r = (.rejected, (step s r).2) := by
        rw [h2eq]
        exact hstep2
      exact ⟨hfirst, hsecond⟩
  · have hstep_eq : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hcond]
    have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_eq]
    rw [h1] at hOk
    exact absurd hOk (by decide)

theorem req_conservation : Conserves step := by
  intro s r hOk
  have hEff := myEffects s r hOk
  obtain ⟨hacc, hlim, hbal⟩ := hEff
  have hnd : s.accounts.Nodup := by
    by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · exact hcond.1
    · have hstep_eq : step s r = (Outcome.rejected, s) := by unfold step; simp [hcond]
      have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_eq]
      rw [h1] at hOk
      exact absurd hOk (by decide)
  have hlegs : LegsOk s s.balance r.legs := by
    by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · have hstep_eq : step s r =
        (match applyAll s s.balance r.legs with
         | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
         | none => (Outcome.rejected, s)) := by unfold step; simp [hcond]
      cases hmatch : applyAll s s.balance r.legs with
      | none =>
        have hstep_none : step s r = (Outcome.rejected, s) := by rw [hstep_eq, hmatch]
        have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_none]
        rw [h1] at hOk
        exact absurd hOk (by decide)
      | some bal => exact applyAll_some_implies_LegsOk2 s r.legs s.balance bal hmatch
    · have hstep_eq : step s r = (Outcome.rejected, s) := by unfold step; simp [hcond]
      have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_eq]
      rw [h1] at hOk
      exact absurd hOk (by decide)
  have hsum : sumOver s.accounts (applyLegs s.balance r.legs) = sumOver s.accounts s.balance :=
    applyLegs_sum_preserve s r.legs s.balance hlegs hnd
  unfold total
  have hcongr : sumOver (step s r).2.accounts (step s r).2.balance = sumOver s.accounts (step s r).2.balance := by
    rw [hacc]
  rw [hcongr]
  have hcongr2 : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (applyLegs s.balance r.legs) := by
    apply sumOver_congr
    intro a ha
    exact hbal a
  rw [hcongr2, hsum]

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hWL
  have hEff_of_ok : ∀ (hOk : (step s r).1 = Outcome.ok),
      (step s r).2.accounts = s.accounts ∧ (step s r).2.limit = s.limit ∧
      (∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a) :=
    fun hOk => myEffects s r hOk
  have hLegsOk_of_ok : ∀ (hOk : (step s r).1 = Outcome.ok), LegsOk s s.balance r.legs := by
    intro hOk
    by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · have hstep_eq : step s r =
        (match applyAll s s.balance r.legs with
         | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
         | none => (Outcome.rejected, s)) := by
        unfold step
        simp [hcond]
      cases hmatch : applyAll s s.balance r.legs with
      | none =>
        have hstep_none : step s r = (Outcome.rejected, s) := by rw [hstep_eq, hmatch]
        have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_none]
        rw [h1] at hOk
        exact absurd hOk (by decide)
      | some bal =>
        exact applyAll_some_implies_LegsOk2 s r.legs s.balance bal hmatch
    · have hstep_eq : step s r = (Outcome.rejected, s) := by
        unfold step
        simp [hcond]
      have h1 : (step s r).1 = Outcome.rejected := by rw [hstep_eq]
      rw [h1] at hOk
      exact absurd hOk (by decide)
  constructor
  · intro a ha
    by_cases hOk : (step s r).1 = Outcome.ok
    · obtain ⟨hacc, hlim, hbal⟩ := hEff_of_ok hOk
      have ha' : a ∈ s.accounts := by rw [← hacc]; exact ha
      have hbase : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ s.balance b := hWL
      have hlegs := hLegsOk_of_ok hOk
      have hpre := legs_prefix_within s r.legs s.balance hbase hlegs r.legs.length a ha'
      have htake : r.legs.take r.legs.length = r.legs := by simp
      rw [htake] at hpre
      have hbal_a : (step s r).2.balance a = applyLegs s.balance r.legs a := hbal a
      have hlim_a : (step s r).2.limit a = s.limit a := by rw [hlim]
      rw [hbal_a, hlim_a]
      exact hpre
    · by_cases hcond : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
      · have hstep_eq : step s r =
          (match applyAll s s.balance r.legs with
           | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
           | none => (Outcome.rejected, s)) := by
          unfold step
          simp [hcond]
        cases hmatch : applyAll s s.balance r.legs with
        | none =>
          have hstep2 : (step s r).2 = s := by rw [hstep_eq, hmatch]
          rw [hstep2] at ha ⊢
          exact hWL a ha
        | some bal =>
          have hstep_some : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
            rw [hstep_eq, hmatch]
          have h1 : (step s r).1 = Outcome.ok := by rw [hstep_some]
          exact absurd h1 hOk
      · have hstep_eq : step s r = (Outcome.rejected, s) := by
          unfold step
          simp [hcond]
        have hstep2 : (step s r).2 = s := by rw [hstep_eq]
        rw [hstep2] at ha ⊢
        exact hWL a ha
  · intro hOk k a ha
    have hbase : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ s.balance b := hWL
    have hlegs := hLegsOk_of_ok hOk
    exact legs_prefix_within s r.legs s.balance hbase hlegs k a ha

end Batch
