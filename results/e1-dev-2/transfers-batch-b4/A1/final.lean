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

def foo := 1

theorem mytest : True := trivial

theorem post_eq_shift2 (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem legAllowed_iff_LegOk_aux2 (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.contains_eq_mem, and_assoc]

theorem applyAll_some_aux (s : State) (bal : AccountId → Int) (legs : List Leg) (h : LegsOk s bal legs) : applyAll s bal legs = some (applyLegs bal legs) := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hl, hrest⟩ := h
    have hallow : legAllowed s bal l = true := (legAllowed_iff_LegOk_aux2 s bal l).mpr hl
    have e1 : applyAll s bal (l :: ls) = applyAll s (post bal l) ls := by simp [applyAll, hallow]
    have e2 : applyLegs bal (l :: ls) = applyLegs (post bal l) ls := by simp [applyLegs, post_eq_shift2]
    rw [e1, e2]
    have hpost : post bal l = shift bal l := post_eq_shift2 _ _
    rw [hpost]
    exact ih _ hrest

theorem applyAll_none_aux (s : State) (bal : AccountId → Int) (legs : List Leg) (h : ¬ LegsOk s bal legs) : applyAll s bal legs = none := by
  cases legs with
  | nil => simp [LegsOk] at h
  | cons l ls =>
    simp only [LegsOk, not_and] at h
    by_cases hall : legAllowed s bal l = true
    · have hleg : LegOk s bal l := (legAllowed_iff_LegOk_aux2 s bal l).mp hall
      have hrest : ¬ LegsOk s (shift bal l) ls := fun hh => h hleg hh
      have hpost : post bal l = shift bal l := post_eq_shift2 _ _
      have e1 : applyAll s bal (l :: ls) = applyAll s (post bal l) ls := by simp [applyAll, hall]
      rw [e1, hpost]
      exact applyAll_none_aux s (shift bal l) ls hrest
    · have e1 : applyAll s bal (l :: ls) = none := by simp [applyAll, hall]
      exact e1

theorem applyAll_some_eq_aux (s : State) (bal : AccountId → Int) (legs : List Leg) (bal' : AccountId → Int)
    (h : applyAll s bal legs = some bal') : bal' = applyLegs bal legs := by
  induction legs generalizing bal bal' with
  | nil =>
    simp [applyAll] at h
    rw [h]
    rfl
  | cons l ls ih =>
    simp only [applyAll] at h
    by_cases hall : legAllowed s bal l = true
    · simp [hall] at h
      have ih' := ih _ _ h
      have hpost : post bal l = shift bal l := post_eq_shift2 _ _
      have happ : applyLegs bal (l :: ls) = applyLegs (post bal l) ls := by
        simp [applyLegs, post_eq_shift2]
      rw [happ, hpost] at *
      exact ih'
    · simp [hall] at h

theorem req_idempotency_aux_test : True := trivial

theorem shift_sum_eq (s : State) (bal : AccountId → Int) (l : Leg)
    (hnodup : s.accounts.Nodup)
    (hsrc : l.source ∈ s.accounts) (htgt : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have hS : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0)
      = (l.amount : Int) := by
    have h := sumOver_ite_eq hnodup l.source (l.amount : Int)
    simp [hsrc] at h
    exact h
  have hT : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0)
      = (l.amount : Int) := by
    have h := sumOver_ite_eq hnodup l.target (l.amount : Int)
    simp [htgt] at h
    exact h
  have heq : ∀ a ∈ s.accounts, shift bal l a = bal a - (if a = l.source then (l.amount : Int) else 0)
      + (if a = l.target then (l.amount : Int) else 0) := by
    intro a _
    rfl
  have hcongr : sumOver s.accounts (shift bal l)
      = sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)
        + (if a = l.target then (l.amount : Int) else 0)) :=
    sumOver_congr _ _ _ heq
  rw [hcongr, sumOver_add, sumOver_sub, hS, hT]
  omega

theorem applyLegs_sum_eq (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hnodup : s.accounts.Nodup) (hlegs : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hl, hrest⟩ := hlegs
    simp only [applyLegs]
    rw [ih (shift bal l) hrest, shift_sum_eq s bal l hnodup hl.2.2.1 hl.2.2.2.1]

theorem applyAll_some_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (bal' : AccountId → Int) (h : applyAll s bal legs = some bal') :
    LegsOk s bal legs := by
  by_cases hok : LegsOk s bal legs
  · exact hok
  · have hnone := applyAll_none_aux s bal legs hok
    rw [hnone] at h
    simp at h

theorem shift_at_source_aux2 (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.source = bal l.source - (l.amount : Int) := by
  unfold shift
  simp [hne]

theorem shift_at_target_aux2 (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.target = bal l.target + (l.amount : Int) := by
  unfold shift
  have hns : l.target ≠ l.source := Ne.symm hne
  simp [hns]

theorem shift_at_other_aux2 (bal : AccountId → Int) (l : Leg) (a : AccountId)
    (hs : a ≠ l.source) (ht : a ≠ l.target) :
    shift bal l a = bal a := by
  unfold shift
  simp [hs, ht]

theorem limit_shift_preserves_aux3 (s : State) (bal : AccountId → Int) (l : Leg)
    (hW : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hLeg : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hLeg
  intro a ha
  by_cases hs : a = l.source
  · subst hs
    rw [shift_at_source_aux2 bal l hne]
    exact hlim
  · by_cases ht : a = l.target
    · subst ht
      rw [shift_at_target_aux2 bal l hne]
      have hbase := hW l.target htgt
      omega
    · rw [shift_at_other_aux2 bal l a hs ht]
      exact hW a ha

theorem limit_applyLegs_take_aux3 (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hW : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hlegs : LegsOk s bal legs) :
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts → -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    have htk : (List.nil : List Leg).take k = [] := by cases k <;> simp
    rw [htk]
    show -(s.limit a : Int) ≤ applyLegs bal [] a
    simp only [applyLegs]
    exact hW a ha
  | cons l ls ih =>
    obtain ⟨hl, hrest⟩ := hlegs
    have hW' : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a :=
      limit_shift_preserves_aux3 s bal l hW hl
    intro k a ha
    cases k with
    | zero =>
      simp only [List.take_zero, applyLegs]
      exact hW a ha
    | succ n =>
      have htake : (l :: ls).take (n + 1) = l :: (ls.take n) := by simp
      have happ : applyLegs bal ((l :: ls).take (n + 1)) = applyLegs (shift bal l) (ls.take n) := by
        rw [htake]
        rfl
      rw [happ]
      exact ih (shift bal l) hW' hrest n a ha

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r hv
  obtain ⟨hnodup, hne, hnmem, hlegs⟩ := hv
  have hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) := ⟨hnodup, hne, hnmem⟩
  have hA := applyAll_some_aux s s.balance r.legs hlegs
  have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
    unfold step
    rw [if_pos hc, hA]
  rw [hstep]

theorem req_atomicity : Atomicity step := by
  intro s r hnv
  unfold step
  by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · simp [hc]
    have hleg : ¬ LegsOk s s.balance r.legs := by
      intro hlegs
      apply hnv
      exact ⟨hc.1, hc.2.1, hc.2.2, hlegs⟩
    rw [applyAll_none_aux s s.balance r.legs hleg]
  · simp [hc]

theorem req_single_leg : SingleLeg step := by
  intro s r l hr hok
  have hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) := by
    by_cases h : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
    · exact h
    · have hstep : step s r = (.rejected, s) := by unfold step; simp [h]
      rw [hstep] at hok
      simp at hok
  have hstep_eq : step s r =
      match applyAll s s.balance r.legs with
      | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
      | none => (.rejected, s) := by
    unfold step
    simp [hc]
  rw [hr] at hstep_eq
  have hall : legAllowed s s.balance l = true := by
    cases hleg : legAllowed s s.balance l with
    | true => rfl
    | false =>
      have happ_none : applyAll s s.balance [l] = none := by simp [applyAll, hleg]
      rw [happ_none] at hstep_eq
      rw [hstep_eq] at hok
      simp at hok
  have hLegOk : LegOk s s.balance l := (legAllowed_iff_LegOk_aux2 s s.balance l).mp hall
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hLegOk
  have happ : applyAll s s.balance [l] = some (post s.balance l) := by simp [applyAll, hall]
  rw [happ] at hstep_eq
  have hbal : (step s r).2.balance = post s.balance l := by rw [hstep_eq]
  rw [hbal]
  have hnsym : l.target ≠ l.source := Ne.symm hne
  constructor
  · show post s.balance l l.source = s.balance l.source - (l.amount : Int)
    unfold post
    have h1 : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by simp
    have h2 : (if l.source = l.target then (l.amount : Int) else 0) = 0 := by simp [hne]
    rw [h1, h2]
    omega
  · show post s.balance l l.target = s.balance l.target + (l.amount : Int)
    unfold post
    have h1 : (if l.target = l.source then (l.amount : Int) else 0) = 0 := by simp [hnsym]
    have h2 : (if l.target = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by simp
    rw [h1, h2]
    omega

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hstep : step s r =
        match applyAll s s.balance r.legs with
        | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
        | none => (.rejected, s) := by
      unfold step
      simp [hc]
    cases hA : applyAll s s.balance r.legs with
    | none =>
      have hrej : step s r = (.rejected, s) := by rw [hstep, hA]
      rw [hrej] at hok
      simp at hok
    | some bal =>
      have hok2 : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
        rw [hstep, hA]
      have hbal_eq : bal = applyLegs s.balance r.legs :=
        applyAll_some_eq_aux s s.balance r.legs bal hA
      refine ⟨?_, ?_, ?_⟩
      · have hh : (step s r).2.accounts = ({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts := by
          rw [hok2]
        simpa using hh
      · have hh : (step s r).2.limit = ({ s with balance := bal, applied := r.batchId :: s.applied } : State).limit := by
          rw [hok2]
        simpa using hh
      · intro a
        have hh : (step s r).2.balance a = bal a := by rw [hok2]
        rw [hh, hbal_eq]
  · have hrej : step s r = (.rejected, s) := by unfold step; simp [hc]
    rw [hrej] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hstep : step s r =
        match applyAll s s.balance r.legs with
        | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
        | none => (.rejected, s) := by
      unfold step
      simp [hc]
    cases hA : applyAll s s.balance r.legs with
    | none =>
      have hrej : step s r = (.rejected, s) := by rw [hstep, hA]
      rw [hrej] at hok
      simp at hok
    | some bal =>
      have hok2 : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
        rw [hstep, hA]
      have h2eq : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
        rw [hok2]
      constructor
      · intro x
        rw [h2eq]
        simp
      · have hmem : r.batchId ∈ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied) := by
          simp
        have hcond : ¬ ((({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧
            r.legs ≠ [] ∧ r.batchId ∉ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied)) := by
          intro h
          exact h.2.2 hmem
        have hstep2 : step ({ s with balance := bal, applied := r.batchId :: s.applied } : State) r =
            (.rejected, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
          unfold step
          simp only [hcond, ite_false]
        rw [← h2eq] at hstep2
        exact hstep2
  · have hrej : step s r = (.rejected, s) := by unfold step; simp [hc]
    rw [hrej] at hok
    simp at hok

theorem req_conservation : Conserves step := by
  intro s r hok
  have heff := req_effects s r hok
  obtain ⟨hacc, hlim, hbal⟩ := heff
  -- extract legs-ok from success
  have hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) := by
    by_cases h : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
    · exact h
    · have hrej : step s r = (.rejected, s) := by unfold step; simp [h]
      rw [hrej] at hok
      simp at hok
  have hstep : step s r =
      match applyAll s s.balance r.legs with
      | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
      | none => (.rejected, s) := by
    unfold step
    simp [hc]
  cases hA : applyAll s s.balance r.legs with
  | none =>
    have hrej : step s r = (.rejected, s) := by rw [hstep, hA]
    rw [hrej] at hok
    simp at hok
  | some bal =>
    have hlegs : LegsOk s s.balance r.legs := applyAll_some_LegsOk s s.balance r.legs bal hA
    have hnodup : s.accounts.Nodup := hc.1
    have hsum : sumOver s.accounts (applyLegs s.balance r.legs) = sumOver s.accounts s.balance :=
      applyLegs_sum_eq s s.balance r.legs hnodup hlegs
    unfold total
    -- goal: sumOver (step ..).2.accounts (step ..).2.balance = sumOver s.accounts s.balance
    have hcongr : sumOver (step s r).2.accounts (step s r).2.balance
        = sumOver s.accounts (applyLegs s.balance r.legs) := by
      rw [hacc]
      exact sumOver_congr s.accounts _ _ (fun a _ => hbal a)
    rw [hcongr]
    exact hsum

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hW
  constructor
  · intro a ha
    by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
    · have hstep : step s r =
          match applyAll s s.balance r.legs with
          | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
          | none => (.rejected, s) := by
        unfold step
        rw [if_pos hc]
      cases hA : applyAll s s.balance r.legs with
      | none =>
        have heq : step s r = (.rejected, s) := by rw [hstep, hA]
        rw [heq] at ha ⊢
        exact hW a ha
      | some bal =>
        have heq : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
          rw [hstep, hA]
        rw [heq] at ha ⊢
        simp only at ha ⊢
        have hlegs : LegsOk s s.balance r.legs :=
          applyAll_some_LegsOk s s.balance r.legs bal hA
        have hbal_eq : bal = applyLegs s.balance r.legs :=
          applyAll_some_eq_aux s s.balance r.legs bal hA
        rw [hbal_eq]
        have hfull := limit_applyLegs_take_aux3 s s.balance r.legs hW hlegs (r.legs.length) a ha
        have htk : r.legs.take r.legs.length = r.legs := by simp
        rw [htk] at hfull
        exact hfull
    · have heq : step s r = (.rejected, s) := by unfold step; rw [if_neg hc]
      rw [heq] at ha ⊢
      exact hW a ha
  · intro hok k a ha
    by_cases hc : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
    · have hstep : step s r =
          match applyAll s s.balance r.legs with
          | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
          | none => (.rejected, s) := by
        unfold step
        rw [if_pos hc]
      cases hA : applyAll s s.balance r.legs with
      | none =>
        have heq : step s r = (.rejected, s) := by rw [hstep, hA]
        rw [heq] at hok
        simp at hok
      | some bal =>
        have hlegs : LegsOk s s.balance r.legs :=
          applyAll_some_LegsOk s s.balance r.legs bal hA
        exact limit_applyLegs_take_aux3 s s.balance r.legs hW hlegs k a ha
    · have heq : step s r = (.rejected, s) := by unfold step; rw [if_neg hc]
      rw [heq] at hok
      simp at hok

end Batch
