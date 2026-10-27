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

/-- Final balances after the legs, or `none` if a leg is not allowed.
    Threads balances forward in list order. -/
def applyAllGo (s : State) (bal : AccountId → Int) : List Leg → Option (AccountId → Int)
  | [] => some bal
  | l :: ls =>
    if legAllowed s bal l then applyAllGo s (post bal l) ls else none

def applyAll (s : State) (legs : List Leg) : Option (AccountId → Int) :=
  applyAllGo s s.balance legs

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied then
    match applyAll s r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

theorem test_contains2 (s : State) (x : AccountId) : (s.accounts.contains x = true) ↔ x ∈ s.accounts := by
  simp

theorem test_ne2 (a b : Nat) (h : (a != b) = true) : a ≠ b := by
  simpa using h

theorem test_decide1 (p : Prop) [Decidable p] (h : decide p = true) : p := of_decide_eq_true h
#check of_decide_eq_true
#check List.contains_eq_mem
#check BEq.beq

theorem legAllowed_ok_true_aux3 (s : State) (bal : AccountId → Int) (l : Leg)
    (h : legAllowed s bal l = true) : LegOk s bal l := by
  unfold legAllowed at h
  simp at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold LegOk
  exact ⟨h1, h2, h3, h4, h5⟩

theorem legAllowed_of_ok_aux3 (s : State) (bal : AccountId → Int) (l : Leg)
    (h : LegOk s bal l) : legAllowed s bal l = true := by
  unfold LegOk at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold legAllowed
  simp
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem post_eq_shift (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem applyLegs_cons (bal : AccountId → Int) (l : Leg) (ls : List Leg) :
    applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl

theorem applyAllGo_of_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : LegsOk s bal legs) : applyAllGo s bal legs = some (applyLegs bal legs) := by
  induction legs generalizing bal with
  | nil => simp [applyAllGo, applyLegs]
  | cons l ls ih =>
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    have hallow : legAllowed s bal l = true := legAllowed_of_ok_aux3 s bal l hok
    have hpost : post bal l = shift bal l := rfl
    simp only [applyAllGo, hallow, ↓reduceIte]
    rw [hpost]
    have h2 := ih (shift bal l) hrest
    simp only [applyLegs_cons] at *
    exact h2

theorem applyAllGo_eq_none_of_not_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : ¬ LegsOk s bal legs) : applyAllGo s bal legs = none := by
  induction legs generalizing bal with
  | nil =>
    exact absurd True.intro h
  | cons l ls ih =>
    simp only [applyAllGo]
    cases heq : legAllowed s bal l with
    | false => simp [heq]
    | true =>
      simp [heq]
      have hok : LegOk s bal l := legAllowed_ok_true_aux3 s bal l heq
      have hrest : ¬ LegsOk s (post bal l) ls := by
        intro hls
        have heq2 : post bal l = shift bal l := rfl
        rw [heq2] at hls
        exact h ⟨hok, hls⟩
      exact ih (post bal l) hrest

theorem req_single_leg_aux4 : SingleLeg step := by
  unfold SingleLeg
  intro s r l hlegs hok
  unfold step at hok ⊢
  rw [hlegs] at hok ⊢
  by_cases hc : s.accounts.Nodup ∧ [l] ≠ [] ∧ r.batchId ∉ s.applied
  · rw [if_pos hc] at hok ⊢
    simp only [applyAll, applyAllGo] at hok ⊢
    cases heq : legAllowed s s.balance l with
    | false =>
      simp [heq] at hok
    | true =>
      simp [heq] at hok ⊢
      have hLeg : LegOk s s.balance l := legAllowed_ok_true_aux3 s s.balance l heq
      obtain ⟨_, hne, _, _, _⟩ := hLeg
      unfold post
      constructor
      · simp [hne]
      · have hne2 : l.target ≠ l.source := Ne.symm hne
        simp [hne2]
  · rw [if_neg hc] at hok
    simp at hok

theorem applyAllGo_some_eq_applyLegs2 (s : State) (bal bal' : AccountId → Int) (legs : List Leg)
    (h : applyAllGo s bal legs = some bal') : bal' = applyLegs bal legs := by
  induction legs generalizing bal bal' with
  | nil =>
    simp [applyAllGo] at h
    subst h
    rfl
  | cons l ls ih =>
    simp only [applyAllGo] at h
    by_cases hall : legAllowed s bal l = true
    · simp [hall] at h
      have hpost : post bal l = shift bal l := rfl
      have ih' := ih (post bal l) bal' h
      rw [hpost] at ih'
      simp only [applyLegs_cons] at *
      exact ih'
    · simp [hall] at h

theorem req_idem_dbg7 : Idempotent step := by
  unfold Idempotent step applyAll
  intro s r hok
  by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · rw [if_pos hc] at hok ⊢
    cases hmatch : applyAllGo s s.balance r.legs with
    | none =>
      simp_all
    | some bal =>
      simp_all
  · rw [if_neg hc] at hok
    simp at hok

theorem shift_total_aux2 (s : State) (bal : AccountId → Int) (l : Leg)
    (hsrc : l.source ∈ s.accounts) (htgt : l.target ∈ s.accounts)
    (hnd : s.accounts.Nodup) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have h1 : (shift bal l) = fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0) := rfl
  rw [h1, sumOver_add, sumOver_sub]
  have hsrc_sum : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hnd l.source (l.amount : Int)
    rw [h]
    simp [hsrc]
  have htgt_sum : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hnd l.target (l.amount : Int)
    rw [h]
    simp [htgt]
  rw [hsrc_sum, htgt_sum]
  omega

theorem applyLegs_total_aux2 (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hnd : s.accounts.Nodup) (hok : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    simp only [LegsOk] at hok
    obtain ⟨hlok, hrest⟩ := hok
    unfold LegOk at hlok
    obtain ⟨_, _, hsrc, htgt, _⟩ := hlok
    show sumOver s.accounts (applyLegs (shift bal l) ls) = sumOver s.accounts bal
    rw [ih (shift bal l) hrest, shift_total_aux2 s bal l hsrc htgt hnd]

theorem applyAllGo_some_implies_LegsOk_aux (s : State) (bal : AccountId → Int) (legs : List Leg) (bal' : AccountId → Int)
    (h : applyAllGo s bal legs = some bal') : LegsOk s bal legs := by
  induction legs generalizing bal bal' with
  | nil => simp only [LegsOk]
  | cons l ls ih =>
    simp only [applyAllGo] at h
    by_cases hall : legAllowed s bal l = true
    · simp [hall] at h
      have hok : LegOk s bal l := legAllowed_ok_true_aux3 s bal l hall
      have hrest : LegsOk s (post bal l) ls := ih (post bal l) bal' h
      have heq2 : post bal l = shift bal l := rfl
      rw [heq2] at hrest
      simp only [LegsOk]
      exact ⟨hok, hrest⟩
    · have heq : legAllowed s bal l = false := by cases he : legAllowed s bal l <;> simp_all
      simp [heq] at h

theorem foo_test123 : True := trivial

theorem foo_lemma_test124 : True := trivial

theorem shift_within_ok : ∀ (s : State) (bal : AccountId → Int) (l : Leg),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) → LegOk s bal l →
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  intro s bal l hWL hOk a ha
  obtain ⟨hpos, hne, hsrc, htgt, hfloor⟩ := hOk
  show -(s.limit a : Int) ≤ (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)
    + (if a = l.target then (l.amount : Int) else 0)) a
  by_cases hs : a = l.source
  · subst hs
    have ht : ¬ (l.source = l.target) := hne
    simp only [ht, ↓reduceIte] at *
    have := hfloor
    omega
  · have h1 : ¬ (a = l.source) := hs
    simp only [h1, ↓reduceIte] at *
    by_cases ht : a = l.target
    · subst ht
      have h := hWL l.target htgt
      omega
    · have h2 : ¬ (a = l.target) := ht
      simp only [h2, ↓reduceIte] at *
      have h := hWL a ha
      omega

theorem prefix_within_ok : ∀ (s : State) (bal : AccountId → Int) (legs : List Leg),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) → LegsOk s bal legs →
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts →
      -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  intro s bal legs hWL hOk
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    simp only [List.take_nil, applyLegs]
    exact hWL a ha
  | cons l ls ih =>
    simp only [LegsOk] at hOk
    obtain ⟨hlok, hrest⟩ := hOk
    intro k a ha
    cases k with
    | zero =>
      simp only [List.take_zero, applyLegs]
      exact hWL a ha
    | succ k' =>
      simp only [List.take_succ_cons]
      have hbal' : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ shift bal l b :=
        shift_within_ok s bal l hWL hlok
      have h := ih (shift bal l) hbal' hrest k' a ha
      -- h : -limit ≤ applyLegs (shift bal l) (take k' ls) a
      -- goal : -limit ≤ applyLegs bal (l :: take k' ls) a
      -- applyLegs bal (l::...) = applyLegs (shift bal l) ...
      have heq : applyLegs bal (l :: (ls.take k')) = applyLegs (shift bal l) (ls.take k') := rfl
      rw [heq]
      exact h

theorem applyLegs_within_ok : ∀ (s : State) (bal : AccountId → Int) (legs : List Leg),
    (∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) → LegsOk s bal legs →
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal legs a := by
  intro s bal legs hWL hOk a ha
  have h := prefix_within_ok s bal legs hWL hOk (legs.length) a ha
  rwa [List.take_length] at h

theorem dbg_simp_probe (s : State) (r : Request)
    (hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
    (bal : AccountId → Int)
    (hmatch : applyAllGo s s.balance r.legs = some bal) :
    (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
  unfold step applyAll
  rw [if_pos hc, hmatch]

theorem req_valid_succeeds : ValidSucceeds step := by
  unfold ValidSucceeds ValidBatch step applyAll
  intro s r h
  obtain ⟨hnd, hne, hfresh, hlegs⟩ := h
  have hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied := ⟨hnd, hne, hfresh⟩
  rw [if_pos hc]
  have hsome : applyAllGo s s.balance r.legs = some (applyLegs s.balance r.legs) :=
    applyAllGo_of_LegsOk s s.balance r.legs hlegs
  rw [hsome]

theorem req_atomicity : Atomicity step := by
  unfold Atomicity ValidBatch step applyAll
  intro s r h
  by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hleg : ¬ LegsOk s s.balance r.legs := by
      intro hlegs
      exact h ⟨hc.1, hc.2.1, hc.2.2, hlegs⟩
    have hnone := applyAllGo_eq_none_of_not_LegsOk s s.balance r.legs hleg
    rw [if_pos hc, hnone]
  · rw [if_neg hc]

theorem req_single_leg       : SingleLeg step := by
  unfold SingleLeg
  intro s r l hlegs hok
  unfold step at hok ⊢
  rw [hlegs] at hok ⊢
  by_cases hc : s.accounts.Nodup ∧ [l] ≠ [] ∧ r.batchId ∉ s.applied
  · rw [if_pos hc] at hok ⊢
    simp only [applyAll, applyAllGo] at hok ⊢
    cases heq : legAllowed s s.balance l with
    | false =>
      simp [heq] at hok
    | true =>
      simp [heq] at hok ⊢
      have hLeg : LegOk s s.balance l := legAllowed_ok_true_aux3 s s.balance l heq
      obtain ⟨_, hne, _, _, _⟩ := hLeg
      unfold post
      constructor
      · simp [hne]
      · have hne2 : l.target ≠ l.source := Ne.symm hne
        simp [hne2]
  · rw [if_neg hc] at hok
    simp at hok

theorem req_effects : Effects step := by
  unfold Effects step applyAll
  intro s r hok
  by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · rw [if_pos hc] at hok ⊢
    cases hmatch : applyAllGo s s.balance r.legs with
    | none =>
      simp [hmatch] at hok
    | some bal =>
      simp [hmatch] at hok ⊢
      have hbal : bal = applyLegs s.balance r.legs :=
        applyAllGo_some_eq_applyLegs2 s s.balance bal r.legs hmatch
      simp [hbal]
  · rw [if_neg hc] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  unfold Idempotent step applyAll
  intro s r hok
  by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · rw [if_pos hc] at hok ⊢
    cases hmatch : applyAllGo s s.balance r.legs with
    | none =>
      simp_all
    | some bal =>
      simp_all
  · rw [if_neg hc] at hok
    simp at hok

theorem req_conservation : Conserves step := by
  unfold Conserves total
  intro s r hok
  by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hok2 : (match applyAll s r.legs with
      | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
      | none => (Outcome.rejected, s)).1 = Outcome.ok := by
      have hstep : step s r =
        (match applyAll s r.legs with
        | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
        | none => (Outcome.rejected, s)) := by
        unfold step
        rw [if_pos hc]
      rw [← hstep]
      exact hok
    have htot : (match applyAll s r.legs with
      | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
      | none => (Outcome.rejected, s)).2 = (step s r).2 := by
      have hstep : step s r =
        (match applyAll s r.legs with
        | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
        | none => (Outcome.rejected, s)) := by
        unfold step
        rw [if_pos hc]
      rw [← hstep]
    rw [← htot]
    cases hmatch : applyAll s r.legs with
    | none =>
      simp [hmatch] at hok2
    | some bal =>
      simp [hmatch] at hok2 ⊢
      unfold applyAll at hmatch
      have hbal : bal = applyLegs s.balance r.legs :=
        applyAllGo_some_eq_applyLegs2 s s.balance bal r.legs hmatch
      have hLegs : LegsOk s s.balance r.legs :=
        applyAllGo_some_implies_LegsOk_aux s s.balance r.legs bal hmatch
      rw [hbal]
      exact applyLegs_total_aux2 s s.balance r.legs hc.1 hLegs
  · have hstep : step s r = (Outcome.rejected, s) := by
      unfold step
      rw [if_neg hc]
    rw [hstep] at hok
    simp at hok

theorem req_limit_every_step : LimitEveryStep step := by
  unfold LimitEveryStep
  intro s r hWL
  refine ⟨?_, ?_⟩
  · show WithinLimits (step s r).2
    unfold WithinLimits at hWL ⊢
    by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · cases hmatch : applyAllGo s s.balance r.legs with
      | none =>
        have h2 : (step s r).2 = s := by unfold step applyAll; rw [if_pos hc, hmatch]
        rw [h2]
        exact hWL
      | some bal =>
        have h2 : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
          unfold step applyAll; rw [if_pos hc, hmatch]
        have hLegs : LegsOk s s.balance r.legs :=
          applyAllGo_some_implies_LegsOk_aux s s.balance r.legs bal hmatch
        have hbal : bal = applyLegs s.balance r.legs :=
          applyAllGo_some_eq_applyLegs2 s s.balance bal r.legs hmatch
        rw [h2]
        intro a ha
        simp only at ha ⊢
        rw [hbal]
        exact applyLegs_within_ok s s.balance r.legs hWL hLegs a ha
    · have h2 : (step s r).2 = s := by unfold step; rw [if_neg hc]
      rw [h2]
      exact hWL
  · intro hok k a ha
    by_cases hc : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · cases hmatch : applyAllGo s s.balance r.legs with
      | none =>
        have h1 : (step s r).1 = Outcome.rejected := by unfold step applyAll; rw [if_pos hc, hmatch]
        rw [h1] at hok
        simp at hok
      | some bal =>
        have hLegs : LegsOk s s.balance r.legs :=
          applyAllGo_some_implies_LegsOk_aux s s.balance r.legs bal hmatch
        exact prefix_within_ok s s.balance r.legs hWL hLegs k a ha
    · have h1 : (step s r).1 = Outcome.rejected := by unfold step; rw [if_neg hc]
      rw [h1] at hok
      simp at hok

end Batch
