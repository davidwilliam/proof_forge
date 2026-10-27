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

/-- Apply the legs in order, updating the balances as each leg is applied; stop at the
first leg that is not allowed. -/
def applyAll (s : State) : (AccountId → Int) → List Leg → Bool × (AccountId → Int)
  | bal, [] => (true, bal)
  | bal, l :: ls => if legAllowed s bal l then applyAll s (post bal l) ls else (false, bal)

def step : Impl := fun s r =>
  if decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) then
    let (done, bal) := applyAll s s.balance r.legs
    if done then (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    else (.rejected, s)
  else (.rejected, s)

theorem foo_test : True := trivial

theorem foo_test2 : 1 = 1 := rfl

theorem test_bne2 (a b : Nat) (h : (a != b) = true) : a ≠ b := by
  simpa using h

theorem test_bne_rev (a b : Nat) (h : a ≠ b) : (a != b) = true := by
  simpa using h

theorem legAllowed_iff_aux (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h1, (by simpa using h2), h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, (by simpa using h2)⟩, h3⟩, h4⟩, h5⟩

theorem post_eq_shift_aux (bal : AccountId → Int) (l : Leg) :
    post bal l = shift bal l := rfl

theorem applyAll_ok_aux (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : LegsOk s bal legs) :
    applyAll s bal legs = (true, applyLegs bal legs) := by
  induction legs generalizing bal with
  | nil => simp [applyAll, applyLegs]
  | cons l ls ih =>
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    have hall : legAllowed s bal l = true := (legAllowed_iff_aux s bal l).mpr hok
    simp only [applyAll, hall, ↓reduceIte]
    have hpost : post bal l = shift bal l := rfl
    rw [hpost]
    rw [ih (shift bal l) hrest]
    rfl

theorem helper_eq_test2 (s : State) (bal : AccountId → Int) (l : Leg) (ls : List Leg)
    (hall : legAllowed s bal l = true) :
    (applyAll s bal (l :: ls)).1 = (applyAll s (post bal l) ls).1 := by
  have h : applyAll s bal (l :: ls) = applyAll s (post bal l) ls := by
    simp [applyAll, hall]
  rw [h]

theorem applyAll_fst_false_of_not_LegsOk3 (s : State) (bal : AccountId → Int) (legs : List Leg)
    (h : ¬ LegsOk s bal legs) :
    (applyAll s bal legs).1 = false := by
  induction legs generalizing bal with
  | nil =>
    simp [LegsOk] at h
  | cons l ls ih =>
    simp only [LegsOk] at h
    by_cases hall : legAllowed s bal l = true
    · have hok : LegOk s bal l := (legAllowed_iff_aux s bal l).mp hall
      have hrest : ¬ LegsOk s (shift bal l) ls := fun hr => h ⟨hok, hr⟩
      have hpost : post bal l = shift bal l := rfl
      have ih' := ih (post bal l) (by rw [hpost]; exact hrest)
      have heq : applyAll s bal (l :: ls) = applyAll s (post bal l) ls := by simp [applyAll, hall]
      rw [heq]
      exact ih'
    · have heq : applyAll s bal (l :: ls) = (false, bal) := by simp [applyAll, hall]
      rw [heq]

theorem mytest_snd_aux (s : State) (r : Request) (h : (step s r).1 = Outcome.ok) :
    (step s r).2 = { s with balance := (applyAll s s.balance r.legs).2, applied := r.batchId :: s.applied } := by
  unfold step at h ⊢
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true :=
      decide_eq_true hpre
    rw [hdec]
    simp only [↓reduceIte]
    cases hAp : applyAll s s.balance r.legs with
    | mk done bal =>
      simp [hAp] at h ⊢
      cases hdone : done <;> simp_all
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    rw [hdec] at h
    simp at h

theorem step_rejected_of_apply_false (s : State) (r : Request)
    (h : (applyAll s s.balance r.legs).1 = false) : (step s r).1 = Outcome.rejected := by
  unfold step
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true :=
      decide_eq_true hpre
    rw [hdec]
    simp only [↓reduceIte]
    cases hAp : applyAll s s.balance r.legs with
    | mk done bal =>
      have hdone : done = false := by
        calc done = (done, bal).1 := rfl
          _ = (applyAll s s.balance r.legs).1 := by rw [hAp]
          _ = false := h
      simp [hdone]
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    rw [hdec]
    simp

theorem single_leg_allow_aux (s : State) (l : Leg) (h : (applyAll s s.balance [l]).1 = true) : legAllowed s s.balance l = true := by
  cases hA : legAllowed s s.balance l
  · have hF2 : (applyAll s s.balance [l]).1 = false := by
      simp [applyAll, hA]
    rw [hF2] at h
    contradiction
  · rfl

theorem req_effects_test1 (s : State) (r : Request)
    (hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true)
    (hAllEq : applyAll s s.balance r.legs = (true, applyLegs s.balance r.legs)) :
    (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by
  simp [step, hdec, hAllEq]

theorem req_effects_test2 (s : State) (r : Request)
    (hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false) :
    (step s r).1 = Outcome.rejected := by
  simp [step, hdec]

theorem req_idempotency_aux_test : True := trivial

theorem req_idempotency_tmp : Idempotent step := by
  intro s r hok
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true :=
      decide_eq_true hpre
    have hfst : (applyAll s s.balance r.legs).1 = true := by
      cases hF : (applyAll s s.balance r.legs).1 with
      | true => rfl
      | false =>
        have hr := step_rejected_of_apply_false s r hF
        rw [hr] at hok
        cases hok
    cases hAp : applyAll s s.balance r.legs with
    | mk done bal =>
      have hdone : done = true := by
        have h1 : (done, bal).1 = true := by rw [← hAp]; exact hfst
        simpa using h1
      have hStepEq : step s r = (Outcome.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
        unfold step
        rw [hdec]
        simp only [↓reduceIte, hAp, hdone, ↓reduceIte]
      have h2 : (step s r).2 = { s with balance := bal, applied := r.batchId :: s.applied } := by
        rw [hStepEq]
      refine ⟨?_, ?_⟩
      · intro x
        rw [h2]
        simp only
        constructor
        · intro hx
          simp at hx
          exact hx
        · intro hx
          simp
          exact hx
      · have hmem : r.batchId ∈ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied := by
          simp
        have hpre2neg : ¬ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied) := by
          intro hC
          exact hC.2.2 hmem
        have hdec2 : decide ((({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied)) = false :=
          decide_eq_false hpre2neg
        have hStep2 : step ({ s with balance := bal, applied := r.batchId :: s.applied } : State) r = (.rejected, { s with balance := bal, applied := r.batchId :: s.applied }) := by
          unfold step
          rw [hdec2]
          simp
        rw [← h2] at hStep2
        exact hStep2
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    have hRej : (step s r).1 = Outcome.rejected :=
      req_effects_test2 s r hdec
    rw [hRej] at hok
    cases hok

theorem total_shift_eq_auxC2 (s : State) (bal : AccountId → Int) (l : Leg)
    (hNodup : s.accounts.Nodup) (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  unfold shift
  have hAdd : sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0))
      = sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
        + sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) := by
    have := sumOver_add s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) (fun a => if a = l.target then (l.amount : Int) else 0)
    simpa using this
  have hSub : sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0))
      = sumOver s.accounts bal - sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) := by
    have := sumOver_sub s.accounts bal (fun a => if a = l.source then (l.amount : Int) else 0)
    simpa using this
  rw [hAdd, hSub]
  have hsIte : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hNodup l.source (l.amount : Int)
    simp [hs] at h
    exact h
  have htIte : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by
    have h := sumOver_ite_eq hNodup l.target (l.amount : Int)
    simp [ht] at h
    exact h
  rw [hsIte, htIte]
  omega

theorem total_applyLegs_eq_auxC2 (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hNodup : s.accounts.Nodup) (hOk : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => simp [applyLegs]
  | cons l ls ih =>
    simp only [LegsOk] at hOk
    obtain ⟨hok, hrest⟩ := hOk
    simp only [applyLegs]
    have hShift : sumOver s.accounts (shift bal l) = sumOver s.accounts bal :=
      total_shift_eq_auxC2 s bal l hNodup hok.2.2.1 hok.2.2.2.1
    have hIH := ih (shift bal l) hrest
    omega

theorem shift_within_HELPER (s : State) (bal : AccountId → Int) (l : Leg)
    (hW : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegOk s bal l) (a : AccountId) (ha : a ∈ s.accounts) :
    -(s.limit a : Int) ≤ shift bal l a := by
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hOk
  show -(s.limit a : Int) ≤ bal a - (if a = l.source then (l.amount : Int) else 0)
    + (if a = l.target then (l.amount : Int) else 0)
  by_cases hs : a = l.source
  · subst hs
    rw [if_pos rfl, if_neg hne]
    simp
    exact hlim
  · rw [if_neg hs]
    have hW' := hW a ha
    by_cases ht : a = l.target
    · rw [if_pos ht]
      have hamt : (0 : Int) ≤ l.amount := by exact_mod_cast Nat.zero_le _
      omega
    · rw [if_neg ht]
      simp
      exact hW'

theorem prefix_within_HELPER2 (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hW : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegsOk s bal legs) :
    ∀ (k : Nat) (a : AccountId), a ∈ s.accounts →
      -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    simp only [List.take_nil, applyLegs]
    exact hW a ha
  | cons l ls ih =>
    simp only [LegsOk] at hOk
    obtain ⟨hok, hrest⟩ := hOk
    intro k a ha
    cases k with
    | zero =>
      simp only [List.take_zero, applyLegs]
      exact hW a ha
    | succ n =>
      simp only [List.take_succ_cons]
      simp only [applyLegs]
      have hW' : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ shift bal l b :=
        fun b hb => shift_within_HELPER s bal l hW hok b hb
      exact ih (shift bal l) hW' hrest n a ha

theorem tmp_single_src3 (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.source = bal l.source - (l.amount : Int) := by
  unfold shift
  simp [hne]

theorem tmp_single_tgt3 (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.target = bal l.target + (l.amount : Int) := by
  have hTne : l.target ≠ l.source := fun h => hne h.symm
  unfold shift
  simp [hTne]





theorem plan0_shift_target (bal : AccountId → Int) (l : Leg)
    (hne : l.source ≠ l.target) :
    shift bal l l.target = bal l.target + (l.amount : Int) := by
  have hTne : l.target ≠ l.source := fun h => hne h.symm
  unfold shift
  simp [hTne]




theorem plan0_balance_of_step_ok (s : State) (r : Request) (a : AccountId)
    (hok : (step s r).1 = Outcome.ok) :
    (step s r).2.balance a = applyLegs s.balance r.legs a := by
  have h2 := mytest_snd_aux s r hok
  have hLegs : LegsOk s s.balance r.legs := by
    by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
    · have hfst : (applyAll s s.balance r.legs).1 = true := by
        cases hF : (applyAll s s.balance r.legs).1 with
        | true => rfl
        | false =>
          have hr := step_rejected_of_apply_false s r hF
          rw [hr] at hok
          cases hok
      by_cases hN : LegsOk s s.balance r.legs
      · exact hN
      · have hF := applyAll_fst_false_of_not_LegsOk3 s s.balance r.legs hN
        rw [hfst] at hF
        contradiction
    · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
        decide_eq_false hpre
      have hRej : (step s r).1 = Outcome.rejected :=
        req_effects_test2 s r hdec
      rw [hRej] at hok
      cases hok
  have hAll : applyAll s s.balance r.legs = (true, applyLegs s.balance r.legs) :=
    applyAll_ok_aux s s.balance r.legs hLegs
  have h2nd : (applyAll s s.balance r.legs).2 = applyLegs s.balance r.legs := by
    rw [hAll]
  calc (step s r).2.balance a = ((applyAll s s.balance r.legs).2) a := by rw [h2]
    _ = applyLegs s.balance r.legs a := by rw [h2nd]




theorem plan0_singleton_check (bal : AccountId → Int) (l : Leg) :
    applyLegs bal [l] = shift bal l := rfl

theorem plan0_applyLegs_singleton (bal : AccountId → Int) (l : Leg) :
    applyLegs bal [l] = shift bal l := rfl

theorem plan0_shift_source (bal : AccountId → Int) (l : Leg)
    (hne : l.source ≠ l.target) :
    shift bal l l.source = bal l.source - (l.amount : Int) := by
  unfold shift
  simp [hne]

theorem plan0_shift_target_proof (bal : AccountId → Int) (l : Leg)
    (hne : l.source ≠ l.target) :
    shift bal l l.target = bal l.target + (l.amount : Int) := by
  have hTne : l.target ≠ l.source := fun h => hne h.symm
  unfold shift
  simp [hTne]

theorem plan0_legsOk_of_step_ok (s : State) (r : Request)
    (hok : (step s r).1 = Outcome.ok) :
    LegsOk s s.balance r.legs := by
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hfst : (applyAll s s.balance r.legs).1 = true := by
      cases hF : (applyAll s s.balance r.legs).1 with
      | true => rfl
      | false =>
        have hr := step_rejected_of_apply_false s r hF
        rw [hr] at hok
        cases hok
    by_cases hN : LegsOk s s.balance r.legs
    · exact hN
    · have hF := applyAll_fst_false_of_not_LegsOk3 s s.balance r.legs hN
      rw [hfst] at hF
      contradiction
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    have hRej : (step s r).1 = Outcome.rejected :=
      req_effects_test2 s r hdec
    rw [hRej] at hok
    cases hok

theorem plan0_balance_tmp (s : State) (r : Request) (a : AccountId)
    (hok : (step s r).1 = Outcome.ok) :
    (step s r).2.balance a = applyLegs s.balance r.legs a := by
  have h2 := mytest_snd_aux s r hok
  have hLegs : LegsOk s s.balance r.legs := by
    by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
    · have hfst : (applyAll s s.balance r.legs).1 = true := by
        cases hF : (applyAll s s.balance r.legs).1 with
        | true => rfl
        | false =>
          have hr := step_rejected_of_apply_false s r hF
          rw [hr] at hok
          cases hok
      by_cases hN : LegsOk s s.balance r.legs
      · exact hN
      · have hF := applyAll_fst_false_of_not_LegsOk3 s s.balance r.legs hN
        rw [hfst] at hF
        contradiction
    · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
        decide_eq_false hpre
      have hRej : (step s r).1 = Outcome.rejected :=
        req_effects_test2 s r hdec
      rw [hRej] at hok
      cases hok
  have hAll : applyAll s s.balance r.legs = (true, applyLegs s.balance r.legs) :=
    applyAll_ok_aux s s.balance r.legs hLegs
  have h2nd : (applyAll s s.balance r.legs).2 = applyLegs s.balance r.legs := by
    rw [hAll]
  calc (step s r).2.balance a = ((applyAll s s.balance r.legs).2) a := by rw [h2]
    _ = applyLegs s.balance r.legs a := by rw [h2nd]

theorem plan0_source_ne_target_of_singleton_ok (s : State) (r : Request) (l : Leg)
    (hlegs : r.legs = [l]) (hok : (step s r).1 = Outcome.ok) :
    l.source ≠ l.target := by
  have hLegs := plan0_legsOk_of_step_ok s r hok
  rw [hlegs] at hLegs
  simp only [LegsOk] at hLegs
  obtain ⟨hokLeg, _⟩ := hLegs
  exact hokLeg.2.1

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hnodup, hne, hnotmem, hlegs⟩ := h
  have hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) :=
    ⟨hnodup, hne, hnotmem⟩
  have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true :=
    decide_eq_true hpre
  have hAll : applyAll s s.balance r.legs = (true, applyLegs s.balance r.legs) :=
    applyAll_ok_aux s s.balance r.legs hlegs
  unfold step
  rw [hdec]
  simp only [↓reduceIte, hAll, ↓reduceIte]

theorem req_atomicity  : Atomicity step := by
  intro s r hn
  simp only [ValidBatch] at hn
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true :=
      decide_eq_true hpre
    have hlegs : ¬ LegsOk s s.balance r.legs := by
      intro hlegs
      apply hn
      exact ⟨hpre.1, hpre.2.1, hpre.2.2, hlegs⟩
    have hfst : (applyAll s s.balance r.legs).1 = false :=
      applyAll_fst_false_of_not_LegsOk3 s s.balance r.legs hlegs
    have hstep : step s r = (.rejected, s) := by
      unfold step
      simp only [hdec, ↓reduceIte]
      cases hAp : applyAll s s.balance r.legs with
      | mk done bal =>
        have hdone : done = false := by
          have := hAp ▸ hfst
          simpa using this
        simp [hdone, hAp]
    exact hstep
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    have hstep : step s r = (.rejected, s) := by
      unfold step
      simp [hdec]
    exact hstep

theorem req_single_leg       : SingleLeg step := by
  intro s r l hlegs hok
  have hne := plan0_source_ne_target_of_singleton_ok s r l hlegs hok
  have hsrc : (step s r).2.balance l.source = applyLegs s.balance r.legs l.source :=
    plan0_balance_tmp s r l.source hok
  have htgt : (step s r).2.balance l.target = applyLegs s.balance r.legs l.target :=
    plan0_balance_tmp s r l.target hok
  rw [hlegs] at hsrc htgt
  rw [plan0_applyLegs_singleton] at hsrc htgt
  rw [plan0_shift_source _ _ hne] at hsrc
  rw [plan0_shift_target_proof _ _ hne] at htgt
  exact ⟨hsrc, htgt⟩

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true :=
      decide_eq_true hpre
    have hfst : (applyAll s s.balance r.legs).1 = true := by
      cases hF : (applyAll s s.balance r.legs).1 with
      | true => rfl
      | false =>
        have hr := step_rejected_of_apply_false s r hF
        rw [hr] at hok
        cases hok
    have hLegs : LegsOk s s.balance r.legs := by
      by_cases hN : LegsOk s s.balance r.legs
      · exact hN
      · have hF := applyAll_fst_false_of_not_LegsOk3 s s.balance r.legs hN
        rw [hfst] at hF
        contradiction
    have hAllEq : applyAll s s.balance r.legs = (true, applyLegs s.balance r.legs) :=
      applyAll_ok_aux s s.balance r.legs hLegs
    have hStep2 : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } :=
      req_effects_test1 s r hdec hAllEq
    refine ⟨?_, ?_, ?_⟩
    · rw [hStep2]
    · rw [hStep2]
    · intro a
      rw [hStep2]
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    have hRej : (step s r).1 = Outcome.rejected :=
      req_effects_test2 s r hdec
    rw [hRej] at hok
    cases hok

theorem req_idempotency      : Idempotent step := by
  intro s r hok
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = true :=
      decide_eq_true hpre
    have hfst : (applyAll s s.balance r.legs).1 = true := by
      cases hF : (applyAll s s.balance r.legs).1 with
      | true => rfl
      | false =>
        have hr := step_rejected_of_apply_false s r hF
        rw [hr] at hok
        cases hok
    cases hAp : applyAll s s.balance r.legs with
    | mk done bal =>
      have hdone : done = true := by
        have h1 : (done, bal).1 = true := by rw [← hAp]; exact hfst
        simpa using h1
      have hStepEq : step s r = (Outcome.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
        unfold step
        rw [hdec]
        simp only [↓reduceIte, hAp, hdone, ↓reduceIte]
      have h2 : (step s r).2 = { s with balance := bal, applied := r.batchId :: s.applied } := by
        rw [hStepEq]
      refine ⟨?_, ?_⟩
      · intro x
        rw [h2]
        simp only
        constructor
        · intro hx
          simp at hx
          exact hx
        · intro hx
          simp
          exact hx
      · have hmem : r.batchId ∈ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied := by
          simp
        have hpre2neg : ¬ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied) := by
          intro hC
          exact hC.2.2 hmem
        have hdec2 : decide ((({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ ({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied)) = false :=
          decide_eq_false hpre2neg
        have hStep2 : step ({ s with balance := bal, applied := r.batchId :: s.applied } : State) r = (.rejected, { s with balance := bal, applied := r.batchId :: s.applied }) := by
          unfold step
          rw [hdec2]
          simp
        rw [← h2] at hStep2
        exact hStep2
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    have hRej : (step s r).1 = Outcome.rejected :=
      req_effects_test2 s r hdec
    rw [hRej] at hok
    cases hok

theorem req_conservation : Conserves step := by
  intro s r hok
  have hEff := req_effects s r hok
  obtain ⟨hAccEq, hLimEq, hBalEq⟩ := hEff
  have hTot : total (step s r).2 = sumOver s.accounts (applyLegs s.balance r.legs) := by
    unfold total
    rw [hAccEq]
    apply sumOver_congr
    intro a ha
    exact hBalEq a
  rw [hTot]
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hNodup : s.accounts.Nodup := hpre.1
    have hfst : (applyAll s s.balance r.legs).1 = true := by
      cases hF : (applyAll s s.balance r.legs).1 with
      | true => rfl
      | false =>
        have hr := step_rejected_of_apply_false s r hF
        rw [hr] at hok
        cases hok
    have hNN : ¬ ¬ LegsOk s s.balance r.legs := by
      intro hN
      have hF := applyAll_fst_false_of_not_LegsOk3 s s.balance r.legs hN
      rw [hfst] at hF
      contradiction
    have hLegs : LegsOk s s.balance r.legs := Classical.not_not.mp hNN
    have hPres := total_applyLegs_eq_auxC2 s s.balance r.legs hNodup hLegs
    have hTotS : total s = sumOver s.accounts s.balance := rfl
    rw [hTotS]
    exact hPres
  · have hdec : decide (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) = false :=
      decide_eq_false hpre
    have hRej : (step s r).1 = Outcome.rejected := req_effects_test2 s r hdec
    rw [hRej] at hok
    cases hok

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hW
  constructor
  · by_cases hV : ValidBatch s r
    · have hok : (step s r).1 = Outcome.ok := req_valid_succeeds s r hV
      obtain ⟨hnodup, hne, hnotmem, hLegs⟩ := hV
      have hEff := req_effects s r hok
      obtain ⟨hAcc, hLim, hBal⟩ := hEff
      intro a ha
      have ha' : a ∈ s.accounts := by rw [← hAcc]; exact ha
      have hPref := prefix_within_HELPER2 s s.balance r.legs hW hLegs
      have hBalA := hBal a
      have hLimA : (step s r).2.limit a = s.limit a := by rw [hLim]
      rw [hLimA, hBalA]
      have h := hPref r.legs.length a ha'
      rw [List.take_length] at h
      exact h
    · have hStep := req_atomicity s r hV
      have hEq : (step s r).2 = s := by rw [hStep]
      rw [hEq]
      exact hW
  · intro hok k a ha
    by_cases hV : ValidBatch s r
    · obtain ⟨hnodup, hne, hnotmem, hLegs⟩ := hV
      exact prefix_within_HELPER2 s s.balance r.legs hW hLegs k a ha
    · have hStep := req_atomicity s r hV
      rw [hStep] at hok
      simp at hok

end Batch
