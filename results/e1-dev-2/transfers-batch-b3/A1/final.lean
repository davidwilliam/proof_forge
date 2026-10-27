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

/-- Final balances after the legs in order, or `none` if a leg is not allowed. -/
def applyAllAux (s : State) (bal : AccountId → Int) : List Leg → Option (AccountId → Int)
  | [] => some bal
  | l :: ls => if legAllowed s bal l then applyAllAux s (post bal l) ls else none

def applyAll (s : State) (legs : List Leg) : Option (AccountId → Int) :=
  applyAllAux s s.balance legs

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied then
    match applyAll s r.legs with
    | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (.rejected, s)
  else (.rejected, s)

theorem probe_contains (l : List Nat) (x : Nat) : (l.contains x = true) ↔ (x ∈ l) := by
  simp [List.contains_eq_mem]

theorem probe_bne (a b : Nat) : ((a != b) = true) ↔ (a ≠ b) := by simp
#check probe_contains
#check probe_bne

theorem legAllowed_correct3 (s : State) (bal : AccountId → Int) (l : Leg) :
    (legAllowed s bal l = true) ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [decide_eq_true_eq, List.contains_eq_mem, Bool.and_eq_true, bne_iff_ne, and_assoc]

theorem post_eq_shift2 (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem applyAllAux_some_of_LegsOk2 (s : State) (bal : AccountId → Int) (legs : List Leg) :
    LegsOk s bal legs → applyAllAux s bal legs = some (applyLegs bal legs) := by
  induction legs generalizing bal with
  | nil => intro _; rfl
  | cons l ls ih =>
    intro h
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    have hallow : legAllowed s bal l = true := (legAllowed_correct3 s bal l).mpr hok
    unfold applyAllAux
    rw [if_pos hallow, post_eq_shift2]
    exact ih _ hrest

theorem applyAllAux_none_of_not_LegsOk2 (s : State) (bal : AccountId → Int) (legs : List Leg) :
    ¬ LegsOk s bal legs → applyAllAux s bal legs = none := by
  induction legs generalizing bal with
  | nil =>
    intro h
    simp only [LegsOk] at h
    exact absurd trivial h
  | cons l ls ih =>
    intro h
    simp only [LegsOk] at h
    by_cases hok : LegOk s bal l
    · have hrest : ¬ LegsOk s (shift bal l) ls := fun hr => h ⟨hok, hr⟩
      have hrest' : ¬ LegsOk s (post bal l) ls := by rwa [post_eq_shift2]
      have hallow : legAllowed s bal l = true := (legAllowed_correct3 s bal l).mpr hok
      unfold applyAllAux
      rw [if_pos hallow]
      exact ih _ hrest'
    · have hallow : legAllowed s bal l = false := by
        rw [Bool.eq_false_iff]
        intro hc
        exact hok ((legAllowed_correct3 s bal l).mp hc)
      unfold applyAllAux
      rw [if_neg]
      intro hc
      rw [hallow] at hc
      exact Bool.false_ne_true hc

theorem req_single_leg_aux_test2 : True := by trivial

theorem test_tactics_auxA (s : State) (r : Request) (h : (step s r).1 = .ok)
  (hpre_neg : ¬ (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)) : False := by
  have hstep : step s r = (.rejected, s) := by
    unfold step
    rw [if_neg hpre_neg]
  rw [hstep] at h
  simp at h

theorem test_post_simp (s : State) (l : Leg) (hne : l.source ≠ l.target) :
  post s.balance l l.source = s.balance l.source - l.amount := by
  unfold post
  simp [hne]

theorem test_post_simp2 (s : State) (l : Leg) (hne : l.target ≠ l.source) :
  post s.balance l l.target = s.balance l.target + l.amount := by
  unfold post
  simp [hne]

theorem test_legok_single (s : State) (bal : AccountId → Int) (l : Leg)
  (h : LegOk s bal l) : LegsOk s bal [l] := by
  simp only [LegsOk]
  exact ⟨h, trivial⟩

theorem test_applylegs_single (bal : AccountId → Int) (l : Leg) :
  applyLegs bal [l] = shift bal l := rfl

theorem test_reduce_aux (s : State) (l : Leg) :
  applyAll s [l] = if legAllowed s s.balance l then some (post s.balance l) else none := by
  unfold applyAll
  simp only [applyAllAux]

theorem applyAllAux_some_eq_applyLegsX (s : State) (bal : AccountId → Int) (legs : List Leg) (out : AccountId → Int)
    (h : applyAllAux s bal legs = some out) : out = applyLegs bal legs := by
  induction legs generalizing bal out with
  | nil =>
    simp only [applyAllAux] at h
    simp only [applyLegs]
    have := Option.some_inj.mp h
    rw [this]
  | cons l ls ih =>
    unfold applyAllAux at h
    split at h
    next hallow =>
      rw [post_eq_shift2] at h
      have ihh := ih _ _ h
      simp only [applyLegs]
      rw [← ihh]
    next hallow =>
      simp at h

theorem req_idempotency_aux : Idempotent step := by
  unfold Idempotent
  intro s r hok
  by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · cases heq : applyAll s r.legs with
    | none =>
      have hstep : step s r = (.rejected, s) := by
        unfold step
        rw [if_pos hpre, heq]
      rw [hstep] at hok
      simp at hok
    | some bal =>
      have hstep : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
        unfold step
        rw [if_pos hpre, heq]
      have hfst : (step s r).1 = Outcome.ok := by rw [hstep]
      have hsnd : (step s r).2 = { s with balance := bal, applied := r.batchId :: s.applied } := by rw [hstep]
      constructor
      · intro x
        rw [hsnd]
        simp only
        constructor
        · intro hx
          simp at hx
          exact hx
        · intro hx
          simp
          exact hx
      · have hmem : r.batchId ∈ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied) := by
          simp
        have hpre2neg : ¬ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied)) := by
          intro h
          have hacc : (({ s with balance := bal, applied := r.batchId :: s.applied } : State).accounts = s.accounts) := rfl
          rw [hacc] at h
          -- h.2.2 : batchId ∉ ...
          have hnot : r.batchId ∉ (({ s with balance := bal, applied := r.batchId :: s.applied } : State).applied) := h.2.2
          simp at hnot
        have hstep2 : step ((step s r).2) r = (.rejected, (step s r).2) := by
          rw [hsnd]
          unfold step
          rw [if_neg hpre2neg]
        exact hstep2
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hpre]
    rw [hstep] at hok
    simp at hok

theorem shift_sum_of_LegOk_aux (s : State) (bal : AccountId → Int) (l : Leg)
    (hok : LegOk s bal l) (hnd : s.accounts.Nodup) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  obtain ⟨_, hne, hsrc, htgt, _⟩ := hok
  have hcongr : sumOver s.accounts (shift bal l) = sumOver s.accounts (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := by
    apply sumOver_congr
    intro a ha
    rfl
  rw [hcongr, sumOver_add]
  have hsub : sumOver s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) = sumOver s.accounts bal - sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0) :=
    sumOver_sub s.accounts bal (fun a => if a = l.source then (l.amount : Int) else 0)
  rw [hsub]
  rw [sumOver_ite_eq hnd l.source (l.amount : Int)]
  rw [sumOver_ite_eq hnd l.target (l.amount : Int)]
  rw [if_pos hsrc, if_pos htgt]
  omega

theorem applyLegs_sum_of_LegsOk_aux2 (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hnd : s.accounts.Nodup) (hok : LegsOk s bal legs) :
    sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    simp only [LegsOk] at hok
    obtain ⟨hok1, hrest⟩ := hok
    simp only [applyLegs]
    rw [ih (shift bal l) hrest]
    exact shift_sum_of_LegOk_aux s bal l hok1 hnd

theorem applyAllAux_some_LegsOk_aux (s : State) (bal : AccountId → Int) (legs : List Leg) (out : AccountId → Int)
    (h : applyAllAux s bal legs = some out) : LegsOk s bal legs := by
  induction legs generalizing bal out with
  | nil => trivial
  | cons l ls ih =>
    simp only [LegsOk]
    unfold applyAllAux at h
    by_cases hallow : legAllowed s bal l = true
    · rw [if_pos hallow] at h
      rw [post_eq_shift2] at h
      have hok : LegOk s bal l := (legAllowed_correct3 s bal l).mp hallow
      exact ⟨hok, ih _ _ h⟩
    · have hfalse : legAllowed s bal l = false := by
        cases hx : legAllowed s bal l with
        | true => rw [hx] at hallow; exact absurd rfl hallow
        | false => rfl
      rw [if_neg (by intro hc; rw [hfalse] at hc; exact Bool.false_ne_true hc)] at h
      simp at h

theorem my_test_thm : True := by trivial

theorem my_lemma2 : True := by trivial

theorem shift_within_aux (s : State) (bal : AccountId → Int) (l : Leg)
    (hok : LegOk s bal l)
    (hw : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ (shift bal l) a := by
  intro a ha
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hok
  have hwa := hw a ha
  unfold shift
  by_cases has : a = l.source
  · subst has
    have ht : ¬ (l.source = l.target) := hne
    simp [ht]
    exact hlim
  · by_cases hat : a = l.target
    · subst hat
      simp [has]
      have := hw l.target htgt
      omega
    · simp [has, hat]
      exact hw a ha

theorem legs_prefix_within_aux (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hok : LegsOk s bal legs)
    (hw : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) :
    ∀ k, ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    have htk : List.take k ([] : List Leg) = [] := by simp
    rw [htk]
    simp [applyLegs]
    exact hw a ha
  | cons l ls ih =>
    intro k a ha
    simp only [LegsOk] at hok
    obtain ⟨hok1, hrest⟩ := hok
    have hw_shift : ∀ b ∈ s.accounts, -(s.limit b : Int) ≤ (shift bal l) b :=
      shift_within_aux s bal l hok1 hw
    cases k with
    | zero =>
      simp
      exact hw a ha
    | succ k' =>
      simp only [List.take_succ_cons, applyLegs]
      exact ih (shift bal l) hrest hw_shift k' a ha

theorem req_valid_succeeds   : ValidSucceeds step := by
  unfold ValidSucceeds ValidBatch
  intro s r h
  obtain ⟨hnd, hne, hnot, hlegs⟩ := h
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied := ⟨hnd, hne, hnot⟩
  have hsome : applyAll s r.legs = some (applyLegs s.balance r.legs) := by
    unfold applyAll
    exact applyAllAux_some_of_LegsOk2 s s.balance r.legs hlegs
  unfold step
  rw [if_pos hpre, hsome]

theorem req_atomicity : Atomicity step := by
  intro s r hneg
  unfold step
  by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hlegs : ¬ LegsOk s s.balance r.legs := by
      intro hlegs
      apply hneg
      unfold ValidBatch
      exact ⟨hpre.1, hpre.2.1, hpre.2.2, hlegs⟩
    have hnone : applyAll s r.legs = none := by
      unfold applyAll
      exact applyAllAux_none_of_not_LegsOk2 s s.balance r.legs hlegs
    rw [if_pos hpre, hnone]
  · rw [if_neg hpre]

theorem req_single_leg : SingleLeg step := by
  unfold SingleLeg
  intro s r l hlegs hok
  have hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied := by
    by_cases h : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · exact h
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        rw [if_neg h]
      rw [hstep] at hok
      simp at hok
  cases hc : applyAll s r.legs with
  | none =>
    have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_pos hpre, hc]
    rw [hstep] at hok
    simp at hok
  | some bal =>
    have hstep : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
      unfold step
      rw [if_pos hpre, hc]
    have h_eq : applyAll s [l] = some bal := by
      rw [← hc, hlegs]
    have hallow : legAllowed s s.balance l = true := by
      cases hx : legAllowed s s.balance l with
      | true => rfl
      | false =>
        have hred := test_reduce_aux s l
        rw [hx] at hred
        simp at hred
        rw [hred] at h_eq
        simp at h_eq
    have hLegOk : LegOk s s.balance l := (legAllowed_correct3 s s.balance l).mp hallow
    obtain ⟨hpos, hne, hsrc_mem, htgt_mem, hlim⟩ := hLegOk
    have hred := test_reduce_aux s l
    rw [hallow] at hred
    simp at hred
    rw [hred] at h_eq
    simp at h_eq
    rw [← h_eq] at hstep
    have hsrc : (step s r).2.balance l.source = s.balance l.source - l.amount := by
      rw [hstep]
      simp only
      exact test_post_simp s l hne
    have htgt : (step s r).2.balance l.target = s.balance l.target + l.amount := by
      rw [hstep]
      simp only
      have hne2 : l.target ≠ l.source := fun h => hne h.symm
      exact test_post_simp2 s l hne2
    exact ⟨hsrc, htgt⟩

theorem req_effects : Effects step := by
  unfold Effects
  intro s r hok
  by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · have hstep : step s r = (match applyAll s r.legs with
      | some bal => (.ok, { s with balance := bal, applied := r.batchId :: s.applied })
      | none => (.rejected, s)) := by
      unfold step
      rw [if_pos hpre]
    cases heq : applyAll s r.legs with
    | none =>
      rw [heq] at hstep
      rw [hstep] at hok
      simp at hok
    | some bal =>
      rw [heq] at hstep
      rw [hstep]
      have hbal_eq : bal = applyLegs s.balance r.legs := by
        unfold applyAll at heq
        exact applyAllAux_some_eq_applyLegsX s s.balance r.legs bal heq
      constructor
      · rfl
      · constructor
        · rfl
        · intro a
          show bal a = applyLegs s.balance r.legs a
          rw [hbal_eq]
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hpre]
    rw [hstep] at hok
    simp at hok

theorem req_idempotency : Idempotent step := req_idempotency_aux

theorem req_conservation : Conserves step := by
  unfold Conserves total
  intro s r hok
  by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
  · cases heq : applyAll s r.legs with
    | none =>
      have hstep : step s r = (.rejected, s) := by
        unfold step
        rw [if_pos hpre, heq]
      rw [hstep] at hok
      simp at hok
    | some bal =>
      have hstep : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
        unfold step
        rw [if_pos hpre, heq]
      have hacc : ((step s r).2.accounts) = s.accounts := by rw [hstep]
      have hbalfun : ∀ a, (step s r).2.balance a = bal a := by
        intro a; rw [hstep]
      -- out equals applyLegs
      have hbal_eq : bal = applyLegs s.balance r.legs := by
        unfold applyAll at heq
        exact applyAllAux_some_eq_applyLegsX s s.balance r.legs bal heq
      -- validity from success
      have hLegsOk : LegsOk s s.balance r.legs := by
        unfold applyAll at heq
        exact applyAllAux_some_LegsOk_aux s s.balance r.legs bal heq
      have hsum : sumOver s.accounts (applyLegs s.balance r.legs) = sumOver s.accounts s.balance :=
        applyLegs_sum_of_LegsOk_aux2 s s.balance r.legs hpre.1 hLegsOk
      calc sumOver (step s r).2.accounts (step s r).2.balance
          = sumOver s.accounts bal := by
            rw [hacc]
            apply sumOver_congr
            intro a ha
            exact hbalfun a
        _ = sumOver s.accounts (applyLegs s.balance r.legs) := by
            rw [hbal_eq]
        _ = sumOver s.accounts s.balance := hsum
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hpre]
    rw [hstep] at hok
    simp at hok

theorem req_limit_every_step : LimitEveryStep step := by
  unfold LimitEveryStep WithinLimits
  intro s r hw
  constructor
  · -- WithinLimits of next state
    by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · cases heq : applyAll s r.legs with
      | none =>
        have hstep : step s r = (.rejected, s) := by
          unfold step
          rw [if_pos hpre, heq]
        have h2 : (step s r).2 = s := by rw [hstep]
        rw [h2]
        exact hw
      | some bal =>
        have hstep : step s r = (.ok, { s with balance := bal, applied := r.batchId :: s.applied }) := by
          unfold step
          rw [if_pos hpre, heq]
        have h2 : (step s r).2 = { s with balance := bal, applied := r.batchId :: s.applied } := by rw [hstep]
        rw [h2]
        intro a ha
        simp only at ha ⊢
        -- ha : a ∈ s.accounts, goal with updated state
        have hLegsOk : LegsOk s s.balance r.legs := by
          unfold applyAll at heq
          exact applyAllAux_some_LegsOk_aux s s.balance r.legs bal heq
        have hbal_eq : bal = applyLegs s.balance r.legs := by
          unfold applyAll at heq
          exact applyAllAux_some_eq_applyLegsX s s.balance r.legs bal heq
        rw [hbal_eq]
        have hfull := legs_prefix_within_aux s s.balance r.legs hLegsOk hw r.legs.length a ha
        have htake : r.legs.take r.legs.length = r.legs := by simp
        rw [htake] at hfull
        exact hfull
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        rw [if_neg hpre]
      have h2 : (step s r).2 = s := by rw [hstep]
      rw [h2]
      exact hw
  · intro hok k a ha
    by_cases hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied
    · cases heq : applyAll s r.legs with
      | none =>
        have hstep : step s r = (.rejected, s) := by
          unfold step
          rw [if_pos hpre, heq]
        rw [hstep] at hok
        simp at hok
      | some bal =>
        have hLegsOk : LegsOk s s.balance r.legs := by
          unfold applyAll at heq
          exact applyAllAux_some_LegsOk_aux s s.balance r.legs bal heq
        exact legs_prefix_within_aux s s.balance r.legs hLegsOk hw k a ha
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        rw [if_neg hpre]
      rw [hstep] at hok
      simp at hok

end Batch
