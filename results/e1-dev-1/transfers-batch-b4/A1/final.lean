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

theorem foo_test : True := trivial

theorem post_eq_shift_aux (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem shift_post_aux2 (bal : AccountId → Int) (l : Leg) (a : AccountId) : post bal l a = shift bal l a := rfl

theorem ne_bne_probe (a b : Nat) (h : (a != b) = true) : a ≠ b := by
  simpa using h

theorem ne_bne_probe2 (a b : Nat) (h : a ≠ b) : (a != b) = true := by
  simpa using h

theorem ne_iff_bne_aux (a b : Nat) : ((a != b) = true) ↔ a ≠ b := by
  constructor
  · intro h; simpa using h
  · intro h; simpa using h

theorem legAllowed_iff_LegOk2 (s : State) (bal : AccountId → Int) (l : Leg) :
    (legAllowed s bal l = true) ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem]
  rw [ne_iff_bne_aux]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem applyAll_of_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg) :
    LegsOk s bal legs → applyAll s bal legs = some (applyLegs bal legs) := by
  induction legs generalizing bal with
  | nil => intro _; rfl
  | cons l ls ih =>
    intro h
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    have hallow : legAllowed s bal l = true := (legAllowed_iff_LegOk2 s bal l).mpr hok
    have hpost : post bal l = shift bal l := rfl
    have hstep : applyAll s bal (l :: ls) = applyAll s (post bal l) ls := by
      simp [applyAll, hallow]
    rw [hstep, hpost]
    have ih' := ih _ hrest
    have happ : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [happ, ih']

theorem applyAll_eq_none_of_not_LegsOk (s : State) (bal : AccountId → Int) (legs : List Leg) :
    ¬ LegsOk s bal legs → applyAll s bal legs = none := by
  induction legs generalizing bal with
  | nil =>
    intro h
    simp [LegsOk] at h
  | cons l ls ih =>
    intro h
    simp only [LegsOk] at h
    by_cases hallow : legAllowed s bal l = true
    · have hok : LegOk s bal l := (legAllowed_iff_LegOk2 s bal l).mp hallow
      have hrest : ¬ LegsOk s (shift bal l) ls := fun hr => h ⟨hok, hr⟩
      have hpost : post bal l = shift bal l := rfl
      have hstep : applyAll s bal (l :: ls) = applyAll s (post bal l) ls := by
        simp [applyAll, hallow]
      rw [hstep, hpost]
      exact ih _ hrest
    · have hstep : applyAll s bal (l :: ls) = none := by
        simp [applyAll, hallow]
      exact hstep

theorem req_single_leg_aux_check (s : State) (l : Leg) (hall : legAllowed s s.balance l = true) :
    applyAll s s.balance [l] = some (post s.balance l) := by
  simp [applyAll, hall]

theorem dbg_step_simp (s : State) (r : Request) (hpre : s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) :
    step s r = (match applyAll s s.balance r.legs with
    | some bal => (Outcome.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (Outcome.rejected, s)) := by
  unfold step
  simp [hpre]

theorem dbg_step_neg (s : State) (r : Request) (hpre : ¬ (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)) :
    step s r = (Outcome.rejected, s) := by
  unfold step
  simp [hpre]

theorem tmp_rw_test (s : State) (r : Request) (l : Leg)
    (hstep0 : step s r = (Outcome.ok, { s with balance := post s.balance l, applied := r.batchId :: s.applied }))
    (hsrc : post s.balance l l.source = s.balance l.source - (l.amount : Int)) :
    (step s r).2.balance l.source = s.balance l.source - (l.amount : Int) := by
  have h1 : (step s r).2 = ({ s with balance := post s.balance l, applied := r.batchId :: s.applied } : State) := by
    simp [hstep0]
  simp [h1, hsrc]

theorem tmp_simp_test (s : State) (r : Request) (l : Leg) (hr : r.legs = [l])
    (hstep0 : step s r = match applyAll s s.balance r.legs with
    | some bal => (Outcome.ok, { s with balance := bal, applied := r.batchId :: s.applied })
    | none => (Outcome.rejected, s))
    (happ : applyAll s s.balance [l] = some (post s.balance l))
    (hsrc : post s.balance l l.source = s.balance l.source - (l.amount : Int))
    (htgt : post s.balance l l.target = s.balance l.target + (l.amount : Int)) :
    (step s r).2.balance l.source = s.balance l.source - (l.amount : Int) ∧
    (step s r).2.balance l.target = s.balance l.target + (l.amount : Int) := by
  simp [hstep0, hr, happ, hsrc, htgt]

theorem applyAll_some_eq_aux (s : State) (bal : AccountId → Int) (legs : List Leg) (bal' : AccountId → Int) :
    applyAll s bal legs = some bal' → bal' = applyLegs bal legs := by
  induction legs generalizing bal bal' with
  | nil =>
    intro h
    simp [applyAll] at h
    subst h
    rfl
  | cons l ls ih =>
    intro h
    cases he : legAllowed s bal l with
    | true =>
      have heq : applyAll s bal (l :: ls) = applyAll s (post bal l) ls := by simp [applyAll, he]
      rw [heq] at h
      exact ih _ _ h
    | false =>
      have heq : applyAll s bal (l :: ls) = none := by simp [applyAll, he]
      rw [heq] at h
      simp at h

theorem req_valid_succeeds   : ValidSucceeds step := by
  intro s r hv
  obtain ⟨hnd, hne, hnap, hlegs⟩ := hv
  have hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied) := ⟨hnd, hne, hnap⟩
  have hsome : applyAll s s.balance r.legs = some (applyLegs s.balance r.legs) :=
    applyAll_of_LegsOk s s.balance r.legs hlegs
  show ((step s r).1 = .ok)
  unfold step
  rw [if_pos hpre, hsome]

theorem req_atomicity : Atomicity step := by
  intro s r hneg
  unfold ValidBatch at hneg
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hlegs : ¬ LegsOk s s.balance r.legs := by
      intro hlegs
      exact hneg ⟨hpre.1, hpre.2.1, hpre.2.2, hlegs⟩
    have hnone : applyAll s s.balance r.legs = none :=
      applyAll_eq_none_of_not_LegsOk s s.balance r.legs hlegs
    unfold step
    rw [if_pos hpre, hnone]
  · unfold step
    rw [if_neg hpre]

theorem req_single_leg : SingleLeg step := by
  intro s r l hr hok
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hstep_if : step s r =
        (match applyAll s s.balance r.legs with
        | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
        | none => (Outcome.rejected, s)) := by
      unfold step
      simp [hpre]
    cases hres : applyAll s s.balance r.legs with
    | none =>
      rw [hstep_if, hres] at hok
      simp at hok
    | some bal =>
      have hstep : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
        rw [hstep_if, hres]
      have h2eq : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
        rw [hstep]
      rw [hr] at hres
      have hallow : legAllowed s s.balance l = true := by
        cases hb : legAllowed s s.balance l with
        | true => rfl
        | false =>
          have heq : applyAll s s.balance [l] = none := by simp [applyAll, hb]
          rw [heq] at hres
          simp at hres
      have hbal : bal = post s.balance l := by
        have heq : applyAll s s.balance [l] = some (post s.balance l) := by simp [applyAll, hallow]
        rw [heq] at hres
        simp at hres
        exact hres.symm
      have hok_leg : LegOk s s.balance l := (legAllowed_iff_LegOk2 s s.balance l).mp hallow
      obtain ⟨_, hne, _, _, _⟩ := hok_leg
      have hs : bal l.source = s.balance l.source - (l.amount : Int) := by
        rw [hbal]
        exact post_source_val2 s.balance l hne
      have ht : bal l.target = s.balance l.target + (l.amount : Int) := by
        rw [hbal]
        exact post_target_val2 s.balance l hne
      constructor
      · rw [h2eq]
        simp [hs]
      · rw [h2eq]
        simp [ht]
  · have hstep_rej : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hpre]
    rw [hstep_rej] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hstep_if : step s r =
      (match applyAll s s.balance r.legs with
      | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
      | none => (Outcome.rejected, s)) := by
      unfold step
      simp [hpre]
    cases hres : applyAll s s.balance r.legs with
    | none =>
      rw [hstep_if, hres] at hok
      simp at hok
    | some bal =>
      have hbal_eq : bal = applyLegs s.balance r.legs :=
        applyAll_some_eq_aux s s.balance r.legs bal hres
      have hstep : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
        rw [hstep_if, hres]
      rw [hstep]
      refine ⟨rfl, rfl, ?_⟩
      intro a
      simp [hbal_eq]
  · have hstep_rej : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hpre]
    rw [hstep_rej] at hok
    simp at hok

theorem req_idempotency      : Idempotent step := by
  intro s r hok
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hstep_if : step s r =
      (match applyAll s s.balance r.legs with
      | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
      | none => (Outcome.rejected, s)) := by
      unfold step
      simp [hpre]
    cases hres : applyAll s s.balance r.legs with
    | none =>
      rw [hstep_if, hres] at hok
      simp at hok
    | some bal =>
      have hstep : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
        rw [hstep_if, hres]
      have h2eq : (step s r).2 = ({ s with balance := bal, applied := r.batchId :: s.applied } : State) := by
        rw [hstep]
      constructor
      · intro x
        rw [h2eq]
        simp
      · have hmem : r.batchId ∈ (({ s with balance := bal, applied := r.batchId :: s.applied } : State)).applied := by
          simp
        have hpre2 : ¬ (((step s r).2.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ (step s r).2.applied)) := by
          rw [h2eq]
          simp
          intro _ _ hm
          exact hm hmem
        have hrej : step (step s r).2 r = (Outcome.rejected, (step s r).2) := by
          unfold step
          rw [if_neg hpre2]
        exact hrej
  · have hstep_rej : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hpre]
    rw [hstep_rej] at hok
    simp at hok

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hpre : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied)
  · have hstep_if : step s r =
        (match applyAll s s.balance r.legs with
        | some bal => (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State))
        | none => (Outcome.rejected, s)) := by
      unfold step
      simp [hpre]
    cases hres : applyAll s s.balance r.legs with
    | none =>
      rw [hstep_if, hres] at hok
      simp at hok
    | some bal =>
      have hstep : step s r = (Outcome.ok, ({ s with balance := bal, applied := r.batchId :: s.applied } : State)) := by
        rw [hstep_if, hres]
      have hsum : sumOver s.accounts bal = sumOver s.accounts s.balance :=
        cons_applyAll_sum2 s s.balance bal r.legs hpre.1 hres
      rw [hstep]
      simp only [total]
      exact hsum
  · have hstep_rej : step s r = (Outcome.rejected, s) := by
      unfold step
      simp [hpre]
    rw [hstep_rej] at hok
    simp at hok

theorem req_limit_every_step : LimitEveryStep step := sorry

end Batch
