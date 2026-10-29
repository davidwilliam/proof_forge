import Batch.Spec
import Batch.Lemmas
namespace Batch
/-- Admission check of one leg against the running balances. -/
def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && decide (l.source ≠ l.target) &&
  decide (l.source ∈ s.accounts) &&
  decide (l.target ∈ s.accounts) &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - l.amount)

/-- Recursive boolean check that every leg is admissible in order. -/
def legsOkB (s : State) : (AccountId → Int) → List Leg → Bool
  | _, [] => true
  | bal, l :: ls => if legAllowed s bal l then legsOkB s (shift bal l) ls else false

def step : Impl := fun s r =>
  if decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else (.rejected, s)

def myTestDef : Nat := 1

theorem myTestThm : True := trivial

theorem legAllowed_true_iff (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  simp [legAllowed, LegOk, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩ := h
    exact ⟨h1,h2,h3,h4,h5⟩
  · intro h
    obtain ⟨h1,h2,h3,h4,h5⟩ := h
    exact ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩

theorem tmpTest (s : State) (bal : AccountId → Int) (l : Leg) (ls : List Leg)
    (h : legAllowed s bal l = true) :
    (if legAllowed s bal l then legsOkB s (shift bal l) ls else false) = legsOkB s (shift bal l) ls := by
  simp [h]

theorem tmpTest2 (s : State) (bal : AccountId → Int) (l : Leg) (ls : List Leg)
    (hc : ¬ legAllowed s bal l = true) :
    ((if legAllowed s bal l then legsOkB s (shift bal l) ls else false) = true) ↔ False := by
  simp [hc]

theorem legsOkB_true_iff_aux (s : State) (bal : AccountId → Int) (legs : List Leg) :
    legsOkB s bal legs = true ↔ LegsOk s bal legs := by
  induction legs generalizing bal with
  | nil => simp [legsOkB, LegsOk]
  | cons l ls ih =>
    have hleg : legAllowed s bal l = true ↔ LegOk s bal l :=
      legAllowed_true_iff s bal l
    by_cases h : legAllowed s bal l = true
    · have h1 : legsOkB s bal (l :: ls) = legsOkB s (shift bal l) ls := by simp [legsOkB, h]
      have h2 : LegOk s bal l := hleg.mp h
      rw [h1, ih]
      constructor
      · intro hx; exact ⟨h2, hx⟩
      · intro hx; exact hx.2
    · have h1 : legsOkB s bal (l :: ls) = false := by simp [legsOkB, h]
      have h2 : ¬ LegOk s bal l := fun hx => h (hleg.mpr hx)
      rw [h1]
      simp only [Bool.false_eq_true]
      apply Iff.symm
      apply iff_false_intro
      intro hx
      exact h2 hx.1

theorem tmp_single_probe2 (a : Int) : a - 0 = a := by simp

theorem tmp_single_probe3 (a : Int) : a + 0 = a := by simp

theorem tmp_bool_probe (c : Bool) (h : c = true) (x y : Nat) : (if c then x else y) = x := by simp [h]

theorem tmp_if_true_probe (a b : Nat) : (if (true : Bool) then a else b) = a := by simp

theorem tmp_if_false_probe (a b : Nat) : (if (false : Bool) then a else b) = b := by simp

theorem tmp_step_true_aux3 (s : State) (r : Request) (h : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    (step s r).1 = Outcome.ok := by
  unfold step
  rw [h]
  simp

theorem tmp_shift_src2 (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.source = bal l.source - (l.amount : Int) := by
  unfold shift
  simp [hne]

theorem tmp_shift_tgt2 (bal : AccountId → Int) (l : Leg) (hne : l.source ≠ l.target) :
    shift bal l l.target = bal l.target + (l.amount : Int) := by
  unfold shift
  have h1 : ¬ (l.target = l.source) := Ne.symm hne
  simp [h1]

theorem tmp_effects_probe2 (s : State) (r : Request)
    (h : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    (step s r).2.accounts = s.accounts := by
  simp only [step, h, ↓reduceIte]

theorem tmp_effects_branch (s : State) (r : Request) (hC : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    (step s r).2.limit = s.limit := by
  simp only [step, hC, ↓reduceIte]

theorem tmp_effects_shape (s : State) (r : Request)
    (h : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    (step s r).1 = Outcome.ok := by
  simp only [step, h, ↓reduceIte]

theorem tmp_effects_goal (s : State) (r : Request)
    (h : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    (step s r).2.accounts = s.accounts ∧ (step s r).2.limit = s.limit ∧ ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
  simp only [step, h, ↓reduceIte]
  exact ⟨trivial, trivial, fun a => trivial⟩

theorem tmp_effects_neg (s : State) (r : Request)
    (hc : ¬ (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    step s r = (Outcome.rejected, s) := by
  simp only [step, if_neg hc]

theorem idem_helper_test (s : State) (r : Request)
    (hc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    step (step s r).2 r = (Outcome.rejected, (step s r).2) := by
  have h2eq : (step s r).2 = ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State) := by
    simp only [step, hc, if_true]
  have hmem : r.batchId ∈ (step s r).2.applied := by
    rw [h2eq]
    simp
  have hdec : ¬ r.batchId ∉ (step s r).2.applied := by
    simp [hmem]
  have hc2 : ¬ (decide ((step s r).2.accounts.Nodup) && decide (r.legs ≠ []) && decide (r.batchId ∉ (step s r).2.applied) && legsOkB (step s r).2 ((step s r).2.balance) r.legs) = true := by
    simp [hdec]
  exact tmp_effects_neg ((step s r).2) r hc2

theorem req_idempotency_aux3 (s : State) (r : Request)
    (hc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    (∀ x, x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied) := by
  have h2eq : (step s r).2 = ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State) := by
    simp only [step, hc, if_true]
  intro x
  rw [h2eq]
  simp

theorem req_idempotency_aux4 (s : State) (r : Request)
    (hc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true) :
    (∀ x, x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied) ∧ step (step s r).2 r = (Outcome.rejected, (step s r).2) := by
  exact ⟨req_idempotency_aux3 s r hc, idem_helper_test s r hc⟩

theorem req_idempotency_final_tmp : Idempotent step := by
  intro s r hok
  by_cases hc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true
  · exact req_idempotency_aux4 s r hc
  · have hstep := tmp_effects_neg s r hc
    rw [hstep] at hok
    simp at hok

theorem conserve_shift_aux (s : State) (bal : AccountId → Int) (l : Leg)
    (hs : l.source ∈ s.accounts) (ht : l.target ∈ s.accounts) (hnd : s.accounts.Nodup) :
    sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have e1 : sumOver s.accounts (fun a => if a = l.source then (l.amount : Int) else 0)
      = (l.amount : Int) := by
    rw [sumOver_ite_eq hnd l.source (l.amount : Int), if_pos hs]
  have e2 : sumOver s.accounts (fun a => if a = l.target then (l.amount : Int) else 0)
      = (l.amount : Int) := by
    rw [sumOver_ite_eq hnd l.target (l.amount : Int), if_pos ht]
  have hrew : (shift bal l) = (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [hrew]
  have hadd := sumOver_add s.accounts (fun a => bal a - (if a = l.source then (l.amount : Int) else 0)) (fun a => if a = l.target then (l.amount : Int) else 0)
  have hsub := sumOver_sub s.accounts bal (fun a => if a = l.source then (l.amount : Int) else 0)
  rw [hadd, hsub, e1, e2]
  omega

theorem conserve_ok_cond (s : State) (r : Request)
    (hok : (step s r).1 = Outcome.ok) :
    (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true := by
  by_cases hc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true
  · exact hc
  · have hstep := tmp_effects_neg s r hc
    rw [hstep] at hok
    simp at hok

theorem conserve_applyLegs_aux (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hnd : s.accounts.Nodup) : LegsOk s bal legs → sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => intro _; rfl
  | cons l ls ih =>
    intro h
    simp only [LegsOk] at h
    obtain ⟨hok, hrest⟩ := h
    obtain ⟨_, _, hs, ht, _⟩ := hok
    simp only [applyLegs]
    rw [ih (shift bal l) hrest, conserve_shift_aux s bal l hs ht hnd]

theorem shift_preserves_aux (s : State) (bal : AccountId → Int) (l : Leg)
    (hWL : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hok : LegOk s bal l) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a := by
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hok
  intro a ha
  unfold shift
  by_cases has : a = l.source
  · subst has
    have ht : ¬ (l.source = l.target) := hne
    simp [ht]
    exact hlim
  · by_cases hat : a = l.target
    · subst hat
      simp [has]
      have hbase := hWL l.target htgt
      have hnn : (0 : Int) ≤ (l.amount : Int) := by
        exact_mod_cast Nat.zero_le _
      omega
    · simp [has, hat]
      exact hWL a ha

theorem applyLegs_take_preserves (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hWL : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegsOk s bal legs) :
    ∀ k, ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    simp
    exact hWL a ha
  | cons l ls ih =>
    simp only [LegsOk] at hOk
    obtain ⟨hok, hrest⟩ := hOk
    have hshiftWL : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ shift bal l a :=
      shift_preserves_aux s bal l hWL hok
    intro k a ha
    cases k with
    | zero =>
      simp
      exact hWL a ha
    | succ n =>
      have ht : ((l :: ls).take (n + 1)) = l :: (ls.take n) := by simp
      rw [ht]
      simp only [applyLegs]
      exact ih (shift bal l) hshiftWL hrest (n) a ha

theorem take_length_eq_self (legs : List Leg) : legs.take legs.length = legs := by
  simp

theorem applyLegs_full_preserves (s : State) (bal : AccountId → Int) (legs : List Leg)
    (hWL : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a)
    (hOk : LegsOk s bal legs) :
    ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ applyLegs bal legs a := by
  have h := applyLegs_take_preserves s bal legs hWL hOk legs.length
  intro a ha
  have heq : legs.take legs.length = legs := by simp
  rw [heq] at h
  exact h a ha

theorem req_single_leg_test_tmp : SingleLeg step := by
  intro s r l hrlegs hok
  have hc := conserve_ok_cond s r hok
  have heff := tmp_effects_goal s r hc
  obtain ⟨_, _, hbal⟩ := heff
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, _⟩, _⟩, hlegsB⟩ := hc
  have hLegsOk : LegsOk s s.balance r.legs :=
    (legsOkB_true_iff_aux s s.balance r.legs).mp hlegsB
  rw [hrlegs] at hLegsOk hbal
  simp only [LegsOk] at hLegsOk
  obtain ⟨hokLeg, _⟩ := hLegsOk
  obtain ⟨_, hne, _, _, _⟩ := hokLeg
  have hsrc_eq : (step s r).2.balance l.source = applyLegs s.balance [l] l.source := hbal l.source
  have htgt_eq : (step s r).2.balance l.target = applyLegs s.balance [l] l.target := hbal l.target
  have happ : ∀ a, applyLegs s.balance [l] a = shift s.balance l a := fun a => rfl
  rw [happ] at hsrc_eq htgt_eq
  rw [tmp_shift_src2 s.balance l hne] at hsrc_eq
  rw [tmp_shift_tgt2 s.balance l hne] at htgt_eq
  exact ⟨hsrc_eq, htgt_eq⟩

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  obtain ⟨hnd, hne, hnmem, hlegs⟩ := h
  have hB : legsOkB s s.balance r.legs = true :=
    (legsOkB_true_iff_aux s s.balance r.legs).mpr hlegs
  have hcond : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true := by
    simp [hnd, hne, hnmem, hB]
  have h1 : (step s r).1 = Outcome.ok := tmp_step_true_aux3 s r hcond
  exact h1

theorem req_atomicity : Atomicity step := by
  intro s r hn
  have hc : ¬ (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true := by
    intro hcond
    apply hn
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨⟨⟨hndB, hneB⟩, hnmemB⟩, hlegsB⟩ := hcond
    exact ⟨of_decide_eq_true hndB, of_decide_eq_true hneB, of_decide_eq_true hnmemB, (legsOkB_true_iff_aux s s.balance r.legs).mp hlegsB⟩
  exact tmp_effects_neg s r hc

theorem req_single_leg : SingleLeg step := by
  intro s r l hrlegs hok
  have hc := conserve_ok_cond s r hok
  have heff := tmp_effects_goal s r hc
  obtain ⟨_, _, hbal⟩ := heff
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, _⟩, _⟩, hlegsB⟩ := hc
  have hLegsOk : LegsOk s s.balance r.legs :=
    (legsOkB_true_iff_aux s s.balance r.legs).mp hlegsB
  rw [hrlegs] at hLegsOk hbal
  simp only [LegsOk] at hLegsOk
  obtain ⟨hokLeg, _⟩ := hLegsOk
  obtain ⟨_, hne, _, _, _⟩ := hokLeg
  have hsrc_eq : (step s r).2.balance l.source = applyLegs s.balance [l] l.source := hbal l.source
  have htgt_eq : (step s r).2.balance l.target = applyLegs s.balance [l] l.target := hbal l.target
  have happ : ∀ a, applyLegs s.balance [l] a = shift s.balance l a := fun a => rfl
  rw [happ] at hsrc_eq htgt_eq
  rw [tmp_shift_src2 s.balance l hne] at hsrc_eq
  rw [tmp_shift_tgt2 s.balance l hne] at htgt_eq
  exact ⟨hsrc_eq, htgt_eq⟩

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true
  · exact tmp_effects_goal s r hc
  · have hstep := tmp_effects_neg s r hc
    rw [hstep] at hok
    simp at hok

theorem req_conservation     : Conserves step := by
  intro s r hok
  have hc := conserve_ok_cond s r hok
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hndB, _hne⟩, _hnmem⟩, hlegsB⟩ := hc
  have hnd : s.accounts.Nodup := of_decide_eq_true hndB
  have hLegsOk : LegsOk s s.balance r.legs := (legsOkB_true_iff_aux s s.balance r.legs).mp hlegsB
  have hsum : sumOver s.accounts (applyLegs s.balance r.legs) = sumOver s.accounts s.balance :=
    conserve_applyLegs_aux s s.balance r.legs hnd hLegsOk
  have heff := req_effects s r hok
  obtain ⟨hacc, _, hbal⟩ := heff
  unfold total
  rw [hacc]
  have hcongr : sumOver s.accounts (step s r).2.balance = sumOver s.accounts (applyLegs s.balance r.legs) := by
    apply sumOver_congr
    intro a _
    exact hbal a
  rw [hcongr, hsum]

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hWL
  constructor
  · -- WithinLimits (step s r).2
    unfold WithinLimits at hWL ⊢
    by_cases hc : (decide s.accounts.Nodup && decide (r.legs ≠ []) && decide (r.batchId ∉ s.applied) && legsOkB s s.balance r.legs) = true
    · have h2eq : (step s r).2 = ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State) := by
        simp only [step, hc, if_true]
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨hndB, _hne⟩, _hnmem⟩, hlegsB⟩ := hc
      have hLegsOk : LegsOk s s.balance r.legs :=
        (legsOkB_true_iff_aux s s.balance r.legs).mp hlegsB
      have hpres := applyLegs_full_preserves s s.balance r.legs hWL hLegsOk
      intro a ha
      rw [h2eq] at ha ⊢
      simp at ha ⊢
      exact hpres a ha
    · have hstep := tmp_effects_neg s r hc
      have h2 : (step s r).2 = s := by rw [hstep]
      rw [h2]
      exact hWL
  · -- success → every prefix within limits
    intro hok k a ha
    have hc := conserve_ok_cond s r hok
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hndB, _hne⟩, _hnmem⟩, hlegsB⟩ := hc
    have hLegsOk : LegsOk s s.balance r.legs :=
      (legsOkB_true_iff_aux s s.balance r.legs).mp hlegsB
    exact applyLegs_take_preserves s s.balance r.legs hWL hLegsOk k a ha

end Batch
