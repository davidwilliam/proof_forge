import Batch.Spec
import Batch.Lemmas
namespace Batch
/-- Admission check of one leg against the running balances. -/
def legAllowed (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
  decide (0 < l.amount) && l.source != l.target &&
  s.accounts.contains l.source &&
  s.accounts.contains l.target &&
  decide (-(s.limit l.source : Int) ≤ bal l.source - l.amount)

/-- Check every leg in order against running balances. -/
def checkAll (s : State) : (AccountId → Int) → List Leg → Bool
  | _, [] => true
  | bal, l :: ls => legAllowed s bal l && checkAll s (shift bal l) ls

def step : Impl := fun s r =>
  if s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else (.rejected, s)

theorem bne_true_iff_ne (a b : Nat) : (a != b) = true ↔ a ≠ b := by
  constructor
  · intro h heq
    subst heq
    simp at h
  · intro h
    simp [h]

theorem nat_beq_test (a b : Nat) (h : (a == b) = true) : a = b := by
  simpa using h

theorem contains_iff_mem_test (s : State) (x : Nat) : (s.accounts.contains x) = true ↔ x ∈ s.accounts := by
  simp [List.contains_eq_mem]
#check List.contains_eq_mem

theorem contains_iff_mem3 (s : State) (x : Nat) : (s.accounts.contains x) = decide (x ∈ s.accounts) := by
  simp [List.contains_eq_mem]

theorem contains_true_iff (l : List Nat) (x : Nat) : (l.contains x) = true ↔ x ∈ l := by
  simp [List.contains_eq_mem]

theorem legAllowed_iff2 (s : State) (bal : AccountId → Int) (l : Leg) :
    (legAllowed s bal l = true) ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  simp only [Bool.and_eq_true]
  rw [decide_eq_true_eq, bne_true_iff_ne, contains_true_iff, contains_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩
    exact ⟨h1,h2,h3,h4,h5⟩
  · rintro ⟨h1,h2,h3,h4,h5⟩
    exact ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩

theorem checkAll_iff (s : State) (bal : AccountId → Int) (legs : List Leg) :
    (checkAll s bal legs = true) ↔ LegsOk s bal legs := by
  induction legs generalizing bal with
  | nil => simp [checkAll, LegsOk]
  | cons l ls ih =>
    simp only [checkAll, LegsOk, Bool.and_eq_true]
    rw [legAllowed_iff2, ih]

theorem step_ok_iff (s : State) (r : Request) :
    ((s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true)) ↔ ValidBatch s r := by
  unfold ValidBatch
  rw [checkAll_iff]

theorem foo_test : True := by trivial

theorem shift_sum_preserve_aux2 (s : State) (bal : AccountId → Int) (l : Leg)
  (hnodup : s.accounts.Nodup)
  (hsrc : l.source ∈ s.accounts) (htgt : l.target ∈ s.accounts) :
  sumOver s.accounts (shift bal l) = sumOver s.accounts bal := by
  have heq : shift bal l = (fun a => (bal a - (if a = l.source then (l.amount : Int) else 0)) + (if a = l.target then (l.amount : Int) else 0)) := rfl
  rw [heq, sumOver_add, sumOver_sub]
  rw [sumOver_ite_eq hnodup l.source ((l.amount : Int)), sumOver_ite_eq hnodup l.target ((l.amount : Int))]
  rw [if_pos hsrc, if_pos htgt]
  omega

theorem applyLegs_sum_preserve_aux2 (s : State) (bal : AccountId → Int) (legs : List Leg)
  (hnodup : s.accounts.Nodup) (hok : LegsOk s bal legs) :
  sumOver s.accounts (applyLegs bal legs) = sumOver s.accounts bal := by
  induction legs generalizing bal with
  | nil => rfl
  | cons l ls ih =>
    simp only [LegsOk] at hok
    obtain ⟨hLegOk, hRest⟩ := hok
    unfold LegOk at hLegOk
    obtain ⟨_, _, hsrc, htgt, _⟩ := hLegOk
    have happ : applyLegs bal (l :: ls) = applyLegs (shift bal l) ls := rfl
    rw [happ]
    rw [ih (shift bal l) hRest, shift_sum_preserve_aux2 s bal l hnodup hsrc htgt]

theorem shift_unfold_test (bal : AccountId → Int) (l : Leg) (a : AccountId) : shift bal l a = bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0) := by rfl

theorem shift_preserves_lim_aux3 (s : State) (bal : AccountId → Int) (l : Leg) (hWL : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) (hok : LegOk s bal l) : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ (shift bal l) a := by
  intro a ha
  obtain ⟨hpos, hne, hsrc, htgt, hlim⟩ := hok
  have hpos2 : (0 : Int) ≤ (l.amount : Int) := by omega
  have h1 := hWL a ha
  have he : shift bal l a = bal a - (if a = l.source then (l.amount : Int) else 0) + (if a = l.target then (l.amount : Int) else 0) := rfl
  rw [he]
  by_cases hsa : a = l.source
  · subst hsa
    rw [if_pos rfl, if_neg hne]
    omega
  · by_cases hta : a = l.target
    · subst hta
      rw [if_neg hsa, if_pos rfl]
      omega
    · rw [if_neg hsa, if_neg hta]
      omega

theorem prefix_within_aux (s : State) (bal : AccountId → Int) (legs : List Leg) (hWL : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ bal a) (hok : LegsOk s bal legs) : ∀ (k : Nat) (a : AccountId), a ∈ s.accounts → -(s.limit a : Int) ≤ applyLegs bal (legs.take k) a := by
  induction legs generalizing bal with
  | nil =>
    intro k a ha
    have he : ([] : List Leg).take k = [] := by cases k with | zero => rfl | succ n => rfl
    rw [he]
    simp [applyLegs]
    exact hWL a ha
  | cons l ls ih =>
    obtain ⟨hLeg, hRest⟩ := hok
    have hWL2 : ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ (shift bal l) a := shift_preserves_lim_aux3 s bal l hWL hLeg
    intro k a ha
    cases k with
    | zero =>
      simp [List.take, applyLegs]
      exact hWL a ha
    | succ n =>
      have he : (l :: ls).take (n + 1) = l :: ((ls).take n) := rfl
      rw [he]
      have happ : applyLegs bal (l :: (ls.take n)) a = applyLegs (shift bal l) (ls.take n) a := rfl
      rw [happ]
      exact ih (shift bal l) hWL2 hRest n a ha

theorem take_len_test (l : List Batch.Leg) : l.take l.length = l := by simp

theorem req_valid_succeeds   : ValidSucceeds step := by
  intro s r h
  have hC : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true) :=
    (step_ok_iff s r).mpr h
  unfold step
  simp [hC]

theorem req_atomicity : Atomicity step := by
  intro s r h
  unfold step
  have hc : ¬ (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true) := by
    intro hc
    apply h
    exact (step_ok_iff s r).mp hc
  simp [hc]

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  by_cases hC : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true)
  · have hstep2 : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      exact if_pos hC
    have hVb : ValidBatch s r := (step_ok_iff s r).mp hC
    obtain ⟨hnodup, hne, hnapplied, hLegsOk⟩ := hVb
    rw [hlegs] at hLegsOk
    simp only [LegsOk] at hLegsOk
    obtain ⟨hLegOk, _⟩ := hLegsOk
    unfold LegOk at hLegOk
    obtain ⟨hpos, hne_st, hsrc_mem, htgt_mem, hlim⟩ := hLegOk
    have e1 : (step s r).2.balance l.source = applyLegs s.balance r.legs l.source := by
      rw [hstep2]
    have e2 : (step s r).2.balance l.target = applyLegs s.balance r.legs l.target := by
      rw [hstep2]
    rw [e1, e2, hlegs]
    have hst : ¬ (l.source = l.target) := hne_st
    have hts : ¬ (l.target = l.source) := fun h => hne_st h.symm
    have hs_eq : (l.source = l.source) := rfl
    have ht_eq : (l.target = l.target) := rfl
    have hS : applyLegs s.balance [l] l.source = s.balance l.source - (l.amount : Int) := by
      show shift s.balance l l.source = _
      unfold shift
      simp [hst]
    have hT : applyLegs s.balance [l] l.target = s.balance l.target + (l.amount : Int) := by
      show shift s.balance l l.target = _
      unfold shift
      simp [hts]
    rw [hS, hT]
    constructor
    · omega
    · omega
  · have hstep : step s r = (.rejected, s) := by unfold step; exact if_neg hC
    rw [hstep] at hok
    simp at hok

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hC : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true)
  · have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      exact if_pos hC
    have h2 : (step s r).2.accounts = s.accounts := by rw [hstep]
    have h3 : (step s r).2.limit = s.limit := by rw [hstep]
    have h4 : ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a := by
      intro a
      rw [hstep]
    exact ⟨h2, h3, h4⟩
  · have hstep : step s r = (.rejected, s) := by unfold step; exact if_neg hC
    rw [hstep] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  by_cases hC : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true)
  · have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      exact if_pos hC
    have h1 : ∀ x, x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied := by
      intro x
      rw [hstep]
      simp
    have h2 : step (step s r).2 r = (.rejected, (step s r).2) := by
      rw [hstep]
      unfold step
      have hmem : ¬ (({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State).accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State).applied ∧ checkAll ({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State) (({ s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } : State).balance) r.legs = true) := by
        intro hcon
        obtain ⟨_, _, hnotin, _⟩ := hcon
        simp at hnotin
      exact if_neg hmem
    exact ⟨h1, h2⟩
  · have hstep : step s r = (.rejected, s) := by unfold step; exact if_neg hC
    rw [hstep] at hok
    simp at hok

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hC : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true)
  · have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      exact if_pos hC
    have hVb : ValidBatch s r := (step_ok_iff s r).mp hC
    obtain ⟨hnodup, hne, hnapplied, hLegsOk⟩ := hVb
    have hbal : (step s r).2.balance = applyLegs s.balance r.legs := by rw [hstep]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep]
    unfold total
    rw [hacc, hbal]
    exact applyLegs_sum_preserve_aux2 s s.balance r.legs hnodup hLegsOk
  · have hstep : step s r = (.rejected, s) := by unfold step; exact if_neg hC
    rw [hstep] at hok
    simp at hok

theorem req_limit_every_step : LimitEveryStep step := by
  intro s r hWL
  by_cases hC : (s.accounts.Nodup ∧ r.legs ≠ [] ∧ r.batchId ∉ s.applied ∧ checkAll s s.balance r.legs = true)
  · have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      exact if_pos hC
    have hVb : ValidBatch s r := (step_ok_iff s r).mp hC
    obtain ⟨hnodup, hne, hnapplied, hLegsOk⟩ := hVb
    have hPref : ∀ (k : Nat) (a : AccountId), a ∈ s.accounts → -(s.limit a : Int) ≤ applyLegs s.balance (r.legs.take k) a :=
      prefix_within_aux s s.balance r.legs hWL hLegsOk
    constructor
    · -- WithinLimits of next state
      rw [hstep]
      intro a ha
      simp at ha ⊢
      -- ha : a ∈ s.accounts, goal with applyLegs
      have h2 := hPref r.legs.length a ha
      have htake : r.legs.take r.legs.length = r.legs := by simp
      rw [htake] at h2
      exact h2
    · intro _ k a ha
      exact hPref k a ha
  · have hstep : step s r = (.rejected, s) := by unfold step; exact if_neg hC
    constructor
    · rw [hstep]
      exact hWL
    · intro hok
      rw [hstep] at hok
      simp at hok

end Batch
