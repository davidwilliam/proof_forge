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

def checkLegs (s : State) (bal : AccountId → Int) : List Leg → Bool
  | [] => true
  | l :: ls => legAllowed s bal l && checkLegs s (post bal l) ls

def step : Impl := fun s r =>
  if decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId && checkLegs s s.balance r.legs then
    (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied })
  else (.rejected, s)

theorem probe_bne (a b : Nat) : (a != b) = decide (a ≠ b) := rfl

theorem and5' (a b c d e : Prop) : (((((a ∧ b) ∧ c) ∧ d) ∧ e) ↔ (a ∧ (b ∧ (c ∧ (d ∧ e))))) := by simp only [and_assoc]

theorem legAllowed_true_iff2 (s : State) (bal : AccountId → Int) (l : Leg) :
    legAllowed s bal l = true ↔ LegOk s bal l := by
  unfold legAllowed LegOk
  rw [List.contains_eq_mem, List.contains_eq_mem, probe_bne]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem post_eq_shift2 (bal : AccountId → Int) (l : Leg) : post bal l = shift bal l := rfl

theorem checkLegs_true_iff3 (s : State) (bal : AccountId → Int) (legs : List Leg) :
    checkLegs s bal legs = true ↔ LegsOk s bal legs := by
  induction legs generalizing bal with
  | nil => simp [checkLegs, LegsOk]
  | cons l ls ih =>
    simp only [checkLegs, LegsOk, Bool.and_eq_true, legAllowed_true_iff2, post_eq_shift2, ih]

theorem cond_true_valid_tmp (s : State) (r : Request)
    (h : (decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId &&
      checkLegs s s.balance r.legs) = true) : ValidBatch s r := by
  have h4 : decide s.accounts.Nodup = true ∧ (!r.legs.isEmpty) = true ∧
    (!s.applied.contains r.batchId) = true ∧ checkLegs s s.balance r.legs = true := by
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨h1, h2, h3, h4⟩ := h4
  have hn : s.accounts.Nodup := of_decide_eq_true h1
  have hne : r.legs ≠ [] := by
    intro hcon
    rw [hcon] at h2
    simp at h2
  have hmem : r.batchId ∉ s.applied := by
    rw [List.contains_eq_mem] at h3
    simp at h3
    exact h3
  have hlegs : LegsOk s s.balance r.legs := (checkLegs_true_iff3 s s.balance r.legs).mp h4
  exact ⟨hn, hne, hmem, hlegs⟩

theorem req_atomicity_tmp5 : Atomicity step := by
  intro s r hn
  have hc : ¬ ((decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId &&
      checkLegs s s.balance r.legs) = true) := fun h => hn (cond_true_valid_tmp s r h)
  have h2 : step s r = (.rejected, s) := by
    simp only [step]
    rw [if_neg hc]
  exact h2

theorem req_valid_succeeds   : ValidSucceeds step := sorry

theorem req_atomicity : Atomicity step := by
  intro s r hn
  have hc : ¬ ((decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId &&
      checkLegs s s.balance r.legs) = true) := fun h => hn (cond_true_valid_tmp s r h)
  have h2 : step s r = (.rejected, s) := by
    simp only [step]
    rw [if_neg hc]
  exact h2

theorem req_single_leg : SingleLeg step := by
  intro s r l hlegs hok
  by_cases hc : ((decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId && checkLegs s s.balance r.legs) = true)
  · have hstep2 : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      rw [if_pos hc]
    have hbal : (step s r).2.balance = applyLegs s.balance r.legs := by rw [hstep2]
    have hvalid : ValidBatch s r := cond_true_valid_tmp s r hc
    obtain ⟨hnodup, hne, hmem, hlegsOk⟩ := hvalid
    rw [hlegs] at hlegsOk
    simp only [LegsOk] at hlegsOk
    obtain ⟨hokLeg, _⟩ := hlegsOk
    unfold LegOk at hokLeg
    obtain ⟨hpos, hne_st, hsrc, htgt, hlim⟩ := hokLeg
    have e1s : (step s r).2.balance l.source = applyLegs s.balance r.legs l.source := by rw [hbal]
    have e1t : (step s r).2.balance l.target = applyLegs s.balance r.legs l.target := by rw [hbal]
    rw [hlegs] at e1s e1t
    have e2s : applyLegs s.balance [l] l.source = shift s.balance l l.source := rfl
    have e2t : applyLegs s.balance [l] l.target = shift s.balance l l.target := rfl
    rw [e2s] at e1s
    rw [e2t] at e1t
    unfold shift at e1s e1t
    have hsrc_if : (if l.source = l.source then (l.amount : Int) else 0) = (l.amount : Int) := by simp
    have htgt_if : (if l.target = l.target then (l.amount : Int) else 0) = (l.amount : Int) := by simp
    have hst : l.target ≠ l.source := fun h => hne_st h.symm
    have hmid_s : (if l.source = l.target then (l.amount : Int) else 0) = 0 := by simp [hne_st]
    have hmid_t : (if l.target = l.source then (l.amount : Int) else 0) = 0 := by simp [hst]
    rw [hsrc_if] at e1s
    rw [hmid_s] at e1s
    rw [hmid_t] at e1t
    rw [htgt_if] at e1t
    simp at e1s e1t
    exact ⟨e1s, e1t⟩
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hc]
    have hcon : (step s r).1 = .rejected := by rw [hstep]
    rw [hok] at hcon
    simp at hcon

theorem req_effects : Effects step := by
  intro s r hok
  by_cases hc : (decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId &&
      checkLegs s s.balance r.legs) = true
  · have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      rw [if_pos hc]
    rw [hstep]
    exact ⟨rfl, rfl, fun a => rfl⟩
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hc]
    rw [hstep] at hok
    simp at hok

theorem req_idempotency : Idempotent step := by
  intro s r hok
  have hc : (decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId &&
      checkLegs s s.balance r.legs) = true := by
    by_cases h : (decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId &&
      checkLegs s s.balance r.legs) = true
    · exact h
    · have hstep : step s r = (.rejected, s) := by
        unfold step
        rw [if_neg h]
      have hrej : (step s r).1 = .rejected := by rw [hstep]
      rw [hok] at hrej
      exact absurd hrej (by simp)
  have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
    unfold step
    rw [if_pos hc]
  constructor
  · intro x
    have happ : (step s r).2.applied = r.batchId :: s.applied := by rw [hstep]
    rw [happ]
    simp only [List.mem_cons]
  · have hs2 : (step s r).2 = { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied } := by rw [hstep]
    have hmem : r.batchId ∈ (step s r).2.applied := by
      rw [hs2]
      simp
    have hcont : ((step s r).2.applied.contains r.batchId) = true := by
      rw [List.contains_eq_mem]
      exact hmem
    have hnot : (!((step s r).2.applied.contains r.batchId)) = false := by
      rw [hcont]
    have hcond2 : ¬ ((decide (step s r).2.accounts.Nodup && !r.legs.isEmpty && !((step s r).2.applied.contains r.batchId) &&
        checkLegs (step s r).2 (step s r).2.balance r.legs) = true) := by
      intro hcon
      have h3 : (!((step s r).2.applied.contains r.batchId)) = true := by
        simp only [Bool.and_eq_true] at hcon
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
        exact h3
      rw [hnot] at h3
      exact Bool.noConfusion h3
    have hstep2 : step (step s r).2 r = (.rejected, (step s r).2) := by
      unfold step
      rw [if_neg hcond2]
    exact hstep2

theorem req_conservation : Conserves step := by
  intro s r hok
  by_cases hc : (decide s.accounts.Nodup && !r.legs.isEmpty && !s.applied.contains r.batchId &&
      checkLegs s s.balance r.legs) = true
  · have hstep : step s r = (.ok, { s with balance := applyLegs s.balance r.legs, applied := r.batchId :: s.applied }) := by
      unfold step
      rw [if_pos hc]
    have hvalid : ValidBatch s r := cond_true_valid_tmp s r hc
    obtain ⟨hnd, _, _, hlegs⟩ := hvalid
    have hsum : sumOver s.accounts (applyLegs s.balance r.legs) = sumOver s.accounts s.balance :=
      applyLegs_sum_aux_thm2 s s.balance r.legs hnd hlegs
    have h1 : total (step s r).2 = sumOver s.accounts (applyLegs s.balance r.legs) := by
      rw [hstep]
      rfl
    have h2 : total s = sumOver s.accounts s.balance := rfl
    rw [h1, h2, hsum]
  · have hstep : step s r = (.rejected, s) := by
      unfold step
      rw [if_neg hc]
    rw [hstep] at hok
    simp at hok

theorem req_limit_every_step : LimitEveryStep step := sorry

end Batch
