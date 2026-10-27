import Transfer.Spec
import Transfer.Lemmas
namespace Transfer
/-- Admission check for a transfer request. -/
def admissible (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.source ≠ r.target ∧
  r.source ∈ s.accounts ∧
  r.target ∈ s.accounts ∧
  s.auth r.requester r.source = true ∧
  -(s.limit r.source : Int) ≤ s.balance r.source - r.amount ∧
  r.txId ∉ s.applied

instance instDecidableAdmissible (s : State) (r : Request) : Decidable (admissible s r) := by
  unfold admissible; infer_instance

def step : Impl := fun s r =>
  if admissible s r then
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_debit_credit_aux_test : DebitCredit step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hne : r.source ≠ r.target := hadm.2.2.1
    have hne' : r.target ≠ r.source := fun heq => hne heq.symm
    have hstep : step s r = (.ok, { s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied }) := by simp [step, hadm]
    have e1 : (step s r).2.balance r.source = s.balance r.source - (r.amount : Int) := by
      rw [hstep]
      show ((fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0)) r.source) = _
      simp [if_neg hne]
    have e2 : (step s r).2.balance r.target = s.balance r.target + (r.amount : Int) := by
      rw [hstep]
      show ((fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0)) r.target) = _
      simp [if_neg hne']
    exact ⟨e1, e2⟩
  · simp [step, hadm] at h

theorem idem_helper_mem (s : State) (r : Request) (x : TxId) :
    x ∈ (r.txId :: s.applied) ↔ (x = r.txId ∨ x ∈ s.applied) := by
  simp

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hadm : admissible s r := h
  simp [step, hadm]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have h2 : ¬ admissible s r := h
  simp [step, h2]

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  by_cases hadm : admissible s r
  · exact hadm.2.2.2.2.2.1
  · simp [step, hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hne : r.source ≠ r.target := hadm.2.2.1
    have hne' : r.target ≠ r.source := fun heq => hne heq.symm
    have hstep : step s r = (.ok, { s with
          balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0),
          applied := r.txId :: s.applied }) := by simp [step, hadm]
    have e1 : (step s r).2.balance r.source = s.balance r.source - (r.amount : Int) := by
      rw [hstep]
      show ((fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0)) r.source) = _
      simp [if_neg hne]
    have e2 : (step s r).2.balance r.target = s.balance r.target + (r.amount : Int) := by
      rw [hstep]
      show ((fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                              + (if a = r.target then (r.amount : Int) else 0)) r.target) = _
      simp [if_neg hne']
    exact ⟨e1, e2⟩
  · simp [step, hadm] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hstep : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by simp [step, hadm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstep]
    · rw [hstep]
    · rw [hstep]
    · intro a
      rw [hstep]
      rfl
  · have h2 : (step s r).1 = .rejected := by simp [step, hadm]
    rw [h2] at h
    contradiction

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hstep : step s r = (.ok, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by simp [step, hadm]
    have h2 : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by rw [hstep]
    constructor
    · intro x
      rw [h2]
      simp
    · have hnadm : ¬ admissible ((step s r).2) r := by
        rw [h2]
        intro hc
        obtain ⟨_, _, _, _, _, _, _, hfresh⟩ := hc
        simp at hfresh
      have hrej : step ((step s r).2) r = (.rejected, (step s r).2) := by
        unfold step
        rw [if_neg hnadm]
      exact hrej
  · have hrej : (step s r).1 = .rejected := by simp [step, hadm]
    rw [hrej] at h
    contradiction

theorem req_limit : LimitRespected step := by
  intro s r hlim
  by_cases hadm : admissible s r
  · have hadm' := hadm
    obtain ⟨hnodup, hpos, hne, hsrc_mem, htgt_mem, hauth, hsrc_lim, hfresh⟩ := hadm'
    have hstep2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by simp [step, hadm]
    rw [hstep2]
    intro a ha
    simp only at ha ⊢
    have ha_mem : a ∈ s.accounts := ha
    have hold : -(s.limit a : Int) ≤ s.balance a := hlim a ha_mem
    by_cases has : a = r.source
    · subst has
      have hsimp : ((s.balance r.source - (if r.source = r.source then (r.amount : Int) else 0)
          + (if r.source = r.target then (r.amount : Int) else 0)) = s.balance r.source - (r.amount : Int)) := by
        simp [hne]
      rw [hsimp]
      exact hsrc_lim
    · by_cases hat : a = r.target
      · subst hat
        have hsimp : ((s.balance r.target - (if r.target = r.source then (r.amount : Int) else 0)
            + (if r.target = r.target then (r.amount : Int) else 0)) = s.balance r.target + (r.amount : Int)) := by
          have h1 : (if r.target = r.source then (r.amount : Int) else 0) = 0 := if_neg has
          have h2 : (if r.target = r.target then (r.amount : Int) else 0) = (r.amount : Int) := if_pos rfl
          rw [h1, h2]; omega
        rw [hsimp]
        have hpos' : (0 : Int) ≤ (r.amount : Int) := by exact_mod_cast Nat.zero_le _
        omega
      · have hsimp : ((s.balance a - (if a = r.source then (r.amount : Int) else 0)
            + (if a = r.target then (r.amount : Int) else 0)) = s.balance a) := by
          simp [has, hat]
        rw [hsimp]
        exact hold
  · have h2 : (step s r).2 = s := by simp [step, hadm]
    rw [h2]
    exact hlim

theorem req_conservation : Conserves step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hadm0 := hadm
    obtain ⟨hnodup, hpos, hne, hsrc_mem, htgt_mem, hauth, hsrc_lim, hfresh⟩ := hadm
    have hstep2 : (step s r).2 = ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State) := by simp [step, hadm0]
    have htot : total (step s r).2
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0)) := by
      rw [hstep2]; rfl
    rw [htot]
    unfold total
    have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          = sumOver s.accounts s.balance - sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) := by
      exact sumOver_sub s.accounts s.balance _
    have hsplit : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
          + sumOver s.accounts (fun a => (if a = r.target then (r.amount : Int) else 0)) := by
      exact sumOver_add s.accounts _ _
    rw [hsplit, hsub]
    have hs : sumOver s.accounts (fun a => (if a = r.source then (r.amount : Int) else 0)) = (r.amount : Int) := by
      have := sumOver_ite_eq hnodup r.source (r.amount : Int)
      simpa [hsrc_mem] using this
    have ht : sumOver s.accounts (fun a => (if a = r.target then (r.amount : Int) else 0)) = (r.amount : Int) := by
      have := sumOver_ite_eq hnodup r.target (r.amount : Int)
      simpa [htgt_mem] using this
    omega
  · simp [step, hadm] at h

end Transfer
