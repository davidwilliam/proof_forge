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

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hadm : admissible s r := h
  unfold step
  simp [hadm]

theorem req_invalid_noop   : InvalidNoop step := by
  intro s r h
  unfold step
  have h' : ¬ admissible s r := h
  simp [h']

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · obtain ⟨_, _, _, _, _, hauth, _, _⟩ := hadm
    exact hauth
  · simp [hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hadm0 := hadm
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlim, hfresh⟩ := hadm
    have hsrc_eq : (if r.source = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by simp
    have hsrc_tgt : (if r.source = r.target then (r.amount : Int) else 0) = 0 := by simp [hne]
    have htgt_src : (if r.target = r.source then (r.amount : Int) else 0) = 0 := by simp [Ne.symm hne]
    have htgt_eq : (if r.target = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by simp
    have hstep : step s r = (Outcome.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hadm0]
    have e1 : (step s r).2.balance r.source = s.balance r.source - (if r.source = r.source then (r.amount : Int) else 0) + (if r.source = r.target then (r.amount : Int) else 0) := by rw [hstep]
    have e2 : (step s r).2.balance r.target = s.balance r.target - (if r.target = r.source then (r.amount : Int) else 0) + (if r.target = r.target then (r.amount : Int) else 0) := by rw [hstep]
    rw [hsrc_eq, hsrc_tgt] at e1
    rw [htgt_src, htgt_eq] at e2
    constructor
    · rw [e1]; omega
    · rw [e2]; omega
  · unfold step at h
    simp [hadm] at h

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · have hstep : step s r = (Outcome.ok, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hadm]
    have h2 : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by rw [hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h2]
    · rw [h2]
    · rw [h2]
    · intro a
      rw [h2]
      rfl
      -- expectedBalance unfolds to same expression
  · simp [hadm] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · have hstep : step s r = (Outcome.ok, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by
      unfold step; simp [hadm]
    have h2 : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by rw [hstep]
    refine ⟨?_, ?_⟩
    · intro x
      rw [h2]
      simp
    · have hnot : ¬ admissible ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r := by
        intro hc
        unfold admissible at hc
        obtain ⟨_, _, _, _, _, _, _, hfresh⟩ := hc
        simp at hfresh
      have hstep2 : step ((step s r).2) r = (Outcome.rejected, (step s r).2) := by
        rw [h2]
        unfold step
        simp [hnot]
      exact hstep2
  · simp [hadm] at h

theorem req_limit : LimitRespected step := by
  intro s r hLim
  by_cases hadm : admissible s r
  · have hadm0 := hadm
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlimSrc, hfresh⟩ := hadm
    have h2 : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by
      unfold step; simp [hadm0]
    rw [h2]
    intro a ha
    have ha' : a ∈ s.accounts := ha
    have hOld : -(s.limit a : Int) ≤ s.balance a := hLim a ha'
    show -(s.limit a : Int) ≤ s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0)
    by_cases hAS : a = r.source
    · by_cases hAT : a = r.target
      · rw [hAS] at hAT; exact absurd hAT hne
      · subst hAS
        have e2 : (if (r.source : Nat) = r.target then (r.amount : Int) else 0) = 0 := by simp [hne]
        rw [e2]
        simp
        exact hlimSrc
    · by_cases hAT : a = r.target
      · subst hAT
        have e1 : (if (r.target : Nat) = r.source then (r.amount : Int) else 0) = 0 := by simp [hAS]
        rw [e1]
        omega
      · have e1 : (if a = r.source then (r.amount : Int) else 0) = 0 := by simp [hAS]
        have e2 : (if a = r.target then (r.amount : Int) else 0) = 0 := by simp [hAT]
        rw [e1, e2]
        omega
  · have h2 : (step s r).2 = s := by unfold step; simp [hadm]
    rw [h2]
    exact hLim

theorem req_conservation   : Conserves step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hadm0 := hadm
    obtain ⟨hnodup, hpos, hne, hsrc, htgt, hauth, hlim, hfresh⟩ := hadm
    have h2 : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by
      unfold step; simp [hadm0]
    have hX : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup r.source (r.amount : Int), if_pos hsrc]
    have hY : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup r.target (r.amount : Int), if_pos htgt]
    have e1 := sumOver_add s.accounts
        (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        (fun a => (if a = r.target then (r.amount : Int) else 0))
    have e2 := sumOver_sub s.accounts s.balance
        (fun a => (if a = r.source then (r.amount : Int) else 0))
    rw [hX] at e2
    have e3 : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - (r.amount : Int) := e2
    have hSum : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance := by
      calc sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
          = sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
            + sumOver s.accounts (fun a => (if a = r.target then (r.amount : Int) else 0)) := e1
        _ = (sumOver s.accounts s.balance - (r.amount : Int)) + (r.amount : Int) := by rw [e3, hY]
        _ = sumOver s.accounts s.balance := by omega
    unfold total
    rw [h2]
    simp only
    exact hSum
  · unfold step at h
    simp [hadm] at h

end Transfer
