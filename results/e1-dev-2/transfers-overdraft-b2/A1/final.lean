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

theorem my_debit_test : DebitCredit step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hne : r.source ≠ r.target := hadm.2.2.1
    have h1 : (if r.source = r.target then (r.amount : Int) else 0) = 0 := if_neg hne
    have h2 : (if r.target = r.source then (r.amount : Int) else 0) = 0 := if_neg (Ne.symm hne)
    unfold step
    simp only [hadm, ↓reduceIte]
    constructor
    · simp [h1]
    · simp [h2]
  · unfold step at h
    simp [hadm] at h

theorem req_idempotency_aux : Idempotent step := by
  intro s r h
  by_cases hadm : admissible s r
  · have e1 : step s r = (Outcome.ok, ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied } : State)) := by
      unfold step
      rw [if_pos hadm]
    rw [e1] at h ⊢
    simp only at h ⊢
    constructor
    · intro x
      simp only [List.mem_cons]
    · have hnadm : ¬ admissible ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r := by
        intro ha
        exact ha.2.2.2.2.2.2.2 (by simp)
      have e2 : step ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) r = (Outcome.rejected, ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State)) := by
        unfold step
        rw [if_neg hnadm]
      exact e2
  · have e1 : step s r = (Outcome.rejected, s) := by
      unfold step
      rw [if_neg hadm]
    rw [e1] at h
    simp at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have hadm : admissible s r := h
  unfold step
  simp [hadm]

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have hn : ¬ admissible s r := fun ha => h ha
  unfold step
  simp [hn]

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
  · have hne : r.source ≠ r.target := hadm.2.2.1
    have h1 : (if r.source = r.target then (r.amount : Int) else 0) = 0 := if_neg hne
    have h2 : (if r.target = r.source then (r.amount : Int) else 0) = 0 := if_neg (Ne.symm hne)
    unfold step
    simp only [hadm, ↓reduceIte]
    constructor
    · simp [h1]
    · simp [h2]
  · unfold step at h
    simp [hadm] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hadm : admissible s r
  · unfold step
    simp only [hadm, ↓reduceIte]
    refine ⟨trivial, trivial, trivial, ?_⟩
    intro a
    rfl
  · unfold step at h
    simp [hadm] at h

theorem req_idempotency : Idempotent step := req_idempotency_aux

theorem req_limit : LimitRespected step := by
  intro s r hWL a ha
  by_cases hadm : admissible s r
  · have hne : r.source ≠ r.target := hadm.2.2.1
    have hlimSrc : -(s.limit r.source : Int) ≤ s.balance r.source - (r.amount : Int) :=
      hadm.2.2.2.2.2.2.1
    have hstep : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by
      unfold step
      simp only [hadm, ↓reduceIte]
    rw [hstep] at ha ⊢
    simp only at ha ⊢
    by_cases has : a = r.source
    · subst has
      simp [hne] at ⊢
      omega
    · simp only [has, ↓reduceIte] at ⊢
      by_cases hat : a = r.target
      · subst hat
        simp at ⊢
        have hold := hWL _ ha
        omega
      · simp only [hat, ↓reduceIte] at ⊢
        have hold := hWL _ ha
        omega
  · have hstep : (step s r).2 = s := by
      unfold step
      simp [hadm]
    rw [hstep] at ha ⊢
    exact hWL a ha

theorem req_conservation : Conserves step := by
  intro s r h
  by_cases hadm : admissible s r
  · have hNodup : s.accounts.Nodup := hadm.1
    have hsrc : r.source ∈ s.accounts := hadm.2.2.2.1
    have htgt : r.target ∈ s.accounts := hadm.2.2.2.2.1
    have hstep2 : (step s r).2 = ({ s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by
      unfold step
      simp only [hadm, ↓reduceIte]
    have hacc : (step s r).2.accounts = s.accounts := by rw [hstep2]
    have hbal : ∀ a, (step s r).2.balance a =
        s.balance a - (if a = r.source then (r.amount : Int) else 0)
          + (if a = r.target then (r.amount : Int) else 0) := by
      intro a; rw [hstep2]
    unfold total
    rw [hacc]
    have hcongr : sumOver s.accounts (step s r).2.balance =
        sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0)) := by
      apply sumOver_congr
      intro a ha
      exact hbal a
    rw [hcongr]
    have hexpand : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0))
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0))
                            + (if a = r.target then (r.amount : Int) else 0)) := rfl
    rw [hexpand, sumOver_add]
    have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
      sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
    rw [hsub]
    rw [sumOver_ite_eq hNodup r.source (r.amount : Int)]
    rw [sumOver_ite_eq hNodup r.target (r.amount : Int)]
    simp only [hsrc, htgt, if_true]
    omega
  · unfold step at h
    simp [hadm] at h

end Transfer
