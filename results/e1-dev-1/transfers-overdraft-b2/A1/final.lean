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

theorem req_debit_credit_aux : True := trivial
#check @admissible
#check @step

theorem req_effects_aux_test (s : State) (r : Request) (hadm : admissible s r) :
    (step s r).2.accounts = s.accounts ∧
    (step s r).2.limit = s.limit ∧
    (step s r).2.auth = s.auth ∧
    ∀ a, (step s r).2.balance a = expectedBalance s r a := by
  unfold step
  simp [hadm]
  intro a
  rfl

theorem req_effects_try : Effects step := by
  intro s r h
  by_cases hadm : admissible s r
  · have e : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [e]
    exact ⟨rfl, rfl, rfl, fun a => rfl⟩
  · exfalso
    unfold step at h
    simp [hadm] at h

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  unfold step
  have h' : admissible s r := h
  simp [h']

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  unfold step
  have h' : ¬ admissible s r := h
  simp [h']

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · exact hadm.2.2.2.2.2.1
  · simp [hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  by_cases hadm : admissible s r
  · unfold step at h ⊢
    simp [hadm] at h ⊢
    constructor
    · have hne : r.source ≠ r.target := hadm.2.2.1
      simp [hne]
    · have hne : r.target ≠ r.source := fun heq => hadm.2.2.1 heq.symm
      simp [hne]
  · unfold step at h
    simp [hadm] at h

theorem req_effects : Effects step := by
  intro s r h
  by_cases hadm : admissible s r
  · have e : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [e]
    exact ⟨rfl, rfl, rfl, fun a => rfl⟩
  · exfalso
    unfold step at h
    simp [hadm] at h

theorem req_idempotency : Idempotent step := by
  intro s r h
  by_cases hadm : admissible s r
  · have e : step s r = (.ok, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hadm]
    rw [e] at h ⊢
    simp at h
    constructor
    · intro x; simp
    · have hnot : ¬ admissible { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } r := by
        intro hc
        exact hc.2.2.2.2.2.2.2 (by simp)
      have e2 : step { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } r =
        (.rejected, { s with
        balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                            + (if a = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied }) := by unfold step; simp [hnot]
      rw [e2]
  · unfold step at h
    simp [hadm] at h

theorem req_limit : LimitRespected step := by
  intro s r hlim a ha
  by_cases hadm : admissible s r
  · have e2 : (step s r).2 = ({ s with
        balance := fun b => s.balance b - (if b = r.source then (r.amount : Int) else 0)
                            + (if b = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by unfold step; simp [hadm]
    rw [e2] at ha ⊢
    simp only at ha ⊢
    have hne : r.source ≠ r.target := hadm.2.2.1
    have hW : -(s.limit a : Int) ≤ s.balance a := hlim a ha
    have hsrc : -(s.limit r.source : Int) ≤ s.balance r.source - (r.amount : Int) := hadm.2.2.2.2.2.2.1
    by_cases has : a = r.source
    · subst has
      simp [hne]
      exact hsrc
    · by_cases hat : a = r.target
      · subst hat
        simp [has]
        omega
      · simp [has, hat]
        exact hW
  · have hstep : step s r = (.rejected, s) := by unfold step; simp [hadm]
    rw [hstep] at ha ⊢
    simp only at ha ⊢
    exact hlim a ha

theorem req_conservation : Conserves step := by
  intro s r h
  by_cases hadm : admissible s r
  · have e2 : (step s r).2 = ({ s with
        balance := fun b => s.balance b - (if b = r.source then (r.amount : Int) else 0)
                            + (if b = r.target then (r.amount : Int) else 0),
        applied := r.txId :: s.applied } : State) := by unfold step; simp [hadm]
    have hnodup : s.accounts.Nodup := hadm.1
    have hsrcMem : r.source ∈ s.accounts := hadm.2.2.2.1
    have htgtMem : r.target ∈ s.accounts := hadm.2.2.2.2.1
    unfold total
    rw [e2]
    simp only
    have hS : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      have := sumOver_ite_eq (l := s.accounts) hnodup r.source (r.amount : Int)
      simp [hsrcMem] at this
      exact this
    have hT : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0)
        = (r.amount : Int) := by
      have := sumOver_ite_eq (l := s.accounts) hnodup r.target (r.amount : Int)
      simp [htgtMem] at this
      exact this
    have hexpand : (fun b => s.balance b - (if b = r.source then (r.amount : Int) else 0)
                            + (if b = r.target then (r.amount : Int) else 0))
        = (fun b => (s.balance b - (if b = r.source then (r.amount : Int) else 0))
                            + (if b = r.target then (r.amount : Int) else 0)) := by
      rfl
    rw [hexpand, sumOver_add]
    have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) := by
      have := sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
      exact this
    rw [hsub, hS, hT]
    omega
  · unfold step at h
    simp [hadm] at h

end Transfer
