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

theorem req_effects_aux : True := trivial
#check @expectedBalance
#check @admissible

theorem req_limit_foo : True := by
  have h1 : ∀ (s : State) (r : Request) (hadm : admissible s r),
    ((if admissible s r then (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
    else (.rejected, s) : Outcome × State)).2.accounts = s.accounts := by
    intro s r hadm
    simp [hadm]
  trivial

theorem req_valid_succeeds : ValidSucceeds step := by
  intro s r h
  have h' : admissible s r := h
  unfold step
  simp [h']

theorem req_invalid_noop : InvalidNoop step := by
  intro s r h
  have h' : ¬ admissible s r := h
  unfold step
  simp [h']

theorem req_authorization : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · exact hadm.2.2.2.2.2.1
  · simp [hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  unfold step at h ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at h ⊢
    have hne : r.source ≠ r.target := hadm.2.2.1
    simp only [hne, ↓reduceIte, Ne.symm hne, ↓reduceIte] at ⊢
    constructor <;> omega
  · simp [hadm] at h

theorem req_effects : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hadm : admissible s r
  · simp [hadm] at h ⊢
    intro a
    rfl
  · simp [hadm] at h

theorem req_idempotency    : Idempotent step := by
  intro s r h
  unfold step at h ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at h ⊢
    have happ : ∀ x, x ∈ (r.txId :: s.applied) ↔ x = r.txId ∨ x ∈ s.applied := by
      intro x; simp
    refine ⟨happ, ?_⟩
    have hnadm : ¬ admissible ({ s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied }) r := by
      intro hadm2
      exact hadm2.2.2.2.2.2.2.2 (by simp)
    simp [hnadm]
  · simp [hadm] at h

theorem req_limit : LimitRespected step := by
  intro s r hwl a ha
  unfold step at ha ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at ha ⊢
    have hwl_a : -(s.limit a : Int) ≤ s.balance a := hwl a ha
    have hne : r.source ≠ r.target := hadm.2.2.1
    have hsrc_lim : -(s.limit r.source : Int) ≤ s.balance r.source - (r.amount : Int) :=
      hadm.2.2.2.2.2.2.1
    by_cases has : a = r.source
    · subst has
      have hnt : r.source ≠ r.target := hne
      simp only [hnt, ↓reduceIte] at ⊢
      omega
    · by_cases hat : a = r.target
      · subst hat
        simp only [has, ↓reduceIte] at ⊢
        omega
      · simp only [has, ↓reduceIte, hat, ↓reduceIte] at ⊢
        omega
  · simp only [hadm, ↓reduceIte] at ha ⊢
    exact hwl a ha

theorem req_conservation : Conserves step := by
  intro s r h
  unfold step at h ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at h ⊢
    unfold total
    simp
    have hnodup : s.accounts.Nodup := hadm.1
    have hsrc_mem : r.source ∈ s.accounts := hadm.2.2.2.1
    have htgt_mem : r.target ∈ s.accounts := hadm.2.2.2.2.1
    have hsrc : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup r.source (r.amount : Int), if_pos hsrc_mem]
    have htgt : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup r.target (r.amount : Int), if_pos htgt_mem]
    have heq : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a = r.target then (r.amount : Int) else 0)) := rfl
    rw [heq, sumOver_add]
    have hsub : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0))
        = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) :=
      sumOver_sub _ _ _
    rw [hsub, hsrc, htgt]
    omega
  · simp [hadm] at h

end Transfer
