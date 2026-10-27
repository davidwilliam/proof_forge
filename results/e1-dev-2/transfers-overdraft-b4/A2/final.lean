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

theorem req_limit_aux6 : LimitRespected step := by
  intro s r hs a ha
  unfold step at ha ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at ha ⊢
    by_cases has : a = r.source
    · subst has
      have hne : r.source ≠ r.target := hadm.2.2.1
      have hsrc : -(s.limit r.source : Int) ≤ s.balance r.source - (r.amount : Int) := hadm.2.2.2.2.2.2.1
      simp only [if_true, hne, if_false] at ⊢
      omega
    · have h1 : (if a = r.source then (r.amount : Int) else 0) = 0 := if_neg has
      rw [h1]
      by_cases hat : a = r.target
      · subst hat
        have hle : -(s.limit r.target : Int) ≤ s.balance r.target := hs r.target ha
        simp only [if_true] at ⊢
        omega
      · have h2 : (if a = r.target then (r.amount : Int) else 0) = 0 := if_neg hat
        rw [h2]
        simpa using hs a ha
  · simp [hadm] at ha ⊢
    exact hs a ha

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

theorem req_authorization  : AuthorizedOnly step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · exact hadm.2.2.2.2.2.1
  · simp [hadm] at h

theorem req_debit_credit : DebitCredit step := by
  intro s r h
  unfold step at h
  by_cases hadm : admissible s r
  · have hne : r.source ≠ r.target := hadm.2.2.1
    simp only [hadm, ↓reduceIte] at h
    unfold step
    simp only [hadm, ↓reduceIte]
    constructor
    · simp [hne]
    · have hts : r.target ≠ r.source := fun heq => hne heq.symm
      simp [hts]
  · simp [hadm] at h

theorem req_effects        : Effects step := by
  intro s r h
  unfold step at h ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at h ⊢
    exact ⟨trivial, trivial, trivial, fun a => rfl⟩
  · simp [hadm] at h

theorem req_idempotency    : Idempotent step := by
  intro s r h
  unfold step at h ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at h ⊢
    constructor
    · intro x
      simp
    · have hmem : r.txId ∈ (r.txId :: s.applied) := by simp
      have hadm2 : ¬ admissible ({ s with balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0), applied := r.txId :: s.applied } : State) r := by
        intro hc
        exact hc.2.2.2.2.2.2.2 hmem
      simp [hadm2]
  · simp [hadm] at h

theorem req_limit : LimitRespected step := by
  intro s r hs a ha
  unfold step at ha ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at ha ⊢
    by_cases has : a = r.source
    · subst has
      have hne : r.source ≠ r.target := hadm.2.2.1
      have hsrc : -(s.limit r.source : Int) ≤ s.balance r.source - (r.amount : Int) := hadm.2.2.2.2.2.2.1
      simp only [if_true, hne, if_false] at ⊢
      omega
    · have h1 : (if a = r.source then (r.amount : Int) else 0) = 0 := if_neg has
      rw [h1]
      by_cases hat : a = r.target
      · subst hat
        have hle : -(s.limit r.target : Int) ≤ s.balance r.target := hs r.target ha
        simp only [if_true] at ⊢
        omega
      · have h2 : (if a = r.target then (r.amount : Int) else 0) = 0 := if_neg hat
        rw [h2]
        simpa using hs a ha
  · simp [hadm] at ha ⊢
    exact hs a ha

theorem req_conservation   : Conserves step := by
  intro s r h
  unfold step at h ⊢
  by_cases hadm : admissible s r
  · simp only [hadm, ↓reduceIte] at h ⊢
    unfold total
    simp only
    have hnodup : s.accounts.Nodup := hadm.1
    have hsrc : r.source ∈ s.accounts := hadm.2.2.2.1
    have htgt : r.target ∈ s.accounts := hadm.2.2.2.2.1
    have e1 : sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup r.source _, if_pos hsrc]
    have e2 : sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) = (r.amount : Int) := by
      rw [sumOver_ite_eq hnodup r.target _, if_pos htgt]
    have hcongr : sumOver s.accounts (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
      = sumOver s.accounts s.balance - sumOver s.accounts (fun a => if a = r.source then (r.amount : Int) else 0) + sumOver s.accounts (fun a => if a = r.target then (r.amount : Int) else 0) := by
      have h1 : (fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0) + (if a = r.target then (r.amount : Int) else 0))
        = (fun a => (s.balance a - (if a = r.source then (r.amount : Int) else 0)) + (if a = r.target then (r.amount : Int) else 0)) := rfl
      rw [h1, sumOver_add]
      congr 1
      exact sumOver_sub s.accounts s.balance (fun a => if a = r.source then (r.amount : Int) else 0)
    rw [hcongr, e1, e2]
    omega
  · simp [hadm] at h

end Transfer
