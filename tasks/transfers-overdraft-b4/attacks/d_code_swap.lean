import Transfer.Spec
import Transfer.Lemmas
namespace Transfer
/-! Reference implementation and its proofs. -/
instance instDecidableValidTransfer (s : State) (r : Request) :
    Decidable (ValidTransfer s r) := by
  unfold ValidTransfer; infer_instance

def refStep : Impl := fun s r =>
  if ValidTransfer s r then
    (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied })
  else
    (.rejected, s)

theorem ref_step_of_valid {s : State} {r : Request} (h : ValidTransfer s r) :
    refStep s r = (.ok, { s with balance := expectedBalance s r, applied := r.txId :: s.applied }) := by
  simp [refStep, h]

theorem ref_step_of_invalid {s : State} {r : Request} (h : ¬ ValidTransfer s r) :
    refStep s r = (.rejected, s) := by
  simp [refStep, h]

theorem ref_ok_valid {s : State} {r : Request} (h : (refStep s r).1 = .ok) : ValidTransfer s r := by
  by_cases hv : ValidTransfer s r
  · exact hv
  · rw [ref_step_of_invalid hv] at h; cases h

theorem ref_req_valid_succeeds : ValidSucceeds refStep := by
  intro s r h; rw [ref_step_of_valid h]

theorem ref_req_invalid_noop : InvalidNoop refStep := by
  intro s r h; exact ref_step_of_invalid h

theorem ref_req_authorization : AuthorizedOnly refStep := by
  intro s r hok
  exact (ref_ok_valid hok).2.2.2.2.2.1

theorem ref_req_debit_credit : DebitCredit refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  have hne : r.source ≠ r.target := hv.2.2.1
  rw [ref_step_of_valid hv]
  simp [expectedBalance, hne, Ne.symm hne]

theorem ref_req_effects : Effects refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  rw [ref_step_of_valid hv]
  exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem ref_req_idempotency : Idempotent refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  rw [ref_step_of_valid hv]
  refine ⟨fun x => by simp, ?_⟩
  apply ref_step_of_invalid
  intro h'
  exact h'.2.2.2.2.2.2.2 (by simp)

theorem ref_req_limit : LimitRespected refStep := by
  intro s r hw
  by_cases hv : ValidTransfer s r
  · rw [ref_step_of_valid hv]
    intro a ha
    have h0 := hw a ha
    have hlim := hv.2.2.2.2.2.2.1
    simp only [expectedBalance]
    by_cases hs : a = r.source
    · subst hs; simp [hv.2.2.1]; omega
    · by_cases ht : a = r.target
      · subst ht; simp [hs]; omega
      · simp [hs, ht]; omega
  · rw [ref_step_of_invalid hv]; exact hw

theorem ref_req_conservation : Conserves refStep := by
  intro s r hok
  have hv := ref_ok_valid hok
  have hnd := hv.1
  have hsrc := hv.2.2.2.1
  have htgt := hv.2.2.2.2.1
  rw [ref_step_of_valid hv]
  unfold total expectedBalance
  simp only
  rw [sumOver_add (f := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)),
    sumOver_sub, sumOver_ite_eq hnd, sumOver_ite_eq hnd]
  simp [hsrc, htgt]

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

def buggyStep : Impl := fun s r =>
  if admissible s r then
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.requester then (r.amount : Int) else 0)
                          + (if a = r.target then (r.amount : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)

@[implemented_by buggyStep]
def step : Impl := refStep

theorem req_valid_succeeds : ValidSucceeds step := ref_req_valid_succeeds
theorem req_invalid_noop : InvalidNoop step := ref_req_invalid_noop
theorem req_authorization : AuthorizedOnly step := ref_req_authorization
theorem req_debit_credit : DebitCredit step := ref_req_debit_credit
theorem req_effects : Effects step := ref_req_effects
theorem req_idempotency : Idempotent step := ref_req_idempotency
theorem req_limit : LimitRespected step := ref_req_limit
theorem req_conservation : Conserves step := ref_req_conservation
end Transfer
