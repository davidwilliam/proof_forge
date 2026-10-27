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
      applied := s.applied })
  else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_authorization  : AuthorizedOnly step := sorry
theorem req_debit_credit   : DebitCredit step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_limit          : LimitRespected step := sorry
theorem req_conservation   : Conserves step := sorry
end Transfer
