import Payout.Spec
import Payout.Lemmas
namespace Payout
def Checks (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧ 0 < r.amount ∧ r.recipients ≠ [] ∧ r.recipients.Nodup ∧
  r.source ∉ r.recipients ∧ r.source ∈ s.accounts ∧ (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧ (r.amount : Int) ≤ s.balance r.source

instance (s : State) (r : Request) : Decidable (Checks s r) := by
  unfold Checks; infer_instance

def step : Impl := fun s r =>
  if Checks s r then
    let s' := { s with balance := expectedBalance s r }
    if r.txId ∈ s.applied then (.rejected, s')
    else (.ok, { s' with applied := r.txId :: s.applied })
  else (.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_fair_shares    : FairShares step := sorry
theorem req_effects        : Effects step := sorry
theorem req_conservation   : Conserves step := sorry
theorem req_nonnegative    : NonNegative step := sorry
theorem req_authorization  : AuthorizedOnly step := sorry
theorem req_idempotency    : Idempotent step := sorry
end Payout
