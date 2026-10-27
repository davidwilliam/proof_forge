import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance

def step : Impl := fun s r =>
  if ValidPayout s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then (((r.amount + n - 1) / n : Nat) : Int) else 0),
      applied := r.txId :: s.applied })
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
