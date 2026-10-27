import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    let n := r.recipients.length
    let extra := r.amount % n
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => ((r.amount / n + if n - extra ≤ i then 1 else 0 : Nat) : Int)
                             | none => 0),
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
