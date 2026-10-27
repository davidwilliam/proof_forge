import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
def step : Impl := fun s r =>
  if ValidPayout s r then
    let n := r.recipients.length
    let fee := r.amount * s.feeBps / 10000
    let share := (r.amount - fee) / n
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then (share : Int) else 0)
                          + (if a = s.feeAccount then (fee : Int) else 0),
      applied := r.txId :: s.applied })
  else (.rejected, s)
theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_authorization  : AuthorizedOnly step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_nonnegative    : NonNegative step := sorry
theorem req_equal_shares   : EqualShares step := sorry
theorem req_fee_collected  : FeeCollected step := sorry
theorem req_conservation   : Conserves step := sorry
end FeePayout
