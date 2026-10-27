import FeePayout.Spec
import FeePayout.Lemmas
namespace FeePayout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
/-- Preconditions checked before a payout is applied. -/
def CanPay (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  s.feeBps ≤ 10000 ∧
  0 < r.amount ∧
  r.recipients ≠ [] ∧
  r.recipients.Nodup ∧
  r.source ∉ r.recipients ∧
  s.feeAccount ∉ r.recipients ∧
  s.feeAccount ≠ r.source ∧
  r.source ∈ s.accounts ∧
  s.feeAccount ∈ s.accounts ∧
  (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧
  (netOf s.feeBps r.amount : Int) ≤ s.balance r.source ∧
  r.txId ∉ s.applied
instance instDecidableCanPay (s : State) (r : Request) : Decidable (CanPay s r) := by
  unfold CanPay; infer_instance
def step : Impl := fun s r =>
  if CanPay s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount n : Int) else 0)
                          + (if a = s.feeAccount then (feeCredit s.feeBps r.amount n : Int) else 0),
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
