import Payout.Spec
import Payout.Lemmas
namespace Payout
instance instDecidableValidPayout (s : State) (r : Request) : Decidable (ValidPayout s r) := by
  unfold ValidPayout; infer_instance
/-- Preconditions checked before a payout is applied. -/
def CanPay (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.recipients ≠ [] ∧
  r.recipients.Nodup ∧
  r.source ∈ s.accounts ∧
  (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧
  (r.amount : Int) ≤ s.balance r.source ∧
  r.txId ∉ s.applied
instance instDecidableCanPay (s : State) (r : Request) : Decidable (CanPay s r) := by
  unfold CanPay; infer_instance
def step : Impl := fun s r =>
  if CanPay s r then
    let n := r.recipients.length
    (.ok, { s with
      balance := fun a => s.balance a - (if a = r.source then (r.amount : Int) else 0)
                          + (match indexOf? r.recipients a with
                             | some i => (fairShare r.amount n i : Int)
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
