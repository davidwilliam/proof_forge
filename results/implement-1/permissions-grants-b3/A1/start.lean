import Grants.Spec

namespace Grants

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun s _ => (Outcome.rejected, s)

theorem req_valid_succeeds  : ValidSucceeds step := sorry
theorem req_invalid_noop    : InvalidNoop step := sorry
theorem req_authorization   : AdminOnly step := sorry
theorem req_no_self_grant   : NoSelfGrant step := sorry
theorem req_others_unchanged : OthersUnchanged step := sorry
theorem req_effects         : Effects step := sorry
theorem req_idempotency     : Idempotent step := sorry
theorem req_last_admin      : KeepsAdmin step := sorry

end Grants
