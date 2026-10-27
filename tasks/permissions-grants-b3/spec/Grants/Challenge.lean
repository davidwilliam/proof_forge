import Grants.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`Grants.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Grants

def step : Impl := sorry

theorem req_valid_succeeds  : ValidSucceeds step := sorry
theorem req_invalid_noop    : InvalidNoop step := sorry
theorem req_authorization   : AdminOnly step := sorry
theorem req_no_self_grant   : NoSelfGrant step := sorry
theorem req_others_unchanged : OthersUnchanged step := sorry
theorem req_effects         : Effects step := sorry
theorem req_idempotency     : Idempotent step := sorry
theorem req_last_admin      : KeepsAdmin step := sorry

end Grants
