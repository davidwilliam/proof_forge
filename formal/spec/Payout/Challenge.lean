import Payout.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`Payout.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Payout

def step : Impl := sorry

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_fair_shares    : FairShares step := sorry
theorem req_effects        : Effects step := sorry
theorem req_conservation   : Conserves step := sorry
theorem req_nonnegative    : NonNegative step := sorry
theorem req_authorization  : AuthorizedOnly step := sorry
theorem req_idempotency    : Idempotent step := sorry

end Payout
