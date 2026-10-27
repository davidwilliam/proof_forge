import FeePayout.Spec
import FeePayout.Lemmas
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`FeePayout.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace FeePayout

def step : Impl := sorry

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
