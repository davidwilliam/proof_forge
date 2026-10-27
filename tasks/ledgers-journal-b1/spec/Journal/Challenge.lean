import Journal.Spec
/-!
# Locked challenge (never imports candidate code)

`Journal.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Journal

def step : Impl := sorry

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_known_accounts : KnownAccounts step := sorry
theorem req_balanced       : Balanced step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_trial_balance  : TrialBalance step := sorry

end Journal
