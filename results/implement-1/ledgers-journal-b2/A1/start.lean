import Journal.Spec
import Journal.Lemmas

namespace Journal

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun s _ => (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_known_accounts : KnownAccounts step := sorry
theorem req_balanced       : Balanced step := sorry
theorem req_effects        : Effects step := sorry
theorem req_idempotency    : Idempotent step := sorry
theorem req_trial_balance  : TrialBalance step := sorry

end Journal
