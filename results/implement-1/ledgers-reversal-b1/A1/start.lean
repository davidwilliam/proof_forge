import Reversal.Spec
import Reversal.Lemmas

namespace Reversal

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun s _ => (Outcome.rejected, s)

theorem req_post_succeeds    : PostSucceeds step := sorry
theorem req_reverse_succeeds : ReverseSucceeds step := sorry
theorem req_invalid_noop     : InvalidNoop step := sorry
theorem req_post_effects     : PostEffects step := sorry
theorem req_reverse_effects  : ReverseEffects step := sorry
theorem req_reverse_once     : ReverseOnce step := sorry
theorem req_roundtrip        : RoundTrip step := sorry
theorem req_trial_balance    : TrialBalance step := sorry
theorem req_well_formed      : StaysWellFormed step := sorry
theorem req_consistent       : StaysConsistent step := sorry

end Reversal
