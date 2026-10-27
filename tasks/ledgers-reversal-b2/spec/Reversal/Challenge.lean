import Reversal.Spec
/-!
# Locked challenge (never imports candidate code)

`Reversal.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Reversal

def step : Impl := sorry

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
