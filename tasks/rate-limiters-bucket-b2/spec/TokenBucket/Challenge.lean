import TokenBucket.Spec
/-!
# Locked challenge (never imports candidate code)

`TokenBucket.step` is a Comparator definition hole. A solution must define it and prove
every theorem below with exactly these statements.
-/

namespace TokenBucket

def step : Impl := sorry

theorem req_valid_succeeds      : ValidSucceeds step := sorry
theorem req_invalid_noop        : InvalidNoop step := sorry
theorem req_allow_iff_sufficient : AllowIffSufficient step := sorry
theorem req_time_monotone       : TimeMonotone step := sorry
theorem req_remaining           : Remaining step := sorry
theorem req_effects             : Effects step := sorry
theorem req_capacity            : CapacityBound step := sorry

end TokenBucket
