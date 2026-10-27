import TokenBucket.Spec
namespace TokenBucket
instance instDecidableAdmissible (s : State) (r : Request) : Decidable (Admissible s r) := by
  unfold Admissible; infer_instance
def step : Impl := fun s r =>
  if s.last ≤ r.time ∧ 0 < r.cost ∧ r.cost < refilled s r.time then
    (.ok, { s with tokens := refilled s r.time - r.cost, last := r.time })
  else (.rejected, s)
theorem req_valid_succeeds       : ValidSucceeds step := sorry
theorem req_invalid_noop         : InvalidNoop step := sorry
theorem req_allow_iff_sufficient : AllowIffSufficient step := sorry
theorem req_time_monotone        : TimeMonotone step := sorry
theorem req_remaining            : Remaining step := sorry
theorem req_effects              : Effects step := sorry
theorem req_capacity             : CapacityBound step := sorry
end TokenBucket
