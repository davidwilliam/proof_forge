import PrioQueue.Spec

namespace PrioQueue

-- Placeholder body; replace it with an implementation that meets the spec.
def step : Impl := fun s _ => (Outcome.rejected, s)

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_capacity       : CapacityBound step := sorry
theorem req_pop_min        : PopMin step := sorry
theorem req_sorted         : KeepsSorted step := sorry
theorem req_insert_effects : InsertEffects step := sorry
theorem req_pop_effects    : PopEffects step := sorry
theorem req_fifo_ties      : FifoTies step := sorry

end PrioQueue
