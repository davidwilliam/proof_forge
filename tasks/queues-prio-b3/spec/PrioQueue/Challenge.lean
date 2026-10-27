import PrioQueue.Spec
/-!
# Locked challenge (never imports candidate code)

`PrioQueue.step` is a Comparator definition hole. A solution must define it and prove
every theorem below with exactly these statements.
-/

namespace PrioQueue

def step : Impl := sorry

theorem req_valid_succeeds : ValidSucceeds step := sorry
theorem req_invalid_noop   : InvalidNoop step := sorry
theorem req_capacity       : CapacityBound step := sorry
theorem req_pop_min        : PopMin step := sorry
theorem req_sorted         : KeepsSorted step := sorry
theorem req_insert_effects : InsertEffects step := sorry
theorem req_pop_effects    : PopEffects step := sorry
theorem req_fifo_ties      : FifoTies step := sorry

end PrioQueue
