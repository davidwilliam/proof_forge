import Batch.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`Batch.step` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace Batch

def step : Impl := sorry

theorem req_valid_succeeds   : ValidSucceeds step := sorry
theorem req_atomicity        : Atomicity step := sorry
theorem req_single_leg       : SingleLeg step := sorry
theorem req_effects          : Effects step := sorry
theorem req_idempotency      : Idempotent step := sorry
theorem req_conservation     : Conserves step := sorry
theorem req_limit_every_step : LimitEveryStep step := sorry

end Batch
