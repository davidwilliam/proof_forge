import Allocation.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`Allocation.allocate` is a Comparator definition hole. A solution must define it and prove
every theorem below with exactly these statements.
-/

namespace Allocation

def allocate : Impl := sorry

theorem req_valid_succeeds    : ValidSucceeds allocate := sorry
theorem req_invalid_fails     : InvalidFails allocate := sorry
theorem req_one_share_each    : OneShareEach allocate := sorry
theorem req_conservation      : Conserves allocate := sorry
theorem req_within_one_unit   : WithinOneUnit allocate := sorry
theorem req_zero_ratio        : ZeroRatio allocate := sorry
theorem req_sign              : Sign allocate := sorry
theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
