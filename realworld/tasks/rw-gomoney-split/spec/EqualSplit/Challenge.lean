import EqualSplit.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`EqualSplit.split` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace EqualSplit

def split : Impl := sorry

theorem req_valid_succeeds  : ValidSucceeds split := sorry
theorem req_invalid_fails   : InvalidFails split := sorry
theorem req_one_share_each  : OneShareEach split := sorry
theorem req_conservation    : Conserves split := sorry
theorem req_within_one_unit : WithinOneUnit split := sorry
theorem req_sign            : Sign split := sorry

end EqualSplit
