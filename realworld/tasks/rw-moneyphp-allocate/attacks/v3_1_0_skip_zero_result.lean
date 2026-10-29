import Allocation.Spec
/-!
Port of `Money::allocate` in moneyphp/money 3.1.0 to 3.1.2 (the fix for issue #436): the
remainder loop skips every party whose share is still zero, and walks past the last party
when no nonzero share is left ("Undefined offset", issue #466), modeled as `none`.
-/
namespace Allocation

/-- Hand out `rem` units in list order, skipping zero shares; `none` past the last party. -/
def handOut : Nat → List Int → Option (List Int)
  | 0, xs => some xs
  | _ + 1, [] => none
  | k + 1, x :: xs =>
    if x = 0 then (handOut (k + 1) xs).map (x :: ·)
    else (handOut k xs).map ((x + 1) :: ·)

def allocate : Impl := fun amount ratios =>
  if ratios = [] ∨ ratios.sum = 0 then none
  else
    let floors := ratios.map fun (r : Nat) => amount * (r : Int) / (ratios.sum : Int)
    handOut (amount - floors.sum).toNat floors

theorem req_valid_succeeds    : ValidSucceeds allocate := sorry
theorem req_invalid_fails     : InvalidFails allocate := sorry
theorem req_one_share_each    : OneShareEach allocate := sorry
theorem req_conservation      : Conserves allocate := sorry
theorem req_within_one_unit   : WithinOneUnit allocate := sorry
theorem req_zero_ratio        : ZeroRatio allocate := sorry
theorem req_sign              : Sign allocate := sorry
theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
