import Allocation.Spec
/-!
Port of `Money::allocate` in moneyphp/money 3.1.3 to 3.2.0 (the fix for issue #466): the
remainder loop skips parties whose ratio is zero and otherwise hands out units in list order,
without regard to which shares were rounded down the most (pull request #492).
-/
namespace Allocation

/-- Hand out `rem` units in list order to parties with a nonzero ratio. -/
def handOut : Nat → List (Int × Nat) → List Int
  | _, [] => []
  | 0, xs => xs.map (·.1)
  | k + 1, (x, r) :: xs =>
    if r = 0 then x :: handOut (k + 1) xs
    else (x + 1) :: handOut k xs

def allocate : Impl := fun amount ratios =>
  if ratios = [] ∨ ratios.sum = 0 then none
  else
    let floors := ratios.map fun (r : Nat) => amount * (r : Int) / (ratios.sum : Int)
    some (handOut (amount - floors.sum).toNat (floors.zip ratios))

theorem req_valid_succeeds    : ValidSucceeds allocate := sorry
theorem req_invalid_fails     : InvalidFails allocate := sorry
theorem req_one_share_each    : OneShareEach allocate := sorry
theorem req_conservation      : Conserves allocate := sorry
theorem req_within_one_unit   : WithinOneUnit allocate := sorry
theorem req_zero_ratio        : ZeroRatio allocate := sorry
theorem req_sign              : Sign allocate := sorry
theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
