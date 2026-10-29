import Allocation.Spec
/-!
Port of `Money::allocate` in moneyphp/money 3.0.9 (src/Money.php): every share is
`floor(amount * ratio / total)`; the remainder is then handed out one unit at a time to the
parties in list order, starting with the first, whatever their ratio. Floating point is not
modeled: the port computes exactly. Empty ratios and a ratio total of zero throw
`InvalidArgumentException`, modeled as `none`.
-/
namespace Allocation

/-- Add one unit to each of the first `k` shares. -/
def addFirst : Nat → List Int → List Int
  | 0, xs => xs
  | _, [] => []
  | k + 1, x :: xs => (x + 1) :: addFirst k xs

def allocate : Impl := fun amount ratios =>
  if ratios = [] ∨ ratios.sum = 0 then none
  else
    let floors := ratios.map fun (r : Nat) => amount * (r : Int) / (ratios.sum : Int)
    some (addFirst (amount - floors.sum).toNat floors)

theorem req_valid_succeeds    : ValidSucceeds allocate := sorry
theorem req_invalid_fails     : InvalidFails allocate := sorry
theorem req_one_share_each    : OneShareEach allocate := sorry
theorem req_conservation      : Conserves allocate := sorry
theorem req_within_one_unit   : WithinOneUnit allocate := sorry
theorem req_zero_ratio        : ZeroRatio allocate := sorry
theorem req_sign              : Sign allocate := sorry
theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
