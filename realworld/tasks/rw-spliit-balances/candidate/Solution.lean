import Allocation.Spec
/-!
Port of the share computation in Spliit 1.21.0 `getBalances` (src/lib/balances.ts) for one
expense: every participant's share `amount * shares / totalShares` is computed separately and
rounded with `Math.round` (half rounds up). The last participant receives the rest of the
amount before rounding, which is the same exact value. Floating point is not modeled: the
port computes exactly. Inputs Spliit cannot store (no participant, all shares zero) are
refused.
-/
namespace Allocation

/-- `Math.round (num / den)` for `den > 0`: the nearest integer, halves rounded up. -/
def roundHalfUp (num den : Int) : Int := (2 * num + den) / (2 * den)

def allocate : Impl := fun amount ratios =>
  if ratios = [] ∨ ratios.sum = 0 then none
  else some (ratios.map fun (r : Nat) => roundHalfUp (amount * (r : Int)) (ratios.sum : Int))

theorem req_valid_succeeds    : ValidSucceeds allocate := sorry
theorem req_invalid_fails     : InvalidFails allocate := sorry
theorem req_one_share_each    : OneShareEach allocate := sorry
theorem req_conservation      : Conserves allocate := sorry
theorem req_within_one_unit   : WithinOneUnit allocate := sorry
theorem req_zero_ratio        : ZeroRatio allocate := sorry
theorem req_sign              : Sign allocate := sorry
theorem req_largest_remainder : LargestRemainder allocate := sorry

end Allocation
