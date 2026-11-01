import VyperSqrt.Spec
import VyperSqrt.Lemmas
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`VyperSqrt.sqrt` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace VyperSqrt

def sqrt : SqrtFn := sorry

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below   : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total       : SqrtTotal sqrt := sorry
theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := sorry
theorem req_deployed_loop    : DeployedLoop sqrt := sorry

end VyperSqrt
