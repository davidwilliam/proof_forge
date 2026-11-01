import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

-- Placeholder body; replace it with an implementation that meets the spec.
def sqrt : SqrtFn := fun _ => none

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below   : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total       : SqrtTotal sqrt := sorry
theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := sorry
theorem req_deployed_loop    : DeployedLoop sqrt := sorry

end VyperSqrt
