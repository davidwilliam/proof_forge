import VyperSqrt.Spec
import VyperSqrt.Lemmas

namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below   : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total       : SqrtTotal sqrt := sorry
theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  unfold sqrt vyperSqrtWith
  simp [hx]
theorem req_deployed_loop    : DeployedLoop sqrt := ⟨_, fun _ => rfl⟩

end VyperSqrt
