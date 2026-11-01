import VyperSqrt.Spec
import VyperSqrt.Lemmas
import ProofForgeFin.Sqrt
/-!
Fixed `sqrt`: the deployed Babylonian loop followed by the choice `min y z`
(`if y < z then y else z`), i.e. the fix of Vyper PR 4486. The loop alone can end
one unit above the root; taking the smaller of the last two iterates rounds down.
-/
namespace VyperSqrt

def sqrt : SqrtFn := vyperSqrtWith (fun y z => if y < z then y else z)

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below   : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total       : SqrtTotal sqrt := sorry
theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := by
  intro x hx
  show vyperSqrtWith _ x = none
  unfold vyperSqrtWith
  rw [if_pos hx]

theorem req_deployed_loop    : DeployedLoop sqrt := ⟨_, fun _ => rfl⟩

end VyperSqrt
