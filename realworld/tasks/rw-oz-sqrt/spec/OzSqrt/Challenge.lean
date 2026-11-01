import OzSqrt.Spec
import OzSqrt.Lemmas
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`OzSqrt.sqrt` is a Comparator definition hole. A solution must define it and prove every theorem
below with exactly these statements.
-/

namespace OzSqrt

def sqrt : SqrtFn := sorry

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := sorry

end OzSqrt
