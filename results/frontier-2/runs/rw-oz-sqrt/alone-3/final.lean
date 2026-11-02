import OzSqrt.Spec
import OzSqrt.Lemmas
namespace OzSqrt

def sqrt : SqrtFn := fun a =>
  if a = 0 then 0
  else
    let result : U256 := (1 : U256) <<< (log2 a >>> 1)
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    let result := (result + a / result) >>> 1
    min result (a / result)

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := by
  refine ⟨7, Nat.le_refl 7, fun a => ?_⟩
  unfold sqrt newtonSqrt iterate newtonStep
  by_cases h : a = 0 <;> simp [h]

end OzSqrt
