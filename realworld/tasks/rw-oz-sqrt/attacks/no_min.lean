import OzSqrt.Spec
import OzSqrt.Lemmas
/-!
Attack: seven Newton steps as in OpenZeppelin `Math.sqrt`, but without the final
`min(result, a / result)` (the flaw class of CVE-2025-26622 in Vyper's `sqrt`: when `a + 1` is a
square the iterates alternate between the root and the root plus one). Plausible variant, not a
release. Returns 2 at `a = 3`. Proofs `sorry`.

```
function sqrt(uint256 a) internal pure returns (uint256) {
    if (a == 0) {
        return 0;
    }
    uint256 result = 1 << (log2(a) >> 1);
    unchecked {
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        result = (result + a / result) >> 1;
        return result;
    }
}
```
-/
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
    result

theorem req_sqrt_not_above : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below : SqrtNotBelow sqrt := sorry
theorem req_sqrt_up_covers : SqrtUpCovers sqrt := sorry
theorem req_sqrt_up_tight  : SqrtUpTight sqrt := sorry
theorem req_mint_backed    : MintBacked sqrt := sorry
theorem req_mint_full      : MintFull sqrt := sorry
theorem req_mint_live      : MintLive sqrt := sorry
theorem req_newton_budget  : NewtonBudget sqrt := sorry

end OzSqrt
