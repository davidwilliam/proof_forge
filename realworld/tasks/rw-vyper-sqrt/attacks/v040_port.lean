import VyperSqrt.Spec
import VyperSqrt.Lemmas
/-!
Port of the code the Vyper compiler v0.4.0 (commit e9db8d9f7486eae38f5b86531629019ad28f514e)
inlines for the builtin `sqrt(d: decimal) -> decimal`, `vyper/builtins/functions.py`, class
`Sqrt` (lines 2117 to 2172):

```
assert x >= 0.0
z: decimal = 0.0

if x == 0.0:
    z = 0.0
else:
    z = x / 2.0 + 0.5
    y: decimal = x

    for i: uint256 in range(256):
        if z == y:
            break
        y = z
        z = (x / z + z) / 2.0
```

The result is `z`. The decimal operations and the loop are the protected `ddiv`, `dadd` and
`loop` of `VyperSqrt/Spec.lean`.
-/
namespace VyperSqrt

def sqrt : SqrtFn := fun x =>
  if x < 0 then none
  else if x = 0 then some 0
  else
    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
      (loop x 256 x z0).map fun p => p.2

theorem req_sqrt_not_above   : SqrtNotAbove sqrt := sorry
theorem req_sqrt_not_below   : SqrtNotBelow sqrt := sorry
theorem req_sqrt_total       : SqrtTotal sqrt := sorry
theorem req_sqrt_neg_reverts : SqrtNegReverts sqrt := sorry
theorem req_deployed_loop    : DeployedLoop sqrt := sorry

end VyperSqrt
