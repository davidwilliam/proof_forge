/-!
# Integer square root of OpenZeppelin `Math` and the first deposit of a volatile pool (protected)

Owner-reviewed definitions for Solidity code of OpenZeppelin Contracts v4.9.6
(commit dc44c9f1a4c3b10af99492eed84f83ed244203f6, `contracts/utils/math/Math.sol`) and of the
volatile pools of Aerodrome (commit d5e48b3b36a08726abd74432974c5bcdb4507bc9,
`contracts/Pool.sol`, built with OpenZeppelin 4.8.0, whose `sqrt` is the same), which call it:

* `Math.log2(uint256 value)` (lines 199 to 234), the floor of the base-2 logarithm by binary
  search on the bits;
* `Math.sqrt(uint256 a)` (lines 152 to 183), the floor of the square root; it is the definition
  hole, and `newtonSqrt` below states the shape of the deployed algorithm;
* `Math.sqrt(uint256 a, Rounding rounding)` (lines 188 to 193) with `Rounding.Up`, the root
  rounded up, as `sqrtUp`;
* the first deposit of `Pool.mint` (Aerodrome lines 313 to 315 and 323 to 324),
  `liquidity = Math.sqrt(_amount0 * _amount1) - MINIMUM_LIQUIDITY` with
  `MINIMUM_LIQUIDITY = 10 ** 3`, as `firstMint`. Velodrome V2 (commit
  e3f62b897fa517bd5e3a5057f7e02ab4b35edbeb, `contracts/Pool.sol` line 305) makes the same call
  but reverts when `liquidity < MINIMUM_LIQUIDITY` (line 314); that variant is not ported.

Solidity's `uint256` is `BitVec 256`. Inside `unchecked` blocks `+`, `*`, `<<` and `>>` wrap or drop
bits exactly like `BitVec`'s operations; `a / b` is `BitVec`'s unsigned division (Solidity reverts
on a zero divisor, which these routines never reach). Checked arithmetic (Solidity 0.8 outside
`unchecked`) reverts on overflow and underflow; a revert is `none`.

Candidates may not edit this file. Every requirement is a predicate over an implementation
`sqrt : SqrtFn`; the locked challenge (`OzSqrt/Challenge.lean`) applies each one to the
definition hole `OzSqrt.sqrt`.
-/

namespace OzSqrt

/-- A Solidity `uint256`. -/
abbrev U256 := BitVec 256

/-- A port of `Math.sqrt(uint256 a) returns (uint256)`. -/
abbrev SqrtFn := U256 → U256

/-- One `if` of `Math.log2`: `if (value >> k > 0) { value >>= k; result += k; }`, on the pair
`(value, result)`. -/
def log2Step (k : Nat) (p : U256 × U256) : U256 × U256 :=
  if p.1 >>> k > 0 then (p.1 >>> k, p.2 + BitVec.ofNat 256 k) else p

/-- `Math.log2(uint256 value)`:

```
uint256 result = 0;
unchecked {
    if (value >> 128 > 0) { value >>= 128; result += 128; }
    if (value >> 64 > 0)  { value >>= 64;  result += 64; }
    if (value >> 32 > 0)  { value >>= 32;  result += 32; }
    if (value >> 16 > 0)  { value >>= 16;  result += 16; }
    if (value >> 8 > 0)   { value >>= 8;   result += 8; }
    if (value >> 4 > 0)   { value >>= 4;   result += 4; }
    if (value >> 2 > 0)   { value >>= 2;   result += 2; }
    if (value >> 1 > 0)   { result += 1; }
}
return result;
```

The last `if` does not shift `value`, which is not read afterwards; shifting it changes nothing
in the result. -/
def log2 (value : U256) : U256 :=
  (log2Step 1 (log2Step 2 (log2Step 4 (log2Step 8 (log2Step 16 (log2Step 32 (log2Step 64
    (log2Step 128 (value, 0))))))))).2

/-- `Math.min(uint256 a, uint256 b)`: `return a < b ? a : b;`. -/
def min (a b : U256) : U256 := if a < b then a else b

/-- One line `result = (result + a / result) >> 1;` of `Math.sqrt`: a Newton step. -/
def newtonStep (a result : U256) : U256 := (result + a / result) >>> 1

/-- `iterate f k x` applies `f` to `x` `k` times. -/
def iterate (f : U256 → U256) : Nat → U256 → U256
  | 0, x => x
  | k + 1, x => iterate f k (f x)

/-- The shape of `Math.sqrt` with `k` Newton steps:

```
if (a == 0) { return 0; }
uint256 result = 1 << (log2(a) >> 1);
unchecked {
    result = (result + a / result) >> 1;   // k times; the deployed code has seven
    return min(result, a / result);
}
```
-/
def newtonSqrt (k : Nat) (a : U256) : U256 :=
  if a = 0 then 0
  else
    let result := iterate (newtonStep a) k ((1 : U256) <<< (log2 a >>> 1))
    min result (a / result)

/-- `Math.sqrt(uint256 a, Rounding rounding)` with `Rounding.Up`, given the floor routine:

```
unchecked {
    uint256 result = sqrt(a);
    return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
}
```
-/
def sqrtUp (sqrt : SqrtFn) (a : U256) : U256 :=
  let result := sqrt a
  result + (if result * result < a then 1 else 0)

/-- `MINIMUM_LIQUIDITY = 10 ** 3` of `Pool`. -/
def MINIMUM_LIQUIDITY : U256 := 1000

/-- The first deposit of a volatile pool, `Pool.mint` when `_totalSupply == 0` and the pool is
not stable, given the square-root routine:

```
liquidity = Math.sqrt(_amount0 * _amount1) - MINIMUM_LIQUIDITY;
_mint(address(1), MINIMUM_LIQUIDITY);
...
if (liquidity == 0) revert InsufficientLiquidityMinted();
_mint(to, liquidity);
```

`_amount0 * _amount1` and `- MINIMUM_LIQUIDITY` are checked: an overflow or an underflow
reverts. The result is the liquidity minted to the depositor; `MINIMUM_LIQUIDITY` more is minted
to `address(1)` and locked. -/
def firstMint (sqrt : SqrtFn) (amount0 amount1 : U256) : Option U256 :=
  if 2 ^ 256 ≤ amount0.toNat * amount1.toNat then none
  else
    let root := sqrt (amount0 * amount1)
    if root < MINIMUM_LIQUIDITY then none
    else
      let liquidity := root - MINIMUM_LIQUIDITY
      if liquidity = 0 then none else some liquidity

/-! ## Requirements on the square root -/

/-- REQ-SQRT-NOT-ABOVE: the result squared never exceeds the input: the root is never overstated. -/
def SqrtNotAbove (sqrt : SqrtFn) : Prop :=
  ∀ a : U256, (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat

/-- REQ-SQRT-NOT-BELOW: the input is below the result plus one, squared: the root is never
understated. With REQ-SQRT-NOT-ABOVE, the result is the floor of the square root. -/
def SqrtNotBelow (sqrt : SqrtFn) : Prop :=
  ∀ a : U256, a.toNat < ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1)

/-- REQ-SQRT-UP-COVERS: the root rounded up, squared, is at least the input. -/
def SqrtUpCovers (sqrt : SqrtFn) : Prop :=
  ∀ a : U256, a.toNat ≤ (sqrtUp sqrt a).toNat * (sqrtUp sqrt a).toNat

/-- REQ-SQRT-UP-TIGHT: the root rounded up is the smallest such number: one less, squared, is
below the input. -/
def SqrtUpTight (sqrt : SqrtFn) : Prop :=
  ∀ a : U256, 0 < (sqrtUp sqrt a).toNat →
    ((sqrtUp sqrt a).toNat - 1) * ((sqrtUp sqrt a).toNat - 1) < a.toNat

/-- REQ-NEWTON-BUDGET: the routine is the deployed algorithm within its gas budget: the
power-of-two estimate from `log2`, at most seven Newton steps, and the final `min`. -/
def NewtonBudget (sqrt : SqrtFn) : Prop :=
  ∃ k, k ≤ 7 ∧ ∀ a : U256, sqrt a = newtonSqrt k a

/-! ## Requirements on the first deposit -/

/-- REQ-MINT-BACKED: the LP supply the first deposit creates, the depositor's liquidity plus the
locked `MINIMUM_LIQUIDITY`, squared, never exceeds `amount0 * amount1`: no LP unit is created
without its share of the geometric mean of the reserves. -/
def MintBacked (sqrt : SqrtFn) : Prop :=
  ∀ amount0 amount1 liquidity : U256, firstMint sqrt amount0 amount1 = some liquidity →
    (liquidity.toNat + 1000) * (liquidity.toNat + 1000) ≤ amount0.toNat * amount1.toNat

/-- REQ-MINT-FULL: the depositor is not shortchanged: one more unit of liquidity would exceed the
geometric mean. -/
def MintFull (sqrt : SqrtFn) : Prop :=
  ∀ amount0 amount1 liquidity : U256, firstMint sqrt amount0 amount1 = some liquidity →
    amount0.toNat * amount1.toNat < (liquidity.toNat + 1001) * (liquidity.toNat + 1001)

/-- REQ-MINT-LIVE: a first deposit whose product fits in 256 bits and is at least `1001 * 1001`
never reverts. -/
def MintLive (sqrt : SqrtFn) : Prop :=
  ∀ amount0 amount1 : U256, amount0.toNat * amount1.toNat < 2 ^ 256 →
    1001 * 1001 ≤ amount0.toNat * amount1.toNat → (firstMint sqrt amount0 amount1).isSome

end OzSqrt
