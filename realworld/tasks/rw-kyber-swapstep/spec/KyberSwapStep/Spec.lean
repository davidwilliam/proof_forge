/-!
# The swap step of KyberSwap Elastic, token1 branches (protected)

Owner-reviewed definitions for Solidity code of KyberSwap Elastic (`KyberNetwork/ks-elastic-sc`,
commit 4ab08c0a60f74809f731bdd333076e32d05f1d17, compiled with Solidity 0.8.9):

* `contracts/libraries/SwapMath.sol`: `computeSwapStep` (lines 28 to 98), `calcReachAmount`
  (102 to 164), `estimateIncrementalLiquidity` (169 to 216), `calcIncrementalLiquidity` (220 to
  249), `calcFinalPrice` (253 to 280) and `calcReturnedAmount` (285 to 320), for
  `isToken0 = false`: the specified amount is in token1, so an exact-input step (token1 in) moves
  the square-root price up and an exact-output step (token1 out) moves it down;
* `contracts/libraries/QuadMath.sol`: `getSmallerRootOfQuadEqn` (lines 8 to 14) and `sqrt`
  (lines 17 to 30, the Babylonian method);
* `contracts/libraries/FullMath.sol`: `mulDivFloor` (lines 15 to 110) and `mulDivCeiling`
  (lines 117 to 126), full-precision `a * b / denominator`;
* `contracts/libraries/SafeCast.sol`: `toUint160`, `toInt256`, `revToInt256`, `revToUint256`;
* `contracts/libraries/MathConstants.sol`: `TWO_FEE_UNITS = 200_000`, `TWO_POW_96 = 2 ** 96`,
  `FEE_UNITS = 100000`, `MAX_TICK_DISTANCE = 480` (strictly less than a 5% price move);
* `contracts/libraries/TickMath.sol`: `MIN_SQRT_RATIO`, `MAX_SQRT_RATIO` (lines 14 to 16);
* `contracts/Pool.sol`: one iteration of the loop of `swap` (lines 371 to 419): the target of the
  step (lines 388 to 392) and the test that decides whether the step crossed the next tick (lines
  412 to 419).

Solidity's `uint256` is `BitVec 256` (`U256`). Every operation of these functions outside the
`unchecked` blocks is checked: it reverts when the exact result does not fit in 256 bits or is
negative, or on a zero divisor. A revert is `none`; every checked operation below is `fit` of its
exact natural-number result. `int256` values are `Int`.

`computeSwapStepWith r` is the deployed computation with the rounding direction of every division
and of the square root chosen by `r : Rounding`. The code at commit 4ab08c0 is
`computeSwapStepWith deployed`. The definition hole `computeSwapStep` of the challenge is the step
under repair; the last requirement (REQ-DEPLOYED-STEP) keeps it a member of this family.

The defect. Lines 186 to 193 compute the fee liquidity `deltaL` of an exact-input step with
`FullMath.mulDivFloor` under a comment saying that `deltaL` is rounded up so that the next price
is rounded down. The floor was introduced by `KyberNetwork/ks-elastic-sc-legacy` pull request 95
("fix ceiling to floor swapmath", commit 33446757d93619b73403573dc309b9a072b167b1), which replaced
`FullMath.mulDivCeiling`. With an amount one unit below the amount that reaches the target, the
next price can pass the target; `Pool.swap` then stops without crossing the tick although the
price is beyond it. This was exploited on 2023-11-22.

Candidates may not edit this file.
-/

namespace KyberSwapStep

/-- A Solidity `uint256`. -/
abbrev U256 := BitVec 256

/-! ## Checked arithmetic -/

/-- The word with value `n` if `n` fits in 256 bits; `none` (a revert) otherwise. -/
def fit (n : Nat) : Option U256 := if n < 2 ^ 256 then some (BitVec.ofNat 256 n) else none

/-- Checked `a + b`. -/
def add (a b : U256) : Option U256 := fit (a.toNat + b.toNat)

/-- Checked `a - b`: reverts when `b > a`. -/
def sub (a b : U256) : Option U256 := if b.toNat ≤ a.toNat then fit (a.toNat - b.toNat) else none

/-- Checked `a * b`. -/
def mul (a b : U256) : Option U256 := fit (a.toNat * b.toNat)

/-- Checked `a / b`, rounded down: reverts on a zero divisor. -/
def divFloor (a b : U256) : Option U256 := if b = 0 then none else fit (a.toNat / b.toNat)

/-- `a / b` rounded up: reverts on a zero divisor. -/
def divCeiling (a b : U256) : Option U256 :=
  if b = 0 then none else fit ((a.toNat + b.toNat - 1) / b.toNat)

/-- `FullMath.mulDivFloor(a, b, denominator)`: `a * b / denominator` with a full-precision
product, rounded down; reverts when `denominator = 0` or the quotient does not fit. -/
def mulDivFloor (a b d : U256) : Option U256 :=
  if d = 0 then none else fit (a.toNat * b.toNat / d.toNat)

/-- `FullMath.mulDivCeiling(a, b, denominator)`: the same, rounded up
(`result = mulDivFloor(a, b, denominator); if (mulmod(a, b, denominator) > 0) result++;`, with a
checked increment). -/
def mulDivCeiling (a b d : U256) : Option U256 :=
  if d = 0 then none else fit ((a.toNat * b.toNat + d.toNat - 1) / d.toNat)

/-- `mulDivFloor` when `up = false`, `mulDivCeiling` when `up = true`. -/
def mulDiv : Bool → U256 → U256 → U256 → Option U256
  | true => mulDivCeiling
  | false => mulDivFloor

/-- Division rounded down when `up = false`, up when `up = true`. -/
def divRound : Bool → U256 → U256 → Option U256
  | true => divCeiling
  | false => divFloor

/-- `SafeCast.toUint160`: the value, if it is below `2^160`. -/
def toUint160 (y : U256) : Option U256 := if y.toNat < 2 ^ 160 then some y else none

/-- `SafeCast.toInt256`: `require(y < 2**255); z = int256(y);`. -/
def toInt256 (y : U256) : Option Int := if y.toNat < 2 ^ 255 then some (y.toNat : Int) else none

/-- `SafeCast.revToInt256`: `require(y < 2**255); z = -int256(y);`. -/
def revToInt256 (y : U256) : Option Int :=
  if y.toNat < 2 ^ 255 then some (-(y.toNat : Int)) else none

/-! ## Constants -/

/-- `MathConstants.TWO_POW_96 = 2 ** 96`: prices are square roots in Q64.96. -/
def TWO_POW_96 : U256 := BitVec.ofNat 256 (2 ^ 96)

/-- `MathConstants.FEE_UNITS = 100000`: the fee is `feeInFeeUnits / FEE_UNITS`. -/
def FEE_UNITS : U256 := BitVec.ofNat 256 100000

/-- `MathConstants.TWO_FEE_UNITS = 200_000`. -/
def TWO_FEE_UNITS : U256 := BitVec.ofNat 256 200000

/-- `TickMath.MIN_SQRT_RATIO`. -/
def MIN_SQRT_RATIO : Nat := 4295128739

/-- `TickMath.MAX_SQRT_RATIO`. -/
def MAX_SQRT_RATIO : Nat := 1461446703485210103287273052203988822378723970342

/-! ## The square root of `QuadMath` -/

/-- The loop of `QuadMath.sqrt` with at most `n` iterations, on `(z, x)`:
`while (x < z) { z = x; x = (y / x + x) / 2; }`; the result is `z`. -/
def babylonian (y : Nat) : Nat → Nat → Nat → Nat
  | 0, z, _ => z
  | n + 1, z, x => if x < z then babylonian y n x ((y / x + x) / 2) else z

/-- `QuadMath.sqrt(uint256 y)` (lines 17 to 30, inside `unchecked`):

```
if (y > 3) {
  z = y;
  uint256 x = y / 2 + 1;
  while (x < z) {
    z = x;
    x = (y / x + x) / 2;
  }
} else if (y != 0) {
  z = 1;
}
```

The `while` loop has no bound in Solidity; on every `uint256` the iterates reach the root within
256 iterations, so the port runs it with a bound of 512, which does not change the result
(`Lemmas.toNat_sqrt`). No operation wraps: the iterates stay at most `y / 2 + 1`. The result is the
square root rounded down. -/
def sqrt (y : U256) : U256 :=
  if 3 < y.toNat then BitVec.ofNat 256 (babylonian y.toNat 512 y.toNat (y.toNat / 2 + 1))
  else if y.toNat ≠ 0 then 1 else 0

/-- The square root rounded up: `sqrt(y)`, plus one when its square is below `y`. -/
def sqrtUp (y : U256) : U256 :=
  if (sqrt y).toNat * (sqrt y).toNat < y.toNat then BitVec.ofNat 256 ((sqrt y).toNat + 1)
  else sqrt y

/-! ## The rounding directions -/

/-- One rounding direction per division of the token1 branches (`true` rounds up), the choice of
the root (`sqrtUp = true`: rounded up) and one structural choice, `feeFromTmp`: whether the fee
liquidity of an exact-input step is computed from `absDelta` as deployed or from the virtual
input `absDelta * 2^96 / currentSqrtP` rounded by `feeTmp`. -/
structure Rounding where
  /-- `calcReachAmount`, exact input, line 135: `mulDivFloor(liquidity, TWO_FEE_UNITS * absPriceDiff, denominator)`. -/
  reachIn1 : Bool
  /-- `calcReachAmount`, exact input, line 140: `mulDivFloor(numerator, currentSqrtP, TWO_POW_96)`. -/
  reachIn2 : Bool
  /-- `calcReachAmount`, exact output, line 160: `mulDivFloor(liquidity, numerator, denominator)`. -/
  reachOut1 : Bool
  /-- `calcReachAmount`, exact output, line 161: `mulDivFloor(numerator, absPriceDiff, TWO_POW_96)`. -/
  reachOut2 : Bool
  /-- `estimateIncrementalLiquidity`, exact input, line 189: the fee liquidity `deltaL`. -/
  feeIn : Bool
  /-- `false`: `deltaL = mulDiv(TWO_POW_96, absDelta * feeInFeeUnits, TWO_FEE_UNITS * currentSqrtP)`
  (deployed); `true`: `deltaL = mulDiv(mulDiv(absDelta, TWO_POW_96, currentSqrtP), feeInFeeUnits, TWO_FEE_UNITS)`. -/
  feeFromTmp : Bool
  /-- The inner division `mulDiv(absDelta, TWO_POW_96, currentSqrtP)` when `feeFromTmp`. -/
  feeTmp : Bool
  /-- `estimateIncrementalLiquidity`, exact output, line 211: the term subtracted from `b`. -/
  quadB : Bool
  /-- `estimateIncrementalLiquidity`, exact output, line 212: `c`. -/
  quadC : Bool
  /-- `QuadMath.getSmallerRootOfQuadEqn`, line 13: the square root (`false`: `QuadMath.sqrt`,
  rounded down; `true`: rounded up). -/
  sqrtUp : Bool
  /-- `QuadMath.getSmallerRootOfQuadEqn`, line 13: the division by `a`. -/
  rootUp : Bool
  /-- `calcFinalPrice`, line 273: `tmp = mulDivFloor(absDelta, TWO_POW_96, currentSqrtP)`. -/
  priceTmp : Bool
  /-- `calcFinalPrice`, exact input, line 275: `mulDivFloor(liquidity + tmp, currentSqrtP, liquidity + deltaL)`. -/
  priceIn : Bool
  /-- `calcFinalPrice`, exact output, line 277: `mulDivCeiling(liquidity - tmp, currentSqrtP, liquidity + deltaL)`. -/
  priceOut : Bool
  /-- `calcIncrementalLiquidity`, line 241: `tmp1 = mulDivFloor(liquidity, currentSqrtP, TWO_POW_96)`. -/
  incL : Bool
  /-- `calcIncrementalLiquidity`, line 243: `tmp3 = mulDivFloor(tmp2, TWO_POW_96, nextSqrtP)`. -/
  incQ : Bool
  /-- `calcReturnedAmount`, line 312: `mulDivCeiling(liquidity + deltaL, TWO_POW_96, nextSqrtP)`. -/
  retNext : Bool
  /-- `calcReturnedAmount`, line 313: `mulDivFloor(liquidity, TWO_POW_96, currentSqrtP)`. -/
  retCur : Bool
deriving DecidableEq, Repr

/-- The rounding directions of the code at commit 4ab08c0. -/
def deployed : Rounding where
  reachIn1 := false
  reachIn2 := false
  reachOut1 := false
  reachOut2 := false
  feeIn := false
  feeFromTmp := false
  feeTmp := false
  quadB := false
  quadC := false
  sqrtUp := false
  rootUp := false
  priceTmp := false
  priceIn := false
  priceOut := true
  incL := false
  incQ := false
  retNext := true
  retCur := false

/-! ## The functions of `SwapMath` and `QuadMath`, token1 branches -/

/-- `calcReachAmount(liquidity, currentSqrtP, targetSqrtP, feeInFeeUnits, isExactInput, false)`
(lines 102 to 164): the amount that moves the price from `currentSqrtP` to `targetSqrtP`.

```
absPriceDiff = (currentSqrtP >= targetSqrtP) ? (currentSqrtP - targetSqrtP) : (targetSqrtP - currentSqrtP);  // unchecked
if (isExactInput) {
  uint256 denominator = C.TWO_FEE_UNITS * currentSqrtP - feeInFeeUnits * targetSqrtP;
  uint256 numerator = FullMath.mulDivFloor(liquidity, C.TWO_FEE_UNITS * absPriceDiff, denominator);
  reachAmount = FullMath.mulDivFloor(numerator, currentSqrtP, C.TWO_POW_96).toInt256();
} else {
  uint256 denominator = C.TWO_FEE_UNITS * targetSqrtP - feeInFeeUnits * currentSqrtP;
  uint256 numerator = denominator - feeInFeeUnits * targetSqrtP;
  numerator = FullMath.mulDivFloor(liquidity, numerator, denominator);
  reachAmount = FullMath.mulDivFloor(numerator, absPriceDiff, C.TWO_POW_96).revToInt256();
}
``` -/
def calcReachAmount (r : Rounding) (liquidity currentSqrtP targetSqrtP feeInFeeUnits : U256)
    (isExactInput : Bool) : Option Int := do
  let absPriceDiff : U256 :=
    if currentSqrtP.toNat ≥ targetSqrtP.toNat then currentSqrtP - targetSqrtP
    else targetSqrtP - currentSqrtP
  if isExactInput then
    let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul feeInFeeUnits targetSqrtP)
    let numerator ← mulDiv r.reachIn1 liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
    toInt256 (← mulDiv r.reachIn2 numerator currentSqrtP TWO_POW_96)
  else
    let denominator ← sub (← mul TWO_FEE_UNITS targetSqrtP) (← mul feeInFeeUnits currentSqrtP)
    let numerator ← sub denominator (← mul feeInFeeUnits targetSqrtP)
    let numerator ← mulDiv r.reachOut1 liquidity numerator denominator
    revToInt256 (← mulDiv r.reachOut2 numerator absPriceDiff TWO_POW_96)

/-- `QuadMath.getSmallerRootOfQuadEqn(a, b, c)` (lines 8 to 14), the smaller root of
`a x^2 - 2 b x + c = 0`: `smallerRoot = (b - sqrt(b * b - a * c)) / a;`. -/
def getSmallerRootOfQuadEqn (r : Rounding) (a b c : U256) : Option U256 := do
  let d ← sub (← mul b b) (← mul a c)
  let s := bif r.sqrtUp then sqrtUp d else sqrt d
  divRound r.rootUp (← sub b s) a

/-- `estimateIncrementalLiquidity(absDelta, liquidity, currentSqrtP, feeInFeeUnits, isExactInput, false)`
(lines 169 to 216): the fee liquidity `deltaL` of a step that does not reach the target.

```
if (isExactInput) {
  // deltaL = feeInFeeUnits * absDelta * / (currentSqrtP * 2)
  // Because nextSqrtP = (liquidity + absDelta / currentSqrtP) * currentSqrtP / (liquidity + deltaL)
  // so we round up deltaL, to round down nextSqrtP
  deltaL = FullMath.mulDivFloor(C.TWO_POW_96, absDelta * feeInFeeUnits, C.TWO_FEE_UNITS * currentSqrtP);
} else {
  // obtain the smaller root of the quadratic equation
  // ax^2 - 2bx + c = 0 such that b > 0, and x denotes deltaL
  uint256 a = feeInFeeUnits;
  uint256 b = (C.FEE_UNITS - feeInFeeUnits) * liquidity;
  uint256 c = feeInFeeUnits * liquidity * absDelta;
  b -= FullMath.mulDivFloor(C.FEE_UNITS * absDelta, C.TWO_POW_96, currentSqrtP);
  c = FullMath.mulDivFloor(c, C.TWO_POW_96, currentSqrtP);
  deltaL = QuadMath.getSmallerRootOfQuadEqn(a, b, c);
}
``` -/
def estimateIncrementalLiquidity (r : Rounding) (absDelta liquidity currentSqrtP feeInFeeUnits : U256)
    (isExactInput : Bool) : Option U256 := do
  if isExactInput then
    match r.feeFromTmp with
    | true => mulDiv r.feeIn (← mulDiv r.feeTmp absDelta TWO_POW_96 currentSqrtP) feeInFeeUnits TWO_FEE_UNITS
    | false => mulDiv r.feeIn TWO_POW_96 (← mul absDelta feeInFeeUnits) (← mul TWO_FEE_UNITS currentSqrtP)
  else
    let b ← mul (← sub FEE_UNITS feeInFeeUnits) liquidity
    let c ← mul (← mul feeInFeeUnits liquidity) absDelta
    let b ← sub b (← mulDiv r.quadB (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
    let c ← mulDiv r.quadC c TWO_POW_96 currentSqrtP
    getSmallerRootOfQuadEqn r feeInFeeUnits b c

/-- `calcFinalPrice(absDelta, liquidity, deltaL, currentSqrtP, isExactInput, false)` (lines 253
to 280): the price of a step that does not reach the target.

```
uint256 tmp = FullMath.mulDivFloor(absDelta, C.TWO_POW_96, currentSqrtP);
if (isExactInput) {
  return FullMath.mulDivFloor(liquidity + tmp, currentSqrtP, liquidity + deltaL);
} else {
  return FullMath.mulDivCeiling(liquidity - tmp, currentSqrtP, liquidity + deltaL);
}
``` -/
def calcFinalPrice (r : Rounding) (absDelta liquidity deltaL currentSqrtP : U256)
    (isExactInput : Bool) : Option U256 := do
  let tmp ← mulDiv r.priceTmp absDelta TWO_POW_96 currentSqrtP
  if isExactInput then
    mulDiv r.priceIn (← add liquidity tmp) currentSqrtP (← add liquidity deltaL)
  else
    mulDiv r.priceOut (← sub liquidity tmp) currentSqrtP (← add liquidity deltaL)

/-- `calcIncrementalLiquidity(absDelta, liquidity, currentSqrtP, nextSqrtP, isExactInput, false)`
(lines 220 to 249): the fee liquidity of a step that ends on the target.

```
uint256 tmp1 = FullMath.mulDivFloor(liquidity, currentSqrtP, C.TWO_POW_96);
uint256 tmp2 = isExactInput ? tmp1 + absDelta : tmp1 - absDelta;
uint256 tmp3 = FullMath.mulDivFloor(tmp2, C.TWO_POW_96, nextSqrtP);
deltaL = (tmp3 > liquidity) ? tmp3 - liquidity : 0;
``` -/
def calcIncrementalLiquidity (r : Rounding) (absDelta liquidity currentSqrtP nextSqrtP : U256)
    (isExactInput : Bool) : Option U256 := do
  let tmp1 ← mulDiv r.incL liquidity currentSqrtP TWO_POW_96
  let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
  let tmp3 ← mulDiv r.incQ tmp2 TWO_POW_96 nextSqrtP
  pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)

/-- `calcReturnedAmount(liquidity, currentSqrtP, nextSqrtP, deltaL, isExactInput, false)` (lines
285 to 320): the token0 amount, negative when the pool pays it out.

```
returnedAmount =
  FullMath.mulDivCeiling(liquidity + deltaL, C.TWO_POW_96, nextSqrtP).toInt256() +
  FullMath.mulDivFloor(liquidity, C.TWO_POW_96, currentSqrtP).revToInt256();
if (isExactInput && returnedAmount == 1) {
  // rounding make returnedAmount == 1
  returnedAmount = 0;
}
```

The `int256` sum is checked; its operands have opposite signs and are below `2^255` in absolute
value, so it never overflows. -/
def calcReturnedAmount (r : Rounding) (liquidity currentSqrtP nextSqrtP deltaL : U256)
    (isExactInput : Bool) : Option Int := do
  let x ← toInt256 (← mulDiv r.retNext (← add liquidity deltaL) TWO_POW_96 nextSqrtP)
  let y ← revToInt256 (← mulDiv r.retCur liquidity TWO_POW_96 currentSqrtP)
  pure (if isExactInput && x + y == 1 then 0 else x + y)

/-- The outputs of `computeSwapStep`. -/
structure Step where
  /-- `usedAmount`: the part of the specified amount the step uses. -/
  usedAmount : Int
  /-- `returnedAmount`: the token0 amount (output when negative, input when positive). -/
  returnedAmount : Int
  /-- `deltaL`: the fee liquidity reinvested. -/
  deltaL : U256
  /-- `nextSqrtP`: the price after the step. -/
  nextSqrtP : U256
deriving DecidableEq, Repr

/-- `computeSwapStep(liquidity, currentSqrtP, targetSqrtP, feeInFeeUnits, specifiedAmount,
isExactInput, false)` (lines 28 to 98) with rounding directions `r`:

```
if (currentSqrtP == targetSqrtP) return (0, 0, 0, currentSqrtP);
usedAmount = calcReachAmount(liquidity, currentSqrtP, targetSqrtP, feeInFeeUnits, isExactInput, isToken0);
if ((isExactInput && usedAmount > specifiedAmount) || (!isExactInput && usedAmount <= specifiedAmount)) {
  usedAmount = specifiedAmount;
} else {
  nextSqrtP = targetSqrtP;
}
uint256 absDelta = usedAmount >= 0 ? uint256(usedAmount) : usedAmount.revToUint256();
if (nextSqrtP == 0) {
  deltaL = estimateIncrementalLiquidity(absDelta, liquidity, currentSqrtP, feeInFeeUnits, isExactInput, isToken0);
  nextSqrtP = calcFinalPrice(absDelta, liquidity, deltaL, currentSqrtP, isExactInput, isToken0).toUint160();
} else {
  deltaL = calcIncrementalLiquidity(absDelta, liquidity, currentSqrtP, nextSqrtP, isExactInput, isToken0);
}
returnedAmount = calcReturnedAmount(liquidity, currentSqrtP, nextSqrtP, deltaL, isExactInput, isToken0);
```

For an `int256` value, `absDelta` is its absolute value (`revToUint256` is `-y` modulo `2^256`). -/
def computeSwapStepWith (r : Rounding) (liquidity currentSqrtP targetSqrtP feeInFeeUnits : U256)
    (specifiedAmount : Int) (isExactInput : Bool) : Option Step := do
  if currentSqrtP = targetSqrtP then return ⟨0, 0, 0, currentSqrtP⟩
  let reach ← calcReachAmount r liquidity currentSqrtP targetSqrtP feeInFeeUnits isExactInput
  let notReached : Bool := (isExactInput && decide (reach > specifiedAmount)) ||
    (!isExactInput && decide (reach ≤ specifiedAmount))
  let usedAmount := if notReached then specifiedAmount else reach
  let nextSqrtP : U256 := if notReached then 0 else targetSqrtP
  let absDelta : U256 := BitVec.ofNat 256 usedAmount.natAbs
  if nextSqrtP = 0 then
    let deltaL ← estimateIncrementalLiquidity r absDelta liquidity currentSqrtP feeInFeeUnits isExactInput
    let nextSqrtP ← toUint160 (← calcFinalPrice r absDelta liquidity deltaL currentSqrtP isExactInput)
    let returnedAmount ← calcReturnedAmount r liquidity currentSqrtP nextSqrtP deltaL isExactInput
    return ⟨usedAmount, returnedAmount, deltaL, nextSqrtP⟩
  else
    let deltaL ← calcIncrementalLiquidity r absDelta liquidity currentSqrtP nextSqrtP isExactInput
    let returnedAmount ← calcReturnedAmount r liquidity currentSqrtP nextSqrtP deltaL isExactInput
    return ⟨usedAmount, returnedAmount, deltaL, nextSqrtP⟩

/-- A swap step for token1 amounts: `step liquidity currentSqrtP targetSqrtP feeInFeeUnits
specifiedAmount isExactInput`. -/
abbrev StepFn := U256 → U256 → U256 → U256 → Int → Bool → Option Step

/-! ## The deployed range -/

/-- Two prices within the range of `TickMath` and less than a 5% price move apart: the range a
step of `Pool.swap` works in (`MAX_TICK_DISTANCE = 480` ticks, "strictly less than 5% price
movement"; the square-root prices satisfy `100 * hi^2 < 105 * lo^2`). -/
def InWindow (p q : U256) : Prop :=
  MIN_SQRT_RATIO ≤ p.toNat ∧ p.toNat < MAX_SQRT_RATIO ∧
  MIN_SQRT_RATIO ≤ q.toNat ∧ q.toNat < MAX_SQRT_RATIO ∧
  100 * (max p.toNat q.toNat) * (max p.toNat q.toNat) < 105 * (min p.toNat q.toNat) * (min p.toNat q.toNat)

/-- The inputs `Pool.swap` passes to a step: a positive liquidity, the sum of two `uint128`
values (`baseL + reinvestL`); a fee below `FEE_UNITS` (`Factory.enableSwapFee`); the two prices
in the window. -/
def InRange (liquidity currentSqrtP targetSqrtP feeInFeeUnits : U256) : Prop :=
  0 < liquidity.toNat ∧ liquidity.toNat < 2 ^ 129 ∧ feeInFeeUnits.toNat < 100000 ∧
  InWindow currentSqrtP targetSqrtP

/-- An exact-input step for token1 (token1 in, price up): `0 < specifiedAmount < 2^255`. -/
def ExactIn (liquidity currentSqrtP targetSqrtP feeInFeeUnits : U256) (specifiedAmount : Int) : Prop :=
  InRange liquidity currentSqrtP targetSqrtP feeInFeeUnits ∧ currentSqrtP.toNat < targetSqrtP.toNat ∧
  0 < specifiedAmount ∧ specifiedAmount < 2 ^ 255

/-- An exact-output step for token1 (token1 out, price down): `-2^255 ≤ specifiedAmount < 0`. -/
def ExactOut (liquidity currentSqrtP targetSqrtP feeInFeeUnits : U256) (specifiedAmount : Int) : Prop :=
  InRange liquidity currentSqrtP targetSqrtP feeInFeeUnits ∧ targetSqrtP.toNat < currentSqrtP.toNat ∧
  specifiedAmount < 0 ∧ -2 ^ 255 ≤ specifiedAmount

/-! ## One iteration of the loop of `Pool.swap` -/

/-- The target of a step (`Pool.sol` lines 388 to 392): the price of the next tick, unless the
price limit comes first.

```
uint160 targetSqrtP = swapData.nextSqrtP;
if (willUpTick == (swapData.nextSqrtP > limitSqrtP)) {
  targetSqrtP = limitSqrtP;
}
```

For token1, `willUpTick = isExactInput` (line 342). -/
def loopTarget (willUpTick : Bool) (tickSqrtP limitSqrtP : U256) : U256 :=
  if willUpTick = decide (tickSqrtP.toNat > limitSqrtP.toNat) then limitSqrtP else tickSqrtP

/-- One iteration of the loop of `Pool.swap` for a token1 swap: the step towards
`loopTarget`, and whether the loop goes on to cross the tick (lines 412 to 419):

```
// if price has not reached the next sqrt price
if (swapData.sqrtP != swapData.nextSqrtP) {
  if (swapData.sqrtP != swapData.startSqrtP) {
    // update the current tick data in case the sqrtP has changed
    swapData.currentTick = TickMath.getTickAtSqrtRatio(swapData.sqrtP);
  }
  break;
}
// otherwise the tick is crossed
```

The result is the step and `true` when the tick is crossed. -/
def loopStep (step : StepFn) (liquidity sqrtP tickSqrtP limitSqrtP feeInFeeUnits : U256)
    (specifiedAmount : Int) (isExactInput : Bool) : Option (Step × Bool) :=
  (step liquidity sqrtP (loopTarget isExactInput tickSqrtP limitSqrtP) feeInFeeUnits
      specifiedAmount isExactInput).map fun s => (s, decide (s.nextSqrtP = tickSqrtP))

/-! ## Requirements -/

/-- REQ-IN-WITHIN-TARGET: an exact-input step (token1 in) never moves the price past the target
and never moves it down: the next price lies between the current price and the target,
inclusive. This is the property Kyber's own fuzz test states (`SwapMathEchidnaTest.sol` lines 83
to 90) and the exploit of 2023-11-22 broke. -/
def InWithinTarget (step : StepFn) : Prop :=
  ∀ (L c t F : U256) (spec : Int) (s : Step), ExactIn L c t F spec → step L c t F spec true = some s →
    c.toNat ≤ s.nextSqrtP.toNat ∧ s.nextSqrtP.toNat ≤ t.toNat

/-- REQ-OUT-WITHIN-TARGET: an exact-output step (token1 out) never moves the price below the
target and never moves it up: the next price lies between the target and the current price,
inclusive. -/
def OutWithinTarget (step : StepFn) : Prop :=
  ∀ (L c t F : U256) (spec : Int) (s : Step), ExactOut L c t F spec → step L c t F spec false = some s →
    t.toNat ≤ s.nextSqrtP.toNat ∧ s.nextSqrtP.toNat ≤ c.toNat

/-- REQ-STEP-REACH: a step that does not use the whole specified amount ends on the target, uses
less than specified, and uses no more than the exact amount that moves the price to the target
(cross-multiplied): for token1 in, `L * 2 * (t - c) * c / (2^96 * (2 * c - fee * t))` with the fee
`F / 100000`; for token1 out, `L * (c - t) * (2 * t - fee * c - fee * t) / (2^96 * (2 * t - fee * c))`. -/
def StepReach (step : StepFn) : Prop :=
  (∀ (L c t F : U256) (spec : Int) (s : Step), ExactIn L c t F spec → step L c t F spec true = some s →
    s.usedAmount ≠ spec →
      s.nextSqrtP = t ∧ 0 ≤ s.usedAmount ∧ s.usedAmount < spec ∧
      s.usedAmount * 2 ^ 96 * (200000 * c.toNat - F.toNat * t.toNat) ≤
        (L.toNat : Int) * 200000 * (t.toNat - c.toNat) * c.toNat) ∧
  (∀ (L c t F : U256) (spec : Int) (s : Step), ExactOut L c t F spec → step L c t F spec false = some s →
    s.usedAmount ≠ spec →
      s.nextSqrtP = t ∧ s.usedAmount ≤ 0 ∧ spec < s.usedAmount ∧
      -s.usedAmount * 2 ^ 96 * (200000 * t.toNat - F.toNat * c.toNat) ≤
        (L.toNat : Int) * (200000 * t.toNat - F.toNat * c.toNat - F.toNat * t.toNat) * (c.toNat - t.toNat))

/-- REQ-STEP-PAID: the pool never moves further than it is paid for. With `L` the liquidity, the
virtual reserves are `L * 2^96 / sqrtP` of token0 and `L * sqrtP / 2^96` of token1, and after the
step the liquidity is `L + deltaL`. Token1 in: the token1 reserve after the step is at most the
reserve before plus the amount used, `(L + deltaL) * next ≤ L * c + used * 2^96`; this holds for
every step except one that ends on the target and reinvests nothing (a reach amount rounded down
by design, `calcReachAmount` line 117). Token1 out: the token0 reserve after the step is at most
the reserve before plus the token0 the trader pays (`returnedAmount`),
`(L + deltaL) * 2^96 * c ≤ next * (L * 2^96 + returned * c)`. -/
def StepPaid (step : StepFn) : Prop :=
  (∀ (L c t F : U256) (spec : Int) (s : Step), ExactIn L c t F spec → step L c t F spec true = some s →
    (s.nextSqrtP ≠ t ∨ 0 < s.deltaL.toNat) →
      ((L.toNat + s.deltaL.toNat) * s.nextSqrtP.toNat : Int) ≤ L.toNat * c.toNat + s.usedAmount * 2 ^ 96) ∧
  (∀ (L c t F : U256) (spec : Int) (s : Step), ExactOut L c t F spec → step L c t F spec false = some s →
    ((L.toNat + s.deltaL.toNat) * 2 ^ 96 * c.toNat : Int) ≤
      s.nextSqrtP.toNat * (L.toNat * 2 ^ 96 + s.returnedAmount * c.toNat))

/-- REQ-IN-FEE-LIQUIDITY: an exact-input step that stops before the target reinvests as fee
liquidity the exact value `fee * used * 2^96 / (2 * c)` (the fee `F / 100000` of the amount used,
as liquidity at the current price, halved) within one unit. -/
def InFeeLiquidity (step : StepFn) : Prop :=
  ∀ (L c t F : U256) (spec : Int) (s : Step), ExactIn L c t F spec → step L c t F spec true = some s →
    s.nextSqrtP ≠ t →
      (F.toNat : Int) * s.usedAmount * 2 ^ 96 < 200000 * c.toNat * (s.deltaL.toNat + 1) ∧
      (200000 * c.toNat * s.deltaL.toNat : Int) < F.toNat * s.usedAmount * 2 ^ 96 + 200000 * c.toNat

/-- REQ-OUT-FEE-LIQUIDITY: an exact-output step that stops before the target reinvests no more fee
liquidity than the exact fee liquidity, the smaller root `x` of the exact equation of
`estimateIncrementalLiquidity`, `F x^2 - 2 B x + C = 0` with `B = (100000 - F) * L - 100000 * a *
2^96 / c` and `C = F * L * a * 2^96 / c` (`a` the amount used, divisions exact): the polynomial is
not negative at `deltaL`, multiplied by `c`. With REQ-OUT-WITHIN-TARGET, which keeps `deltaL` far
below the larger root, `deltaL` is at most the smaller root. -/
def OutFeeLiquidity (step : StepFn) : Prop :=
  ∀ (L c t F : U256) (spec : Int) (s : Step), ExactOut L c t F spec → step L c t F spec false = some s →
    s.nextSqrtP ≠ t →
      2 * (s.deltaL.toNat : Int) *
          ((100000 - F.toNat) * L.toNat * c.toNat + 100000 * s.usedAmount * 2 ^ 96) ≤
        F.toNat * c.toNat * s.deltaL.toNat * s.deltaL.toNat - F.toNat * L.toNat * s.usedAmount * 2 ^ 96

/-- REQ-POOL-CROSSES: an iteration of the loop of `Pool.swap` stops without crossing the next
tick only when the price is strictly before the tick's price: the loop never stops with the price
on or beyond a tick it did not cross (the state the exploit of 2023-11-22 produced). The step
starts at `sqrtP`, the tick price `tickSqrtP` is within the window of a step, and the price limit
is on the side the swap moves to (`Pool.sol` lines 358 to 368). -/
def PoolCrosses (step : StepFn) : Prop :=
  (∀ (L p tick limit F : U256) (spec : Int) (s : Step) (crossed : Bool),
    InRange L p tick F → p.toNat < tick.toNat → p.toNat < limit.toNat → limit.toNat < MAX_SQRT_RATIO →
    0 < spec → spec < 2 ^ 255 →
    loopStep step L p tick limit F spec true = some (s, crossed) → crossed = false →
      s.nextSqrtP.toNat < tick.toNat) ∧
  (∀ (L p tick limit F : U256) (spec : Int) (s : Step) (crossed : Bool),
    InRange L p tick F → tick.toNat < p.toNat → limit.toNat < p.toNat → MIN_SQRT_RATIO < limit.toNat →
    spec < 0 → -2 ^ 255 ≤ spec →
    loopStep step L p tick limit F spec false = some (s, crossed) → crossed = false →
      tick.toNat < s.nextSqrtP.toNat)

/-- REQ-DEPLOYED-STEP: the step is the deployed computation with some choice of rounding
directions (each division rounded down or up, the root rounded down or up, the fee liquidity of
an exact-input step computed as deployed or from the rounded virtual input), on every input. A
step that caps the price at the target, or that reinvests no fee liquidity, is not of this form. -/
def DeployedStep (step : StepFn) : Prop :=
  ∃ r : Rounding, ∀ (L c t F : U256) (spec : Int) (isExactInput : Bool),
    step L c t F spec isExactInput = computeSwapStepWith r L c t F spec isExactInput

end KyberSwapStep
