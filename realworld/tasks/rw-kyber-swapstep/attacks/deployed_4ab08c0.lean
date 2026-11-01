import KyberSwapStep.Spec
import KyberSwapStep.Lemmas
/-!
Attack: the code at commit 4ab08c0 (the start candidate), with proofs `sorry`. Exact input: the fee
liquidity is rounded down although the comment says up; with an amount one unit below the reach
amount the next price passes the target (the exploit of 2023-11-22). Exact output: the smaller root
of `estimateIncrementalLiquidity` with the square root rounded down is above the real root and the
price passes the target.
-/
namespace KyberSwapStep

/-- `SwapMath.calcReachAmount(liquidity, currentSqrtP, targetSqrtP, feeInFeeUnits, isExactInput, false)`
(`SwapMath.sol` lines 102 to 164): the amount that moves the price to the target. -/
def reachAmount (liquidity currentSqrtP targetSqrtP feeInFeeUnits : U256) (isExactInput : Bool) :
    Option Int := do
  let absPriceDiff : U256 :=
    if currentSqrtP.toNat ≥ targetSqrtP.toNat then currentSqrtP - targetSqrtP
    else targetSqrtP - currentSqrtP
  if isExactInput then
    let denominator ← sub (← mul TWO_FEE_UNITS currentSqrtP) (← mul feeInFeeUnits targetSqrtP)
    let numerator ← mulDivFloor liquidity (← mul TWO_FEE_UNITS absPriceDiff) denominator
    toInt256 (← mulDivFloor numerator currentSqrtP TWO_POW_96)
  else
    let denominator ← sub (← mul TWO_FEE_UNITS targetSqrtP) (← mul feeInFeeUnits currentSqrtP)
    let numerator ← sub denominator (← mul feeInFeeUnits targetSqrtP)
    let numerator ← mulDivFloor liquidity numerator denominator
    revToInt256 (← mulDivFloor numerator absPriceDiff TWO_POW_96)

/-- `QuadMath.getSmallerRootOfQuadEqn(a, b, c)` (`QuadMath.sol` lines 8 to 14):
`smallerRoot = (b - sqrt(b * b - a * c)) / a;`. -/
def smallerRoot (a b c : U256) : Option U256 := do
  let d ← sub (← mul b b) (← mul a c)
  let s := sqrt d
  divFloor (← sub b s) a

/-- `SwapMath.estimateIncrementalLiquidity(absDelta, liquidity, currentSqrtP, feeInFeeUnits, isExactInput, false)`
(`SwapMath.sol` lines 169 to 216): the fee liquidity of a step that stops before the target.

```
if (isExactInput) {
  // deltaL = feeInFeeUnits * absDelta * / (currentSqrtP * 2)
  // Because nextSqrtP = (liquidity + absDelta / currentSqrtP) * currentSqrtP / (liquidity + deltaL)
  // so we round up deltaL, to round down nextSqrtP
  deltaL = FullMath.mulDivFloor(C.TWO_POW_96, absDelta * feeInFeeUnits, C.TWO_FEE_UNITS * currentSqrtP);
} else {
  uint256 a = feeInFeeUnits;
  uint256 b = (C.FEE_UNITS - feeInFeeUnits) * liquidity;
  uint256 c = feeInFeeUnits * liquidity * absDelta;
  b -= FullMath.mulDivFloor(C.FEE_UNITS * absDelta, C.TWO_POW_96, currentSqrtP);
  c = FullMath.mulDivFloor(c, C.TWO_POW_96, currentSqrtP);
  deltaL = QuadMath.getSmallerRootOfQuadEqn(a, b, c);
}
``` -/
def estimateDeltaL (absDelta liquidity currentSqrtP feeInFeeUnits : U256) (isExactInput : Bool) :
    Option U256 := do
  if isExactInput then
    mulDivFloor TWO_POW_96 (← mul absDelta feeInFeeUnits) (← mul TWO_FEE_UNITS currentSqrtP)
  else
    let b ← mul (← sub FEE_UNITS feeInFeeUnits) liquidity
    let c ← mul (← mul feeInFeeUnits liquidity) absDelta
    let b ← sub b (← mulDivFloor (← mul FEE_UNITS absDelta) TWO_POW_96 currentSqrtP)
    let c ← mulDivFloor c TWO_POW_96 currentSqrtP
    smallerRoot feeInFeeUnits b c

/-- `SwapMath.calcFinalPrice(absDelta, liquidity, deltaL, currentSqrtP, isExactInput, false)`
(`SwapMath.sol` lines 253 to 280): the price of a step that stops before the target. -/
def finalPrice (absDelta liquidity deltaL currentSqrtP : U256) (isExactInput : Bool) : Option U256 := do
  let tmp ← mulDivFloor absDelta TWO_POW_96 currentSqrtP
  if isExactInput then
    mulDivFloor (← add liquidity tmp) currentSqrtP (← add liquidity deltaL)
  else
    mulDivCeiling (← sub liquidity tmp) currentSqrtP (← add liquidity deltaL)

/-- `SwapMath.calcIncrementalLiquidity(absDelta, liquidity, currentSqrtP, nextSqrtP, isExactInput, false)`
(`SwapMath.sol` lines 220 to 249): the fee liquidity of a step that ends on the target. -/
def incrementalDeltaL (absDelta liquidity currentSqrtP nextSqrtP : U256) (isExactInput : Bool) :
    Option U256 := do
  let tmp1 ← mulDivFloor liquidity currentSqrtP TWO_POW_96
  let tmp2 ← if isExactInput then add tmp1 absDelta else sub tmp1 absDelta
  let tmp3 ← mulDivFloor tmp2 TWO_POW_96 nextSqrtP
  pure (if tmp3.toNat > liquidity.toNat then tmp3 - liquidity else 0)

/-- `SwapMath.calcReturnedAmount(liquidity, currentSqrtP, nextSqrtP, deltaL, isExactInput, false)`
(`SwapMath.sol` lines 285 to 320): the token0 amount. -/
def returnedAmount (liquidity currentSqrtP nextSqrtP deltaL : U256) (isExactInput : Bool) : Option Int := do
  let x ← toInt256 (← mulDivCeiling (← add liquidity deltaL) TWO_POW_96 nextSqrtP)
  let y ← revToInt256 (← mulDivFloor liquidity TWO_POW_96 currentSqrtP)
  pure (if isExactInput && x + y == 1 then 0 else x + y)

/-- `SwapMath.computeSwapStep(liquidity, currentSqrtP, targetSqrtP, feeInFeeUnits, specifiedAmount,
isExactInput, false)` (`SwapMath.sol` lines 28 to 98). -/
def computeSwapStep : StepFn := fun liquidity currentSqrtP targetSqrtP feeInFeeUnits specifiedAmount isExactInput => do
  if currentSqrtP = targetSqrtP then return ⟨0, 0, 0, currentSqrtP⟩
  let reach ← reachAmount liquidity currentSqrtP targetSqrtP feeInFeeUnits isExactInput
  let notReached : Bool := (isExactInput && decide (reach > specifiedAmount)) ||
    (!isExactInput && decide (reach ≤ specifiedAmount))
  let usedAmount := if notReached then specifiedAmount else reach
  let nextSqrtP : U256 := if notReached then 0 else targetSqrtP
  let absDelta : U256 := BitVec.ofNat 256 usedAmount.natAbs
  if nextSqrtP = 0 then
    let deltaL ← estimateDeltaL absDelta liquidity currentSqrtP feeInFeeUnits isExactInput
    let nextSqrtP ← toUint160 (← finalPrice absDelta liquidity deltaL currentSqrtP isExactInput)
    let returnedAmount ← returnedAmount liquidity currentSqrtP nextSqrtP deltaL isExactInput
    return ⟨usedAmount, returnedAmount, deltaL, nextSqrtP⟩
  else
    let deltaL ← incrementalDeltaL absDelta liquidity currentSqrtP nextSqrtP isExactInput
    let returnedAmount ← returnedAmount liquidity currentSqrtP nextSqrtP deltaL isExactInput
    return ⟨usedAmount, returnedAmount, deltaL, nextSqrtP⟩

theorem req_in_within_target  : InWithinTarget computeSwapStep := sorry
theorem req_out_within_target : OutWithinTarget computeSwapStep := sorry
theorem req_step_reach        : StepReach computeSwapStep := sorry
theorem req_step_paid         : StepPaid computeSwapStep := sorry
theorem req_in_fee_liquidity  : InFeeLiquidity computeSwapStep := sorry
theorem req_out_fee_liquidity : OutFeeLiquidity computeSwapStep := sorry
theorem req_pool_crosses      : PoolCrosses computeSwapStep := sorry
theorem req_deployed_step     : DeployedStep computeSwapStep := sorry

end KyberSwapStep
