import BalancerSwap.Spec
/-!
Port of the regular-swap path of Balancer V2's Composable Stable Pool, as deployed for the
osETH/WETH pool on Ethereum (0xDACf5Fa19b1f720111609043ac67A9818262850c, source verified on
Sourcify with an exact match, solc 0.7.1):

* `@balancer-labs/v2-pool-utils/contracts/BaseGeneralPool.sol`, `_swapGivenIn` (lines 49 to 66)
  and `_swapGivenOut` (lines 68 to 85);
* `@balancer-labs/v2-pool-utils/contracts/BasePool.sol`, `_addSwapFeeAmount` (618 to 621),
  `_subtractSwapFeeAmount` (626 to 630), `_upscale` (680 to 686), `_upscaleArray` (692 to 699),
  `_downscaleDown` (705 to 707), `_downscaleUp` (726 to 728);
* `@balancer-labs/v2-solidity-utils/contracts/math/FixedPoint.sol`, `mulDown`, `mulUp`,
  `divDown`, `divUp` (48 to 102) and `complement` (158 to 160).

The same logic is in balancer/balancer-v2-monorepo at commit
88842344fb5f44d8ed6f8f944acd3be80627df87 (`pkg/solidity-utils/contracts/helpers/ScalingHelpers.sol`
lines 35 to 56, `pkg/pool-utils/contracts/BaseGeneralPool.sol` lines 49 to 85).

`ComposableStablePool._swapGivenOut` forwards regular (non-BPT) swaps to
`BaseGeneralPool._swapGivenOut`, and `_onRegularSwap` calls the pool math with the balances
without the BPT. Here the math is the parameter `m`; `StableMath._calcInGivenOut` starts with
`balances[tokenIndexOut].sub(tokenAmountOut)`, which reverts when the amount out exceeds the
balance, and that check is kept. A revert is `none`. Arithmetic is unbounded, so the overflow
checks of `mulDown`, `mulUp`, `divDown` and `divUp` never fail.
-/
namespace BalancerSwap

/-! ## FixedPoint -/

/-- `FixedPoint.mulDown`. -/
def mulDown (a b : Nat) : Nat := a * b / ONE

/-- `FixedPoint.mulUp`. -/
def mulUp (a b : Nat) : Nat := if a * b = 0 then 0 else (a * b - 1) / ONE + 1

/-- `FixedPoint.divDown`: reverts on division by zero. -/
def divDown (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some (a * ONE / b)

/-- `FixedPoint.divUp`: reverts on division by zero. -/
def divUp (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some ((a * ONE - 1) / b + 1)

/-- `FixedPoint.complement`. -/
def complement (x : Nat) : Nat := if x < ONE then ONE - x else 0

/-! ## BasePool -/

/-- `_upscale`: `FixedPoint.mulDown(amount, scalingFactor)`. -/
def upscale (amount scalingFactor : Nat) : Nat := mulDown amount scalingFactor

/-- `_upscaleArray` over the pool's balances. -/
def upscaleArray (p : Pool) : Nat → Nat := fun k => mulDown (p.balance k) (p.rate k)

/-- `_downscaleDown`. -/
def downscaleDown (amount scalingFactor : Nat) : Option Nat := divDown amount scalingFactor

/-- `_downscaleUp`. -/
def downscaleUp (amount scalingFactor : Nat) : Option Nat := divUp amount scalingFactor

/-- `_subtractSwapFeeAmount`: `amount.sub(amount.mulUp(fee))`. -/
def subtractSwapFeeAmount (amount fee : Nat) : Option Nat :=
  if mulUp amount fee ≤ amount then some (amount - mulUp amount fee) else none

/-- `_addSwapFeeAmount`: `amount.divUp(fee.complement())`. -/
def addSwapFeeAmount (amount fee : Nat) : Option Nat := divUp amount (complement fee)

/-! ## BaseGeneralPool -/

/-- `_swapGivenIn`. -/
def swapGivenIn (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  match subtractSwapFeeAmount s.amount p.fee with
  | none => none
  | some amount =>
    let balances := upscaleArray p
    let amount := upscale amount (p.rate s.tokenIn)
    let amountOut := m.outGivenIn balances s.tokenIn s.tokenOut amount
    downscaleDown amountOut (p.rate s.tokenOut)

/-- `_swapGivenOut`. -/
def swapGivenOut (m : PoolMath) (p : Pool) (s : Swap) : Option Nat :=
  let balances := upscaleArray p
  let amount := upscale s.amount (p.rate s.tokenOut)
  if balances s.tokenOut < amount then none
  else
    match downscaleUp (m.inGivenOut balances s.tokenIn s.tokenOut amount) (p.rate s.tokenIn) with
    | none => none
    | some amountIn => addSwapFeeAmount amountIn p.fee

/-- `onSwap` for a regular swap. -/
def onSwap : Impl := fun m p s =>
  match s.kind with
  | .givenIn => swapGivenIn m p s
  | .givenOut => swapGivenOut m p s

theorem req_given_in_succeeds        : GivenInSucceeds onSwap := sorry
theorem req_given_out_succeeds       : GivenOutSucceeds onSwap := sorry
theorem req_given_in_pays_at_most    : GivenInPaysAtMost onSwap := sorry
theorem req_given_in_pays_at_least   : GivenInPaysAtLeast onSwap := sorry
theorem req_given_out_charges_at_least : GivenOutChargesAtLeast onSwap := sorry
theorem req_given_out_charges_at_most  : GivenOutChargesAtMost onSwap := sorry
theorem req_swap_keeps_value         : SwapKeepsValue onSwap := sorry
theorem req_batch_keeps_value        : BatchKeepsValue onSwap := sorry

end BalancerSwap
