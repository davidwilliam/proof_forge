import ProofForgeFin.Evm.Uint
import ProofForgeFin.Evm.Bits
import ProofForgeFin.Evm.MulDiv
import ProofForgeFin.Evm.FullMath
import ProofForgeFin.Evm.FixedQ
import ProofForgeFin.Evm.SqrtPrice
import ProofForgeFin.Evm.Signed
import ProofForgeFin.Evm.Pow
/-!
# EVM and machine arithmetic

Machine words as `BitVec w`, with every result characterized through `toNat` in natural numbers.

* `ProofForgeFin.Evm.Uint`: wrapping and checked (Solidity 0.8) arithmetic, checked casts, and
  the overflow tests of deployed code.
* `ProofForgeFin.Evm.Bits`: checked shifts, `BitMath.mostSignificantBit`, floor and ceiling
  base-2 logarithms, trailing zeros.
* `ProofForgeFin.Evm.MulDiv`: the specification of full-precision `mulDiv` and
  `mulDivRoundingUp`, `UnsafeMath.divRoundingUp`, `Math.ceilDiv` and Move's `div_round`.
* `ProofForgeFin.Evm.FullMath`: the 512-bit algorithm of `FullMath.mulDiv` and
  `FullMath.mulDivRoundingUp`, proved equal to the specification on every input.
* `ProofForgeFin.Evm.FixedQ`: binary fixed-point formats (Q64.64, Q64.96, Q128.128), conversions
  between them with both roundings, and the conversion of `TickMath.getSqrtRatioAtTick`.
* `ProofForgeFin.Evm.SqrtPrice`: Uniswap v3 `SqrtPriceMath.getAmount0Delta`, `getAmount1Delta`
  and `getNextSqrtPriceFromAmount0RoundingUp`, with exact rounding bounds.
* `ProofForgeFin.Evm.Signed`: truncated, floor and ceiling integer division and their bounds;
  checked `intN` arithmetic, `SafeCast` conversions, `SignedMath.abs`, `LiquidityMath.addDelta`.
* `ProofForgeFin.Evm.Pow`: fixed-point exponentiation by squaring (`rpow`) with each rounding,
  an invariant principle for it, and error bounds.
-/
