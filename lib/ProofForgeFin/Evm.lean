import ProofForgeFin.Evm.Uint
import ProofForgeFin.Evm.Bits
import ProofForgeFin.Evm.MulDiv
import ProofForgeFin.Evm.FullMath
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
-/
