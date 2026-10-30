import ProofForgeFin.Rounding
import ProofForgeFin.FixedPoint
import ProofForgeFin.Word
/-!
# ProofForgeFin

Proved foundations for specifications and proofs about financial code, on `Nat` and `Int`, with
no dependency beyond the Lean core library.

* `ProofForgeFin.Rounding`: floor and ceiling division and their exact bounds.
* `ProofForgeFin.FixedPoint`: fixed-point products and quotients at any scale, scaled and
  decimal conversions, round trips.
* `ProofForgeFin.Word`: exactness conditions for `BitVec` arithmetic and shift overflow.
-/
