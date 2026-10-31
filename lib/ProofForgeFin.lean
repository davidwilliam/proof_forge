import ProofForgeFin.Rounding
import ProofForgeFin.FixedPoint
import ProofForgeFin.Word
import ProofForgeFin.Shares
import ProofForgeFin.Seq
import ProofForgeFin.Ledger
import ProofForgeFin.Trading
import ProofForgeFin.Machine
import ProofForgeFin.Evm
import ProofForgeFin.Money
import ProofForgeFin.DeFi
import ProofForgeFin.Tactic
import ProofForgeFin.Sums
import ProofForgeFin.Accrual
import ProofForgeFin.Harvested
import ProofForgeFin.Salvaged
/-!
# ProofForgeFin

Proved foundations for specifications and proofs about financial code, on `Nat` and `Int`, with
no dependency beyond the Lean core library.

* `ProofForgeFin.Rounding`: floor and ceiling division and their exact bounds.
* `ProofForgeFin.FixedPoint`: fixed-point products and quotients at any scale, scaled and
  decimal conversions, round trips.
* `ProofForgeFin.Word`: exactness conditions for `BitVec` arithmetic and shift overflow.
* `ProofForgeFin.Shares`: vault share conversions and share value.
* `ProofForgeFin.Seq`: runs of operations, traces, atomic runs, reachable states, invariants and
  accumulated bounds.
* `ProofForgeFin.Ledger`: sums over accounts and conservation under transfers, mints and burns.
* `ProofForgeFin.Sums`: sums restated by recursion, sums over positions, sums after one entry
  changes, and sums of rounded-down parts.
* `ProofForgeFin.Accrual`: a part rounded down plus at most one unit is within one unit; capped
  increments stay within their cap.
-/
