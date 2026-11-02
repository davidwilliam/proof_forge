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
import ProofForgeFin.Sqrt
import ProofForgeFin.SqrtIter
import ProofForgeFin.NatSqrt
import ProofForgeFin.WordBridge
import ProofForgeFin.Accumulator
import ProofForgeFin.QuadRoot
import ProofForgeFin.RoundCompose
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
* `ProofForgeFin.Sqrt`: the integer square root `Nat.sqrt` and one Newton step `(x + a / x) / 2`:
  bounds of the root, the error relation of a step, quadratic and halving convergence, and the
  end of the iteration.
* `ProofForgeFin.SqrtIter`: Newton iteration over `k` steps, `newtonIter`: the error after `k`
  steps from above and from below the root, power-of-two estimates through `Nat.log2`, when an
  iterate reaches the root or the root plus one, and Newton steps on machine words.
* `ProofForgeFin.NatSqrt`: order facts about `Nat.sqrt` and bounds of `Nat.log2` in the `Nat`
  namespace, under the names Mathlib uses (`Nat.le_sqrt`, `Nat.sqrt_lt`, ...).
* `ProofForgeFin.WordBridge`: `BitVec w` to `Nat` and back at any width: exactness of `+`, `*`,
  `-`, `<<<` without overflow (as equivalences), `/`, `>>>` and comparisons, shifts by a word,
  sizes of sums and products below `2^w`, and iterations on words as iterations on values.
* `ProofForgeFin.Accumulator`: index-based reward accumulators over sequences of actions: index
  updates covered by the emission they index, potentials over the accounts across an update and a
  settlement, chains of primitive moves inside one action, the induction over a run given by its
  defining equations, from a scaled potential to an amount, sums of amounts rounded down, and
  the complete bounds for any market with two reward sides from one case analysis of its step.
* `ProofForgeFin.QuadRoot`: the integer smaller root of `a x² - 2 b x + c` computed with an
  integer square root: the side of the real root it lands on with the root rounded up or down,
  and its order against any rational point where the quadratic is not positive.
* `ProofForgeFin.RoundCompose`: two roundings in a row against the exact value, cross-multiplied:
  two floors, a floor below another floor, and a fraction rounded up of a value rounded down.
-/
