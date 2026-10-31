import ProofForgeFin.Sums.Eqns
import ProofForgeFin.Sums.Index
import ProofForgeFin.Sums.Update
import ProofForgeFin.Sums.Floor
/-!
# Sums over lists and positions

The goals proofs about money code fail on most often, read from the open goals of runs that
were not accepted (`results/feedback-library-1`), are sums: a sum after one entry of a ledger
changes, a sum over the positions of a recipient list, the parts of a split rounded down, and a
sum the specification restated with its own recursion. The library had these facts for its own
definitions; this module states them for the forms specifications write.

* `ProofForgeFin.Sums.Eqns`: a sum restated by recursion or as a fold is `List.sum` of the mapped
  list (or `sumOver`), from its defining equations.
* `ProofForgeFin.Sums.Index`: sums over a list as sums over its positions; indicator, one-position,
  constant and counting sums over positions.
* `ProofForgeFin.Sums.Update`: the total after one position of a list or one account of a balance
  function changes.
* `ProofForgeFin.Sums.Floor`: sums of rounded-down parts and their remainders.
-/
