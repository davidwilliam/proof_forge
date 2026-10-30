import ProofForgeFinDemo.Money.Allocation
import ProofForgeFinDemo.Money.EqualSplit
import ProofForgeFinDemo.Money.WeightedPayout
import ProofForgeFinDemo.Money.FeePayout
/-!
# ProofForgeFin.Money demonstrations

Requirements and lemmas of tasks re-proved with `ProofForgeFin.Money`, over definitions copied
from the task files (the task files are not imported or modified).

* `Allocation`: the eight requirements of `rw-moneyphp-allocate` (and `rw-spliit-balances`,
  whose specification is the same) for the library's largest-remainder allocation.
* `EqualSplit`: the six requirements of `rw-gomoney-split` for a port of go-money's fixed
  `Money.Split`.
* `WeightedPayout`: `leftover_lt`, `sum_weighted` and `weighted_bound` of
  `payouts-weighted-b1`.
* `FeePayout`: `fee_le` and `split_sum` of `payouts-fee-b1`.
-/
