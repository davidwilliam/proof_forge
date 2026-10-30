import ProofForgeFinDemo.ShareVault
import ProofForgeFinDemo.BatchTransfer
import ProofForgeFinDemo.Compound
import ProofForgeFinDemo.Euler
import ProofForgeFinDemo.Trading
import ProofForgeFinDemo.Machine
import ProofForgeFinDemo.Evm
import ProofForgeFinDemo.Money
import ProofForgeFinDemo.DeFi
import ProofForgeFinDemo.Tactic
/-!
# ProofForgeFin demonstrations

Lemmas of task reference solutions re-proved with the library, over definitions copied from the
task files (the task files are not imported or modified).

* `ShareVault`: REQ-SHARE-VALUE of `rw-hundred-vault` for the reference implementation.
* `BatchTransfer`: `sum_shift` and `sum_applyLegs` of `transfers-batch-b3`.
* `Compound`: `run_inv`, `run_pot` and the final bound of `rw-compound-comp`, for every
  implementation, invariant and potential.
* `Euler`: REQ-NO-BAD-DEBT of `rw-euler-donate` from REQ-STAYS-HEALTHY, for every implementation.
-/
