import ProofForgeFinDemo.DeFi.Compound
import ProofForgeFinDemo.DeFi.Euler
import ProofForgeFinDemo.DeFi.Hundred
/-!
# DeFi demonstrations

Requirements of real-world tasks re-proved with `ProofForgeFin.DeFi`, over definitions copied
from the task files (the task files are not imported or modified). Each sequence requirement is
proved for every implementation that meets the task's per-call requirements, not only for the
reference implementation.

* `Compound`: REQ-REWARDS-BOUNDED, REQ-ACCOUNT-BOUNDED and REQ-NO-BACKDATED-REWARDS of
  `rw-compound-comp`, from the five per-call requirements.
* `Euler`: REQ-STAYS-HEALTHY and REQ-NO-BAD-DEBT of `rw-euler-donate`, from REQ-EFFECTS and
  REQ-ACTOR-HEALTHY.
* `Hundred`: REQ-SHARE-VALUE of `rw-hundred-vault`, from the effect and rounding requirements of
  the three calls.
-/
