import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.DeFi.Distributor
/-!
# DeFi primitives

Proved building blocks for specifications and proofs about decentralized-finance protocols.

* `ProofForgeFin.DeFi.Rewards`: index-based reward accrual (Compound, MasterChef, Synthetix):
  pending rewards, credits rounded down, index increments, settlement, accounts without a recorded
  checkpoint, sums over accounts, and MasterChef's `rewardDebt` accounting.
* `ProofForgeFin.DeFi.Distributor`: a reward distributor with its bounds over every sequence of
  operations, in total and per account.
-/
