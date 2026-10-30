import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.DeFi.Distributor
import ProofForgeFin.DeFi.Chef
import ProofForgeFin.DeFi.Lending
import ProofForgeFin.DeFi.AMM
import ProofForgeFin.DeFi.Vault
/-!
# DeFi primitives

Proved building blocks for specifications and proofs about decentralized-finance protocols.

* `ProofForgeFin.DeFi.Rewards`: index-based reward accrual (Compound, MasterChef, Synthetix):
  pending rewards, credits rounded down, index increments, settlement, accounts without a recorded
  checkpoint, sums over accounts, and MasterChef's `rewardDebt` accounting.
* `ProofForgeFin.DeFi.Distributor`: a reward distributor with its bounds over every sequence of
  operations, in total and per account.
* `ProofForgeFin.DeFi.Chef`: MasterChef's `rewardDebt` accounting with its bound over every
  sequence, which adds one reward unit of rounding per deposit or withdrawal.
* `ProofForgeFin.DeFi.Lending`: health preservation, borrow limits and debt values with prices and
  collateral factors, liquidation bounds, interest indices, and pool solvency.
* `ProofForgeFin.DeFi.AMM`: constant-product quotes with a fee, the K check, price impact,
  liquidity tokens and a pool model; invariant pools with scaled balances and batches.
* `ProofForgeFin.DeFi.Vault`: ERC-4626 vaults with virtual shares and assets (OpenZeppelin's
  decimals offset): previews and their rounding directions, `maxWithdraw` and `maxRedeem`, the
  inflation-attack bounds, and share value over every sequence of operations.
-/
