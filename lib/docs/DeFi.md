# ProofForgeFin.DeFi

`ProofForgeFin.DeFi` (area root `lib/ProofForgeFin/DeFi.lean`) is the part of ProofForgeFin for
decentralized-finance protocols: index-based reward accrual, lending, automated market makers and
ERC-4626 vaults. It builds on `Rounding`, `FixedPoint`, `Seq`, `Shares` and `Ledger`, depends on
the Lean core library only, and every theorem is proved with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.

Six modules declare 186 theorems and 96 definitions (structures and inductive types included).
Four demonstrations under `lib/ProofForgeFinDemo/DeFi/` (95 theorems) re-prove requirements of
`rw-compound-comp`, `rw-euler-donate`, `rw-hundred-vault` and `rw-balancer-upscale` over
definitions copied from the task specifications. Each demonstration proves its requirements for
every implementation that meets the task's per-call requirements, where the reference solution
proves them for its own implementation only.

Statements below are paraphrased; the Lean names are exact. All quantities are `Nat`; `a / b`
rounds down, and bounds are stated by cross-multiplication.

## `ProofForgeFin.DeFi.Rewards`: index-based reward accrual

The pattern of Compound's Comptroller (`compSupplyState.index`, `compSupplierIndex`), Synthetix's
`StakingRewards` (`rewardPerTokenStored`, `userRewardPerTokenPaid`) and SushiSwap's MasterChef
(`accSushiPerShare`, `rewardDebt`): a global index at scale `one` grows by the rewards emitted per
unit of stake, each account records the index at its last settlement, and a settlement credits the
units times the index gained, rounded down.

Definitions: `pending units start index = units * (index - start)`,
`credit one units start index = units * (index - start) / one`,
`indexDelta one emission total = emission * one / total`, `effStart init recorded` (the start of an
account whose recorded checkpoint is 0, that is none: the value `init` the index started from),
`firstStart init recorded index` (Compound after Proposal 64), `p62Start` (Proposal 62),
`debtOf` and `harvest` (MasterChef).

* `credit_mul_le`: `credit * one ≤ pending`; `pending_lt_credit_add_one_mul` (less than one unit
  lost).
* `settle_le`: for `p ≤ q` and `index ≤ p'`, `r' = r + credit one units q index` gives
  `r' * one + pending units p' index ≤ r * one + pending units p index`. A settlement that credits
  from any start `q` at or after the start `p` the potential counts from, and records the index,
  never raises the scaled credited amount plus the pending amount. `settle_le_self` is the form with
  the checkpoint at the index; `pending_units_change` lets the stake change at a settled account.
* `pending_le_add`, `pending_add_eq`, `pending_trans`, monotonicity in start, index and units.
* `total_mul_indexDelta_le`: `total * indexDelta one E total ≤ E * one` (the index never distributes
  more than was emitted); `lt_total_mul_indexDelta_add_one`; `units_mul_le_of_le_total`.
* `ite_accrue_le`: the per-account accrual inequality. With `units ≤ total`,
  `total * d + c * un' ≤ c * un` and `units' = units ∨ un' = 0`:
  `units * d + c * (if 0 < units' then un' else 0) ≤ c * (if 0 < units then un else 0)`. An account
  is owed the emission not yet in the index only while it holds a stake.
* `elapsed_add_mul`: `(now + k - last) * rate = (now - last) * rate + k * rate` for `last ≤ now`.
* Accounts without a recorded checkpoint: `pending_effStart_self` (recording the index settles the
  account, even an index of 0), `le_effStart_self`, `effStart_le_firstStart` (for an index that
  started from 0 or `init` and has not fallen below its start, the Proposal 64 start is at or after
  the potential's start: the condition the Proposal 62 code broke), `firstStart_le_index`,
  `p62Start_eq_firstStart` (they differ only for an index exactly at `init`), and `p62_overcredit`
  (an account with `units` and no checkpoint, at an index set to exactly `init = one`, is credited
  `units` by the Proposal 62 start and 0 by the safe one).
* Sums over accounts: `sum_le_of_index_le` (each term grows by at most `units * d`, total units
  times `d` covered by `E`: the total grows by at most `E`), `sum_le_of_index_le₂` (two indices at
  once, a supply and a borrow side), `sum_modify_index_le` (accrue the index and settle one account
  of a `List.modify`), `sum_pending_le_add`, `sum_mul_le_of_le`, `sum_map_add`,
  `forall_mem_modify`.
* MasterChef: `harvest_eq` (a harvest pays the debt difference), `harvest_term_eq` (a harvest
  followed by recording the new debt keeps the potential term `credited * one + units * index -
  debt * one` exactly), `harvest_lt` (a harvest pays less than the exact rewards plus one unit),
  `restake_term_lt` (a stake change raises the term by less than one reward unit).

## `ProofForgeFin.DeFi.Distributor`: a reward distributor and its bounds

A single-index distributor (`State`: index, emission not yet indexed, accounts with units,
checkpoint, accrued and paid) with operations `emit`, `update`, `stake`, `unstake` and `claim`
(`step one init`); every interaction updates the index and settles the account from its
effective start before its stake changes, as `StakingRewards.updateReward`, `updatePool` plus
harvest, and `distributeSupplierComp` do. Emission over zero units is discarded.

* `run_credited_le`: for `0 < one`, every state and every sequence,
  `(run s ops).credited ≤ s.credited + s.owed one init + emitted ops`, where `owed` is the pending
  rewards of all accounts rounded down once plus the unindexed emission.
* `run_creditedTo_le`: the same for each account with `owedTo` (its pending rewards rounded down,
  plus the unindexed emission while it holds a stake).
* `run_creditedTo_le_of_units_eq_zero`: an account without a stake gains at most the rewards
  emitted from then on (no backdated rewards).
* `owed_of_fresh`: when rewards have just started (index at `init`, every account settled or
  without a checkpoint) nothing but the unindexed emission is owed; accounts that held a stake
  before rewards started are owed nothing for the time before.
* The proof pieces are reusable for other potentials: `pot_step`, `potTo_step`, `pot_update`,
  `pot_modify`, `term_le_of_settled`, `run_le_of_pot` (the sequence bound for any potential that
  each operation raises by at most `one` times its emission).

## `ProofForgeFin.DeFi.Chef`: MasterChef's `rewardDebt` accounting

A one-pool model of SushiSwap's `MasterChef` (`State`: `accSushiPerShare`, rewards emitted and not
yet in the index, accounts with `amount`, `rewardDebt` and rewards paid; `step one`: emit,
`updatePool`, deposit, withdraw, harvest). Every interaction updates the pool, pays
`amount * index / one - rewardDebt` and records `rewardDebt = amount' * index / one`, both rounded
down, as the contract does.

* `run_paid_le`: from a state with the invariant `Inv` (no debt above `units * index / one`), for
  every sequence, `(run s ops).paid ≤ s.paid + s.owed one + allowed ops`, where `allowed` is the
  rewards emitted plus one unit per deposit or withdrawal. The extra unit per stake change is the
  rounding that MasterChef's `safeSushiTransfer` ("just in case if rounding error causes pool to
  not have enough SUSHIs") absorbs.
* `run_paidTo_le`: the same for each account.
* Per step: `term_harvest_le` (a harvest keeps the potential term exactly), `term_restake_le` (a
  stake change raises it by less than one unit), `pot_step`, `potTo_step`, `inv_step`.

## `ProofForgeFin.DeFi.Lending`: health, liquidation, interest, solvency

* Health preservation for any health predicate `H` monotone under an order `Safer`
  (`Monotone H Safer`): `keepsHealthy_of` (if each account ends healthy, ends at least as safe, or
  was unhealthy before, every healthy account stays healthy), `reachable_healthy` (then every
  account of every reachable state is healthy), `runAll_healthy`, `checked` and `checked_healthy`
  (an update guarded by a health check leaves the checked account healthy).
* One collateral asset and one debt asset (`Params`: scale `one`, prices, collateral factor;
  `Position`): `borrowLimit = collateral * collPrice / one * factor / one` and
  `debtValue = ceil(debt * debtPrice / one)`, in the protocol's favour as Morpho Blue's `_isHealthy`
  computes them; `Healthy`. `Healthy.exact`: a healthy position satisfies
  `debt * debtPrice * one ≤ collateral * collPrice * factor`. `healthy_mono`,
  `healthy_of_debt_eq_zero`, `healthy_of_params` (higher collateral price, lower debt price, higher
  factor keep health). `healthFactor` (borrow limit over debt value at scale `one`, Aave's
  `healthFactor`) and `one_le_healthFactor_iff` (a position with debt is healthy exactly when its
  health factor is at least 1).
* Liquidation: `seize incentive repay = repay * debtPrice * incentive / (collPrice * one)`
  (Compound's `liquidateCalculateSeizeTokens`). `seize_value_le`:
  `seize * collPrice * one ≤ repay * debtPrice * incentive` (seized value at most the repaid value
  times `1 + bonus`); `seize_value_gt` (within one collateral unit); `maxRepay` and `maxRepay_le`
  (close factor at most 1). `liquidate_shortfall_le`: with `incentive * factor ≤ one * one` and the
  seizure and repayment within the position, the exact shortfall does not grow, stated as
  `D' + C ≤ D + C'`.
* Interest indices: `accrueIndex one index rate dt = index + index * (rate * dt) / one` (Compound's
  `accrueInterest`), `le_accrueIndex`, `accrueIndex_mono`, `accrueIndex_mul_le`. Debts read through
  index ratios: `debtDown` (Compound's `borrowBalanceStored`, rounded down) and `debtUp` (rounded up,
  in the protocol's favour); exactness, `debtDown_le_debtUp`, `debtDown_self`, `debtUp_self`,
  monotonicity in the index; `debtUp_resnap` (re-recording a debt rounded up at an intermediate
  index never lowers the debt read later) and `debtDown_resnap` (rounded down, it never raises it);
  `sum_debtDown_le` (debts against one snapshot, rounded down, add up to at most the total read
  from the summed principals).
* A pool (`Pool`: cash, borrows, reserves, supplied; `PoolOp`: supply, withdraw, borrow, repay,
  accrue with a reserve factor, bad-debt write-off; `poolStep`): `poolStep_balanced` and
  `run_balanced` (`cash + borrows = supplied + reserves` over every sequence, for a reserve factor
  at most 1), `Pool.borrows_le` and `run_borrows_le` (total borrows at most supplied plus
  reserves), `Pool.cash_eq`.

## `ProofForgeFin.DeFi.AMM`: constant product and invariant pools

Constant product with fee `fee / D`, `g = D - fee`, as in `UniswapV2Library`:
`amountOut D g x y dx = dx * g * y / (x * D + dx * g)` (`getAmountOut`) and
`amountIn D g x y dy = x * dy * D / ((y - dy) * g) + 1` (`getAmountIn`).

* `k_check_amountOut`: `x * y * D ≤ (x * D + dx * g) * (y - amountOut)`, the pair's K check with
  the fee (`balance0Adjusted * balance1Adjusted >= reserve0 * reserve1 * 1000**2`, divided by `D`).
  `k_check_amountIn`: the same for `getAmountIn`, for `dy < y`.
* `k_le_swapOut`, `k_le_swapIn`: for `0 < g ≤ D` the product of the reserves never decreases on a
  swap.
* `amountOut_lt` (below the reserve), `amountOut_mul_le_spot` (`out * x ≤ dx * y`, never better
  than spot), `amountOut_mono`, and `amountOut_avg_le` (price impact: for `0 < dx'` and
  `dx ≤ dx'`, `out(dx') * dx < (out(dx) + 1) * dx'`).
* Liquidity tokens (`CPool`: `x`, `y`, `L`): `KPerLNotBelow p q` (`p.x * p.y * q.L^2 ≤
  q.x * q.y * p.L^2`), `kPerL_trans` (through positive `L`), `mint_kPerL` (minting at most
  `min(dx * L / x, dy * L / y)`), `burn_kPerL` (burning pro rata, rounded down).
* The pool model `step D g` (swaps both ways, adds, removes; a removal of every token refused, as
  the minimum liquidity is locked): `run_k_le` (the product of the reserves never decreases over
  any sequence of swaps and adds), `run_kPerL` and `run_kPerL_of_pos` (the product per liquidity
  token squared never decreases over any sequence of swaps, adds and removes from a pool with
  liquidity).
* Invariant pools (Balancer's `WellBehaved` contract, Curve's `D`): `update2`,
  `InvariantMonotone`, `invariant_le_of_dominates` (a swap keeps the invariant when the priced trade
  keeps it and the settled balances dominate the priced ones), `scaleDown_add_ge`,
  `scaleDown_sub_ge`, `scaled_dominates` (for balances in scaled units rounded down, the domination
  follows from `gain * one ≤ ain * rate i` and `aout * rate j ≤ loss * one`: the math credited at
  most the amount in rounded down and debited at least the amount out), and `runAll_invariant_le`
  (a batch keeps the invariant when each swap does).
* The pool-math interface: `PoolMath` (invariant, `outGivenIn`, `inGivenOut`), `OutGivenInSound`,
  `InGivenOutSound`, `WellBehaved` (the contract of Balancer's swap specification, stated the same
  way, so a specification can use it directly); `WellBehaved.scaled_swapIn` and
  `WellBehaved.scaled_swapOut` (a swap settled in raw units keeps the invariant of the scaled
  balances, from the credit rounded down and the debit rounded up); `constantProduct` and
  `constantProduct_wellBehaved` (the two-token constant product meets the contract).

## `ProofForgeFin.DeFi.Vault`: ERC-4626 with virtual shares and assets

A vault's books are a `Shares.Pool`; an `Offset` adds virtual assets and shares (OpenZeppelin's
`ozOffset d = ⟨1, 10^d⟩`, `noOffset` for the plain ratio). Every conversion is the `Shares`
conversion of `virt o p`, so the `Shares` lemmas apply.

* `previewDeposit`, `previewMint`, `previewRedeem`, `previewWithdraw`, `convertToShares`,
  `convertToAssets`, `maxWithdraw`, `maxRedeem`; `previewDeposit_oz` and `previewRedeem_oz` are
  OpenZeppelin's `_convertToShares` and `_convertToAssets` with `Floor`.
* Rounding per EIP-4626: `previewDeposit_spec`, `previewMint_spec`, `previewRedeem_spec`,
  `previewWithdraw_spec`, `previewDeposit_le_previewWithdraw`, `previewRedeem_le_previewMint`.
* `previewMint_previewDeposit_le` (minting the shares a deposit gives costs at most the deposit),
  `previewWithdraw_maxWithdraw_le` (withdrawing `maxWithdraw` burns at most the balance),
  `maxWithdraw_le_assets` (with virtual assets at most 1 and positive virtual shares, a holder of
  at most the supply never withdraws the virtual assets), `previewRedeem_le_assets_oz`.
* The inflation attack: `previewDeposit_pos_iff` (a deposit of `x` mints a share exactly when
  `assets + va ≤ x * (supply + vs)`); `no_zero_shares`: with offset `10^d`, a donation `D` with
  `assets + D < x * 10^d` cannot make a later deposit of `x` mint nothing; `donation_needed` (the
  contrapositive: zero shares imply `x * 10^d ≤ assets + D`); `no_zero_shares_of_le` (the same for
  every offset `e ≥ d`); `donate_redeem_le` (holders of `S` shares capture at most `S / (S + vs)` of
  a donation, so the donor loses at least the rest).
* The vault model `step o` (deposit, mint, redeem, withdraw, donate, priced from the virtual
  pool): `step_value`, `run_value` and `run_value_oz`. With positive virtual assets and shares the
  value of a share never falls over any sequence of operations, with no condition on the shares
  outstanding (`Shares.run_value` needs shares outstanding along the trace).

## Demonstrations

Each file copies the namespace body of the task's `Spec.lean` without change and proves the
requirements below with the library. Sizes are code lines (non-blank lines outside comments),
counted by the same script for both sides.

| File | Proved | Reference proof | Library-based proof |
|---|---|---|---|
| `Compound.lean` (`rw-compound-comp`) | `bounds_of_calls`: REQ-REWARDS-BOUNDED, REQ-ACCOUNT-BOUNDED and REQ-NO-BACKDATED-REWARDS for every implementation meeting REQ-CALLS-SUCCEED, REQ-SUPPLY-HOOK, REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS | 984 (list lemmas 126, potentials and bounds 858), its own implementation only | 626 |
| `Euler.lean` (`rw-euler-donate`) | `stays_healthy`, `no_bad_debt` for every implementation meeting REQ-EFFECTS and REQ-ACTOR-HEALTHY | 57 (`healthy_mono`, `healthy_zero`, `req_stays_healthy`, `req_no_bad_debt`) | 68 |
| `Hundred.lean` (`rw-hundred-vault`) | `share_value`: REQ-SHARE-VALUE for every implementation meeting the effect and rounding requirements of deposit, redeem and withdraw | 57 (`value_trans`, `exec_value`, `run_value`, `req_share_value`) | 56 |
| `Balancer.lean` (`rw-balancer-upscale`) | `batch_keeps_value` (REQ-BATCH-KEEPS-VALUE from REQ-SWAP-KEEPS-VALUE), `given_in_keeps_value`, `given_out_keeps_value` (a swap keeps value under REQ-GIVEN-IN-PAYS-AT-MOST, REQ-GIVEN-OUT-CHARGES-AT-LEAST) | 122 (scaling helpers, `settle_balance`, `step_some`, `dominates`, the two requirements) | 95 |
| `Balancer.lean`, Sanity | `constantProduct_wellBehaved` of `spec/BalancerSwap/Sanity.lean` | 56 (`cp_out_le` to `constantProduct_wellBehaved`) | 13 (bridge to `AMM.constantProduct_wellBehaved`) |

Notes on the comparison:

* The reference sizes prove each requirement for the reference implementation, from facts about
  that implementation; the library-based proofs assume only the task's per-call requirements, so
  they apply to any implementation that proves those. For Compound this is the step the Muse runs
  did not reach: the A2 runs proved the five per-call requirements and none of the three bounds.
* Compound's demonstration also proves REQ-CALLS-SUCCEED's precondition (`Consistent`) along every
  run, which the reference does not need for its own implementation: a speed change that an
  implementation refused would keep the old speed while `emitted` counts the new one, so the bounds
  need REQ-CALLS-SUCCEED. The per-operation lemmas are short with the library: settling one side of
  an account (`term_settleS`) is a two-line proof on `Rewards.settle_le_self` and
  `Rewards.effStart_le_firstStart`; accruing and settling (`phi_moves.supply`) is seven lines, on
  `Rewards.sum_le_of_index_le₂` and `Ledger.sum_map_modify_le`.
* For Euler, Hundred and Balancer the library-based proofs are about the size of the reference
  proofs and more general; their per-call reasoning is case analysis on the specification's
  effects, which the library does not shorten. Where the task needs a fact the library states
  generally, the proof is a bridge: the constant product's contract is 13 lines against 56.

Axioms of the main results (`#print axioms`, pinned image):

```
'ProofForgeFin.DeFi.Rewards.settle_le' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Rewards.effStart_le_firstStart' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Rewards.p62_overcredit' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Rewards.sum_modify_index_le' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Rewards.harvest_lt' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Distributor.run_credited_le' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Distributor.run_creditedTo_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.Distributor.run_creditedTo_le_of_units_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.Chef.run_paid_le' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Chef.run_paidTo_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.Lending.reachable_healthy' does not depend on any axioms
'ProofForgeFin.DeFi.Lending.Params.one_le_healthFactor_iff' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Lending.Params.Healthy.exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.Lending.Params.seize_value_le' depends on axioms: [propext]
'ProofForgeFin.DeFi.Lending.Params.liquidate_shortfall_le' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Lending.debtUp_resnap' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.Lending.run_borrows_le' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.AMM.k_check_amountOut' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.AMM.k_le_swapIn' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.AMM.amountOut_avg_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.AMM.run_kPerL_of_pos' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.AMM.scaled_dominates' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.AMM.WellBehaved.scaled_swapOut' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.AMM.constantProduct_wellBehaved' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.Vault.maxWithdraw_le_assets' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.DeFi.Vault.no_zero_shares_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.DeFi.Vault.run_value_oz' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFinDemo.DeFi.Compound.bounds_of_calls' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFinDemo.DeFi.Euler.no_bad_debt' depends on axioms: [propext, Quot.sound]
'ProofForgeFinDemo.DeFi.Hundred.share_value' depends on axioms: [propext, Quot.sound]
'ProofForgeFinDemo.DeFi.Balancer.batch_keeps_value' depends on axioms: [propext]
'ProofForgeFinDemo.DeFi.Balancer.given_out_keeps_value' depends on axioms: [propext, Classical.choice, Quot.sound]
```

With the DeFi modules and demonstrations the audit of the whole library reports
`audit: 3632 constants, 1038 theorems, 0 violations` and `axioms used: [Classical.choice,
Quot.sound, propext]`, and `tests/test_fin_lib.py` passes.

## Limits

* Arithmetic is unbounded `Nat`: no overflow of 256-bit words, of the 224-bit Compound index, or of
  Uniswap's 112-bit reserves is modelled; `ProofForgeFin.Word` states when a word operation is
  exact.
* Rewards: the distributor and MasterChef models have one index and one pool; the two-sided
  Compound case is the demonstration, built from the kit. The MasterChef per-account bound counts
  the stake changes of all accounts, not only the account's own. Reward rates that change
  over time are the emission amounts of `emit`; reward periods, reward tokens that the contract
  does not hold, and transfers of the reward token are not modelled.
* Lending: one collateral and one debt asset with fixed prices; no oracle, price movement over time,
  multi-asset accounts, isolation modes, interest-rate models, or reserve-factor changes. Health
  preservation holds at fixed prices only (`healthy_of_params` states the direction prices may move
  without breaking health). The shortfall bound is exact arithmetic, not the rounded protocol
  computation.
* AMMs: constant product only (no concentrated liquidity, no Curve or Balancer invariant
  formulas); the first mint (`sqrt(x * y) - MINIMUM_LIQUIDITY`) is not modelled, a pool starts with
  liquidity; protocol fees (`kLast`), flash swaps and TWAP oracles are not modelled. The
  invariant-pool part takes the pool math's contract as a hypothesis, as Balancer's specification
  does.
* Vaults: fees, deposit and withdrawal limits other than the books, and asynchronous (ERC-7540)
  flows are not modelled; `maxDeposit` and `maxMint` are unbounded as in OpenZeppelin and have no
  definition here.
* Candidates may import the library; the task projects are unchanged (see `lib/README.md`,
  Integration).
