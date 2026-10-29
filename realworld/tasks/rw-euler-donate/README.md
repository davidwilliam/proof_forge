# rw-euler-donate: a donation that skipped the liquidity check

On 13 March 2023 an attacker took about $197M in net profit from Euler Finance v1 (Cyfrin); Zellic puts the loss at "over 190 million USD", and CoinDesk reported on 3 April 2023 that Euler had returned all "recoverable funds". The root cause is `EToken.donateToReserves`: it moves eTokens from an account to the reserves without the liquidity check that `withdraw`, `mint` and `transferFrom` perform, so an account could make its own position insolvent and have a second account liquidate it at the maximum discount.

## What is proved

The task is a locked Lean 4 (v4.35.0, core only) specification of a single-asset Euler v1 market with one definition hole, `EulerLending.step : St → Op → Option St`, and six required theorems. The reference solution (`reference/SolutionA.lean`) proves all six; it is accepted by Comparator's six kernels and leanchecker, and its axioms are `propext` and `Quot.sound` only.

| Requirement | Theorem | Statement |
|---|---|---|
| REQ-HONEST-FLOW | `req_honest_flow` | A concrete honest session runs to completion: a lender deposits 1000; a borrower deposits 100, borrows 95 (exactly the 95% limit) and repays; a third account deposits 10, mints 190 (leverage to exactly the limit), burns and withdraws. Every position ends settled. |
| REQ-ALLOWED-SUCCEEDS | `req_allowed_succeeds` | From any state, every operation whose balances suffice and whose checked accounts end healthy succeeds (deposit, withdraw, borrow, repay, mint, burn, transfer, donate, and liquidation of an unhealthy account). |
| REQ-EFFECTS | `req_effects` | From any state, a successful operation produces exactly the specified next state: every account, the pool's cash and the reserves. |
| REQ-ACTOR-HEALTHY | `req_actor_healthy` | From any state, after a successful withdraw, borrow, mint, burn, transfer or donation the acting account is healthy, and after a liquidation the liquidator is healthy. |
| REQ-STAYS-HEALTHY | `req_stays_healthy` | From any state, no successful operation makes a healthy account unhealthy. |
| REQ-NO-BAD-DEBT | `req_no_bad_debt` | In every state reachable from the empty market by any sequence of operations, every account is healthy: no account holds more debt than its risk-adjusted collateral. |

`Healthy ⟨e, d⟩` is `d * 20 / 19 ≤ e` (floor division): Euler's own test for a self-collateralized position. REQ-ALLOWED-SUCCEEDS and REQ-HONEST-FLOW rule out a repair that refuses operations to stay solvent.

## The vulnerable port and its refutation

`candidate/Solution.lean` (also `attacks/buggy_original.lean`) is the port of the Euler v1 logic at commit `b1ee3265853628d5a529081d7908c38404201b4e`. It differs from the reference in one guard: `donate` checks only `x ≤ e`, as `donateToReserves` does (EToken.sol lines 359 to 386: `require(origBalance >= amount, "e/insufficient-balance")`, then the balance moves to the reserves, with no `checkLiquidity(account)`).

`witnesses/buggy_original.lean` refutes it in the Lean kernel (`decide`) with the attack's shape, in whole DAI with the exchange rate at 1:

| Step | Operation | Violator (collateral, debt) |
|---|---|---|
| 1 | lender (account 0) deposits 8,904,507 | |
| 2 | violator (account 1) deposits 20,000,000 | 20,000,000, 0 |
| 3 | mints 200,000,000 | 220,000,000, 200,000,000 |
| 4 | repays 10,000,000 | 220,000,000, 190,000,000 |
| 5 | mints 200,000,000 | 420,000,000, 390,000,000 (healthy) |
| 6 | donates 100,000,000 eTokens | 320,000,000, 390,000,000 (unhealthy) |
| 7 | liquidator (account 2) takes over the largest repay, 256,000,000, at the 20% maximum discount (health score 0.7794) | 0, 134,000,000 |
| 8 | liquidator withdraws the whole pool, 38,904,507 | |

The kernel checks every value above, that `NoBadDebt step` and `StaysHealthy step` and `ActorHealthy step` are false for the port, and the final state: the liquidator holds 281,095,493 of collateral against 261,120,000 of debt (256,000,000 plus the 2% reserves fee), the reserves hold 105,120,000, the pool is empty, and 134,000,000 of debt has no collateral behind it. The attacker put in 30,000,000 and took out 38,904,507: the lender's whole deposit.

The binary check refutes the port on generated sequences with violations of exactly REQ-ACTOR-HEALTHY, REQ-STAYS-HEALTHY and REQ-NO-BAD-DEBT (`validation.json`); the other three requirements hold for it.

Euler's own unit tests for the function, `test/reservesDonate.js` at the same commit, are ported in `unit-tests/ReservesDonate.lean`: "basic", "max uint" and "insufficient balance" pass on the port in the Lean kernel, as they do on the reference. The fourth test ("non-18 decimal places token") is about decimal scaling, which the model does not have. All four donate from an account without debt, where the missing check cannot matter.

Two further seeded wrong candidates are rejected: `attacks/solvent_not_risk_adjusted.lean` refuses a donation only when debt would exceed collateral (not 95% of it), and `attacks/donate_disabled.lean` refuses every donation (REQ-ALLOWED-SUCCEEDS).

## Muse repair

`agents/repair.py` with Muse Spark 1.3 on the Contributor tier and no planner (arm A1), from the vulnerable port, under a cap of $10 at standard list prices and 7,200 s, repaired the task in its first attempt (`results/euler-1/rw-euler-donate/repair-A1-1`). The repair adds `Healthy a` to the donation guard, the same check as the reference, and proves all six requirements. It used 40 model calls, $0.83 at list prices and $0.05 charged, in 1,682 s. `bin/proofforge check` issued a VERIFIED Passport (sha256 `6de7bb94c38cf23a31ba08174d7505b4b8d54dddc9ffbd6d177dde4981b82002`: Comparator's six kernels, leanchecker, axioms `propext` and `Quot.sound` only, 2,001 property cases), and `bin/proofforge verify` reproduced every hash and status. Arm A2 (Wonder planner) was not run, since A1 succeeded. The real-code comparison below uses this repair as the proved component.

## How the model maps to Euler's contracts

| Model | Euler v1 at b1ee326 |
|---|---|
| `Acct.e`, `Acct.d` | eToken balance and dToken balance of an account, in underlying units |
| `St.cash`, `St.reserves` | `poolSize` (the asset held by the Euler contract) and `reserveBalance` |
| `deposit` | `EToken.deposit` (lines 139 to 175): checks liquidity when the account has debt |
| `withdraw` | `EToken.withdraw` (lines 180 to 200): `e/insufficient-pool-size`, `checkLiquidity` |
| `borrow`, `repay` | `DToken.borrow` (lines 98 to 121), `DToken.repay` (lines 126 to 148): repay pays at most the amount owed |
| `mint`, `burn` | `EToken.mint` (lines 206 to 229), `EToken.burn` (lines 234 to 264) |
| `transfer` | `EToken.transferFrom` (lines 323 to 354): checks the sender, and the receiver when it has debt |
| `donate` | `EToken.donateToReserves` (lines 359 to 386) |
| `liquidate` | `Liquidation.computeLiqOpp`, `liquidate`, `executeLiquidation` (lines 55 to 283), same asset as debt and collateral |
| `Healthy` | `RiskManager.computeLiquidityRaw` (lines 290 to 353) and `requireLiquidity`: with `SELF_COLLATERAL_FACTOR = 0.95 * 4e9`, a self-collateralized position fails the check exactly when `debt * 4e9 / 3.8e9 > balance` |
| `healthScore`, `discount`, `conversionRate`, `maxRepay`, `liqFee` | `computeLiqOpp` in 1e18 fixed point: base discount `0.02 + (1 - healthScore)`, capped at `MAXIMUM_DISCOUNT = 0.20`; yield `repay * conversionRate`; repay capped so the yield is at most the collateral; `UNDERLYING_RESERVES_FEE = 0.02` added to the liquidator's debt and credited to the reserves |

The reference adds the check that the other balance-lowering functions perform: a donation succeeds only if the donor is healthy afterward. In Solidity that is `checkLiquidity(account);` before `logAssetStatus(assetCache);` in `donateToReserves`. Euler did not patch v1: `EToken.sol` on the archived repository's master branch is byte-identical to the pinned commit.

## What was simplified or not proved

- One asset, priced at 1, with borrow factor 1 (Euler's reference asset is pegged at 1e18). The attack's DAI market had another borrow factor; Cyfrin reports a health score of 0.7510 after the donation where the model gives 0.7794. Both are below the 0.82 at which the discount reaches its 20% cap.
- The eToken exchange rate is fixed at 1 and no interest accrues. On chain, 20M DAI bought about 19.5M eTokens (Cyfrin), so the on-chain eToken and dToken amounts differ from the model's: Cyfrin reports 311M eTokens and 259M dTokens to the liquidator and about 135.77M dTokens left on the violator, against 320M, 261.12M and 134M here.
- Interest accrual and price changes are not operations. REQ-ACTOR-HEALTHY, REQ-STAYS-HEALTHY, REQ-ALLOWED-SUCCEEDS and REQ-EFFECTS hold from any state, including unhealthy states that interest could produce; REQ-NO-BAD-DEBT is about states reachable by user operations.
- Not modeled: flash loans (the attacker's 30M DAI is the violator's wallet), sub-accounts, deferred liquidity checks and batches, the discount booster for liquidators that track average liquidity, borrow isolation across markets, multiple collateral assets, decimals other than 18, and the `type(uint).max` shortcuts.
- Two edge cases differ from Euler: Euler lets a zero-amount transfer and a liquidation of a healthy account succeed as no-ops, where the model refuses them; and Euler's partial liquidations convert the requested repay by `1 / 1.02`, while the model's liquidator states the repay before the fee.
- The JSON wrapper `app/Main.lean` is tested, not proved. The real contracts are tested, not proved.

## Real contracts

`eval/realworld_euler.py` fetches the contracts at the pinned commit, checks each file it relies on against the commit's git blob hashes, deploys the modules unmodified in a local Foundry test (`realworld/adapters/euler`, solc 0.8.10 with the optimizer settings of the repository's `hardhat.config.js`), and runs the attack sequence (amounts times 1e18), Euler's three donate test scenarios and 1,000 generated sequences on both the unmodified contracts and a local copy with the one-line check added. After every operation it compares the contracts' state with the task's requirements, with Euler's own liquidity computation (`Exec.liquidity`) and with the proved component's output on the same sequence. Results are in `results/euler-1/rw-euler-donate/real-code/report.json`:

| Contracts | Sequences violating a requirement | Sequences with Euler's collateralValue < liabilityValue | Sequences identical to the proved component after every operation |
|---|---|---|---|
| b1ee326, unmodified | 57 of 1,004 (REQ-ACTOR-HEALTHY, REQ-STAYS-HEALTHY, REQ-NO-BAD-DEBT) | 57 | 947 |
| b1ee326 with `checkLiquidity(account)` in donateToReserves (local copy, not an upstream release) | 0 | 0 | 1,004 |

On the unmodified contracts the attack runs to the same final state as the Lean witness, times 1e18: the violator owes 134,000,000e18 with no collateral, the liquidator holds 281,095,493e18 against 261,120,000e18, the reserves hold 105,120,000e18 and the pool is empty. On the patched copy the donation reverts with `e/collateral-violation`. Euler's three donate test scenarios give the outcomes `test/reservesDonate.js` expects on both. The solvency witnesses found in the real contracts are confirmed in the Lean kernel as `¬ Healthy ⟨e, d⟩` goals (`real-code/Confirm.lean`).

Harness details: the driver sends 1e6 wei of the asset to the Euler contract after activating the market, so the pool holds as many units as the `INITIAL_RESERVES` eTokens and the exchange rate is exactly 1; it liquidates with the largest repay `checkLiquidation` offers and a minimum yield of 0 (with `minYield` equal to `checkLiquidation`'s yield, rounding makes some liquidations of small positions revert with `e/liq/min-yield`); `hardhat/console.sol`, imported by Euler's test token, is replaced by a no-op logging stub. Euler's no-op successes (a zero-amount transfer, a liquidation without opportunity) are counted separately and compared by state.

## Sources

- Source at the pinned commit: https://github.com/euler-xyz/euler-contracts/blob/b1ee3265853628d5a529081d7908c38404201b4e/contracts/modules/EToken.sol (the repository is archived and now named euler-legacy-xyz/euler-contracts; `donateToReserves` was added in commit 85abe8d0986f97557159d26c5e79df6d78eccc53, authored 2022-06-21; b1ee326 was authored 2022-09-07 and is the last change to EToken.sol)
- Euler's unit tests for the function: `test/reservesDonate.js` at the same commit
- License: Business Source License 1.1 with Change Date 2023-12-13 and Change License GPL-2.0-or-later (the repository's LICENSE); `EToken.sol` carries SPDX GPL-2.0-or-later
- Cyfrin analysis (step amounts, 95% self-collateral factor, 20% maximum discount, health score after the donation, amounts after the liquidation, about $197M net profit): https://www.cyfrin.io/blog/how-did-the-euler-finance-hack-happen-hack-analysis
- Zellic analysis (root cause: the transfer of eTokens ordinarily requires a liquidity check, absent in donateToReserves; loss of over 190 million USD): https://www.zellic.io/blog/euler-finance-exploit-analysis
- CoinDesk on the return of recoverable funds: https://www.coindesk.com/business/2023/04/03/euler-says-all-recoverable-funds-stolen-in-200m-hack-have-been-returned
