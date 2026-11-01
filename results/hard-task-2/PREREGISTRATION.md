# hard-task-2: preregistration

Written on 2026-11-01 on `main` at `8159985`, before the task of this experiment is built and before
any model call on it. No model has seen it. This file is committed before the task, the library
additions and the reference proof; later changes go into dated addenda at the end and never rewrite
the sections above them.

## Question

On the swap step of KyberSwap Elastic, the code behind the exploit of 2023-11-22, does Muse Code with
ProofForge produce a verified repair more often than Muse Code alone, at equal caps?

## Context

`results/hard-task-1` separated the arms on `rw-vyper-sqrt` (2 of 5 alone, 5 of 5 with ProofForge,
p = 0.083) and not on `rw-oz-sqrt` (0 of 5 each). Since then ProofForge has changed: the library
modules `ProofForgeFin.SqrtIter`, `ProofForgeFin.WordBridge` and `ProofForgeFin.NatSqrt` (commit
`eafe3fc`) and the `proofforge-full` changes that keep the best compiling version and report progress
per requirement (commits `cdd96ca` to `8159985`). This experiment measures the ProofForge of that
state, plus the library work listed below, on a task chosen after those changes.

## Selection

The criteria of `results/hard-task-1/PREREGISTRATION.md` apply unchanged. Ten candidates were
evaluated without model calls (provenance fetched from GitHub and the advisories); the ranking:

| Candidate | Decision |
|---|---|
| KyberSwap Elastic `SwapMath.computeSwapStep`, token1 branches | **Chosen: task `rw-kyber-swapstep`.** |
| Curve StableSwap 3pool `get_y` with `exchange` (commit `bae23a2`) | Deferred. The defect found (the `- 1` margin lowers the invariant by one unit on some inputs) comes from a simulation, is dust that any nonzero fee covers, and is not reported by anyone. |
| Curve stableswap-ng `get_D` (incorrect variant `7ac164b`, restored in `4b3cb6d`) | Deferred: a statement for every input needs a balance-ratio domain; reference proof risk high. |
| Balancer V2 StableMath solver | Rejected: no refutable start candidate found. |
| Solidly-family stable `_get_y` | Rejected: safety is case analysis; the bug reverts router swaps. |
| Yearn yETH `_calc_supply` | Rejected: no clean statement for every input is known to hold. |
| Uniswap `TickMath` | Rejected: no deployed bug; reference proof without Mathlib not credible. |
| Aave compounded interest; exp, ln and pow libraries; ray rounding, Comet, ERC-4626 fees | Rejected: shallow and covered by the library, or the specification needs exp and ln. |

Provenance of the chosen task:

- Code: `KyberNetwork/ks-elastic-sc` at `4ab08c0a60f74809f731bdd333076e32d05f1d17`,
  `contracts/libraries/SwapMath.sol` (`computeSwapStep` lines 28 to 98, `calcReachAmount` 102 to 164,
  `estimateIncrementalLiquidity` 169 to 216, `calcIncrementalLiquidity` 220 to 249, `calcFinalPrice`
  253 to 280, `calcReturnedAmount` 285 to 320) and `contracts/Pool.sol` lines 412 to 419 (the tick
  crossing test). The source matches the exploited pool contract through Sourcify.
- Defect: lines 186 to 193 compute `deltaL` with `FullMath.mulDivFloor` under a comment that says it
  is rounded up. Introduced by `KyberNetwork/ks-elastic-sc-legacy` pull request 95, "fix ceiling to
  floor swapmath", commit `33446757d93619b73403573dc309b9a072b167b1` (2022-06-04), which changes this
  call from `mulDivCeiling` to `mulDivFloor`. Both forms are real commits.
- Incident: KyberSwap post-mortem of 2023-11-22 (about $55.23M taken, $48.67M by the main
  exploiter); BlockSec analysis naming the line; Kyber's Echidna test
  (`contracts/echidna/SwapMathEchidnaTest.sol` lines 32 to 55) states the violated property.
- A second, undocumented defect in the exact-output token1 branch was found by simulation (the
  smaller quadratic root computed with a floor square root rounds `deltaL` the wrong way). It is used
  only if a kernel-checked counterexample confirms it under the deployed range checks; otherwise the
  start candidate is refuted on the exact-input branch only, and this is recorded in an addendum.

## Task to build

Format of `realworld/tasks/*`: locked specification with a plain-language doc comment per
requirement, the port with source references, the start candidate (the code at `4ab08c0`, repair
mode), an implement-mode stub, a reference solution with a complete proof, attacks, kernel-checked
counterexamples for the start candidate, oracle and property tests (2,001 cases), the executable,
README, `validation.json` and a spec-strength report. `bin/proofforge check` must REFUTE the start
candidate and VERIFY the reference.

Scope: the two token1 branches (token1 in, price up; token1 out, price down) of `calcReachAmount`,
`estimateIncrementalLiquidity`, `calcFinalPrice`, `calcIncrementalLiquidity`, the `computeSwapStep`
decision and the crossing test of `Pool.sol`, over `BitVec 256` under the deployed range checks.

Requirements planned (the Lean statements are fixed when the task is locked; the locked manifest hash
goes into an addendum before any measured run):

- the step that does not reach the target leaves the next price between the current price and the
  target, inclusive;
- the pool never moves further than it is paid for (the virtual reserve after the step is backed by
  the amount used);
- the reinvested fee liquidity is the exact value rounded once in the pool's favour;
- the step that reaches the target ends on the target and returns no more than the exact amount;
- a step that leaves the price on the target's side crosses the tick (the property the exploit broke);
- the step is the deployed computation with each division a floor or ceiling division and the square
  root a floor or ceiling root (no-shortcut requirement: capping the price at the target, or a zero
  fee liquidity, violates the other requirements; the repair is a choice of rounding directions).

## Library work for this experiment

General mathematics only, in its own modules with doc strings, no task, protocol or codebase name,
checked by the six kernels and the axiom audit. Planned:

- monotonicity of linear fractional maps on `Nat` in cross-multiplied form, with floor and ceiling;
- composition of roundings and the sign of the composed error;
- the integer smaller root of a quadratic with floor and ceiling square roots, and the side of the
  real root each lands on;
- inequality lemmas for products of bounded naturals.

The library will not contain the swap step, its reach amount, its price formula or any statement
about them. Every library addition made for this experiment is listed in an addendum before the
first measured run, with the library source tree hash at measurement.

## Arms

As in hard-task-1, with ProofForge at its current state:

- `alone`: `agents/muse_code.py --arm alone`.
- `proofforge`: `agents/muse_code.py --arm proofforge-full`, at the commit recorded in an addendum
  before the first measured run.

Model `muse-spark-1.3-contributor` at medium effort, Muse Code 1.4.14, caps $10 at list prices and
14,400 s per run, a fresh workspace per run that never contains references, attacks, witnesses,
README or results.

## Runs

- Repair mode, 10 runs per arm, 20 in total. The number is fixed; no extension, no early stopping.
- Order: interleaved (`alone:1`, `proofforge-full:1`, `alone:2`, ...), `--parallel 2`,
  `PF_CONTAINER_SLOTS=1`, no other model experiment on the host.
- A run is set aside only for an infrastructure failure that leaves no Lean verdict, decided without
  looking at the arm; it is rerun and both are reported.

## Outcomes and analysis

- Primary outcome per run: VERIFIED by `bin/proofforge check` on the run's final candidate, judged
  outside the budget from the frozen commit; every VERIFIED Passport reproduced with
  `bin/proofforge verify`. The final candidate of each arm is the one that arm's code selects.
- Primary analysis: one-sided Fisher exact test, `proofforge` verifies more often than `alone`,
  alpha 0.05. With 10 runs per arm, p < 0.05 needs, for 10, 9, 8, 7, 6 or 5 verified with
  ProofForge, at most 6, 5, 3, 2, 1 or 0 verified alone.
- Secondary, without a confirmatory claim: list dollars per verified run; one-sided Mann-Whitney U
  on list dollars per run; runs stopped by a cap; dollars charged; wall time; requirements proved in
  the final candidate; REFUTED, UNRESOLVED or not building for each unverified run.

## Commitments

- No model call on this task by the build team before the measured runs; no tuning of either arm on
  it; no task-specific code, prompt or hint in the harness.
- The task, the library additions and the arm code are frozen before the first measured run; their
  hashes and commits go into an addendum.
- Every run is reported in `results/hard-task-2/README.md`, including an outcome with no gap.

## Addendum 1 (2026-11-01): task and library built, before any measured run

The task `rw-kyber-swapstep` and the library additions were built as planned above; no model was
called on the task.

| | `rw-kyber-swapstep` |
|---|---|
| Task commit | `855fb70` |
| Locked manifest sha256 | `46d3ba5391739b16c3b0919c546cdf5619527ee150272dd6404d3b7cde0e3fc8` |
| Requirements | REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-STEP-REACH, REQ-STEP-PAID, REQ-IN-FEE-LIQUIDITY, REQ-OUT-FEE-LIQUIDITY, REQ-POOL-CROSSES, REQ-DEPLOYED-STEP |
| Start candidate | the code at `4ab08c0` (repair mode) |
| Reference proof | `reference/SolutionA.lean`: 811 non-blank lines, 41 theorems (689 non-blank lines after the code) |

Source. `SwapMath.sol`, `QuadMath.sol`, `FullMath.sol`, `Pool.sol`, `Factory.sol`, `SafeCast.sol`,
`MathConstants.sol`, `TickMath.sol` and `SwapMathEchidnaTest.sol` were fetched at `4ab08c0` with
`gh api`, and commit `33446757d93619b73403573dc309b9a072b167b1` of `ks-elastic-sc-legacy` with its
diff (line 177 of `SwapMath.sol`, `mulDivCeiling` to `mulDivFloor`; pull request 95, merged
2022-06-06 as `6401b62`). Each ported function cites its file and lines in
`spec/KyberSwapStep/Spec.lean`.

Both defects are confirmed by refutations that `bin/proofforge check` generated from the property
tests and checked with Comparator's six kernels, `leanchecker` and the axiom audit
(`passports/kyber-start.json`, Passport `a73c8bd1e11cf770`, reproduced by `bin/proofforge verify`;
also `witnesses/deployed_4ab08c0.lean`, `decide`):

- Exact input (the exploit): liquidity 529700652, current price 26908681593376338809905220921561871,
  target 27180014754403994732126507336932861, fee 300, input 1816821696332 (one below the reach
  amount): next price 27180014754675749645719300096015422, above the target. REQ-IN-WITHIN-TARGET is
  refuted.
- Exact output, the second defect: it holds under the deployed range checks (prices within
  `[MIN_SQRT_RATIO, MAX_SQRT_RATIO)` less than a 5% price move apart, a fee below 100000, liquidity
  below `2^129`, Solidity 0.8 checked arithmetic, including the checked `b * b` of `QuadMath`).
  With liquidity 488099447615, current price 12702106732281905876958584314416, target
  12689701559484189505314970178876, fee 8 and an output of 76421257163 units, the step ends at
  12689701559483980415274287706444, below the target; the fee liquidity 19087 is above the smaller
  root of the fee equation. REQ-OUT-WITHIN-TARGET and REQ-OUT-FEE-LIQUIDITY are refuted. Rounding
  the square root up removes it.
- REQ-POOL-CROSSES is refuted on an iteration of the loop of `Pool.swap` (exact output, fee 1) that
  stops without crossing a tick with the price beyond it.

The reference is VERIFIED (`passports/kyber-reference.json`, Passport `8daa0235dbc0dc04`,
reproduced). `harness/validate_task.py rw-kyber-swapstep --cases 2000`: VALID (reference accepted,
binary PASS; start rejected, binary REFUTED; six attacks as expected). `bin/proofforge
spec-strength` (`spec-strength/rw-kyber-swapstep/report.json`, report `b84f75bfae396bd1`): 151
mutants of the reference; 13 do not compile; of the 138 that compile, 70 are killed, all 70 by a
kernel-checked refutation, and 68 survive, 37 with no observed difference and 31 with a behaviour
difference. Every requirement except REQ-DEPLOYED-STEP is shown not trivially true by a
kernel-checked refutation. The survivors that differ change code outside the eighteen choices of
`Rounding`, so each meets REQ-DEPLOYED-STEP only if it equals a member of the family on every
input; the testable requirements do not exclude them: the returned amount of an exact-input step
(8 mutants), the fee liquidity of a step that ends on the target (7, including no fee liquidity at
the target), the choice of branch (6, including one that ends every step on the target, like the
cap) and subtractions with swapped or fixed operands that make the step revert where the reference does not
(10; no requirement asks a step not to revert). The mutation operators do not exchange `mulDivFloor` and
`mulDivCeiling`; in a simulation of the eighteen single changes of the reference's choices on
20,000 generated cases, sixteen violate a requirement and two do not: the exact-output price
rounded down, which keeps every requirement by the same argument, and the coefficient `c` of the
fee equation rounded up.

Library additions, all written by the build team knowing the task, none naming a swap step, a price,
a fee or a reach amount: `ProofForgeFin.QuadRoot` (4 theorems: `quad_nonneg_of_sqrt_ge`,
`quad_neg_of_sqrt_le`, `factor_neg_of_lt_vertex`, `le_of_quad_nonpos`) and
`ProofForgeFin.RoundCompose` (3 theorems: `mul_le_of_floor_floor`, `le_of_floor_le_floor`,
`ceil_frac_floor_bounds`), commit `557167d`, library source tree
`5151f309eb61a2dcc331a54f01e0d87e41c0aa473c1b7be0fd471fd4c10be1f9`. Their 36 constants (counting
compiler-generated ones) pass the six kernels and `leanchecker` (`kernels-library.json`); the axiom
audit of the whole library reports 0 violations (`audit-library.txt`); `harness/fin_lib.py scan`
passes and the search index lists the new declarations. The reference uses all of them except
`quad_neg_of_sqrt_le`, and `ProofForgeFin.div_eq_of_bounds` of `ProofForgeFin.Rounding`. No other library change was
made.

Differences from the plan above:

- The requirements are split by branch where the two branches differ (eight, against six planned):
  within the target and fee liquidity have a token1-in and a token1-out requirement each.
- The repair is not only a choice of rounding directions. Rounding the deployed fee expression up
  (the code before pull request 95) moves the price down on a token1-in step whose input is below
  `currentSqrtP / 2^96`, which breaks the lower half of Kyber's own Echidna property
  (`attacks/legacy_ceiling.lean` is refuted). In a simulation of the 32 rounding choices of the five
  divisions on the exact-input path, every choice either passed the target or moved the price down
  on some input of the deployed range (rounding the virtual input of `calcFinalPrice` up as well
  passes the target only at fees near 100%, for example 99999). The family of REQ-DEPLOYED-STEP
  therefore has one structural choice besides the roundings: the fee liquidity of an exact-input
  step may be computed from the virtual input `absDelta * 2^96 / currentSqrtP` rounded first. The
  reference uses it (`deltaL = mulDivCeiling(mulDivFloor(absDelta, 2^96, currentSqrtP), fee,
  TWO_FEE_UNITS)`) and rounds the square root of `QuadMath` up.
- Capping the price at the target does not violate the other requirements, as the plan expected:
  with the deployed exact-input rounding and a cap, every requirement except REQ-DEPLOYED-STEP holds
  and is proved (`attacks/cap_restated.lean`, rejected by Comparator only through the restated
  REQ-DEPLOYED-STEP; ordinary checking accepts it). A step without fee liquidity is refuted by
  REQ-IN-FEE-LIQUIDITY and REQ-IN-WITHIN-TARGET.
- REQ-STEP-PAID is stated for the input token: token1 for exact input, with an exception for a step
  that ends on the target and reinvests nothing (the reach amount is rounded down by design, line
  117, and the virtual reserve can then exceed the input by less than one unit), and token0 for
  exact output (the deployed price of an exact-output step is rounded up by design).
- REQ-OUT-FEE-LIQUIDITY bounds the fee liquidity from above only (not negative at `deltaL`); a lower
  bound within one unit of the exact root does not hold, because the coefficients of the quadratic
  are themselves rounded. REQ-IN-FEE-LIQUIDITY is within one unit on both sides.
- "Returns no more than the exact amount" is stated on the amount used by a step that ends on the
  target (REQ-STEP-REACH); the returned token0 amount is constrained by REQ-STEP-PAID.
- The library has no module for linear fractional maps or for products of bounded naturals: the
  reference compares the cross-multiplied forms directly (with `grind` for the ring identities).
- `QuadMath.sqrt` is ported as its loop with a bound of 512 iterations; the protected lemma
  `toNat_sqrt` proves it equal to `Nat.sqrt` on every `uint256`. The protected lemmas also give the
  checked operations, `mulDivFloor`, `mulDivCeiling` and the casts through `toNat`.
- The domain of every requirement is stated as `ExactIn`/`ExactOut`: `0 < L < 2^129`, fee below
  100000, both prices in the range of `TickMath` with `100 * hi² < 105 * lo²`.

The commit of the `proofforge` arm's code is recorded in an Addendum 2 before the first measured
run, and no run starts before that.
