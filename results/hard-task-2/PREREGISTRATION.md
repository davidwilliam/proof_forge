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
