# hard-task-1: preregistration

Written on 2026-10-31, on branch `hard-task` from `main` at `ee69a0e`, before any task of this
experiment was built and before any model call on it. No model has seen these tasks. This file is
committed before the tasks, the library additions and the reference proofs; later changes go into
dated addenda at the end and never rewrite the sections above them.

## Question

Is there a real-world financial code component, short but mathematically deep, on which Muse Code
alone is very unlikely to produce a verified repair within $10 and 4 hours, while Muse Code with
everything ProofForge offers has a substantially higher chance?

The measured evidence so far does not show such a gap. Muse Code alone verified Knight (2 of 2),
Cetus (1 of 1) and Balancer (1 of 3); Muse Code with ProofForge verified Knight 2 of 2, Cetus 1 of
1, Balancer 2 of 3 (`results/muse-code-1`). Compound is not verified by any arm: the sequence-level
reward bounds stay open in every run (`results/library-1`, `web/generated/shapes/summary.json`).
On the frozen benchmark the arms do not separate (`results/e1-test-1`).

## Selection criteria

A candidate component is selected only if all of these hold.

1. Real code. A faithful port of code deployed in a major codebase, pinned to a commit, with a real
   bug history or a documented incorrect variant. Where the start candidate is not a historical
   release it is labelled "plausible variant, not a release".
2. Short. The implementation is roughly under 60 lines of Lean.
3. Deep. Correctness for every input needs a mathematical insight (an invariant, an error bound,
   a number-theoretic identity), not case analysis or length.
4. Relevant. The component computes money or prices in deployed financial code.
5. Provable by the build team. A reference solution with a complete proof is accepted by the judge
   (Comparator's six kernels, `leanchecker`, axioms only `propext`, `Classical.choice`,
   `Quot.sound`) before any measurement.
6. No shortcut. A correct candidate cannot avoid the mathematics by replacing the algorithm with a
   different one whose proof is already available (for example Lean core's `Nat.sqrt`, whose
   lemmas `Nat.sqrt_le` and `Nat.lt_succ_sqrt` are in the core library both arms have). Where this
   is possible, the locked specification states the deployed algorithm's shape as a requirement.
7. Decisive general help. What ProofForge offers applies to the task without any task-specific hint:
   the library holds general mathematics only, and the harness has no code or prompt for these
   tasks.
8. Not already solved by the library. A component whose correctness theorem ProofForgeFin already
   proves would measure a lookup, not proving.

## Candidates considered

Provenance below was checked against the sources on 2026-10-31 (GitHub API and the advisories);
commit hashes are the ones the tasks will cite.

| Candidate | Provenance | Decision and reason |
|---|---|---|
| Integer square root, OpenZeppelin `Math.sqrt` (power-of-two estimate from `log2`, seven Newton steps, `min(result, a / result)`) | OpenZeppelin Contracts v4.9.6, commit `dc44c9f1a4c3b10af99492eed84f83ed244203f6`, `contracts/utils/math/Math.sol` lines 152 to 193 (`sqrt`, `sqrt` with rounding), 199 to 234 (`log2`); the same `sqrt` text in v4.8.0 and v5.0.x; replaced by a six-step version with a 3/2 estimate in pull request 4403 (2024-02-16, released in v5.1.0). Used for first-deposit liquidity, `Math.sqrt(_amount0 * _amount1) - MINIMUM_LIQUIDITY`, in Aerodrome `contracts/Pool.sol` line 314 (commit `d5e48b3b36`, OpenZeppelin 4.8.0) and Velodrome V2 `contracts/Pool.sol` line 305 (commit `e3f62b897f`) | **Chosen: task `rw-oz-sqrt`.** Correctness for every uint256 needs the quadratic error bound of Newton's method with floors: the estimate has one correct bit, each step at least doubles the correct bits, seven steps reach the root or the root plus one, and the final `min` removes the one. Start candidate: the same code with six Newton steps (plausible variant, not a release: the step count of the v5.1 rewrite on the v4.9 estimate). Six steps return the root minus one from 204-bit inputs on (first found at `2^204 - 1`), and the root minus 198202503 at `2^256 - 1`. |
| Decimal square root, Vyper builtin `sqrt()` (Babylonian loop, at most 256 iterations, stop when two iterates are equal) | Vyper v0.4.0, commit `e9db8d9f7486eae38f5b86531629019ad28f514e`, `vyper/builtins/functions.py` class `Sqrt` (lines 2117 to 2172); advisory GHSA-2p94-8669-xg86, CVE-2025-26622, "sqrt doesn't define rounding behavior", published 2025-02-21: on `0.9999999998` it returns `0.9999999999`, the root rounded up; fixed by pull request 4486 (merge commit `2ffc8b3db8b7e32257a72560fa89e7dcf81b5384`, 2025-02-23), which adds `if y < z: z = y` after the loop, released in v0.4.1 | **Chosen, second: task `rw-vyper-sqrt`**, built if the build team completes its reference proof. A real released bug and its real fix. Correctness needs a bound on the number of iterations (the error at least halves per step from a seed up to about 2^66 times the root, so the loop reaches the root or the root plus one well within 256 iterations) and the oscillation argument (when `x + 1` is a perfect square the iterates alternate between the root and the root plus one, and only the smaller of the last two is the floor). The start candidate is the v0.4.0 code. Financial relevance: Vyper is the language of Curve and other DeFi contracts; the fix's commit message names applications that use `sqrt()` to determine boundary conditions. |
| Integer square root with a bit-trick estimate (Solmate `FixedPointMathLib.sqrt`, Vyper `isqrt`: estimate `181 << k`, then `z * (y + 65536) / 2^18`, seven steps, final correction) | Vyper v0.4.0 `functions.py` class `ISqrt`; Solmate; Solady notes that its `sqrtWad` convergence was checked with z3 (pull request 967) | Rejected. That seven steps suffice depends on a numeric case analysis of the estimate over 2^24 residues, not on a short argument; the build team cannot give a kernel-checked reference proof by a short insight. |
| Uniswap V2 `Math.sqrt` (Babylonian loop until the iterate stops decreasing) | Uniswap v2-core `contracts/libraries/Math.sol` | Rejected. The loop runs to its fixed point with no step bound, so no error bound is needed; it is the algorithm of Lean core's `Nat.sqrt.iter`, whose proof is in the core library both arms have. |
| OpenZeppelin `Math.sqrt` v5.1 (3/2 estimate, six steps, `xn - (xn > a / xn)`) | pull request 4403, released in v5.1.0 | Not built separately: the same algorithm family as `rw-oz-sqrt`, with a smaller margin. |
| Full-precision `mulDiv` (Uniswap V3/V4 `FullMath.mulDiv`, OpenZeppelin `Math.mulDiv`: 512-bit product, inverse modulo 2^256 by Newton iteration) | Uniswap v4-core `FullMath.sol` | Rejected by criterion 8: `ProofForgeFin.Evm.FullMath.mulDiv512_eq` already proves the deployed algorithm equal to the exact floor quotient on every input, so the ProofForge arm would cite one theorem. |
| Reward-per-share accumulators (MasterChef, Synthetix StakingRewards: claimable never exceeds emitted, a potential argument) | | Rejected. `rw-compound-comp` is this class and no arm verifies it (Muse Code alone 5 of 8, with ProofForge 0 of 8); `ProofForgeFin.DeFi.Chef.run_paid_le` proves the MasterChef bound (criterion 8). |
| Constant-product swap with fee (Uniswap V2: fee-adjusted balances keep `k`) | | Rejected by criterion 8 (`ProofForgeFin.DeFi.AMM`: `k_le_swapOut`, `k_le_swapIn`, `constantProduct_wellBehaved`), and the swap-value class is where Muse Code alone is already strong (Balancer). |
| Largest-remainder apportionment | moneyphp `allocate`, Spliit | Rejected. `ProofForgeFin.Money.Hamilton` and two existing tasks (`rw-moneyphp-allocate`, `rw-spliit-balances`) cover it, and the proof is bookkeeping rather than one insight. |
| Integer cube root (Solady `cbrt`, `cbrtWad`) | Solady pull request 967 (2024-06-21) fixes `cbrtWad`; its author notes z3 does not terminate on it | Rejected. Same estimate analysis as Solmate's `sqrt`, a three-term AM-GM without Mathlib, and limited production use (the pull request says so). |
| "MathMasters" square root (CodeHawks contest 2024-01) | a contest codebase with seeded bugs | Excluded: not deployed code. |

Every candidate that is built is reported, whether or not it shows a gap.

## Tasks to build

Both tasks follow the format of `realworld/tasks/*`: locked specification with a plain-language doc
comment per requirement, the port of the deployed code with source references, the buggy start
candidate (repair mode), an implement-mode stub (the generator of `agents/repair.py`), a reference
solution with a complete proof, attacks, a kernel-checked counterexample for the start candidate,
oracle and property tests (2,001 cases), the executable, README, `validation.json` from
`harness/validate_task.py`, and a spec-strength report from `bin/proofforge spec-strength`.
`bin/proofforge check` must REFUTE the start candidate and VERIFY the reference.

Requirements planned (plain language; the Lean statements are fixed when the tasks are locked and
their locked manifest hashes go into an addendum before any measured run):

`rw-oz-sqrt` (definition hole `sqrt : BitVec 256 → BitVec 256`):

- the result squared never exceeds the input (the root is never overstated);
- the input is below the result plus one, squared (the root is never understated);
- `sqrt(a, Rounding.Up)`, the library's own rounding-up wrapper (protected): its square covers the
  input, and one less does not;
- the first deposit of an Aerodrome/Velodrome volatile pool (protected port of the
  `_totalSupply == 0` branch of `Pool.mint`, with the routine as a parameter): the LP supply it
  creates, including the locked 1,000 units, squared, never exceeds `amount0 * amount1`; the
  depositor is never shortchanged by a unit or more; a deposit whose product fits and whose root is
  above the minimum liquidity never reverts;
- the routine is the deployed algorithm: the `log2` estimate, at most seven Newton steps, and the
  final `min` (criterion 6; seven steps is OpenZeppelin's gas budget).

`rw-vyper-sqrt` (definition hole: the builtin's routine on Vyper decimals, `Int → Option Int`,
`none` for a revert):

- for a valid decimal input `x >= 0`, the result `r` (in units of 10^-10) satisfies
  `r * r <= x * 10^10` (rounded down: never above the true root) and `x * 10^10 < (r + 1)^2`;
- a valid non-negative input never reverts; a negative input reverts;
- the routine is the deployed loop (seed `x / 2.0 + 0.5`, at most 256 iterations, stop when two
  successive iterates are equal) followed by a choice between the last two iterates, which is where
  pull request 4486 changed the code (criterion 6).

## Library work for this experiment

Allowed only as general mathematics a careful library would contain, in its own module with doc
strings, with no task, protocol or codebase name, checked by the six kernels
(`harness/fin_kernels.py`) and axiom audited (`lib/Audit.lean`). Planned: `ProofForgeFin.Sqrt`,
facts about the integer Newton step `newton a x = (x + a / x) / 2` and Lean core's `Nat.sqrt`:

- the step never goes below the root, from any positive iterate (AM-GM with floors);
- above the root the step strictly decreases;
- the exact integer error relation `2 * x * (newton a x - s) <= (x - s)^2 + 2 * s`, `s = Nat.sqrt a`,
  from either side of the root, and its two consequences: the quadratic bound
  (`newton a x - s <= (x - s)^2 / (2 * s) + 1`) and the halving bound
  (`newton a x - s <= (x - s) / 2 + 1`);
- termination at the root: a square error at most `2 * s` gives the root or the root plus one in one
  step; from the root or the root plus one the step stays there; the only fixed point of the step
  is the root;
- the final corrections `min x (a / x)` and `x - (if a / x < x then 1 else 0)` return the root from
  the root or the root plus one;
- the root and powers of two (`2^(2k) <= a` gives `2^k <= Nat.sqrt a`, `a < 2^(2k)` gives
  `Nat.sqrt a < 2^k`), uniqueness of the root from its two bounds, monotonicity.

The library will not contain: the step count of either routine, the estimate of either routine, a
statement about seven or 256 iterations, `BitVec` versions of either routine, or anything about
decimals. Any further library addition made for this experiment is listed in an addendum before
the first measured run, and the library's source tree hash at measurement is recorded there.

## Arms

Two arms, identical model, prompt template, caps and judge; only what ProofForge adds differs.

- **`alone`: Muse Code alone.** `agents/muse_code.py --arm alone`: Muse Code with the locked task
  project, the start candidate and the issue report, and Lean 4.35 through one MCP tool
  (`lean_build`, Lean's own output). Compile-and-retry continuation messages with Lean's errors or
  the theorems still using `sorry`. No judge, no property tests, no counterexamples, no library, no
  planner.
- **`proofforge`: Muse Code with everything ProofForge offers.** The same, plus: the locked
  specification and the official check with witnesses and kernel-checked counterexamples
  (`check_candidate`), ProofForgeFin vendored (including `ProofForgeFin.Sqrt`) with library search,
  the planner and top-down decomposition, the tactic portfolio, the goal tool, refutation of helper
  lemmas on concrete values, and the attempt ledger, as provided by the ProofForge integration for
  Muse Code at the commit recorded in the addendum. The arm's code is frozen at that commit for all
  runs of this experiment.

Settings for every run: model `muse-spark-1.3-contributor` at medium effort for the prover (any
planner model the `proofforge` arm calls is charged to the same budget); caps $10 at standard list
prices (metered per call, `integrations/muse/meter.py`) and 14,400 s of wall time; the Muse Code
flags of `results/muse-code-1`; a fresh workspace per run that never contains references, attacks,
witnesses, README or results.

## Runs

- Mode: repair (start candidate = the buggy port). Primary.
- Number: 5 runs per arm per task, so 20 runs if both tasks are built (10 if only `rw-oz-sqrt` is).
  The number is fixed; there is no extension and no early stopping on results.
- Order: the runs of a task interleave the arms (`alone`, `proofforge`, `alone`, ...), at the same
  concurrency, so host load affects both arms alike.
- Implement mode (start = the generated stub) is secondary and optional; if run, it is 5 runs per
  arm per task with the same caps, analysed the same way and reported separately.
- A run is set aside only for an infrastructure failure that leaves no Lean verdict (the Docker
  daemon not answering, the meter failing), decided by a rule that does not look at the arm; it is
  rerun, and both the failed and the rerun are reported.

## Outcomes and analysis

- Primary outcome per run: VERIFIED by `bin/proofforge check` on the run's final candidate, judged
  outside the budget (every requirement proved, Comparator's six kernels, `leanchecker`, the axiom
  audit, and the rebuilt executable passing 2,001 property cases). Every VERIFIED Passport is
  reproduced with `bin/proofforge verify`.
- Primary analysis, per task: one-sided Fisher exact test of H1 "the `proofforge` arm verifies more
  often than the `alone` arm" on the 2 x 2 table (arm by verified), alpha 0.05. Both p-values are
  reported; with two tasks, a claim for both at once uses alpha 0.025 each.
- Secondary: the same test on the counts pooled over the two tasks; list dollars per verified run
  (all list dollars of an arm divided by its verified runs; no verified run gives "no verified run"
  rather than a number); dollars charged; wall time; requirements proved in the last compiling
  version; for each unverified run, whether its final candidate is REFUTED, UNRESOLVED or does not
  build.
- Power, stated in advance: with 5 runs per arm the one-sided test reaches p < 0.05 only with a
  difference of at least four (4 of 5 against 0 of 5, or 5 of 5 against 1 of 5, p = 0.024); 3 of 5
  against 0 of 5 gives p = 0.083. A smaller difference will be reported as not significant.

## Commitments

- No model call on these tasks by the build team before the measured runs; no tuning of either arm
  on them; no task-specific code, prompt or hint in the harness.
- The tasks, the library module and the arm code are frozen before the first measured run; their
  hashes and commits go into the addendum.
- Every built candidate and every run is reported in `results/hard-task-1/README.md`, including a
  task that shows no gap and a `proofforge` arm that verifies nothing.
- The README states the library work done for this experiment, so that a gap can be read as the
  contribution of ProofForge including that library work.
