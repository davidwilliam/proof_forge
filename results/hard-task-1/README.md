# hard-task-1: two decisive tasks for Muse Code alone against Muse Code with ProofForge

Status: the two tasks and the library module are built, validated and frozen. No model has been
run on them; the measured runs are pending. The plan, the arms, the caps, the number of runs and
the analysis were committed before anything was built (`PREREGISTRATION.md`, commit `54bf8cc`);
its addenda record what changed since.

## The tasks

Both are integer square roots in deployed code, short (twelve and six lines of Lean for the
routine), where correctness for every input needs an error bound for Newton's method with floor
divisions, which Lean's core library (no Mathlib) does not provide.

| Task id | Component | Start candidate (repair mode) | Requirements | Reference proof |
|---|---|---|---|---|
| `rw-oz-sqrt` | OpenZeppelin `Math.sqrt` v4.9.6 (seven Newton steps from a power-of-two estimate, then `min(result, a / result)`), its rounding-up wrapper, and the first deposit of Aerodrome's `Pool.mint` (`Math.sqrt(_amount0 * _amount1) - 1000`) | six Newton steps: plausible variant, not a release; refuted at `2^204 - 1` (the root minus one) and at `2^256 - 1` (the root minus 198202503) | 8 | 281 non-blank lines, 19 theorems |
| `rw-vyper-sqrt` | Vyper's `sqrt()` builtin on decimals (Babylonian loop of at most 256 iterations), with the decimal arithmetic of the compiler | the v0.4.0 code: CVE-2025-26622 (GHSA-2p94-8669-xg86), `sqrt(0.9999999998)` returns `0.9999999999` | 5 | 218 non-blank lines, 14 theorems |

Task READMEs: `realworld/tasks/rw-oz-sqrt/README.md`, `realworld/tasks/rw-vyper-sqrt/README.md`.
Each locked specification has one requirement that keeps the deployed algorithm
(REQ-NEWTON-BUDGET, REQ-DEPLOYED-LOOP). It is extensional: a routine meets it when it equals the
deployed algorithm on every input. Without it, Lean core's `Nat.sqrt` would satisfy every other
requirement with a short proof; the attack `nat_sqrt_restated.lean` of each task shows this and is
rejected.

Implement mode: `implement/Solution.lean` in each task is the stub `agents/repair.py` generates from
the locked challenge.

## Checks (no model calls)

| Check | `rw-oz-sqrt` | `rw-vyper-sqrt` |
|---|---|---|
| Locked manifest sha256 | `62af2324e4c0cf68ea45b7b88fa861f4d8b211e4c98eb25f256e59e917083616` | `ea5b5e443d8f028f5bd161c67e95a1ff2046fec2de44a43f04a7936e51622fb1` |
| `harness/validate_task.py --cases 2000` | VALID: reference accepted by the judge, binary PASS; start rejected, binary REFUTED; three attacks as expected | VALID: reference accepted, binary PASS; start rejected, binary REFUTED; two attacks as expected |
| `bin/proofforge check`, start candidate | REFUTED: REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS, REQ-MINT-FULL, each by a generated refutation accepted by Comparator's six kernels and `leanchecker` (axiom `propext`); Passport `0fc77e346f297a3b` | REFUTED: REQ-SQRT-NOT-ABOVE on `0.9999999998`, generated refutation accepted by the six kernels (no axioms); Passport `a9ed71918b55704a` |
| `bin/proofforge check`, reference | VERIFIED, 8 of 8, with `ProofForgeFin.Sqrt` vendored; Passport `bbac8f6c77e8f931`, reproduced by `bin/proofforge verify` | VERIFIED, 5 of 5, with `ProofForgeFin.Sqrt` vendored; Passport `4f3abccf305d3c51`, reproduced by `bin/proofforge verify` |
| `bin/proofforge spec-strength` | 48 mutants of the reference; 8 do not compile (the ceiling-division operator has no `BitVec` form); of the 40 that compile, 37 are killed, all 37 by a kernel-checked refutation, and 3 survive with no observed behaviour difference (the `a == 0` guard removed, the arguments of `min` swapped, the estimate doubled: each returns the root on every input tried, so each also meets the extensional REQ-NEWTON-BUDGET if it is correct everywhere); every requirement except REQ-NEWTON-BUDGET is shown not trivially true by a kernel-checked refutation | 33 mutants of the reference; 4 do not compile; 1 has an executable identical to the reference's; of the other 28, 19 are killed, all 19 by a kernel-checked refutation, and 9 survive with no observed behaviour difference on 12,002 inputs (other seeds: `x / 3.0 + 0.5`, `x / 2.0 + 1.0`, `x / 2.0 + 0.3333333333`; the constant `0.5` computed with ceiling division, the same value; 255, 257 or 2,560 iterations; `<=` for `<` in the choice; the arguments of `+ 0.5` swapped: the loop still reaches the root, so each also meets the extensional REQ-DEPLOYED-LOOP if it is correct everywhere); every requirement except REQ-DEPLOYED-LOOP is shown not trivially true by a kernel-checked refutation |

Passports and their console output: `passports/`. Spec-strength reports: `spec-strength/`.

## Library work done for this experiment

`ProofForgeFin.Sqrt` (`lib/ProofForgeFin/Sqrt.lean`, commit `b3a851a`; library source tree
`5190779eefac61f328a4d5a7a2dfa91d42ea6d191fa707eedc5b71b65798a44a`): facts about Lean core's
`Nat.sqrt` and one Newton step `(x + a / x) / 2` on natural numbers: AM-GM with floors, the exact
error relation of one step from either side of the root, quadratic and halving convergence, the
only fixed point, the end of an iteration, and the corrections `min x (a / x)`,
`x - (if a / x < x then 1 else 0)` and the smaller of two iterates. No statement names a step count,
an estimate, a machine word or a decimal. Its 71 constants pass the six kernels and `leanchecker`
(`kernels-sqrt.json`).

The module was written by the build team, which knew both tasks when it chose what to include.
The task-specific parts of both reference proofs are not in it: the power-of-two estimate, the
error recurrence `s / 2^k + 2` to `s / 2^(2k+1) + 2`, the count of seven steps, the 256-iteration
loop, the `BitVec` and decimal range arguments. A gap between the arms, if one is measured, is the
contribution of ProofForge including this module, and is reported that way.

The protected lemmas of each task (`spec/*/Lemmas.lean`: the port of `log2` is `Nat.log2`, a
Newton line is the step on values when it does not wrap, the decimal operations on non-negative
values, one iteration of the Vyper loop) are visible to both arms.

## For the measurement

Task ids: `rw-oz-sqrt`, `rw-vyper-sqrt`. Repair mode from `candidate/Solution.lean`, 5 runs per arm
per task, arms `alone` and `proofforge` as defined in the preregistration, $10 at list prices and
14,400 s per run, every final candidate judged by `bin/proofforge check`.

## Reproduce

```sh
bin/proofforge verify results/hard-task-1/passports/oz-reference.json --candidate realworld/tasks/rw-oz-sqrt/reference/SolutionA.lean
bin/proofforge verify results/hard-task-1/passports/vyper-reference.json --candidate realworld/tasks/rw-vyper-sqrt/reference/SolutionA.lean
bin/proofforge verify results/hard-task-1/passports/oz-start.json --candidate realworld/tasks/rw-oz-sqrt/candidate/Solution.lean
bin/proofforge verify results/hard-task-1/passports/vyper-start.json --candidate realworld/tasks/rw-vyper-sqrt/candidate/Solution.lean
.venv/bin/python harness/validate_task.py rw-oz-sqrt --cases 2000
.venv/bin/python harness/validate_task.py rw-vyper-sqrt --cases 2000
bin/proofforge spec-strength --verify results/hard-task-1/spec-strength/rw-oz-sqrt/report.json
bin/proofforge spec-strength --verify results/hard-task-1/spec-strength/rw-vyper-sqrt/report.json
.venv/bin/python harness/fin_kernels.py --modules ProofForgeFin.Sqrt
```
