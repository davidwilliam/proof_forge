# hard-task-1: two decisive tasks for Muse Code alone against Muse Code with ProofForge

Status: measured. The 20 preregistered runs (5 per arm per task) ran from 2026-10-31 20:48 to
2026-11-01 06:06 EDT with the arm code, tasks and library frozen in the addenda of
`PREREGISTRATION.md` (plan committed before anything was built, commit `54bf8cc`). Every final
candidate was judged again from the frozen commit and every Passport reproduced.

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

## Results

Primary outcome: VERIFIED by `bin/proofforge check` on the run's final candidate, judged again
outside the budget from commit `baa38a0` (`judged/<task>/<run>/passport.json`); all 20 Passports
reproduced by `bin/proofforge verify` (`judged/<task>/<run>/verify.txt`).

| Task | `alone` (Muse Code) | `proofforge` (Muse Code with ProofForge) | One-sided Fisher exact test |
|---|---|---|---|
| `rw-vyper-sqrt` | 2 of 5 | 5 of 5 | p = 0.083 |
| `rw-oz-sqrt` | 0 of 5 | 0 of 5 | p = 1 |
| Both tasks (secondary) | 2 of 10 | 5 of 10 | p = 0.175 |

Neither difference is significant at the preregistered alpha. On `rw-vyper-sqrt` the difference is
three; the preregistration states that 5 runs per arm reach p < 0.05 only with a difference of
four. No run was set aside and none was rerun.

| Task | Arm | List dollars | Per verified run | Dollars charged | Runs stopped by the $10 cap |
|---|---|---|---|---|---|
| `rw-vyper-sqrt` | `alone` | $45.88 | $22.94 | $1.47 | 3 of 5 |
| `rw-vyper-sqrt` | `proofforge` | $27.46 | $5.49 | $0.96 | 0 of 5 |
| `rw-oz-sqrt` | `alone` | $48.53 | no verified run | $1.82 | 5 of 5 |
| `rw-oz-sqrt` | `proofforge` | $46.06 | no verified run | $1.68 | 5 of 5 |

List dollars are the meter's charge at standard list prices, the quantity the cap applies to;
dollars charged are what the contributor tier billed.

Every run. "Proved in the last compiling version" counts the required theorems proved without
`sorry` in the last version of the run that built (`ledger.json`, `best_candidate`).

| Task | Run | Passport status | Final candidate | Proved in the last compiling version | List dollars | Wall time | Passport |
|---|---|---|---|---|---|---|---|
| `rw-vyper-sqrt` | alone-1 | UNRESOLVED | does not build | 2 of 5 | $9.87 | 20 min | `201ac173f19897c4` |
| `rw-vyper-sqrt` | alone-2 | VERIFIED | VERIFIED | 5 of 5 | $9.22 | 88 min | `60089873b4cf6bb1` |
| `rw-vyper-sqrt` | alone-3 | VERIFIED | VERIFIED | 5 of 5 | $7.72 | 47 min | `5dc7cffb5f27603b` |
| `rw-vyper-sqrt` | alone-4 | UNRESOLVED | builds with `sorry` | 0 of 5 | $9.53 | 57 min | `a615801f7172750a` |
| `rw-vyper-sqrt` | alone-5 | UNRESOLVED | builds with `sorry` | 2 of 5 | $9.55 | 38 min | `f72d8f9fd570f027` |
| `rw-vyper-sqrt` | proofforge-full-1 | VERIFIED | VERIFIED | 5 of 5 | $6.13 | 21 min | `4f5a15c052197dcf` |
| `rw-vyper-sqrt` | proofforge-full-2 | VERIFIED | VERIFIED | 5 of 5 | $4.79 | 35 min | `8184ef36fc5a13df` |
| `rw-vyper-sqrt` | proofforge-full-3 | VERIFIED | VERIFIED | 5 of 5 | $4.05 | 53 min | `869f15d14b4b02c2` |
| `rw-vyper-sqrt` | proofforge-full-4 | VERIFIED | VERIFIED | 5 of 5 | $7.19 | 74 min | `633c857097c55e39` |
| `rw-vyper-sqrt` | proofforge-full-5 | VERIFIED | VERIFIED | 5 of 5 | $5.29 | 14 min | `5e872b17ec048114` |
| `rw-oz-sqrt` | alone-1 | UNRESOLVED | does not build | 2 of 8 | $9.88 | 66 min | `302a022931ba0b27` |
| `rw-oz-sqrt` | alone-2 | UNRESOLVED | builds with `sorry` | 2 of 8 | $9.72 | 27 min | `397132f48046b65c` |
| `rw-oz-sqrt` | alone-3 | UNRESOLVED | builds with `sorry` | 4 of 8 | $9.67 | 152 min | `f275358143dc5978` |
| `rw-oz-sqrt` | alone-4 | UNRESOLVED | builds with `sorry` | 3 of 8 | $9.34 | 81 min | `fbe6aec72793478d` |
| `rw-oz-sqrt` | alone-5 | UNRESOLVED | builds with `sorry` | 2 of 8 | $9.93 | 65 min | `538cfc3f1ff595c7` |
| `rw-oz-sqrt` | proofforge-full-1 | UNRESOLVED | does not build | 0 of 8 | $9.22 | 83 min | `c03a03d3da4880e8` |
| `rw-oz-sqrt` | proofforge-full-2 | UNRESOLVED | builds with `sorry` | 3 of 8 | $9.62 | 79 min | `693932e21a84e16e` |
| `rw-oz-sqrt` | proofforge-full-3 | UNRESOLVED | does not build | 1 of 8 | $9.48 | 81 min | `4cdc7c9ed4b15710` |
| `rw-oz-sqrt` | proofforge-full-4 | UNRESOLVED | does not build | 0 of 8 | $8.38 | 37 min | `3cb06f5511259f98` |
| `rw-oz-sqrt` | proofforge-full-5 | UNRESOLVED | does not build | 1 of 8 | $9.36 | 102 min | `c98db7bd40193b3b` |

No unverified final candidate is REFUTED: each fails on proof (a `sorry` left or a build error),
not on a counterexample.

On `rw-oz-sqrt` no run of either arm proved REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS, REQ-MINT-FULL or
REQ-MINT-LIVE, the requirements that need the error bound of seven Newton steps from the
power-of-two estimate over every 256-bit input. The `alone` arm kept more required theorems proved
in its last compiling version (13 over five runs against 5), and four of the five `proofforge`
final candidates do not build: those runs ended at the cap in the middle of a restructuring of the
proof.

Run directories: `runs/<task>/<run>/` (`summary.json`, `ledger.json`, `final.lean`, the model calls
in `calls.jsonl` and `requests.jsonl`, the MCP calls in `mcp-calls.jsonl`, the Muse Code event
stream in `events.jsonl.gz`). Intermediate candidate versions are not committed.

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

## Reproduce

```sh
bin/proofforge verify results/hard-task-1/judged/rw-vyper-sqrt/proofforge-full-1/passport.json --candidate results/hard-task-1/runs/rw-vyper-sqrt/proofforge-full-1/final.lean
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
