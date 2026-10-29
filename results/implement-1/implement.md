# Implement mode on the E1 test tasks

Arm: the E1 A1 configuration (muse-spark-1.3-contributor, no planner) with `--mode implement`. Each run starts from a stub generated from the locked challenge: the required definition keeps its exact signature with a placeholder body that rejects every input and returns the state unchanged, and every required theorem is `sorry`. The brief asks for an implementation of the definition from the spec, which it names as the source of truth; the issue report, the buggy candidate and the reference solutions are not used. Per-run caps: $3 at standard list prices and 3600 s. A run is accepted when the official judge accepts its final candidate and the binary rebuilt from it passes 2000 property cases (seed 1), the E1 evaluator unchanged. One run per task, no reruns.

The 30 tasks are 9 base specifications with 3 or 4 variants each. Variants differ only in their buggy candidate and issue report, so in implement mode they share the starting stub and the prompt: the variants of a base are repeated trials of the same problem, not independent problems. Every specification states its validity condition and the required effect on the state as Lean predicates, so implementing from it means turning a precise formal specification into executable code; this does not measure writing code from an informal description.

Accepted: 30 of 30.

Repair mode, same arm, same tasks (`results/e1-test-1`, A1): 30 of 30. Paired: 30 accepted in both modes, 0 only in implement mode, 0 only in repair mode (McNemar exact p = 1.0000).

| | Implement mode | Repair mode (E1 A1) |
|---|---|---|
| Accepted | 30 of 30 | 30 of 30 |
| Total at standard list prices | $24.99 | $18.35 |
| Total charged (Contributor tier) | $1.39 | $1.01 |
| List $ per accepted run | 0.83 | 0.61 |
| Budget stops (dollars / wall clock) | 0 / 0 | |
| Mean seconds per run | 1275 | 862 |

The most expensive run used $2.56 of the $3 cap and the longest 3075 s of 3600 s. In 25 of 30 runs the model's first call of the property tests passed (the harness's own test call on the stub is not counted); in 8 runs the per-obligation proof phases did not finish every theorem and the closing whole-file phase completed the proofs (ledgers-log-b4, queues-bounded-b2, queues-prio-b1, queues-prio-b3, queues-ring-b1, queues-ring-b2, queues-ring-b3, queues-ring-b4).

Conditions that differ from the repair run: the judge image is the current pinned build (`sha256:7d5b583a0fe4c4cef9d78f4a5b0c929da97d6ec20f11cfc6b6806e005f76e18a`), not the one E1 used (`sha256:ca2d62230dc81631cf1d394f999eee0e3c692b823d16083702971e5046066b19`); the Lean toolchain is the same v4.35.0. The batch ran in the main checkout, where other work could use the host's shared container slots, so Lean calls may have waited longer than in E1; no run reached either cap.

## Per family

| Family | Implement accepted | Repair (E1 A1) completed | List $ | Charged $ |
|---|---|---|---|---|
| ledgers | 10 of 10 | 10 of 10 | 6.95 | 0.41 |
| permissions | 10 of 10 | 10 of 10 | 5.70 | 0.32 |
| queues | 10 of 10 | 10 of 10 | 12.34 | 0.67 |

## Per base specification

| Base | Implement accepted | Repair (E1 A1) completed |
|---|---|---|
| ledgers-journal | 3 of 3 | 3 of 3 |
| ledgers-log | 4 of 4 | 4 of 4 |
| ledgers-reversal | 3 of 3 | 3 of 3 |
| permissions-acl | 3 of 3 | 3 of 3 |
| permissions-grants | 4 of 4 | 4 of 4 |
| permissions-workflow | 3 of 3 | 3 of 3 |
| queues-bounded | 3 of 3 | 3 of 3 |
| queues-prio | 3 of 3 | 3 of 3 |
| queues-ring | 4 of 4 | 4 of 4 |

## Per task

| Task | Result | List $ | Charged $ | Seconds | Stop |
|---|---|---|---|---|---|
| ledgers-journal-b1 | accepted | 0.28 | 0.0155 | 559 | - |
| ledgers-journal-b2 | accepted | 0.37 | 0.0200 | 801 | - |
| ledgers-journal-b3 | accepted | 0.48 | 0.0259 | 1286 | - |
| ledgers-log-b1 | accepted | 0.54 | 0.0305 | 1367 | - |
| ledgers-log-b2 | accepted | 0.23 | 0.0131 | 656 | - |
| ledgers-log-b3 | accepted | 0.19 | 0.0106 | 474 | - |
| ledgers-log-b4 | accepted | 0.38 | 0.0203 | 864 | - |
| ledgers-reversal-b1 | accepted | 1.78 | 0.1076 | 2697 | - |
| ledgers-reversal-b2 | accepted | 1.41 | 0.0868 | 2017 | - |
| ledgers-reversal-b3 | accepted | 1.29 | 0.0755 | 1982 | - |
| permissions-acl-b1 | accepted | 0.80 | 0.0475 | 1532 | - |
| permissions-acl-b2 | accepted | 0.84 | 0.0465 | 1473 | - |
| permissions-acl-b3 | accepted | 0.73 | 0.0411 | 1216 | - |
| permissions-grants-b1 | accepted | 0.41 | 0.0221 | 823 | - |
| permissions-grants-b2 | accepted | 0.57 | 0.0313 | 1164 | - |
| permissions-grants-b3 | accepted | 0.29 | 0.0161 | 559 | - |
| permissions-grants-b4 | accepted | 0.39 | 0.0214 | 740 | - |
| permissions-workflow-b1 | accepted | 0.88 | 0.0478 | 1566 | - |
| permissions-workflow-b2 | accepted | 0.47 | 0.0263 | 738 | - |
| permissions-workflow-b3 | accepted | 0.32 | 0.0177 | 454 | - |
| queues-bounded-b1 | accepted | 0.12 | 0.0072 | 204 | - |
| queues-bounded-b2 | accepted | 0.34 | 0.0182 | 498 | - |
| queues-bounded-b3 | accepted | 0.11 | 0.0061 | 200 | - |
| queues-prio-b1 | accepted | 2.14 | 0.1182 | 2419 | - |
| queues-prio-b2 | accepted | 0.96 | 0.0506 | 1313 | - |
| queues-prio-b3 | accepted | 2.36 | 0.1304 | 2359 | - |
| queues-ring-b1 | accepted | 0.83 | 0.0443 | 1050 | - |
| queues-ring-b2 | accepted | 2.56 | 0.1409 | 3075 | - |
| queues-ring-b3 | accepted | 1.63 | 0.0857 | 2342 | - |
| queues-ring-b4 | accepted | 1.29 | 0.0660 | 1824 | - |

## Runs not accepted

None.

## Coverage

Batch spend at list prices: $24.99. Every task ran. Interrupted runs set aside: 0.
