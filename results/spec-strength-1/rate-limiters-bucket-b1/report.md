# Specification strength: rate-limiters-bucket-b1

Reference `tasks/rate-limiters-bucket-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `560a197a4f630790`; report `c3ce955a50905fd6`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 10 | 10 | 8 | 0 | 8 | 0 | 0 | 8 | 0 | 0 | 8 of 8 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 1 | kernel-checked |
| REQ-INVALID-NOOP | 1 | 1 | kernel-checked |
| REQ-ALLOW-IFF-SUFFICIENT | 2 | 1 | kernel-checked |
| REQ-TIME-MONOTONE | 3 | 2 | kernel-checked |
| REQ-REMAINING | 4 | 3 | kernel-checked |
| REQ-EFFECTS | 6 | 1 | kernel-checked |
| REQ-CAPACITY | 1 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | arith | `step` | `-` replaced by `+` | killed by property tests | REQ-CAPACITY, REQ-EFFECTS, REQ-REMAINING | REQ-REMAINING |
| M002 | guard | `step` | condition `Admissible s r` replaced by `true` | killed by property tests | REQ-ALLOW-IFF-SUFFICIENT, REQ-INVALID-NOOP, REQ-TIME-MONOTONE | REQ-INVALID-NOOP |
| M003 | guard | `step` | condition `Admissible s r` replaced by `false` | killed by property tests | REQ-ALLOW-IFF-SUFFICIENT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M004 | field | `step` | update of field `tokens` dropped | killed by property tests | REQ-EFFECTS, REQ-REMAINING | REQ-EFFECTS |
| M005 | field | `step` | field read `r.time` replaced by `r.cost` | killed by property tests | REQ-EFFECTS, REQ-REMAINING | REQ-REMAINING |
| M006 | field | `step` | field read `r.cost` replaced by `r.time` | killed by property tests | REQ-EFFECTS, REQ-REMAINING | REQ-REMAINING |
| M007 | field | `step` | update of field `last` dropped | killed by property tests | REQ-EFFECTS, REQ-TIME-MONOTONE | REQ-TIME-MONOTONE |
| M008 | field | `step` | field read `r.time` replaced by `r.cost` | killed by property tests | REQ-EFFECTS, REQ-TIME-MONOTONE | REQ-TIME-MONOTONE |
| M009 | swap | `step` | arguments `s` and `r` of `Admissible` swapped | does not compile |  |  |
| M010 | swap | `step` | arguments `s` and `r.time` of `refilled` swapped | does not compile |  |  |
