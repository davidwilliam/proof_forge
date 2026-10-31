# Specification strength: permissions-grants-b1

Reference `tasks/permissions-grants-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `b9422a8b69025c85`; report `632dc779262971a2`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 22 | 22 | 11 | 0 | 11 | 0 | 0 | 0 | 0 | 0 | 11 of 11 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-AUTHORIZATION | 1 | 0 | tested |
| REQ-NO-SELF-GRANT | 1 | 0 | tested |
| REQ-OTHERS-UNCHANGED | 6 | 0 | tested |
| REQ-EFFECTS | 5 | 0 | tested |
| REQ-IDEMPOTENCY | 6 | 0 | tested |
| REQ-LAST-ADMIN | 6 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | equality | `setGrant` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-IDEMPOTENCY, REQ-OTHERS-UNCHANGED |  |
| M002 | equality | `setGrant` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-IDEMPOTENCY, REQ-LAST-ADMIN, REQ-OTHERS-UNCHANGED |  |
| M003 | equality | `step` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-IDEMPOTENCY |  |
| M004 | logic | `setGrant` | `∧` replaced by `∨` | killed by property tests | REQ-LAST-ADMIN, REQ-OTHERS-UNCHANGED |  |
| M005 | drop-conjunct | `setGrant` | conjunct `v = u` replaced by `True` | killed by property tests | REQ-LAST-ADMIN, REQ-OTHERS-UNCHANGED |  |
| M006 | drop-conjunct | `setGrant` | conjunct `p = q` replaced by `True` | killed by property tests | REQ-LAST-ADMIN, REQ-OTHERS-UNCHANGED |  |
| M007 | guard | `setGrant` | condition `v = u ∧ p = q` replaced by `true` | killed by property tests | REQ-LAST-ADMIN, REQ-OTHERS-UNCHANGED |  |
| M008 | guard | `setGrant` | condition `v = u ∧ p = q` replaced by `false` | killed by property tests | REQ-EFFECTS, REQ-IDEMPOTENCY |  |
| M009 | guard | `step` | condition `ValidCommand s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M010 | guard | `step` | condition `ValidCommand s r` replaced by `true` | killed by property tests | REQ-AUTHORIZATION, REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LAST-ADMIN, REQ-NO-SELF-GRANT |  |
| M011 | field | `step` | update of field `has` dropped | killed by property tests | REQ-EFFECTS, REQ-IDEMPOTENCY |  |
| M012 | field | `step` | field read `r.target` replaced by `r.op` | does not compile |  |  |
| M013 | field | `step` | field read `r.target` replaced by `r.role` | does not compile |  |  |
| M014 | field | `step` | field read `r.role` replaced by `r.op` | does not compile |  |  |
| M015 | field | `step` | field read `r.role` replaced by `r.target` | does not compile |  |  |
| M016 | field | `step` | field read `r.op` replaced by `r.target` | does not compile |  |  |
| M017 | field | `step` | field read `r.op` replaced by `r.role` | does not compile |  |  |
| M018 | swap | `setGrant` | arguments `v` and `p` of `has` swapped | does not compile |  |  |
| M019 | swap | `step` | arguments `s` and `r` of `ValidCommand` swapped | does not compile |  |  |
| M020 | swap | `step` | arguments `s.has` and `r.target` of `setGrant` swapped | does not compile |  |  |
| M021 | swap | `step` | arguments `r.target` and `r.role` of `setGrant` swapped | does not compile |  |  |
| M022 | swap | `step` | arguments `r.role` and `(decide (r.op = .grant))` of `setGrant` swapped | does not compile |  |  |
