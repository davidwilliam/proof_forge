# Specification strength: ledgers-log-b1

Reference `tasks/ledgers-log-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `871eec453fd0c9f3`; report `52d5f3d50d8bad26`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 16 | 16 | 11 | 0 | 11 | 0 | 0 | 0 | 0 | 0 | 11 of 11 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-DUPLICATE | 1 | 0 | tested |
| REQ-EFFECTS | 9 | 0 | tested |
| REQ-APPEND-ONLY | 0 | 0 | not shown |
| REQ-UNIQUE-IDS | 0 | 0 | not shown |
| REQ-NONNEGATIVE | 4 | 0 | tested |
| REQ-CONSISTENT | 9 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | equality | `appendEntry` | `=` replaced by `≠` | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS, REQ-NONNEGATIVE |  |
| M002 | arith | `appendEntry` | `+` replaced by `-` | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS, REQ-NONNEGATIVE |  |
| M003 | guard | `appendEntry` | condition `a = e.account` replaced by `false` | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS |  |
| M004 | guard | `appendEntry` | condition `a = e.account` replaced by `true` | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS, REQ-NONNEGATIVE |  |
| M005 | guard | `step` | condition `ValidEntry s e` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M006 | guard | `step` | condition `ValidEntry s e` replaced by `true` | killed by property tests | REQ-INVALID-NOOP, REQ-NONNEGATIVE |  |
| M007 | field | `appendEntry` | update of field `log` dropped | killed by property tests | REQ-CONSISTENT, REQ-DUPLICATE, REQ-EFFECTS |  |
| M008 | field | `appendEntry` | field read `s.log` replaced by `s.balance` | does not compile |  |  |
| M009 | field | `appendEntry` | update of field `balance` dropped | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS |  |
| M010 | field | `appendEntry` | field read `s.balance` replaced by `s.log` | does not compile |  |  |
| M011 | field | `appendEntry` | field read `e.account` replaced by `e.amount` | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS |  |
| M012 | field | `appendEntry` | field read `e.amount` replaced by `e.account` | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS |  |
| M013 | swap | `step` | arguments `s.log` and `e.id` of `receiptOf` swapped | does not compile |  |  |
| M014 | swap | `step` | arguments `s` and `e` of `ValidEntry` swapped | does not compile |  |  |
| M015 | swap | `step` | arguments `s` and `e` of `appendEntry` swapped | does not compile |  |  |
| M016 | constant | `appendEntry` | constant `0` replaced by `1` | killed by property tests | REQ-CONSISTENT, REQ-EFFECTS |  |
