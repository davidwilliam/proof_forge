# Specification strength: ledgers-journal-b1

Reference `tasks/ledgers-journal-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `62559f1297478a8a`; report `fbe97dac08e2da6d`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 17 | 17 | 8 | 0 | 8 | 0 | 0 | 8 | 0 | 0 | 8 of 8 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 1 | kernel-checked |
| REQ-INVALID-NOOP | 1 | 1 | kernel-checked |
| REQ-KNOWN-ACCOUNTS | 1 | 0 | tested |
| REQ-BALANCED | 1 | 1 | kernel-checked |
| REQ-EFFECTS | 5 | 5 | kernel-checked |
| REQ-IDEMPOTENCY | 2 | 1 | kernel-checked |
| REQ-TRIAL-BALANCE | 0 | 0 | not shown |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | equality | `adjust` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M002 | arith | `adjust` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M003 | guard | `adjust` | condition `b = a` replaced by `false` | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M004 | guard | `adjust` | condition `b = a` replaced by `true` | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M005 | guard | `step` | condition `ValidEntry s e` replaced by `true` | killed by property tests | REQ-BALANCED, REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-KNOWN-ACCOUNTS | REQ-INVALID-NOOP |
| M006 | guard | `step` | condition `ValidEntry s e` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M007 | field | `step` | update of field `balance` dropped | killed by property tests | REQ-EFFECTS | REQ-EFFECTS |
| M008 | field | `step` | field read `e.lines` replaced by `e.id` | does not compile |  |  |
| M009 | field | `step` | field read `s.balance` replaced by `s.posted` | does not compile |  |  |
| M010 | field | `step` | update of field `posted` dropped | killed by property tests | REQ-IDEMPOTENCY | REQ-IDEMPOTENCY |
| M011 | field | `step` | field read `e.id` replaced by `e.lines` | does not compile |  |  |
| M012 | field | `step` | field read `s.posted` replaced by `s.balance` | does not compile |  |  |
| M013 | swap | `postLines` | arguments `ls` and `(adjust bal l.1 l.2)` of `postLines` swapped | does not compile |  |  |
| M014 | swap | `postLines` | arguments `bal` and `l.1` of `adjust` swapped | does not compile |  |  |
| M015 | swap | `postLines` | arguments `l.1` and `l.2` of `adjust` swapped | does not compile |  |  |
| M016 | swap | `step` | arguments `s` and `e` of `ValidEntry` swapped | does not compile |  |  |
| M017 | swap | `step` | arguments `e.lines` and `s.balance` of `postLines` swapped | does not compile |  |  |
