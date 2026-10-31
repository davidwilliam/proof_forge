# Specification strength: permissions-workflow-b1

Reference `tasks/permissions-workflow-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `ebbc2f7f1d5d0c49`; report `1d4e9b6220c336fb`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | 9 | 5 | 0 | 5 | 0 | 0 | 0 | 0 | 0 | 5 of 5 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-AUTHORIZATION | 1 | 0 | tested |
| REQ-SINGLE-DOC | 0 | 0 | not shown |
| REQ-PUBLISHED-IMMUTABLE | 1 | 0 | tested |
| REQ-NO-UNPUBLISH | 1 | 0 | tested |
| REQ-EFFECTS | 3 | 0 | tested |
| REQ-AUDIT-APPEND-ONLY | 0 | 0 | not shown |
| REQ-AUDIT-CONSISTENT | 2 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | guard | `step` | condition `ValidRequest s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M002 | guard | `step` | condition `ValidRequest s r` replaced by `true` | killed by property tests | REQ-AUTHORIZATION, REQ-INVALID-NOOP, REQ-NO-UNPUBLISH, REQ-PUBLISHED-IMMUTABLE |  |
| M003 | field | `step` | update of field `status` dropped | killed by property tests | REQ-AUDIT-CONSISTENT, REQ-EFFECTS |  |
| M004 | field | `step` | update of field `content` dropped | killed by property tests | REQ-EFFECTS |  |
| M005 | field | `step` | update of field `audit` dropped | killed by property tests | REQ-AUDIT-CONSISTENT, REQ-EFFECTS |  |
| M006 | swap | `step` | arguments `s` and `r` of `ValidRequest` swapped | does not compile |  |  |
| M007 | swap | `step` | arguments `s` and `r` of `expectedStatus` swapped | does not compile |  |  |
| M008 | swap | `step` | arguments `s` and `r` of `expectedContent` swapped | does not compile |  |  |
| M009 | swap | `step` | arguments `s` and `r` of `expectedAudit` swapped | does not compile |  |  |
