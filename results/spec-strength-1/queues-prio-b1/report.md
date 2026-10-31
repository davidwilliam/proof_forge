# Specification strength: queues-prio-b1

Reference `tasks/queues-prio-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `eb5618b49e88196a`; report `509aebf29c9e4585`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 11 | 11 | 8 | 0 | 8 | 0 | 0 | 0 | 0 | 0 | 8 of 8 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-CAPACITY | 1 | 0 | tested |
| REQ-POP-MIN | 1 | 0 | tested |
| REQ-SORTED | 3 | 0 | tested |
| REQ-INSERT-EFFECTS | 5 | 0 | tested |
| REQ-POP-EFFECTS | 1 | 0 | tested |
| REQ-FIFO-TIES | 6 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `ins` | `<` replaced by `≤` | killed by property tests | REQ-FIFO-TIES, REQ-INSERT-EFFECTS |  |
| M002 | guard | `ins` | condition `e.prio < x.prio` replaced by `true` | killed by property tests | REQ-FIFO-TIES, REQ-INSERT-EFFECTS, REQ-SORTED |  |
| M003 | guard | `ins` | condition `e.prio < x.prio` replaced by `false` | killed by property tests | REQ-INSERT-EFFECTS, REQ-SORTED |  |
| M004 | guard | `step` | condition `Valid s op` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M005 | guard | `step` | condition `Valid s op` replaced by `true` | killed by property tests | REQ-CAPACITY, REQ-FIFO-TIES, REQ-INVALID-NOOP, REQ-POP-MIN |  |
| M006 | field | `step` | update of field `items` dropped | killed by property tests | REQ-FIFO-TIES, REQ-INSERT-EFFECTS |  |
| M007 | field | `step` | update of field `items` dropped | killed by property tests | REQ-FIFO-TIES, REQ-POP-EFFECTS |  |
| M008 | swap | `ins` | operands of `<` swapped | killed by property tests | REQ-FIFO-TIES, REQ-INSERT-EFFECTS, REQ-SORTED |  |
| M009 | swap | `ins` | arguments `e` and `xs` of `ins` swapped | does not compile |  |  |
| M010 | swap | `step` | arguments `s` and `op` of `Valid` swapped | does not compile |  |  |
| M011 | swap | `step` | arguments `e` and `s.items` of `ins` swapped | does not compile |  |  |
