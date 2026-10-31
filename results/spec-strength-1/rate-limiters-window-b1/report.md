# Specification strength: rate-limiters-window-b1

Reference `tasks/rate-limiters-window-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `e666fa0e4756130a`; report `6f818a87feb22b58`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 20 | 20 | 8 | 0 | 8 | 0 | 0 | 0 | 0 | 0 | 8 of 8 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-ISOLATION | 3 | 0 | tested |
| REQ-RESET | 5 | 0 | tested |
| REQ-EFFECTS | 6 | 0 | tested |
| REQ-WINDOW-BOUND | 5 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `instDecidableAdmits` | `≤` replaced by `<` | does not compile |  |  |
| M002 | boundary | `instDecidableAdmits` | `<` replaced by `≤` | does not compile |  |  |
| M003 | equality | `touch` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-ISOLATION, REQ-RESET, REQ-WINDOW-BOUND |  |
| M004 | logic | `instDecidableAdmits` | `∧` replaced by `∨` | does not compile |  |  |
| M005 | drop-conjunct | `instDecidableAdmits` | conjunct `c.start ≤ t` replaced by `True` | does not compile |  |  |
| M006 | drop-conjunct | `instDecidableAdmits` | conjunct `windowCount s c t < s.limit` replaced by `True` | does not compile |  |  |
| M007 | guard | `touch` | condition `c.id = r.client` replaced by `true` | killed by property tests | REQ-EFFECTS, REQ-ISOLATION, REQ-WINDOW-BOUND |  |
| M008 | guard | `touch` | condition `c.id = r.client` replaced by `false` | killed by property tests | REQ-EFFECTS, REQ-RESET |  |
| M009 | guard | `step` | condition `Admissible s r` replaced by `true` | killed by property tests | REQ-INVALID-NOOP, REQ-WINDOW-BOUND |  |
| M010 | guard | `step` | condition `Admissible s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M011 | field | `touch` | field read `r.client` replaced by `r.time` | killed by property tests | REQ-EFFECTS, REQ-ISOLATION, REQ-RESET, REQ-WINDOW-BOUND |  |
| M012 | field | `touch` | field read `r.time` replaced by `r.client` | killed by property tests | REQ-EFFECTS, REQ-RESET, REQ-WINDOW-BOUND |  |
| M013 | field | `step` | update of field `clients` dropped | killed by property tests | REQ-EFFECTS, REQ-RESET |  |
| M014 | swap | `instDecidableAdmits` | operands of `≤` swapped | does not compile |  |  |
| M015 | swap | `instDecidableAdmits` | arguments `s` and `c` of `windowCount` swapped | does not compile |  |  |
| M016 | swap | `instDecidableAdmits` | arguments `c` and `t` of `windowCount` swapped | does not compile |  |  |
| M017 | swap | `touch` | arguments `s` and `c` of `advance` swapped | does not compile |  |  |
| M018 | swap | `touch` | arguments `c` and `r.time` of `advance` swapped | does not compile |  |  |
| M019 | swap | `step` | arguments `s` and `r` of `Admissible` swapped | does not compile |  |  |
| M020 | swap | `step` | arguments `s` and `r` of `touch` swapped | does not compile |  |  |
