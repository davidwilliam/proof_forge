# Specification strength: ledgers-reversal-b1

Reference `tasks/ledgers-reversal-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `307ab4a11c8a5261`; report `c3f37c1a37d71e71`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 29 | 29 | 13 | 0 | 13 | 0 | 0 | 0 | 0 | 0 | 13 of 13 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-POST-SUCCEEDS | 1 | 0 | tested |
| REQ-REVERSE-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 2 | 0 | tested |
| REQ-POST-EFFECTS | 6 | 0 | tested |
| REQ-REVERSE-EFFECTS | 7 | 0 | tested |
| REQ-REVERSE-ONCE | 2 | 0 | tested |
| REQ-ROUNDTRIP | 11 | 0 | tested |
| REQ-TRIAL-BALANCE | 1 | 0 | tested |
| REQ-WELL-FORMED | 1 | 0 | tested |
| REQ-CONSISTENT | 11 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | equality | `adjust` | `=` replaced by `≠` | killed by property tests | REQ-CONSISTENT, REQ-POST-EFFECTS, REQ-REVERSE-EFFECTS, REQ-ROUNDTRIP |  |
| M002 | arith | `adjust` | `+` replaced by `-` | killed by property tests | REQ-CONSISTENT, REQ-POST-EFFECTS, REQ-REVERSE-EFFECTS, REQ-ROUNDTRIP |  |
| M003 | arith | `negate` | unary minus dropped | killed by property tests | REQ-CONSISTENT, REQ-REVERSE-EFFECTS, REQ-ROUNDTRIP |  |
| M004 | guard | `adjust` | condition `b = a` replaced by `true` | killed by property tests | REQ-CONSISTENT, REQ-POST-EFFECTS, REQ-REVERSE-EFFECTS, REQ-ROUNDTRIP |  |
| M005 | guard | `adjust` | condition `b = a` replaced by `false` | killed by property tests | REQ-CONSISTENT, REQ-POST-EFFECTS, REQ-REVERSE-EFFECTS, REQ-ROUNDTRIP |  |
| M006 | guard | `step` | condition `ValidPost s e` replaced by `true` | killed by property tests | REQ-CONSISTENT, REQ-INVALID-NOOP, REQ-ROUNDTRIP, REQ-TRIAL-BALANCE, REQ-WELL-FORMED |  |
| M007 | guard | `step` | condition `ValidPost s e` replaced by `false` | killed by property tests | REQ-POST-SUCCEEDS |  |
| M008 | guard | `step` | condition `i ∈ s.reversed` replaced by `true` | killed by property tests | REQ-REVERSE-SUCCEEDS, REQ-ROUNDTRIP |  |
| M009 | guard | `step` | condition `i ∈ s.reversed` replaced by `false` | killed by property tests | REQ-CONSISTENT, REQ-INVALID-NOOP, REQ-REVERSE-ONCE |  |
| M010 | field | `postState` | update of field `balance` dropped | killed by property tests | REQ-CONSISTENT, REQ-POST-EFFECTS, REQ-ROUNDTRIP |  |
| M011 | field | `postState` | field read `s.balance` replaced by `s.journal` | does not compile |  |  |
| M012 | field | `postState` | update of field `journal` dropped | killed by property tests | REQ-CONSISTENT, REQ-POST-EFFECTS, REQ-ROUNDTRIP |  |
| M013 | field | `postState` | field read `s.journal` replaced by `s.balance` | does not compile |  |  |
| M014 | field | `revState` | update of field `balance` dropped | killed by property tests | REQ-CONSISTENT, REQ-REVERSE-EFFECTS, REQ-ROUNDTRIP |  |
| M015 | field | `revState` | field read `s.balance` replaced by `s.reversed` | does not compile |  |  |
| M016 | field | `revState` | update of field `reversed` dropped | killed by property tests | REQ-CONSISTENT, REQ-REVERSE-EFFECTS, REQ-REVERSE-ONCE, REQ-ROUNDTRIP |  |
| M017 | field | `revState` | field read `s.reversed` replaced by `s.balance` | does not compile |  |  |
| M018 | field | `step` | field read `s.journal` replaced by `s.reversed` | does not compile |  |  |
| M019 | field | `step` | field read `s.reversed` replaced by `s.journal` | does not compile |  |  |
| M020 | swap | `postLines` | arguments `ls` and `(adjust bal l.1 l.2)` of `postLines` swapped | does not compile |  |  |
| M021 | swap | `postLines` | arguments `bal` and `l.1` of `adjust` swapped | does not compile |  |  |
| M022 | swap | `postLines` | arguments `l.1` and `l.2` of `adjust` swapped | does not compile |  |  |
| M023 | swap | `postState` | arguments `e.lines` and `s.balance` of `postLines` swapped | does not compile |  |  |
| M024 | swap | `revState` | arguments `(negate e.lines)` and `s.balance` of `postLines` swapped | does not compile |  |  |
| M025 | swap | `step` | arguments `s` and `e` of `ValidPost` swapped | does not compile |  |  |
| M026 | swap | `step` | arguments `s` and `e` of `postState` swapped | does not compile |  |  |
| M027 | swap | `step` | arguments `s.journal` and `i` of `findEntry` swapped | does not compile |  |  |
| M028 | swap | `step` | arguments `s` and `i` of `revState` swapped | does not compile |  |  |
| M029 | swap | `step` | arguments `i` and `e` of `revState` swapped | does not compile |  |  |
