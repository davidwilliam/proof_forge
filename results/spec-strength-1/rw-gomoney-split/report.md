# Specification strength: rw-gomoney-split

Reference `realworld/tasks/rw-gomoney-split/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `20cb301dda09ad4b`; report `f77980b73cf4d5cd`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 19 | 19 | 16 | 0 | 16 | 0 | 0 | 16 | 0 | 0 | 16 of 16 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 3 | 3 | kernel-checked |
| REQ-INVALID-FAILS | 2 | 2 | kernel-checked |
| REQ-ONE-SHARE-EACH | 0 | 0 | not shown |
| REQ-CONSERVATION | 13 | 9 | kernel-checked |
| REQ-WITHIN-ONE-UNIT | 9 | 1 | kernel-checked |
| REQ-SIGN | 9 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `shares` | floor division `/` replaced by ceiling division | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M002 | boundary | `shares` | `<` replaced by `≤` | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-WITHIN-ONE-UNIT |
| M003 | boundary | `split` | `<` replaced by `≤` | killed by property tests | REQ-CONSERVATION, REQ-INVALID-FAILS | REQ-INVALID-FAILS |
| M004 | arith | `shares` | `+` replaced by `-` | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-SIGN |
| M005 | guard | `shares` | condition `i < (amount % (n : Int)).toNat` replaced by `true` | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M006 | guard | `shares` | condition `i < (amount % (n : Int)).toNat` replaced by `false` | killed by property tests | REQ-CONSERVATION | REQ-CONSERVATION |
| M007 | guard | `split` | condition `0 < n` replaced by `true` | killed by property tests | REQ-CONSERVATION, REQ-INVALID-FAILS | REQ-INVALID-FAILS |
| M008 | guard | `split` | condition `0 < n` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M009 | field | `shares` | projection `.map` replaced by `.toNat` | does not compile |  |  |
| M010 | field | `shares` | projection `.toNat` replaced by `.map` | does not compile |  |  |
| M011 | swap | `shares` | operands of `/` swapped | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M012 | swap | `shares` | operands of `<` swapped | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M013 | swap | `shares` | operands of `%` swapped | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M014 | swap | `split` | operands of `<` swapped | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M015 | swap | `split` | arguments `amount` and `n` of `shares` swapped | does not compile |  |  |
| M016 | constant | `shares` | constant `1` replaced by `2` | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M017 | constant | `shares` | constant `1` replaced by `0` | killed by property tests | REQ-CONSERVATION | REQ-CONSERVATION |
| M018 | constant | `shares` | constant `0` replaced by `1` | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M019 | constant | `split` | constant `0` replaced by `1` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
