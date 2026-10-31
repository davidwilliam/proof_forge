# Specification strength: payout-flagship

Reference `formal/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `53e32ebeda25c170`; report `a7a9184445ff80f7`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 47 | 47 | 32 | 0 | 32 | 0 | 0 | 32 | 0 | 0 | 32 of 32 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 1 | kernel-checked |
| REQ-INVALID-NOOP | 1 | 1 | kernel-checked |
| REQ-AUTHORIZATION | 0 | 0 | not shown |
| REQ-EFFECTS | 9 | 9 | kernel-checked |
| REQ-IDEMPOTENCY | 2 | 1 | kernel-checked |
| REQ-NONNEGATIVE | 0 | 0 | not shown |
| REQ-FAIR-SHARES | 27 | 19 | kernel-checked |
| REQ-CONSERVATION | 24 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `newBalance` | floor division `/` replaced by ceiling division | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M002 | boundary | `payAll` | `<` replaced by `≤` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-CONSERVATION |
| M003 | equality | `adjust` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-FAIR-SHARES | REQ-EFFECTS |
| M004 | arith | `adjust` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS, REQ-FAIR-SHARES | REQ-EFFECTS |
| M005 | arith | `payAll` | `-` replaced by `+` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M006 | arith | `payAll` | `+` replaced by `-` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M007 | arith | `newBalance` | unary minus dropped | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS | REQ-EFFECTS |
| M008 | guard | `adjust` | condition `b = a` replaced by `false` | killed by property tests | REQ-EFFECTS, REQ-FAIR-SHARES | REQ-EFFECTS |
| M009 | guard | `adjust` | condition `b = a` replaced by `true` | killed by property tests | REQ-EFFECTS, REQ-FAIR-SHARES | REQ-EFFECTS |
| M010 | guard | `payAll` | condition `0 < extra` replaced by `false` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M011 | guard | `payAll` | condition `0 < extra` replaced by `true` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M012 | guard | `step` | condition `ValidPayout s r` replaced by `true` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M013 | guard | `step` | condition `ValidPayout s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M014 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M015 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M016 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M017 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M018 | field | `newBalance` | field read `r.recipients` replaced by `r.amount` | does not compile |  |  |
| M019 | field | `newBalance` | field read `r.recipients` replaced by `r.source` | does not compile |  |  |
| M020 | field | `newBalance` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-FAIR-SHARES | REQ-EFFECTS |
| M021 | field | `newBalance` | field read `r.source` replaced by `r.recipients` | does not compile |  |  |
| M022 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M023 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS | REQ-EFFECTS |
| M024 | field | `step` | update of field `balance` dropped | killed by property tests | REQ-EFFECTS, REQ-FAIR-SHARES | REQ-EFFECTS |
| M025 | field | `step` | update of field `applied` dropped | killed by property tests | REQ-IDEMPOTENCY | REQ-IDEMPOTENCY |
| M026 | swap | `payAll` | arguments `base` and `(extra - 1)` of `payAll` swapped | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M027 | swap | `payAll` | arguments `(extra - 1)` and `xs` of `payAll` swapped | does not compile |  |  |
| M028 | swap | `payAll` | operands of `-` swapped | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M029 | swap | `payAll` | arguments `xs` and `(adjust bal x (base + if 0 < extra then 1 else 0 : Nat))` of `payAll` swapped | does not compile |  |  |
| M030 | swap | `payAll` | arguments `bal` and `x` of `adjust` swapped | does not compile |  |  |
| M031 | swap | `payAll` | arguments `x` and `(base + if 0 < extra then 1 else 0 : Nat)` of `adjust` swapped | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-FAIR-SHARES | REQ-EFFECTS |
| M032 | swap | `payAll` | operands of `<` swapped | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M033 | swap | `newBalance` | arguments `(r.amount / n)` and `(r.amount % n)` of `payAll` swapped | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M034 | swap | `newBalance` | operands of `/` swapped | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M035 | swap | `newBalance` | arguments `(r.amount % n)` and `r.recipients` of `payAll` swapped | does not compile |  |  |
| M036 | swap | `newBalance` | operands of `%` swapped | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M037 | swap | `newBalance` | arguments `r.recipients` and `(adjust s.balance r.source (-(r.amount : Int)))` of `payAll` swapped | does not compile |  |  |
| M038 | swap | `newBalance` | arguments `s.balance` and `r.source` of `adjust` swapped | does not compile |  |  |
| M039 | swap | `newBalance` | arguments `r.source` and `(-(r.amount : Int))` of `adjust` swapped | does not compile |  |  |
| M040 | swap | `step` | arguments `s` and `r` of `ValidPayout` swapped | does not compile |  |  |
| M041 | swap | `step` | arguments `s` and `r` of `newBalance` swapped | does not compile |  |  |
| M042 | constant | `payAll` | constant `1` replaced by `2` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M043 | constant | `payAll` | constant `1` replaced by `0` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M044 | constant | `payAll` | constant `0` replaced by `1` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M045 | constant | `payAll` | constant `1` replaced by `0` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M046 | constant | `payAll` | constant `1` replaced by `2` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
| M047 | constant | `payAll` | constant `0` replaced by `1` | killed by property tests | REQ-CONSERVATION, REQ-FAIR-SHARES | REQ-FAIR-SHARES |
