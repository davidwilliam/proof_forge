# Specification strength: payouts-fee-b1

Reference `tasks/payouts-fee-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `7005e80e81dde232`; report `2db563903847a276`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 50 | 50 | 28 | 0 | 28 | 0 | 0 | 0 | 0 | 0 | 28 of 28 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-AUTHORIZATION | 0 | 0 | not shown |
| REQ-EFFECTS | 9 | 0 | tested |
| REQ-IDEMPOTENCY | 2 | 0 | tested |
| REQ-NONNEGATIVE | 5 | 0 | tested |
| REQ-EQUAL-SHARES | 21 | 0 | tested |
| REQ-FEE-COLLECTED | 21 | 0 | tested |
| REQ-CONSERVATION | 14 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `newBalance` | floor division `/` replaced by ceiling division | killed by property tests | REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M002 | rounding | `newBalance` | floor division `/` replaced by ceiling division | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES |  |
| M003 | equality | `adjust` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED, REQ-NONNEGATIVE |  |
| M004 | arith | `adjust` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED, REQ-NONNEGATIVE |  |
| M005 | arith | `newBalance` | `*` replaced by `/` | killed by property tests | REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M006 | arith | `newBalance` | `-` replaced by `+` | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M007 | arith | `newBalance` | unary minus dropped | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS |  |
| M008 | arith | `newBalance` | `+` replaced by `-` | killed by property tests | REQ-CONSERVATION, REQ-FEE-COLLECTED |  |
| M009 | guard | `adjust` | condition `b = a` replaced by `false` | killed by property tests | REQ-EFFECTS, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M010 | guard | `adjust` | condition `b = a` replaced by `true` | killed by property tests | REQ-EFFECTS, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M011 | guard | `step` | condition `ValidPayout s r` replaced by `true` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-NONNEGATIVE |  |
| M012 | guard | `step` | condition `ValidPayout s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M013 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M014 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M015 | field | `newBalance` | field read `s.feeBps` replaced by `s.balance` | does not compile |  |  |
| M016 | field | `newBalance` | field read `s.feeBps` replaced by `s.feeAccount` | killed by property tests | REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M017 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M018 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M019 | field | `newBalance` | field read `r.recipients` replaced by `r.amount` | does not compile |  |  |
| M020 | field | `newBalance` | field read `r.recipients` replaced by `r.source` | does not compile |  |  |
| M021 | field | `newBalance` | field read `s.balance` replaced by `s.feeAccount` | does not compile |  |  |
| M022 | field | `newBalance` | field read `s.balance` replaced by `s.feeBps` | does not compile |  |  |
| M023 | field | `newBalance` | field read `r.source` replaced by `r.recipients` | does not compile |  |  |
| M024 | field | `newBalance` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED, REQ-NONNEGATIVE |  |
| M025 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-NONNEGATIVE |  |
| M026 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M027 | field | `newBalance` | field read `s.feeAccount` replaced by `s.feeBps` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M028 | field | `newBalance` | field read `s.feeAccount` replaced by `s.balance` | does not compile |  |  |
| M029 | field | `step` | update of field `balance` dropped | killed by property tests | REQ-EFFECTS, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M030 | field | `step` | update of field `applied` dropped | killed by property tests | REQ-IDEMPOTENCY |  |
| M031 | swap | `payEach` | arguments `amt` and `xs` of `payEach` swapped | does not compile |  |  |
| M032 | swap | `payEach` | arguments `xs` and `(adjust bal x amt)` of `payEach` swapped | does not compile |  |  |
| M033 | swap | `payEach` | arguments `bal` and `x` of `adjust` swapped | does not compile |  |  |
| M034 | swap | `payEach` | arguments `x` and `amt` of `adjust` swapped | does not compile |  |  |
| M035 | swap | `newBalance` | operands of `/` swapped | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M036 | swap | `newBalance` | operands of `-` swapped | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M037 | swap | `newBalance` | arguments `((net / n : Nat) : Int)` and `r.recipients` of `payEach` swapped | does not compile |  |  |
| M038 | swap | `newBalance` | operands of `/` swapped | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES |  |
| M039 | swap | `newBalance` | arguments `r.recipients` and `(adjust s.balance r.source (-(r.amount : Int)))` of `payEach` swapped | does not compile |  |  |
| M040 | swap | `newBalance` | arguments `s.balance` and `r.source` of `adjust` swapped | does not compile |  |  |
| M041 | swap | `newBalance` | arguments `r.source` and `(-(r.amount : Int))` of `adjust` swapped | does not compile |  |  |
| M042 | swap | `newBalance` | arguments `paid` and `s.feeAccount` of `adjust` swapped | does not compile |  |  |
| M043 | swap | `newBalance` | arguments `s.feeAccount` and `((fee + net % n : Nat) : Int)` of `adjust` swapped | does not compile |  |  |
| M044 | swap | `newBalance` | operands of `%` swapped | killed by property tests | REQ-CONSERVATION, REQ-FEE-COLLECTED |  |
| M045 | swap | `step` | arguments `s` and `r` of `ValidPayout` swapped | does not compile |  |  |
| M046 | swap | `step` | arguments `s` and `r` of `newBalance` swapped | does not compile |  |  |
| M047 | constant | `newBalance` | constant `10000` replaced by `100000` | killed by property tests | REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M048 | constant | `newBalance` | constant `10000` replaced by `10001` | killed by property tests | REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M049 | constant | `newBalance` | constant `10000` replaced by `1000` | killed by property tests | REQ-CONSERVATION, REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
| M050 | constant | `newBalance` | constant `10000` replaced by `9999` | killed by property tests | REQ-EQUAL-SHARES, REQ-FEE-COLLECTED |  |
