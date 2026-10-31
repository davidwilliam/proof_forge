# Specification strength: payouts-weighted-b1

Reference `tasks/payouts-weighted-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `280e8cbd125fb4fb`; report `8562f0384a5b538c`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 80 | 80 | 47 | 0 | 46 | 0 | 0 | 0 | 0 | 1 | 46 of 47 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-AUTHORIZATION | 0 | 0 | not shown |
| REQ-EFFECTS | 10 | 0 | tested |
| REQ-IDEMPOTENCY | 2 | 0 | tested |
| REQ-NONNEGATIVE | 5 | 0 | tested |
| REQ-PRO-RATA-SHARES | 41 | 0 | tested |
| REQ-ROUNDING-BOUND | 19 | 0 | tested |
| REQ-CONSERVATION | 38 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `floorTotal` | floor division `/` replaced by ceiling division | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M002 | rounding | `payAll` | floor division `/` replaced by ceiling division | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M003 | boundary | `payAll` | `<` replaced by `≤` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M004 | equality | `adjust` | `=` replaced by `≠` | killed by property tests | REQ-EFFECTS, REQ-NONNEGATIVE, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M005 | arith | `adjust` | `+` replaced by `-` | killed by property tests | REQ-EFFECTS, REQ-NONNEGATIVE, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M006 | arith | `floorTotal` | `*` replaced by `/` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M007 | arith | `floorTotal` | `+` replaced by `-` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M008 | arith | `payAll` | `-` replaced by `+` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M009 | arith | `payAll` | `*` replaced by `/` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M010 | arith | `payAll` | `+` replaced by `-` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M011 | arith | `newBalance` | `-` replaced by `+` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M012 | arith | `newBalance` | unary minus dropped | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS |  |
| M013 | guard | `adjust` | condition `b = a` replaced by `false` | killed by property tests | REQ-EFFECTS, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M014 | guard | `adjust` | condition `b = a` replaced by `true` | killed by property tests | REQ-EFFECTS, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M015 | guard | `payAll` | condition `0 < extra` replaced by `false` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M016 | guard | `payAll` | condition `0 < extra` replaced by `true` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M017 | guard | `step` | condition `ValidPayout s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M018 | guard | `step` | condition `ValidPayout s r` replaced by `true` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-NONNEGATIVE |  |
| M019 | field | `payAll` | field read `ws.tail` replaced by `ws.headD` | does not compile |  |  |
| M020 | field | `payAll` | field read `ws.headD` replaced by `ws.tail` | does not compile |  |  |
| M021 | field | `newBalance` | field read `r.weights` replaced by `r.amount` | does not compile |  |  |
| M022 | field | `newBalance` | field read `r.weights` replaced by `r.source` | does not compile |  |  |
| M023 | field | `newBalance` | field read `r.weights` replaced by `r.recipients` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M024 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M025 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M026 | field | `newBalance` | field read `r.amount` replaced by `r.weights` | does not compile |  |  |
| M027 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M028 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M029 | field | `newBalance` | field read `r.amount` replaced by `r.weights` | does not compile |  |  |
| M030 | field | `newBalance` | field read `r.weights` replaced by `r.amount` | does not compile |  |  |
| M031 | field | `newBalance` | field read `r.weights` replaced by `r.source` | does not compile |  |  |
| M032 | field | `newBalance` | field read `r.weights` replaced by `r.recipients` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M033 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M034 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M035 | field | `newBalance` | field read `r.amount` replaced by `r.weights` | does not compile |  |  |
| M036 | field | `newBalance` | field read `r.recipients` replaced by `r.source` | does not compile |  |  |
| M037 | field | `newBalance` | field read `r.recipients` replaced by `r.weights` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M038 | field | `newBalance` | field read `r.recipients` replaced by `r.amount` | does not compile |  |  |
| M039 | field | `newBalance` | field read `r.weights` replaced by `r.amount` | does not compile |  |  |
| M040 | field | `newBalance` | field read `r.weights` replaced by `r.recipients` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M041 | field | `newBalance` | field read `r.weights` replaced by `r.source` | does not compile |  |  |
| M042 | field | `newBalance` | field read `r.source` replaced by `r.weights` | does not compile |  |  |
| M043 | field | `newBalance` | field read `r.source` replaced by `r.recipients` | does not compile |  |  |
| M044 | field | `newBalance` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-NONNEGATIVE, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M045 | field | `newBalance` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-NONNEGATIVE |  |
| M046 | field | `newBalance` | field read `r.amount` replaced by `r.weights` | does not compile |  |  |
| M047 | field | `newBalance` | field read `r.amount` replaced by `r.recipients` | does not compile |  |  |
| M048 | field | `step` | update of field `balance` dropped | killed by property tests | REQ-EFFECTS, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M049 | field | `step` | update of field `applied` dropped | killed by property tests | REQ-IDEMPOTENCY |  |
| M050 | swap | `floorTotal` | operands of `/` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M051 | swap | `floorTotal` | arguments `A` and `W` of `floorTotal` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M052 | swap | `floorTotal` | arguments `W` and `ws` of `floorTotal` swapped | does not compile |  |  |
| M053 | swap | `payAll` | arguments `A` and `W` of `payAll` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M054 | swap | `payAll` | arguments `W` and `(extra - 1)` of `payAll` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M055 | swap | `payAll` | arguments `(extra - 1)` and `xs` of `payAll` swapped | does not compile |  |  |
| M056 | swap | `payAll` | operands of `-` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M057 | swap | `payAll` | arguments `xs` and `ws.tail` of `payAll` swapped | does not compile |  |  |
| M058 | swap | `payAll` | arguments `ws.tail` and `(adjust bal x ((A * ws.headD 0 / W + if 0 < extra then 1 ...` of `payAll` swapped | does not compile |  |  |
| M059 | swap | `payAll` | arguments `bal` and `x` of `adjust` swapped | does not compile |  |  |
| M060 | swap | `payAll` | arguments `x` and `((A * ws.headD 0 / W + if 0 < extra then 1 else 0 : Nat) ...` of `adjust` swapped | does not compile |  |  |
| M061 | swap | `payAll` | operands of `<` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M062 | swap | `newBalance` | arguments `r.amount` and `W` of `floorTotal` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M063 | swap | `newBalance` | arguments `W` and `r.weights` of `floorTotal` swapped | does not compile |  |  |
| M064 | swap | `newBalance` | arguments `r.amount` and `W` of `payAll` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M065 | swap | `newBalance` | arguments `W` and `extra` of `payAll` swapped | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M066 | swap | `newBalance` | arguments `extra` and `r.recipients` of `payAll` swapped | does not compile |  |  |
| M067 | swap | `newBalance` | arguments `r.recipients` and `r.weights` of `payAll` swapped | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M068 | swap | `newBalance` | arguments `r.weights` and `(adjust s.balance r.source (-(r.amount : Int)))` of `payAll` swapped | does not compile |  |  |
| M069 | swap | `newBalance` | arguments `s.balance` and `r.source` of `adjust` swapped | does not compile |  |  |
| M070 | swap | `newBalance` | arguments `r.source` and `(-(r.amount : Int))` of `adjust` swapped | does not compile |  |  |
| M071 | swap | `step` | arguments `s` and `r` of `ValidPayout` swapped | does not compile |  |  |
| M072 | swap | `step` | arguments `s` and `r` of `newBalance` swapped | does not compile |  |  |
| M073 | constant | `floorTotal` | constant `0` replaced by `1` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M074 | constant | `payAll` | constant `1` replaced by `0` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M075 | constant | `payAll` | constant `1` replaced by `2` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M076 | constant | `payAll` | constant `0` replaced by `1` | survived, no observed difference |  |  |
| M077 | constant | `payAll` | constant `0` replaced by `1` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M078 | constant | `payAll` | constant `1` replaced by `0` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |
| M079 | constant | `payAll` | constant `1` replaced by `2` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES, REQ-ROUNDING-BOUND |  |
| M080 | constant | `payAll` | constant `0` replaced by `1` | killed by property tests | REQ-CONSERVATION, REQ-PRO-RATA-SHARES |  |

## Survivors

### M076: survived, no observed difference

constant `0` replaced by `1` in `payAll` (line 29); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -28,3 +28,3 @@
       payAll A W (extra - 1) xs ws.tail
-        (adjust bal x ((A * ws.headD 0 / W + if 0 < extra then 1 else 0 : Nat) : Int))
+        (adjust bal x ((A * ws.headD 1 / W + if 0 < extra then 1 else 0 : Nat) : Int))
 
```

