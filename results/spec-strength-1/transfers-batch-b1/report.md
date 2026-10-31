# Specification strength: transfers-batch-b1

Reference `tasks/transfers-batch-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `02b006f24b96e2d4`; report `8c3ad46714085500`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 71 | 71 | 56 | 0 | 53 | 0 | 0 | 0 | 0 | 3 | 53 of 56 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 32 | 0 | tested |
| REQ-ATOMICITY | 39 | 0 | tested |
| REQ-SINGLE-LEG | 15 | 0 | tested |
| REQ-EFFECTS | 15 | 0 | tested |
| REQ-IDEMPOTENCY | 5 | 0 | tested |
| REQ-CONSERVATION | 8 | 0 | tested |
| REQ-LIMIT-EVERY-STEP | 16 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `admit` | `<` replaced by `≤` | killed by property tests | REQ-ATOMICITY |  |
| M002 | boundary | `admit` | `≤` replaced by `<` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M003 | equality | `adjust` | `=` replaced by `≠` | killed by property tests | REQ-ATOMICITY, REQ-EFFECTS, REQ-LIMIT-EVERY-STEP, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M004 | equality | `admit` | `!=` replaced by `==` | killed by property tests | REQ-ATOMICITY, REQ-VALID-SUCCEEDS |  |
| M005 | arith | `adjust` | `+` replaced by `-` | killed by property tests | REQ-ATOMICITY, REQ-EFFECTS, REQ-LIMIT-EVERY-STEP, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M006 | arith | `move` | unary minus dropped | killed by property tests | REQ-ATOMICITY, REQ-CONSERVATION, REQ-EFFECTS, REQ-SINGLE-LEG |  |
| M007 | arith | `admit` | `+` replaced by `-` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M008 | logic | `admit` | `&&` replaced by `//` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP |  |
| M009 | logic | `admit` | `&&` replaced by `//` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP |  |
| M010 | logic | `admit` | `&&` replaced by `//` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP |  |
| M011 | logic | `admit` | `&&` replaced by `//` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP |  |
| M012 | logic | `header` | `&&` replaced by `//` | killed by property tests | REQ-ATOMICITY, REQ-IDEMPOTENCY |  |
| M013 | logic | `header` | `&&` replaced by `//` | killed by property tests | REQ-ATOMICITY, REQ-IDEMPOTENCY |  |
| M014 | drop-conjunct | `admit` | conjunct `decide (0 < l.amount)` replaced by `true` | killed by property tests | REQ-ATOMICITY |  |
| M015 | drop-conjunct | `admit` | conjunct `l.source != l.target` replaced by `true` | killed by property tests | REQ-ATOMICITY |  |
| M016 | drop-conjunct | `admit` | conjunct `s.accounts.contains l.source` replaced by `true` | survived, no observed difference |  |  |
| M017 | drop-conjunct | `admit` | conjunct `s.accounts.contains l.target` replaced by `true` | killed by property tests | REQ-ATOMICITY |  |
| M018 | drop-conjunct | `admit` | conjunct `decide ((l.amount : Int) ≤ bal l.source + s.limit l.source)` replaced by `true` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP |  |
| M019 | drop-conjunct | `header` | conjunct `decide s.accounts.Nodup` replaced by `true` | survived, no observed difference |  |  |
| M020 | drop-conjunct | `header` | conjunct `!r.legs.isEmpty` replaced by `true` | killed by property tests | REQ-ATOMICITY |  |
| M021 | drop-conjunct | `header` | conjunct `!decide (r.batchId ∈ s.applied)` replaced by `true` | killed by property tests | REQ-ATOMICITY, REQ-IDEMPOTENCY |  |
| M022 | guard | `adjust` | condition `b = a` replaced by `false` | killed by property tests | REQ-ATOMICITY, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M023 | guard | `adjust` | condition `b = a` replaced by `true` | killed by property tests | REQ-ATOMICITY, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M024 | guard | `run` | condition `admit s bal l` replaced by `true` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP |  |
| M025 | guard | `run` | condition `admit s bal l` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M026 | guard | `step` | condition `header s r` replaced by `true` | killed by property tests | REQ-ATOMICITY, REQ-IDEMPOTENCY |  |
| M027 | guard | `step` | condition `header s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M028 | field | `move` | field read `l.source` replaced by `l.amount` | killed by property tests | REQ-ATOMICITY, REQ-CONSERVATION, REQ-EFFECTS, REQ-LIMIT-EVERY-STEP, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M029 | field | `move` | field read `l.source` replaced by `l.target` | killed by property tests | REQ-ATOMICITY, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M030 | field | `move` | field read `l.amount` replaced by `l.target` | killed by property tests | REQ-ATOMICITY, REQ-CONSERVATION, REQ-EFFECTS, REQ-LIMIT-EVERY-STEP, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M031 | field | `move` | field read `l.amount` replaced by `l.source` | killed by property tests | REQ-ATOMICITY, REQ-CONSERVATION, REQ-EFFECTS, REQ-LIMIT-EVERY-STEP, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M032 | field | `move` | field read `l.target` replaced by `l.source` | killed by property tests | REQ-ATOMICITY, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M033 | field | `move` | field read `l.target` replaced by `l.amount` | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M034 | field | `move` | field read `l.amount` replaced by `l.source` | killed by property tests | REQ-ATOMICITY, REQ-CONSERVATION, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M035 | field | `move` | field read `l.amount` replaced by `l.target` | killed by property tests | REQ-ATOMICITY, REQ-CONSERVATION, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M036 | field | `admit` | field read `l.amount` replaced by `l.source` | killed by property tests | REQ-ATOMICITY |  |
| M037 | field | `admit` | field read `l.amount` replaced by `l.target` | killed by property tests | REQ-ATOMICITY |  |
| M038 | field | `admit` | field read `l.source` replaced by `l.target` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M039 | field | `admit` | field read `l.source` replaced by `l.amount` | killed by property tests | REQ-ATOMICITY, REQ-VALID-SUCCEEDS |  |
| M040 | field | `admit` | field read `l.target` replaced by `l.source` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M041 | field | `admit` | field read `l.target` replaced by `l.amount` | killed by property tests | REQ-ATOMICITY, REQ-VALID-SUCCEEDS |  |
| M042 | field | `admit` | field read `l.source` replaced by `l.target` | survived, no observed difference |  |  |
| M043 | field | `admit` | field read `l.source` replaced by `l.amount` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M044 | field | `admit` | field read `l.target` replaced by `l.amount` | killed by property tests | REQ-ATOMICITY, REQ-VALID-SUCCEEDS |  |
| M045 | field | `admit` | field read `l.target` replaced by `l.source` | killed by property tests | REQ-ATOMICITY |  |
| M046 | field | `admit` | field read `l.amount` replaced by `l.target` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP, REQ-VALID-SUCCEEDS |  |
| M047 | field | `admit` | field read `l.amount` replaced by `l.source` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP, REQ-VALID-SUCCEEDS |  |
| M048 | field | `admit` | field read `l.source` replaced by `l.amount` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP, REQ-VALID-SUCCEEDS |  |
| M049 | field | `admit` | field read `l.source` replaced by `l.target` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP, REQ-VALID-SUCCEEDS |  |
| M050 | field | `admit` | field read `l.source` replaced by `l.amount` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M051 | field | `admit` | field read `l.source` replaced by `l.target` | killed by property tests | REQ-ATOMICITY, REQ-LIMIT-EVERY-STEP, REQ-VALID-SUCCEEDS |  |
| M052 | field | `step` | field read `s.balance` replaced by `s.applied` | does not compile |  |  |
| M053 | field | `step` | field read `r.legs` replaced by `r.batchId` | does not compile |  |  |
| M054 | field | `step` | update of field `balance` dropped | killed by property tests | REQ-EFFECTS, REQ-SINGLE-LEG |  |
| M055 | field | `step` | update of field `applied` dropped | killed by property tests | REQ-IDEMPOTENCY |  |
| M056 | field | `step` | field read `r.batchId` replaced by `r.legs` | does not compile |  |  |
| M057 | field | `step` | field read `s.applied` replaced by `s.balance` | does not compile |  |  |
| M058 | swap | `move` | arguments `(adjust bal l.source (-(l.amount : Int)))` and `l.target` of `adjust` swapped | does not compile |  |  |
| M059 | swap | `move` | arguments `bal` and `l.source` of `adjust` swapped | does not compile |  |  |
| M060 | swap | `move` | arguments `l.source` and `(-(l.amount : Int))` of `adjust` swapped | does not compile |  |  |
| M061 | swap | `move` | arguments `l.target` and `l.amount` of `adjust` swapped | killed by property tests | REQ-CONSERVATION, REQ-EFFECTS, REQ-SINGLE-LEG, REQ-VALID-SUCCEEDS |  |
| M062 | swap | `admit` | operands of `<` swapped | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M063 | swap | `run` | arguments `s` and `bal` of `admit` swapped | does not compile |  |  |
| M064 | swap | `run` | arguments `bal` and `l` of `admit` swapped | does not compile |  |  |
| M065 | swap | `run` | arguments `s` and `(move bal l)` of `run` swapped | does not compile |  |  |
| M066 | swap | `run` | arguments `(move bal l)` and `ls` of `run` swapped | does not compile |  |  |
| M067 | swap | `run` | arguments `bal` and `l` of `move` swapped | does not compile |  |  |
| M068 | swap | `step` | arguments `s` and `r` of `header` swapped | does not compile |  |  |
| M069 | swap | `step` | arguments `s` and `s.balance` of `run` swapped | does not compile |  |  |
| M070 | swap | `step` | arguments `s.balance` and `r.legs` of `run` swapped | does not compile |  |  |
| M071 | constant | `admit` | constant `0` replaced by `1` | killed by property tests | REQ-VALID-SUCCEEDS |  |

## Survivors

### M016: survived, no observed difference

conjunct `s.accounts.contains l.source` replaced by `true` in `admit` (line 22); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -21,3 +21,3 @@
 def admit (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
-  decide (0 < l.amount) && l.source != l.target && s.accounts.contains l.source &&
+  decide (0 < l.amount) && l.source != l.target && true &&
   s.accounts.contains l.target && decide ((l.amount : Int) ≤ bal l.source + s.limit l.source)
```

### M019: survived, no observed difference

conjunct `decide s.accounts.Nodup` replaced by `true` in `header` (line 32); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -31,3 +31,3 @@
 def header (s : State) (r : Request) : Bool :=
-  decide s.accounts.Nodup && !r.legs.isEmpty && !decide (r.batchId ∈ s.applied)
+  true && !r.legs.isEmpty && !decide (r.batchId ∈ s.applied)
 
```

### M042: survived, no observed difference

field read `l.source` replaced by `l.target` in `admit` (line 22); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -21,3 +21,3 @@
 def admit (s : State) (bal : AccountId → Int) (l : Leg) : Bool :=
-  decide (0 < l.amount) && l.source != l.target && s.accounts.contains l.source &&
+  decide (0 < l.amount) && l.source != l.target && s.accounts.contains l.target &&
   s.accounts.contains l.target && decide ((l.amount : Int) ≤ bal l.source + s.limit l.source)
```

