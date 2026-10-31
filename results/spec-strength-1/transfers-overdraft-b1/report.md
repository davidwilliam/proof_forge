# Specification strength: transfers-overdraft-b1

Reference `tasks/transfers-overdraft-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `29db422e6ccae122`; report `743c1153ef4b2e72`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 110 | 110 | 93 | 0 | 89 | 0 | 0 | 89 | 0 | 4 | 89 of 93 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 45 | 45 | kernel-checked |
| REQ-INVALID-NOOP | 54 | 20 | kernel-checked |
| REQ-AUTHORIZATION | 0 | 0 | not shown |
| REQ-DEBIT-CREDIT | 19 | 16 | kernel-checked |
| REQ-EFFECTS | 5 | 1 | kernel-checked |
| REQ-IDEMPOTENCY | 17 | 5 | kernel-checked |
| REQ-LIMIT | 30 | 1 | kernel-checked |
| REQ-CONSERVATION | 12 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `admits` | `<` replaced by `≤` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M002 | boundary | `admits` | `≤` replaced by `<` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M003 | equality | `adjust` | `=` replaced by `≠` | killed by property tests | REQ-DEBIT-CREDIT, REQ-LIMIT | REQ-DEBIT-CREDIT |
| M004 | equality | `admits` | `!=` replaced by `==` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M005 | arith | `adjust` | `+` replaced by `-` | killed by property tests | REQ-DEBIT-CREDIT, REQ-LIMIT | REQ-LIMIT |
| M006 | arith | `admits` | `+` replaced by `-` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M007 | arith | `step` | unary minus dropped | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT | REQ-CONSERVATION |
| M008 | logic | `admits` | `&&` replaced by `//` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-IDEMPOTENCY |
| M009 | logic | `admits` | `&&` replaced by `//` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M010 | logic | `admits` | `&&` replaced by `//` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M011 | logic | `admits` | `&&` replaced by `//` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M012 | logic | `admits` | `&&` replaced by `//` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M013 | logic | `admits` | `&&` replaced by `//` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M014 | logic | `admits` | `&&` replaced by `//` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M015 | drop-conjunct | `admits` | conjunct `decide s.accounts.Nodup` replaced by `true` | survived, no observed difference |  |  |
| M016 | drop-conjunct | `admits` | conjunct `decide (0 < r.amount)` replaced by `true` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M017 | drop-conjunct | `admits` | conjunct `r.source != r.target` replaced by `true` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M018 | drop-conjunct | `admits` | conjunct `s.accounts.contains r.source` replaced by `true` | survived, no observed difference |  |  |
| M019 | drop-conjunct | `admits` | conjunct `s.accounts.contains r.target` replaced by `true` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M020 | drop-conjunct | `admits` | conjunct `s.auth r.requester r.source` replaced by `true` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M021 | drop-conjunct | `admits` | conjunct `decide ((r.amount : Int) ≤ s.balance r.source + s.limit r...` replaced by `true` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M022 | drop-conjunct | `admits` | conjunct `!decide (r.txId ∈ s.applied)` replaced by `true` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M023 | guard | `adjust` | condition `b = a` replaced by `false` | killed by property tests | REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M024 | guard | `adjust` | condition `b = a` replaced by `true` | killed by property tests | REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M025 | guard | `step` | condition `admits s r` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M026 | guard | `step` | condition `admits s r` replaced by `true` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-LIMIT | REQ-INVALID-NOOP |
| M027 | field | `admits` | field read `s.accounts.Nodup` replaced by `s.accounts.contains` | does not compile |  |  |
| M028 | field | `admits` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M029 | field | `admits` | field read `r.amount` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M030 | field | `admits` | field read `r.amount` replaced by `r.target` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M031 | field | `admits` | field read `r.amount` replaced by `r.txId` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M032 | field | `admits` | field read `r.source` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M033 | field | `admits` | field read `r.source` replaced by `r.txId` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M034 | field | `admits` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M035 | field | `admits` | field read `r.source` replaced by `r.target` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M036 | field | `admits` | field read `r.target` replaced by `r.amount` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M037 | field | `admits` | field read `r.target` replaced by `r.txId` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M038 | field | `admits` | field read `r.target` replaced by `r.source` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M039 | field | `admits` | field read `r.target` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M040 | field | `admits` | field read `r.source` replaced by `r.target` | survived, no observed difference |  |  |
| M041 | field | `admits` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M042 | field | `admits` | field read `r.source` replaced by `r.requester` | survived, no observed difference |  |  |
| M043 | field | `admits` | field read `r.source` replaced by `r.txId` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M044 | field | `admits` | field read `r.target` replaced by `r.source` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M045 | field | `admits` | field read `r.target` replaced by `r.amount` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M046 | field | `admits` | field read `r.target` replaced by `r.txId` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M047 | field | `admits` | field read `r.target` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP | REQ-INVALID-NOOP |
| M048 | field | `admits` | field read `s.auth` replaced by `s.balance` | does not compile |  |  |
| M049 | field | `admits` | field read `s.auth` replaced by `s.applied` | does not compile |  |  |
| M050 | field | `admits` | field read `s.auth` replaced by `s.limit` | does not compile |  |  |
| M051 | field | `admits` | field read `r.requester` replaced by `r.amount` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M052 | field | `admits` | field read `r.requester` replaced by `r.source` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M053 | field | `admits` | field read `r.requester` replaced by `r.txId` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M054 | field | `admits` | field read `r.requester` replaced by `r.target` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M055 | field | `admits` | field read `r.source` replaced by `r.txId` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M056 | field | `admits` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M057 | field | `admits` | field read `r.source` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M058 | field | `admits` | field read `r.source` replaced by `r.target` | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M059 | field | `admits` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M060 | field | `admits` | field read `r.amount` replaced by `r.txId` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M061 | field | `admits` | field read `r.amount` replaced by `r.target` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M062 | field | `admits` | field read `r.amount` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M063 | field | `admits` | field read `s.balance` replaced by `s.limit` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M064 | field | `admits` | field read `s.balance` replaced by `s.auth` | does not compile |  |  |
| M065 | field | `admits` | field read `s.balance` replaced by `s.applied` | does not compile |  |  |
| M066 | field | `admits` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M067 | field | `admits` | field read `r.source` replaced by `r.target` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M068 | field | `admits` | field read `r.source` replaced by `r.txId` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M069 | field | `admits` | field read `r.source` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M070 | field | `admits` | field read `s.limit` replaced by `s.applied` | does not compile |  |  |
| M071 | field | `admits` | field read `s.limit` replaced by `s.balance` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M072 | field | `admits` | field read `s.limit` replaced by `s.auth` | does not compile |  |  |
| M073 | field | `admits` | field read `r.source` replaced by `r.txId` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M074 | field | `admits` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M075 | field | `admits` | field read `r.source` replaced by `r.requester` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M076 | field | `admits` | field read `r.source` replaced by `r.target` | killed by property tests | REQ-INVALID-NOOP, REQ-LIMIT, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M077 | field | `admits` | field read `r.txId` replaced by `r.requester` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M078 | field | `admits` | field read `r.txId` replaced by `r.target` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M079 | field | `admits` | field read `r.txId` replaced by `r.source` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M080 | field | `admits` | field read `r.txId` replaced by `r.amount` | killed by property tests | REQ-IDEMPOTENCY, REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M081 | field | `admits` | field read `s.applied` replaced by `s.limit` | does not compile |  |  |
| M082 | field | `admits` | field read `s.applied` replaced by `s.balance` | does not compile |  |  |
| M083 | field | `admits` | field read `s.applied` replaced by `s.auth` | does not compile |  |  |
| M084 | field | `step` | field read `s.balance` replaced by `s.applied` | does not compile |  |  |
| M085 | field | `step` | field read `r.source` replaced by `r.txId` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-EFFECTS, REQ-LIMIT | REQ-EFFECTS |
| M086 | field | `step` | field read `r.source` replaced by `r.target` | killed by property tests | REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M087 | field | `step` | field read `r.source` replaced by `r.amount` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-EFFECTS, REQ-LIMIT | REQ-DEBIT-CREDIT |
| M088 | field | `step` | field read `r.amount` replaced by `r.target` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-LIMIT | REQ-DEBIT-CREDIT |
| M089 | field | `step` | field read `r.amount` replaced by `r.txId` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-LIMIT | REQ-DEBIT-CREDIT |
| M090 | field | `step` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-LIMIT | REQ-DEBIT-CREDIT |
| M091 | field | `step` | update of field `balance` dropped | killed by property tests | REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M092 | field | `step` | field read `r.target` replaced by `r.amount` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-EFFECTS | REQ-DEBIT-CREDIT |
| M093 | field | `step` | field read `r.target` replaced by `r.txId` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-EFFECTS | REQ-DEBIT-CREDIT |
| M094 | field | `step` | field read `r.target` replaced by `r.source` | killed by property tests | REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M095 | field | `step` | field read `r.amount` replaced by `r.txId` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M096 | field | `step` | field read `r.amount` replaced by `r.source` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M097 | field | `step` | field read `r.amount` replaced by `r.target` | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT | REQ-DEBIT-CREDIT |
| M098 | field | `step` | update of field `applied` dropped | killed by property tests | REQ-IDEMPOTENCY | REQ-IDEMPOTENCY |
| M099 | field | `step` | field read `r.txId` replaced by `r.amount` | killed by property tests | REQ-IDEMPOTENCY | REQ-IDEMPOTENCY |
| M100 | field | `step` | field read `r.txId` replaced by `r.source` | killed by property tests | REQ-IDEMPOTENCY | REQ-IDEMPOTENCY |
| M101 | field | `step` | field read `r.txId` replaced by `r.target` | killed by property tests | REQ-IDEMPOTENCY | REQ-IDEMPOTENCY |
| M102 | field | `step` | field read `s.applied` replaced by `s.balance` | does not compile |  |  |
| M103 | swap | `admits` | operands of `<` swapped | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M104 | swap | `admits` | arguments `r.requester` and `r.source` of `s.auth` swapped | killed by property tests | REQ-INVALID-NOOP, REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M105 | swap | `step` | arguments `s` and `r` of `admits` swapped | does not compile |  |  |
| M106 | swap | `step` | arguments `s.balance` and `r.source` of `adjust` swapped | does not compile |  |  |
| M107 | swap | `step` | arguments `r.source` and `(-(r.amount : Int))` of `adjust` swapped | does not compile |  |  |
| M108 | swap | `step` | arguments `debited` and `r.target` of `adjust` swapped | does not compile |  |  |
| M109 | swap | `step` | arguments `r.target` and `r.amount` of `adjust` swapped | killed by property tests | REQ-CONSERVATION, REQ-DEBIT-CREDIT, REQ-EFFECTS | REQ-DEBIT-CREDIT |
| M110 | constant | `admits` | constant `0` replaced by `1` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |

## Survivors

### M015: survived, no observed difference

conjunct `decide s.accounts.Nodup` replaced by `true` in `admits` (line 18); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -17,3 +17,3 @@
 def admits (s : State) (r : Request) : Bool :=
-  decide s.accounts.Nodup && decide (0 < r.amount) && r.source != r.target &&
+  true && decide (0 < r.amount) && r.source != r.target &&
   s.accounts.contains r.source && s.accounts.contains r.target &&
```

### M018: survived, no observed difference

conjunct `s.accounts.contains r.source` replaced by `true` in `admits` (line 19); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -18,3 +18,3 @@
   decide s.accounts.Nodup && decide (0 < r.amount) && r.source != r.target &&
-  s.accounts.contains r.source && s.accounts.contains r.target &&
+  true && s.accounts.contains r.target &&
   s.auth r.requester r.source &&
```

### M040: survived, no observed difference

field read `r.source` replaced by `r.target` in `admits` (line 19); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -18,3 +18,3 @@
   decide s.accounts.Nodup && decide (0 < r.amount) && r.source != r.target &&
-  s.accounts.contains r.source && s.accounts.contains r.target &&
+  s.accounts.contains r.target && s.accounts.contains r.target &&
   s.auth r.requester r.source &&
```

### M042: survived, no observed difference

field read `r.source` replaced by `r.requester` in `admits` (line 19); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -18,3 +18,3 @@
   decide s.accounts.Nodup && decide (0 < r.amount) && r.source != r.target &&
-  s.accounts.contains r.source && s.accounts.contains r.target &&
+  s.accounts.contains r.requester && s.accounts.contains r.target &&
   s.auth r.requester r.source &&
```

