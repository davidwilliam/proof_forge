# Specification strength: rw-hundred-vault

Reference `realworld/tasks/rw-hundred-vault/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `37515f0be09213bb`; report `76d276e0d5594953`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 130 | 130 | 96 | 0 | 92 | 1 | 0 | 57 | 0 | 3 | 93 of 96 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-DEPOSIT-SUCCEEDS | 6 | 6 | kernel-checked |
| REQ-REDEEM-SUCCEEDS | 6 | 6 | kernel-checked |
| REQ-WITHDRAW-SUCCEEDS | 19 | 18 | kernel-checked |
| REQ-DEPOSIT-EFFECTS | 13 | 0 | tested |
| REQ-REDEEM-EFFECTS | 15 | 0 | tested |
| REQ-WITHDRAW-EFFECTS | 19 | 0 | tested |
| REQ-DEPOSIT-ROUNDS-DOWN | 15 | 0 | tested |
| REQ-REDEEM-ROUNDS-DOWN | 7 | 0 | tested |
| REQ-WITHDRAW-ROUNDS-UP | 24 | 0 | tested |
| REQ-SHARE-VALUE | 31 | 27 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `sharesUp` | ceiling division idiom `(a + b - 1) / b` replaced by floor division | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP | REQ-SHARE-VALUE |
| M002 | rounding | `sharesUp` | floor division `/` replaced by ceiling division | killed by property tests | REQ-WITHDRAW-ROUNDS-UP, REQ-WITHDRAW-SUCCEEDS |  |
| M003 | rounding | `vault` | floor division `/` replaced by ceiling division | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M004 | rounding | `vault` | floor division `/` replaced by ceiling division | killed by property tests | REQ-REDEEM-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M005 | boundary | `vault` | `≤` replaced by `<` | killed by property tests | REQ-REDEEM-SUCCEEDS | REQ-REDEEM-SUCCEEDS |
| M006 | boundary | `vault` | `≤` replaced by `<` | killed by property tests | REQ-REDEEM-SUCCEEDS | REQ-REDEEM-SUCCEEDS |
| M007 | boundary | `vault` | `<` replaced by `≤` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP |  |
| M008 | boundary | `vault` | `<` replaced by `≤` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP |  |
| M009 | boundary | `vault` | `≤` replaced by `<` | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M010 | boundary | `vault` | `≤` replaced by `<` | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M011 | boundary | `vault` | `≤` replaced by `<` | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M012 | equality | `mintTo` | `=` replaced by `≠` | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M013 | equality | `burnFrom` | `=` replaced by `≠` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-WITHDRAW-EFFECTS |  |
| M014 | equality | `vault` | `=` replaced by `≠` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-DEPOSIT-SUCCEEDS | REQ-DEPOSIT-SUCCEEDS |
| M015 | equality | `vault` | `=` replaced by `≠` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-DEPOSIT-SUCCEEDS | REQ-DEPOSIT-SUCCEEDS |
| M016 | arith | `mintTo` | `+` replaced by `-` | killed by property tests | REQ-DEPOSIT-EFFECTS, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M017 | arith | `mintTo` | `+` replaced by `-` | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M018 | arith | `mintTo` | `+` replaced by `-` | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M019 | arith | `burnFrom` | `-` replaced by `+` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-WITHDRAW-EFFECTS |  |
| M020 | arith | `burnFrom` | `-` replaced by `+` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-SHARE-VALUE, REQ-WITHDRAW-EFFECTS | REQ-SHARE-VALUE |
| M021 | arith | `burnFrom` | `-` replaced by `+` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-WITHDRAW-EFFECTS |  |
| M022 | arith | `sharesUp` | `*` replaced by `/` | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP | REQ-SHARE-VALUE |
| M023 | arith | `sharesUp` | `+` replaced by `-` | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP | REQ-SHARE-VALUE |
| M024 | arith | `sharesUp` | `-` replaced by `+` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP, REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M025 | arith | `vault` | `*` replaced by `/` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN |  |
| M026 | arith | `vault` | `*` replaced by `/` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN |  |
| M027 | arith | `vault` | `*` replaced by `/` | killed by property tests | REQ-REDEEM-ROUNDS-DOWN |  |
| M028 | logic | `vault` | `∧` replaced by `∨` | killed by property tests | REQ-REDEEM-EFFECTS |  |
| M029 | logic | `vault` | `∧` replaced by `∨` | killed by property tests | REQ-WITHDRAW-EFFECTS, REQ-WITHDRAW-ROUNDS-UP |  |
| M030 | logic | `vault` | `∧` replaced by `∨` | killed by property tests | REQ-WITHDRAW-EFFECTS, REQ-WITHDRAW-ROUNDS-UP |  |
| M031 | logic | `vault` | `∧` replaced by `∨` | killed by property tests | REQ-WITHDRAW-EFFECTS, REQ-WITHDRAW-ROUNDS-UP |  |
| M032 | logic | `vault` | `∧` replaced by `∨` | killed by property tests | REQ-WITHDRAW-EFFECTS, REQ-WITHDRAW-ROUNDS-UP |  |
| M033 | drop-conjunct | `vault` | conjunct `t ≤ s.balance who` replaced by `True` | killed by property tests | REQ-REDEEM-EFFECTS |  |
| M034 | drop-conjunct | `vault` | conjunct `t ≤ s.supply` replaced by `True` | survived, no observed difference |  |  |
| M035 | drop-conjunct | `vault` | conjunct `0 < s.supply` replaced by `True` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP |  |
| M036 | drop-conjunct | `vault` | conjunct `0 < s.assets` replaced by `True` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP |  |
| M037 | drop-conjunct | `vault` | conjunct `sharesUp s x ≤ s.balance who` replaced by `True` | killed by property tests | REQ-WITHDRAW-EFFECTS |  |
| M038 | drop-conjunct | `vault` | conjunct `sharesUp s x ≤ s.supply` replaced by `True` | survived, no observed difference |  |  |
| M039 | drop-conjunct | `vault` | conjunct `x ≤ s.assets` replaced by `True` | survived, no observed difference |  |  |
| M040 | guard | `mintTo` | condition `b = who` replaced by `true` | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M041 | guard | `mintTo` | condition `b = who` replaced by `false` | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M042 | guard | `burnFrom` | condition `b = who` replaced by `true` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-WITHDRAW-EFFECTS |  |
| M043 | guard | `burnFrom` | condition `b = who` replaced by `false` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-WITHDRAW-EFFECTS |  |
| M044 | guard | `vault` | condition `s.supply = 0` replaced by `true` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M045 | guard | `vault` | condition `s.supply = 0` replaced by `false` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-DEPOSIT-SUCCEEDS | REQ-DEPOSIT-SUCCEEDS |
| M046 | guard | `vault` | condition `s.assets = 0` replaced by `false` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN |  |
| M047 | guard | `vault` | condition `s.assets = 0` replaced by `true` | killed by property tests | REQ-DEPOSIT-SUCCEEDS | REQ-DEPOSIT-SUCCEEDS |
| M048 | guard | `vault` | condition `t ≤ s.balance who ∧ t ≤ s.supply` replaced by `true` | killed by property tests | REQ-REDEEM-EFFECTS |  |
| M049 | guard | `vault` | condition `t ≤ s.balance who ∧ t ≤ s.supply` replaced by `false` | killed by property tests | REQ-REDEEM-SUCCEEDS | REQ-REDEEM-SUCCEEDS |
| M050 | guard | `vault` | condition `0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance wh...` replaced by `true` | killed by property tests | REQ-WITHDRAW-EFFECTS, REQ-WITHDRAW-ROUNDS-UP |  |
| M051 | guard | `vault` | condition `0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance wh...` replaced by `false` | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M052 | field | `mintTo` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-DEPOSIT-EFFECTS, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M053 | field | `mintTo` | field read `s.assets` replaced by `s.balance` | does not compile |  |  |
| M054 | field | `mintTo` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M055 | field | `mintTo` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-DEPOSIT-EFFECTS, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M056 | field | `mintTo` | field read `s.balance` replaced by `s.assets` | does not compile |  |  |
| M057 | field | `mintTo` | field read `s.balance` replaced by `s.supply` | does not compile |  |  |
| M058 | field | `mintTo` | field read `s.balance` replaced by `s.assets` | does not compile |  |  |
| M059 | field | `mintTo` | field read `s.balance` replaced by `s.supply` | does not compile |  |  |
| M060 | field | `burnFrom` | field read `s.assets` replaced by `s.balance` | does not compile |  |  |
| M061 | field | `burnFrom` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-REDEEM-ROUNDS-DOWN, REQ-SHARE-VALUE, REQ-WITHDRAW-EFFECTS | REQ-SHARE-VALUE |
| M062 | field | `burnFrom` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-REDEEM-EFFECTS, REQ-SHARE-VALUE, REQ-WITHDRAW-EFFECTS | REQ-SHARE-VALUE |
| M063 | field | `burnFrom` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M064 | field | `burnFrom` | field read `s.balance` replaced by `s.assets` | does not compile |  |  |
| M065 | field | `burnFrom` | field read `s.balance` replaced by `s.supply` | does not compile |  |  |
| M066 | field | `burnFrom` | field read `s.balance` replaced by `s.assets` | does not compile |  |  |
| M067 | field | `burnFrom` | field read `s.balance` replaced by `s.supply` | does not compile |  |  |
| M068 | field | `sharesUp` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP, REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M069 | field | `sharesUp` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP, REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M070 | field | `sharesUp` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP, REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M071 | field | `vault` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M072 | field | `vault` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN |  |
| M073 | field | `vault` | field read `s.assets` replaced by `s.balance` | does not compile |  |  |
| M074 | field | `vault` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN |  |
| M075 | field | `vault` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M076 | field | `vault` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M077 | field | `vault` | field read `s.assets` replaced by `s.balance` | does not compile |  |  |
| M078 | field | `vault` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M079 | field | `vault` | field read `s.balance` replaced by `s.assets` | does not compile |  |  |
| M080 | field | `vault` | field read `s.balance` replaced by `s.supply` | does not compile |  |  |
| M081 | field | `vault` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-REDEEM-SUCCEEDS | REQ-REDEEM-SUCCEEDS |
| M082 | field | `vault` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M083 | field | `vault` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-REDEEM-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M084 | field | `vault` | field read `s.assets` replaced by `s.balance` | does not compile |  |  |
| M085 | field | `vault` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M086 | field | `vault` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-REDEEM-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M087 | field | `vault` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP |  |
| M088 | field | `vault` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M089 | field | `vault` | field read `s.assets` replaced by `s.balance` | does not compile |  |  |
| M090 | field | `vault` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP |  |
| M091 | field | `vault` | field read `s.balance` replaced by `s.assets` | does not compile |  |  |
| M092 | field | `vault` | field read `s.balance` replaced by `s.supply` | does not compile |  |  |
| M093 | field | `vault` | field read `s.supply` replaced by `s.assets` | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M094 | field | `vault` | field read `s.supply` replaced by `s.balance` | does not compile |  |  |
| M095 | field | `vault` | field read `s.assets` replaced by `s.balance` | does not compile |  |  |
| M096 | field | `vault` | field read `s.assets` replaced by `s.supply` | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M097 | swap | `burnFrom` | operands of `-` swapped | killed by property tests | REQ-REDEEM-ROUNDS-DOWN, REQ-SHARE-VALUE, REQ-WITHDRAW-EFFECTS | REQ-SHARE-VALUE |
| M098 | swap | `burnFrom` | operands of `-` swapped | killed by property tests | REQ-REDEEM-EFFECTS, REQ-WITHDRAW-EFFECTS |  |
| M099 | swap | `sharesUp` | operands of `/` swapped | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP, REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M100 | swap | `sharesUp` | operands of `-` swapped | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP | REQ-SHARE-VALUE |
| M101 | swap | `vault` | arguments `who` and `x` of `deposit` swapped | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M102 | swap | `vault` | arguments `s` and `who` of `mintTo` swapped | does not compile |  |  |
| M103 | swap | `vault` | arguments `who` and `x` of `mintTo` swapped | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M104 | swap | `vault` | arguments `x` and `(initialSharesPerUnit * x)` of `mintTo` swapped | killed by property tests | REQ-DEPOSIT-EFFECTS |  |
| M105 | swap | `vault` | arguments `s` and `who` of `mintTo` swapped | does not compile |  |  |
| M106 | swap | `vault` | arguments `who` and `x` of `mintTo` swapped | killed by property tests | REQ-DEPOSIT-EFFECTS, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M107 | swap | `vault` | arguments `x` and `(x * s.supply / s.assets)` of `mintTo` swapped | killed by property tests | REQ-DEPOSIT-EFFECTS, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M108 | swap | `vault` | operands of `/` swapped | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M109 | swap | `vault` | arguments `who` and `t` of `redeem` swapped | killed by property tests | REQ-REDEEM-EFFECTS, REQ-REDEEM-SUCCEEDS | REQ-REDEEM-SUCCEEDS |
| M110 | swap | `vault` | operands of `≤` swapped | killed by property tests | REQ-REDEEM-SUCCEEDS | REQ-REDEEM-SUCCEEDS |
| M111 | swap | `vault` | arguments `s` and `who` of `burnFrom` swapped | does not compile |  |  |
| M112 | swap | `vault` | arguments `who` and `t` of `burnFrom` swapped | killed by property tests | REQ-REDEEM-EFFECTS, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M113 | swap | `vault` | arguments `t` and `(t * s.assets / s.supply)` of `burnFrom` swapped | killed by property tests | REQ-REDEEM-EFFECTS, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M114 | swap | `vault` | operands of `/` swapped | killed by property tests | REQ-REDEEM-ROUNDS-DOWN, REQ-SHARE-VALUE | REQ-SHARE-VALUE |
| M115 | swap | `vault` | arguments `who` and `x` of `withdraw` swapped | killed by property tests | REQ-WITHDRAW-EFFECTS, REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M116 | swap | `vault` | operands of `<` swapped | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M117 | swap | `vault` | operands of `<` swapped | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M118 | swap | `vault` | arguments `s` and `x` of `sharesUp` swapped | does not compile |  |  |
| M119 | swap | `vault` | arguments `s` and `x` of `sharesUp` swapped | does not compile |  |  |
| M120 | swap | `vault` | operands of `≤` swapped | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M121 | swap | `vault` | arguments `s` and `who` of `burnFrom` swapped | does not compile |  |  |
| M122 | swap | `vault` | arguments `who` and `(sharesUp s x)` of `burnFrom` swapped | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-EFFECTS, REQ-WITHDRAW-ROUNDS-UP | REQ-SHARE-VALUE |
| M123 | swap | `vault` | arguments `(sharesUp s x)` and `x` of `burnFrom` swapped | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-EFFECTS | REQ-SHARE-VALUE |
| M124 | swap | `vault` | arguments `s` and `x` of `sharesUp` swapped | does not compile |  |  |
| M125 | constant | `sharesUp` | constant `1` replaced by `0` | killed by property tests | REQ-WITHDRAW-ROUNDS-UP, REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M126 | constant | `sharesUp` | constant `1` replaced by `2` | killed by property tests | REQ-SHARE-VALUE, REQ-WITHDRAW-ROUNDS-UP | REQ-SHARE-VALUE |
| M127 | constant | `vault` | constant `0` replaced by `1` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-DEPOSIT-SUCCEEDS | REQ-DEPOSIT-SUCCEEDS |
| M128 | constant | `vault` | constant `0` replaced by `1` | killed by property tests | REQ-DEPOSIT-ROUNDS-DOWN, REQ-DEPOSIT-SUCCEEDS | REQ-DEPOSIT-SUCCEEDS |
| M129 | constant | `vault` | constant `0` replaced by `1` | killed by property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |
| M130 | constant | `vault` | constant `0` replaced by `1` | killed by extended property tests | REQ-WITHDRAW-SUCCEEDS | REQ-WITHDRAW-SUCCEEDS |

## Survivors

### M034: survived, no observed difference

conjunct `t ≤ s.supply` replaced by `True` in `vault` (line 34); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -33,3 +33,3 @@
   | .redeem who t =>
-    if t ≤ s.balance who ∧ t ≤ s.supply then
+    if t ≤ s.balance who ∧ True then
       some (burnFrom s who t (t * s.assets / s.supply))
```

### M038: survived, no observed difference

conjunct `sharesUp s x ≤ s.supply` replaced by `True` in `vault` (line 38); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -37,3 +37,3 @@
   | .withdraw who x =>
-    if 0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance who ∧ sharesUp s x ≤ s.supply ∧
+    if 0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance who ∧ True ∧
         x ≤ s.assets then
```

### M039: survived, no observed difference

conjunct `x ≤ s.assets` replaced by `True` in `vault` (line 39); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -38,3 +38,3 @@
     if 0 < s.supply ∧ 0 < s.assets ∧ sharesUp s x ≤ s.balance who ∧ sharesUp s x ≤ s.supply ∧
-        x ≤ s.assets then
+        True then
       some (burnFrom s who (sharesUp s x) x)
```

