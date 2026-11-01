# Specification strength: rw-oz-sqrt

Reference `realworld/tasks/rw-oz-sqrt/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `62af2324e4c0cf68`; report `8f739cf001c50e84`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 48 | 48 | 40 | 0 | 37 | 0 | 0 | 37 | 0 | 3 | 37 of 40 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-SQRT-NOT-ABOVE | 2 | 1 | kernel-checked |
| REQ-SQRT-NOT-BELOW | 35 | 32 | kernel-checked |
| REQ-SQRT-UP-COVERS | 34 | 1 | kernel-checked |
| REQ-SQRT-UP-TIGHT | 2 | 1 | kernel-checked |
| REQ-MINT-BACKED | 1 | 1 | kernel-checked |
| REQ-MINT-FULL | 28 | 1 | kernel-checked |
| REQ-MINT-LIVE | 21 | 1 | kernel-checked |
| REQ-NEWTON-BUDGET | 0 | 0 | not shown |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M002 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M003 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M004 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M005 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M006 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M007 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M008 | rounding | `sqrt` | floor division `/` replaced by ceiling division | does not compile |  |  |
| M009 | equality | `sqrt` | `=` replaced by `≠` | killed by property tests | REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M010 | arith | `sqrt` | `+` replaced by `-` | killed by property tests | REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-UP-COVERS |
| M011 | arith | `sqrt` | `+` replaced by `-` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-MINT-FULL |
| M012 | arith | `sqrt` | `+` replaced by `-` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-MINT-LIVE |
| M013 | arith | `sqrt` | `+` replaced by `-` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M014 | arith | `sqrt` | `+` replaced by `-` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M015 | arith | `sqrt` | `+` replaced by `-` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M016 | arith | `sqrt` | `+` replaced by `-` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M017 | guard | `sqrt` | condition `a = 0` replaced by `false` | survived, no observed difference |  |  |
| M018 | guard | `sqrt` | condition `a = 0` replaced by `true` | killed by property tests | REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M019 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M020 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M021 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M022 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M023 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M024 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M025 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M026 | swap | `sqrt` | `min` replaced by `max` | killed by property tests | REQ-MINT-BACKED, REQ-SQRT-NOT-ABOVE, REQ-SQRT-UP-TIGHT | REQ-SQRT-NOT-ABOVE |
| M027 | swap | `sqrt` | arguments `result` and `(a / result)` of `min` swapped | survived, no observed difference |  |  |
| M028 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M029 | constant | `sqrt` | constant `0` replaced by `1` | killed by property tests | REQ-SQRT-NOT-BELOW | REQ-SQRT-NOT-BELOW |
| M030 | constant | `sqrt` | constant `0` replaced by `1` | killed by property tests | REQ-SQRT-NOT-ABOVE, REQ-SQRT-UP-TIGHT | REQ-SQRT-UP-TIGHT |
| M031 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M032 | constant | `sqrt` | constant `1` replaced by `2` | survived, no observed difference |  |  |
| M033 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M034 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M035 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M036 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M037 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M038 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M039 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M040 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M041 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M042 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-FULL, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M043 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M044 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M045 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M046 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M047 | constant | `sqrt` | constant `1` replaced by `0` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |
| M048 | constant | `sqrt` | constant `1` replaced by `2` | killed by property tests | REQ-MINT-FULL, REQ-MINT-LIVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS | REQ-SQRT-NOT-BELOW |

## Survivors

### M017: survived, no observed difference

condition `a = 0` replaced by `false` in `sqrt` (line 44); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -43,3 +43,3 @@
 def sqrt : SqrtFn := fun a =>
-  if a = 0 then 0
+  if false then 0
   else
```

### M027: survived, no observed difference

arguments `result` and `(a / result)` of `min` swapped in `sqrt` (line 54); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -53,3 +53,3 @@
     let result := (result + a / result) >>> 1
-    min result (a / result)
+    min (a / result) result
 
```

### M032: survived, no observed difference

constant `1` replaced by `2` in `sqrt` (line 46); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -45,3 +45,3 @@
   else
-    let result : U256 := (1 : U256) <<< (log2 a >>> 1)
+    let result : U256 := (2 : U256) <<< (log2 a >>> 1)
     let result := (result + a / result) >>> 1
```

