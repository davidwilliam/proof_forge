# Specification strength: rw-vyper-sqrt

Reference `realworld/tasks/rw-vyper-sqrt/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `ea5b5e443d8f028f`; report `e9a0fdce320a2140`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 33 | 33 | 29 | 1 | 19 | 0 | 0 | 19 | 0 | 9 | 19 of 28 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-SQRT-NOT-ABOVE | 5 | 5 | kernel-checked |
| REQ-SQRT-NOT-BELOW | 3 | 3 | kernel-checked |
| REQ-SQRT-TOTAL | 12 | 10 | kernel-checked |
| REQ-SQRT-NEG-REVERTS | 2 | 1 | kernel-checked |
| REQ-DEPLOYED-LOOP | 0 | 0 | not shown |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `sqrt` | floor division `/` replaced by ceiling division | survived, no observed difference |  |  |
| M002 | boundary | `sqrt` | `<` replaced by `≤` | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M003 | boundary | `sqrt` | `<` replaced by `≤` | survived, no observed difference |  |  |
| M004 | equality | `sqrt` | `=` replaced by `≠` | killed by property tests | REQ-SQRT-NOT-BELOW, REQ-SQRT-TOTAL | REQ-SQRT-NOT-BELOW |
| M005 | arith | `sqrt` | `*` replaced by `/` | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M006 | guard | `sqrt` | condition `x < 0` replaced by `false` | killed by property tests | REQ-SQRT-NEG-REVERTS | REQ-SQRT-NEG-REVERTS |
| M007 | guard | `sqrt` | condition `x < 0` replaced by `true` | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M008 | guard | `sqrt` | condition `x = 0` replaced by `false` | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M009 | guard | `sqrt` | condition `x = 0` replaced by `true` | killed by property tests | REQ-SQRT-NOT-BELOW | REQ-SQRT-NOT-BELOW |
| M010 | guard | `sqrt` | condition `p.1 < p.2` replaced by `false` | killed by property tests | REQ-SQRT-NOT-ABOVE | REQ-SQRT-NOT-ABOVE |
| M011 | guard | `sqrt` | condition `p.1 < p.2` replaced by `true` | killed by property tests | REQ-SQRT-NOT-ABOVE | REQ-SQRT-NOT-ABOVE |
| M012 | field | `sqrt` | projection `.bind` replaced by `.map` | does not compile |  |  |
| M013 | field | `sqrt` | projection `.bind` replaced by `.map` | does not compile |  |  |
| M014 | field | `sqrt` | projection `.map` replaced by `.bind` | equivalent (identical executable) |  |  |
| M015 | swap | `sqrt` | operands of `<` swapped | killed by property tests | REQ-SQRT-NEG-REVERTS, REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M016 | swap | `sqrt` | arguments `x` and `(2 * DIVISOR)` of `ddiv` swapped | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M017 | swap | `sqrt` | arguments `h` and `(DIVISOR / 2)` of `dadd` swapped | survived, no observed difference |  |  |
| M018 | swap | `sqrt` | operands of `/` swapped | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M019 | swap | `sqrt` | arguments `x` and `256` of `loop` swapped | does not compile |  |  |
| M020 | swap | `sqrt` | arguments `256` and `x` of `loop` swapped | does not compile |  |  |
| M021 | swap | `sqrt` | arguments `x` and `z0` of `loop` swapped | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M022 | swap | `sqrt` | operands of `<` swapped | killed by property tests | REQ-SQRT-NOT-ABOVE | REQ-SQRT-NOT-ABOVE |
| M023 | constant | `sqrt` | constant `0` replaced by `1` | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M024 | constant | `sqrt` | constant `0` replaced by `1` | killed by property tests | REQ-SQRT-NOT-BELOW, REQ-SQRT-TOTAL | REQ-SQRT-NOT-BELOW |
| M025 | constant | `sqrt` | constant `0` replaced by `1` | killed by property tests | REQ-SQRT-NOT-ABOVE | REQ-SQRT-NOT-ABOVE |
| M026 | constant | `sqrt` | constant `2` replaced by `3` | survived, no observed difference |  |  |
| M027 | constant | `sqrt` | constant `2` replaced by `1` | killed by property tests | REQ-SQRT-TOTAL | REQ-SQRT-TOTAL |
| M028 | constant | `sqrt` | constant `2` replaced by `1` | survived, no observed difference |  |  |
| M029 | constant | `sqrt` | constant `2` replaced by `3` | survived, no observed difference |  |  |
| M030 | constant | `sqrt` | constant `256` replaced by `25` | killed by property tests | REQ-SQRT-NOT-ABOVE | REQ-SQRT-NOT-ABOVE |
| M031 | constant | `sqrt` | constant `256` replaced by `2560` | survived, no observed difference |  |  |
| M032 | constant | `sqrt` | constant `256` replaced by `257` | survived, no observed difference |  |  |
| M033 | constant | `sqrt` | constant `256` replaced by `255` | survived, no observed difference |  |  |

## Survivors

### M001: survived, no observed difference

floor division `/` replaced by ceiling division in `sqrt` (line 35); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -3,2 +3,10 @@
 import ProofForgeFin.Sqrt
+
+/-- Inserted by harness/spec_strength.py for a rounding mutant: ceiling division. -/
+class PfCeilDiv (α : Type) where
+  cdiv : α → α → α
+instance : PfCeilDiv Nat := ⟨fun a b => (a + b - 1) / b⟩
+instance : PfCeilDiv Int := ⟨fun a b => -((-a) / b)⟩
+infixl:70 " ⌈/⌉ " => PfCeilDiv.cdiv
+
 /-!
@@ -34,3 +42,3 @@
   else
-    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
+    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR ⌈/⌉ 2)).bind fun z0 =>
       (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
```

### M003: survived, no observed difference

`<` replaced by `≤` in `sqrt` (line 36); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -35,3 +35,3 @@
     ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
-      (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
+      (loop x 256 x z0).map fun p => if p.1 ≤ p.2 then p.1 else p.2
 
```

### M017: survived, no observed difference

arguments `h` and `(DIVISOR / 2)` of `dadd` swapped in `sqrt` (line 35); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -34,3 +34,3 @@
   else
-    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
+    ((ddiv x (2 * DIVISOR)).bind fun h => dadd (DIVISOR / 2) h).bind fun z0 =>
       (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
```

### M026: survived, no observed difference

constant `2` replaced by `3` in `sqrt` (line 35); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -34,3 +34,3 @@
   else
-    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
+    ((ddiv x (3 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
       (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
```

### M028: survived, no observed difference

constant `2` replaced by `1` in `sqrt` (line 35); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -34,3 +34,3 @@
   else
-    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
+    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 1)).bind fun z0 =>
       (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
```

### M029: survived, no observed difference

constant `2` replaced by `3` in `sqrt` (line 35); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -34,3 +34,3 @@
   else
-    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
+    ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 3)).bind fun z0 =>
       (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
```

### M031: survived, no observed difference

constant `256` replaced by `2560` in `sqrt` (line 36); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -35,3 +35,3 @@
     ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
-      (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
+      (loop x 2560 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
 
```

### M032: survived, no observed difference

constant `256` replaced by `257` in `sqrt` (line 36); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -35,3 +35,3 @@
     ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
-      (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
+      (loop x 257 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
 
```

### M033: survived, no observed difference

constant `256` replaced by `255` in `sqrt` (line 36); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -35,3 +35,3 @@
     ((ddiv x (2 * DIVISOR)).bind fun h => dadd h (DIVISOR / 2)).bind fun z0 =>
-      (loop x 256 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
+      (loop x 255 x z0).map fun p => if p.1 < p.2 then p.1 else p.2
 
```

