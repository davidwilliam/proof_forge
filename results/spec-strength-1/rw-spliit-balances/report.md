# Specification strength: rw-spliit-balances

Reference `realworld/tasks/rw-spliit-balances/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `32bf7261d904341e`; report `638ddbb99f1e407e`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 58 | 58 | 30 | 0 | 27 | 0 | 0 | 16 | 2 | 1 | 27 of 30 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 0 | 0 | not shown |
| REQ-INVALID-FAILS | 0 | 0 | not shown |
| REQ-ONE-SHARE-EACH | 0 | 0 | not shown |
| REQ-CONSERVATION | 9 | 8 | kernel-checked |
| REQ-WITHIN-ONE-UNIT | 12 | 5 | kernel-checked |
| REQ-ZERO-RATIO | 10 | 1 | kernel-checked |
| REQ-SIGN | 12 | 1 | kernel-checked |
| REQ-LARGEST-REMAINDER | 10 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | rounding | `floors` | floor division `/` replaced by ceiling division | killed by property tests | REQ-CONSERVATION | REQ-CONSERVATION |
| M002 | boundary | `argmaxTo` | `<` replaced by `≤` | survived, behaviour differs |  |  |
| M003 | equality | `bump` | `=` replaced by `≠` | killed by property tests | REQ-CONSERVATION, REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-WITHIN-ONE-UNIT |
| M004 | arith | `sumTo` | `+` replaced by `-` | does not compile |  |  |
| M005 | arith | `sumTo` | `+` replaced by `-` | killed (property tests stopped at the time limit) |  |  |
| M006 | arith | `argmaxTo` | `+` replaced by `-` | does not compile |  |  |
| M007 | arith | `need` | `*` replaced by `/` | killed by property tests | WRAPPER |  |
| M008 | arith | `need` | `-` replaced by `+` | killed by property tests | REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-ZERO-RATIO |
| M009 | arith | `need` | `*` replaced by `/` | killed by property tests | REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-SIGN |
| M010 | arith | `bump` | `+` replaced by `-` | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M011 | arith | `hand` | `+` replaced by `-` | does not compile |  |  |
| M012 | arith | `floors` | `*` replaced by `/` | killed (property tests stopped at the time limit) |  |  |
| M013 | arith | `shares` | `-` replaced by `+` | killed by property tests | WRAPPER |  |
| M014 | guard | `argmaxTo` | condition `g k < g n` replaced by `true` | killed by property tests | REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-LARGEST-REMAINDER |
| M015 | guard | `argmaxTo` | condition `g k < g n` replaced by `false` | killed by property tests | REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-WITHIN-ONE-UNIT |
| M016 | guard | `bump` | condition `j = k` replaced by `true` | killed by property tests | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-CONSERVATION |
| M017 | guard | `bump` | condition `j = k` replaced by `false` | killed by property tests | REQ-CONSERVATION | REQ-CONSERVATION |
| M018 | guard | `allocate` | condition `Valid amount ratios` replaced by `true` | killed (property tests stopped at the time limit) |  |  |
| M019 | guard | `allocate` | condition `Valid amount ratios` replaced by `false` | killed by property tests | WRAPPER |  |
| M020 | field | `shares` | field read `ratios.sum` replaced by `ratios.length` | killed (property tests stopped at the time limit) |  |  |
| M021 | field | `shares` | field read `ratios.length` replaced by `ratios.sum` | killed by property tests | WRAPPER |  |
| M022 | swap | `sumTo` | arguments `f` and `n` of `sumTo` swapped | does not compile |  |  |
| M023 | swap | `argmaxTo` | arguments `g` and `n` of `argmaxTo` swapped | does not compile |  |  |
| M024 | swap | `hand` | arguments `a` and `S` of `hand` swapped | killed by property tests | REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-WITHIN-ONE-UNIT |
| M025 | swap | `hand` | arguments `S` and `r` of `hand` swapped | does not compile |  |  |
| M026 | swap | `hand` | arguments `r` and `n` of `hand` swapped | does not compile |  |  |
| M027 | swap | `hand` | arguments `n` and `t` of `hand` swapped | does not compile |  |  |
| M028 | swap | `hand` | arguments `t` and `(bump x (argmaxTo (need a S r x) n))` of `hand` swapped | does not compile |  |  |
| M029 | swap | `hand` | arguments `x` and `(argmaxTo (need a S r x) n)` of `bump` swapped | does not compile |  |  |
| M030 | swap | `hand` | arguments `(need a S r x)` and `n` of `argmaxTo` swapped | does not compile |  |  |
| M031 | swap | `hand` | arguments `a` and `S` of `need` swapped | killed by property tests | REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-WITHIN-ONE-UNIT |
| M032 | swap | `hand` | arguments `S` and `r` of `need` swapped | does not compile |  |  |
| M033 | swap | `hand` | arguments `r` and `x` of `need` swapped | killed by property tests | REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-WITHIN-ONE-UNIT |
| M034 | swap | `ratioAt` | arguments `j` and `0` of `ratios.getD` swapped | killed (property tests stopped at the time limit) |  |  |
| M035 | swap | `shares` | arguments `amount` and `S` of `floors` swapped | killed (property tests stopped at the time limit) |  |  |
| M036 | swap | `shares` | arguments `S` and `r` of `floors` swapped | does not compile |  |  |
| M037 | swap | `shares` | arguments `x0` and `n` of `sumTo` swapped | does not compile |  |  |
| M038 | swap | `shares` | arguments `amount` and `S` of `hand` swapped | killed by property tests | WRAPPER |  |
| M039 | swap | `shares` | arguments `S` and `r` of `hand` swapped | does not compile |  |  |
| M040 | swap | `shares` | arguments `r` and `n` of `hand` swapped | does not compile |  |  |
| M041 | swap | `shares` | arguments `n` and `left.toNat` of `hand` swapped | killed by property tests | REQ-CONSERVATION, REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-ZERO-RATIO | REQ-CONSERVATION |
| M042 | swap | `shares` | arguments `left.toNat` and `x0` of `hand` swapped | does not compile |  |  |
| M043 | swap | `allocate` | arguments `amount` and `ratios` of `Valid` swapped | does not compile |  |  |
| M044 | swap | `allocate` | arguments `amount` and `ratios` of `shares` swapped | does not compile |  |  |
| M045 | constant | `sumTo` | constant `0` replaced by `1` | does not compile |  |  |
| M046 | constant | `sumTo` | constant `0` replaced by `1` | killed by property tests | REQ-CONSERVATION | REQ-CONSERVATION |
| M047 | constant | `sumTo` | constant `1` replaced by `2` | does not compile |  |  |
| M048 | constant | `sumTo` | constant `1` replaced by `0` | does not compile |  |  |
| M049 | constant | `argmaxTo` | constant `0` replaced by `1` | does not compile |  |  |
| M050 | constant | `argmaxTo` | constant `0` replaced by `1` | survived, behaviour differs |  |  |
| M051 | constant | `argmaxTo` | constant `1` replaced by `2` | does not compile |  |  |
| M052 | constant | `argmaxTo` | constant `1` replaced by `0` | does not compile |  |  |
| M053 | constant | `bump` | constant `1` replaced by `2` | killed by property tests | REQ-CONSERVATION, REQ-LARGEST-REMAINDER, REQ-SIGN, REQ-WITHIN-ONE-UNIT | REQ-CONSERVATION |
| M054 | constant | `bump` | constant `1` replaced by `0` | killed by property tests | REQ-CONSERVATION | REQ-CONSERVATION |
| M055 | constant | `hand` | constant `0` replaced by `1` | does not compile |  |  |
| M056 | constant | `hand` | constant `1` replaced by `0` | does not compile |  |  |
| M057 | constant | `hand` | constant `1` replaced by `2` | does not compile |  |  |
| M058 | constant | `ratioAt` | constant `0` replaced by `1` | survived, no observed difference |  |  |

## Survivors

### M002: survived, behaviour differs

`<` replaced by `≤` in `argmaxTo` (line 20); outputs differ from the reference on 2195 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -19,3 +19,3 @@
   | 0 => 0
-  | n + 1 => let k := argmaxTo g n; if g k < g n then n else k
+  | n + 1 => let k := argmaxTo g n; if g k ≤ g n then n else k
 
```

First differing case:

```json
{"input": {"amount": 100, "ratios": [1, 1, 1]}, "output": {"shares": [33, 33, 34]}, "reference_output": {"shares": [34, 33, 33]}}
```

### M050: survived, behaviour differs

constant `0` replaced by `1` in `argmaxTo` (line 19); outputs differ from the reference on 674 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -18,3 +18,3 @@
 def argmaxTo (g : Nat → Int) : Nat → Nat
-  | 0 => 0
+  | 0 => 1
   | n + 1 => let k := argmaxTo g n; if g k < g n then n else k
```

First differing case:

```json
{"input": {"amount": 100, "ratios": [1, 1, 1]}, "output": {"shares": [33, 34, 33]}, "reference_output": {"shares": [34, 33, 33]}}
```

### M058: survived, no observed difference

constant `0` replaced by `1` in `ratioAt` (line 33); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -32,3 +32,3 @@
 
-def ratioAt (ratios : List Nat) (j : Nat) : Int := (ratios.getD j 0 : Int)
+def ratioAt (ratios : List Nat) (j : Nat) : Int := (ratios.getD j 1 : Int)
 
```

