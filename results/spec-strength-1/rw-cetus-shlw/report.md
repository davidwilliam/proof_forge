# Specification strength: rw-cetus-shlw

Reference `realworld/tasks/rw-cetus-shlw/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `880efe719beae154`; report `784d6eb8e8254973`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 25 | 25 | 17 | 0 | 16 | 0 | 0 | 16 | 1 | 0 | 16 of 17 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-SHLW-COMPLETE | 7 | 7 | kernel-checked |
| REQ-SHLW-EXACT | 10 | 7 | kernel-checked |
| REQ-DELTA-A-FLOOR | 1 | 1 | kernel-checked |
| REQ-DELTA-A-TIGHT | 1 | 1 | kernel-checked |
| REQ-DELTA-A-COVERS | 8 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | boundary | `checkedShlw` | `≥` replaced by `>` | killed by property tests | REQ-SHLW-EXACT | REQ-SHLW-EXACT |
| M002 | logic | `checkedShlw` | `true` replaced by `false` | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-EXACT | REQ-DELTA-A-COVERS |
| M003 | logic | `checkedShlw` | `false` replaced by `true` | killed by property tests | REQ-SHLW-COMPLETE | REQ-SHLW-COMPLETE |
| M004 | guard | `checkedShlw` | condition `n ≥ mask` replaced by `true` | killed by property tests | REQ-SHLW-COMPLETE | REQ-SHLW-COMPLETE |
| M005 | guard | `checkedShlw` | condition `n ≥ mask` replaced by `false` | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-EXACT | REQ-SHLW-EXACT |
| M006 | swap | `checkedShlw` | operands of `≥` swapped | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-COMPLETE, REQ-SHLW-EXACT | REQ-SHLW-COMPLETE |
| M007 | constant | `checkedShlw` | constant `256` replaced by `255` | does not compile |  |  |
| M008 | constant | `checkedShlw` | constant `256` replaced by `257` | does not compile |  |  |
| M009 | constant | `checkedShlw` | constant `256` replaced by `25` | does not compile |  |  |
| M010 | constant | `checkedShlw` | constant `256` replaced by `2560` | does not compile |  |  |
| M011 | constant | `checkedShlw` | constant `1` replaced by `0` | killed by property tests | REQ-SHLW-COMPLETE | REQ-SHLW-COMPLETE |
| M012 | constant | `checkedShlw` | constant `1` replaced by `2` | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-EXACT | REQ-SHLW-EXACT |
| M013 | constant | `checkedShlw` | constant `256` replaced by `257` | does not compile |  |  |
| M014 | constant | `checkedShlw` | constant `256` replaced by `255` | does not compile |  |  |
| M015 | constant | `checkedShlw` | constant `256` replaced by `25` | does not compile |  |  |
| M016 | constant | `checkedShlw` | constant `256` replaced by `2560` | does not compile |  |  |
| M017 | constant | `checkedShlw` | constant `192` replaced by `1920` | killed by property tests | REQ-SHLW-COMPLETE | REQ-SHLW-COMPLETE |
| M018 | constant | `checkedShlw` | constant `192` replaced by `193` | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-EXACT | REQ-SHLW-EXACT |
| M019 | constant | `checkedShlw` | constant `192` replaced by `191` | killed by property tests | REQ-SHLW-COMPLETE | REQ-SHLW-COMPLETE |
| M020 | constant | `checkedShlw` | constant `192` replaced by `19` | killed by property tests | REQ-SHLW-COMPLETE | REQ-SHLW-COMPLETE |
| M021 | constant | `checkedShlw` | constant `0` replaced by `1` | survived, behaviour differs |  |  |
| M022 | constant | `checkedShlw` | constant `64` replaced by `6` | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-EXACT | REQ-SHLW-EXACT |
| M023 | constant | `checkedShlw` | constant `64` replaced by `640` | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-EXACT | REQ-SHLW-EXACT |
| M024 | constant | `checkedShlw` | constant `64` replaced by `65` | killed by property tests | REQ-DELTA-A-FLOOR, REQ-DELTA-A-TIGHT, REQ-SHLW-EXACT | REQ-DELTA-A-FLOOR |
| M025 | constant | `checkedShlw` | constant `64` replaced by `63` | killed by property tests | REQ-DELTA-A-COVERS, REQ-SHLW-EXACT | REQ-SHLW-EXACT |

## Survivors

### M021: survived, behaviour differs

constant `0` replaced by `1` in `checkedShlw` (line 25); outputs differ from the reference on 4055 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -24,3 +24,3 @@
   let mask : BitVec 256 := (1 : BitVec 256) <<< 192
-  if n ≥ mask then (0, true) else (n <<< 64, false)
+  if n ≥ mask then (1, true) else (n <<< 64, false)
 
```

First differing case:

```json
{"input": {"n": 6277101735386683105903941386108044688699448269690241981769, "op": "shlw"}, "output": {"overflow": true, "value": 1}, "reference_output": {"overflow": true, "value": 0}}
```

