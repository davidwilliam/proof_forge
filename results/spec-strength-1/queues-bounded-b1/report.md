# Specification strength: queues-bounded-b1

Reference `tasks/queues-bounded-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `9bae05f38db3ab58`; report `821b4683d3a259b0`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 14 | 14 | 9 | 0 | 8 | 0 | 0 | 0 | 0 | 1 | 8 of 9 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 0 | tested |
| REQ-INVALID-NOOP | 1 | 0 | tested |
| REQ-CAPACITY | 1 | 0 | tested |
| REQ-ENQUEUE-EFFECTS | 1 | 0 | tested |
| REQ-DEQUEUE-EFFECTS | 5 | 0 | tested |
| REQ-FIFO | 3 | 0 | tested |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | arith | `step` | `+` replaced by `-` | killed by property tests | REQ-DEQUEUE-EFFECTS |  |
| M002 | guard | `step` | condition `Valid s op` replaced by `true` | killed by property tests | REQ-CAPACITY, REQ-FIFO, REQ-INVALID-NOOP |  |
| M003 | guard | `step` | condition `Valid s op` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS |  |
| M004 | field | `step` | update of field `items` dropped | killed by property tests | REQ-ENQUEUE-EFFECTS, REQ-FIFO |  |
| M005 | field | `step` | field read `s.items` replaced by `s.served` | does not compile |  |  |
| M006 | field | `step` | field read `s.items.headD` replaced by `s.items.tail` | does not compile |  |  |
| M007 | field | `step` | update of field `items` dropped | killed by property tests | REQ-DEQUEUE-EFFECTS, REQ-FIFO |  |
| M008 | field | `step` | field read `s.items.tail` replaced by `s.items.headD` | does not compile |  |  |
| M009 | field | `step` | update of field `served` dropped | killed by property tests | REQ-DEQUEUE-EFFECTS |  |
| M010 | field | `step` | field read `s.served` replaced by `s.items` | does not compile |  |  |
| M011 | swap | `step` | arguments `s` and `op` of `Valid` swapped | does not compile |  |  |
| M012 | constant | `step` | constant `0` replaced by `1` | survived, no observed difference |  |  |
| M013 | constant | `step` | constant `1` replaced by `2` | killed by property tests | REQ-DEQUEUE-EFFECTS |  |
| M014 | constant | `step` | constant `1` replaced by `0` | killed by property tests | REQ-DEQUEUE-EFFECTS |  |

## Survivors

### M012: survived, no observed difference

constant `0` replaced by `1` in `step` (line 17); outputs differ from the reference on 0 cases.

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -16,3 +16,3 @@
     | .enqueue x => (.ok, { s with items := s.items ++ [x] })
-    | .dequeue => (.got (s.items.headD 0), { s with items := s.items.tail, served := s.served + 1 })
+    | .dequeue => (.got (s.items.headD 1), { s with items := s.items.tail, served := s.served + 1 })
   else (.rejected, s)
```

