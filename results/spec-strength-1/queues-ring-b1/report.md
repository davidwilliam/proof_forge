# Specification strength: queues-ring-b1

Reference `tasks/queues-ring-b1/reference/SolutionA.lean` with every proof replaced by `sorry`; locked manifest `35cfe3f669ba5e11`; report `5360301d1703d38a`.

| Generated | Selected | Compiled | Equivalent | Killed (tests) | Killed (extended tests) | Killed (kernel only) | With kernel-checked counterexample | Survived (differs) | Survived (same) | Kill ratio |
|---|---|---|---|---|---|---|---|---|---|---|
| 34 | 34 | 26 | 0 | 26 | 0 | 0 | 26 | 0 | 0 | 26 of 26 |

## Requirements

| Requirement | Mutants violating it | Kernel-checked refutations | Not trivially true |
|---|---|---|---|
| REQ-VALID-SUCCEEDS | 1 | 1 | kernel-checked |
| REQ-INVALID-NOOP | 1 | 1 | kernel-checked |
| REQ-WELL-FORMED | 4 | 3 | kernel-checked |
| REQ-ENQUEUE-EFFECTS | 8 | 4 | kernel-checked |
| REQ-DEQUEUE-EFFECTS | 16 | 12 | kernel-checked |
| REQ-ENQUEUE-CONTENTS | 8 | 2 | kernel-checked |
| REQ-DEQUEUE-CONTENTS | 16 | 2 | kernel-checked |
| REQ-FIFO | 25 | 1 | kernel-checked |

## Mutants

| Mutant | Operator | Declaration | Change | Result | Requirements violated | Kernel-checked |
|---|---|---|---|---|---|---|
| M001 | equality | `pushed` | `=` replaced by `≠` | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO | REQ-ENQUEUE-EFFECTS |
| M002 | arith | `pushed` | `+` replaced by `-` | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO | REQ-ENQUEUE-CONTENTS |
| M003 | arith | `popped` | `+` replaced by `-` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M004 | arith | `popped` | `-` replaced by `+` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO, REQ-WELL-FORMED | REQ-WELL-FORMED |
| M005 | guard | `pushed` | condition `i = slot s s.count` replaced by `false` | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO | REQ-FIFO |
| M006 | guard | `pushed` | condition `i = slot s s.count` replaced by `true` | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO | REQ-ENQUEUE-EFFECTS |
| M007 | guard | `step` | condition `Valid s op` replaced by `true` | killed by property tests | REQ-FIFO, REQ-INVALID-NOOP, REQ-WELL-FORMED | REQ-INVALID-NOOP |
| M008 | guard | `step` | condition `Valid s op` replaced by `false` | killed by property tests | REQ-VALID-SUCCEEDS | REQ-VALID-SUCCEEDS |
| M009 | field | `pushed` | update of field `buf` dropped | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO | REQ-ENQUEUE-EFFECTS |
| M010 | field | `pushed` | field read `s.count` replaced by `s.buf` | does not compile |  |  |
| M011 | field | `pushed` | field read `s.buf` replaced by `s.count` | does not compile |  |  |
| M012 | field | `pushed` | update of field `count` dropped | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO | REQ-ENQUEUE-CONTENTS |
| M013 | field | `pushed` | field read `s.count` replaced by `s.buf` | does not compile |  |  |
| M014 | field | `popped` | update of field `head` dropped | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-CONTENTS |
| M015 | field | `popped` | field read `s.head` replaced by `s.count` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M016 | field | `popped` | field read `s.head` replaced by `s.capacity` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M017 | field | `popped` | field read `s.capacity` replaced by `s.count` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M018 | field | `popped` | field read `s.capacity` replaced by `s.head` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO, REQ-WELL-FORMED | REQ-WELL-FORMED |
| M019 | field | `popped` | update of field `count` dropped | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M020 | field | `popped` | field read `s.count` replaced by `s.capacity` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-CONTENTS |
| M021 | field | `popped` | field read `s.count` replaced by `s.head` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M022 | field | `step` | field read `s.buf` replaced by `s.head` | does not compile |  |  |
| M023 | field | `step` | field read `s.head` replaced by `s.buf` | does not compile |  |  |
| M024 | swap | `pushed` | arguments `s` and `s.count` of `slot` swapped | does not compile |  |  |
| M025 | swap | `popped` | operands of `%` swapped | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M026 | swap | `popped` | operands of `-` swapped | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M027 | swap | `step` | arguments `s` and `op` of `Valid` swapped | does not compile |  |  |
| M028 | swap | `step` | arguments `s` and `x` of `pushed` swapped | does not compile |  |  |
| M029 | constant | `pushed` | constant `1` replaced by `2` | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO, REQ-WELL-FORMED | REQ-WELL-FORMED |
| M030 | constant | `pushed` | constant `1` replaced by `0` | killed by property tests | REQ-ENQUEUE-CONTENTS, REQ-ENQUEUE-EFFECTS, REQ-FIFO | REQ-ENQUEUE-EFFECTS |
| M031 | constant | `popped` | constant `1` replaced by `0` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M032 | constant | `popped` | constant `1` replaced by `2` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M033 | constant | `popped` | constant `1` replaced by `2` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
| M034 | constant | `popped` | constant `1` replaced by `0` | killed by property tests | REQ-DEQUEUE-CONTENTS, REQ-DEQUEUE-EFFECTS, REQ-FIFO | REQ-DEQUEUE-EFFECTS |
