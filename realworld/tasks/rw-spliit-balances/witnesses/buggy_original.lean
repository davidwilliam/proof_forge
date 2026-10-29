import Solution
/-!
Kernel-checked refutation of the Spliit 1.21.0 port (`attacks/buggy_original.lean`) on the
input of issue #374: 100 cents split evenly among three participants.
-/
open Allocation

theorem port_output : allocate 100 [1, 1, 1] = some [33, 33, 33] := by decide

theorem port_refuted : ¬ Conserves allocate :=
  fun h => absurd (h 100 [1, 1, 1] [33, 33, 33] port_output) (by decide)
