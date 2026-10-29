import Solution
/-!
Kernel-checked refutation of the moneyphp 3.0.9 port (`attacks/buggy_original.lean`) on the
input of issue #436: 5 cents with ratios [0, 7, 3].
-/
open Allocation

theorem port_output : allocate 5 [0, 7, 3] = some [1, 3, 1] := by decide

theorem port_refuted : ¬ ZeroRatio allocate :=
  fun h => absurd (h 5 [0, 7, 3] [1, 3, 1] port_output) (by decide)
