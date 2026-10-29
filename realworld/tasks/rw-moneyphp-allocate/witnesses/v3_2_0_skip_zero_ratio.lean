import Solution
/-!
Kernel-checked refutation of the moneyphp 3.2.0 port (`attacks/v3_2_0_skip_zero_ratio.lean`)
on the input of pull request #492: 9999 cents with ratios [75, 25].
-/
open Allocation

theorem port_output : allocate 9999 [75, 25] = some [7500, 2499] := by decide

theorem port_refuted : ¬ LargestRemainder allocate :=
  fun h => absurd (h 9999 [75, 25] [7500, 2499] port_output) (by decide)
