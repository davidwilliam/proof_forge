import Solution
/-!
Kernel-checked refutation of the moneyphp 3.1.0 port (`attacks/v3_1_0_skip_zero_result.lean`)
on the input of issue #466: 1 cent with ratios [1, 1].
-/
open Allocation

theorem port_output : allocate 1 [1, 1] = none := by decide

theorem port_refuted : ¬ ValidSucceeds allocate := by
  intro h
  have := h 1 [1, 1] (by decide)
  rw [port_output] at this
  contradiction
