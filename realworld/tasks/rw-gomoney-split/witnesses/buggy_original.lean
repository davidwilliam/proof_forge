import Solution
/-!
Kernel-checked refutation of the go-money 1.0.3 port (`attacks/buggy_original.lean`) on the
input of pull request #94: -101 cents split four ways.
-/
open EqualSplit

theorem port_output : split (-101) 4 = none := by decide

theorem port_refuted : ¬ ValidSucceeds split := by
  intro h
  have := h (-101) 4 (by decide)
  rw [port_output] at this
  contradiction
