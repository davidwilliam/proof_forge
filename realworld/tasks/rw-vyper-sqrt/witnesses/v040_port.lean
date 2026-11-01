import Solution
/-!
Kernel-checked refutation of the port of Vyper v0.4.0 `sqrt()` (`candidate/Solution.lean`, the
same as `attacks/v040_port.lean`) on the input of advisory GHSA-2p94-8669-xg86 (CVE-2025-26622).
-/
open VyperSqrt

/-- `sqrt(0.9999999998)` returns `0.9999999999`: the loop runs all 256 iterations, alternating
between 9999999998 and 9999999999, and returns the last. -/
theorem port_advisory : sqrt 9999999998 = some 9999999999 := by decide +kernel

/-- `0.9999999999` squared is above `0.9999999998`: the root is rounded up. -/
theorem port_refuted_not_above : ¬ SqrtNotAbove sqrt := fun h =>
  absurd (h 9999999998 9999999999 (by decide) port_advisory) (by decide)
