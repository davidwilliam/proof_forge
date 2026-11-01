import Solution
/-!
Kernel-checked refutation of the start candidate (`candidate/Solution.lean`, the same as
`attacks/six_steps.lean`): `Math.sqrt` with six Newton steps instead of OpenZeppelin's seven.
-/
open OzSqrt

/-- At `a = 2^204 - 1` the six-step routine returns `2^102 - 2`; the floor of the root is
`2^102 - 1`. -/
theorem port_root : (sqrt (BitVec.ofNat 256 (2 ^ 204 - 1))).toNat = 2 ^ 102 - 2 := by decide

theorem port_refuted_not_below : ¬ SqrtNotBelow sqrt := fun h =>
  absurd (h (BitVec.ofNat 256 (2 ^ 204 - 1))) (by rw [port_root]; decide)

/-- The first deposit of `2^102 + 1` and `2^102 - 1` mints `2^102 - 1002` units; the depositor is
owed `2^102 - 1001`. -/
theorem port_mint :
    firstMint sqrt (BitVec.ofNat 256 (2 ^ 102 + 1)) (BitVec.ofNat 256 (2 ^ 102 - 1)) =
      some (BitVec.ofNat 256 (2 ^ 102 - 1002)) := by decide

theorem port_refuted_mint_full : ¬ MintFull sqrt := fun h =>
  absurd (h _ _ _ port_mint) (by decide)

/-- At `a = 2^256 - 1` the six-step routine returns the root minus 198202503. -/
theorem port_root_max :
    (sqrt (BitVec.ofNat 256 (2 ^ 256 - 1))).toNat = 2 ^ 128 - 1 - 198202503 := by decide
