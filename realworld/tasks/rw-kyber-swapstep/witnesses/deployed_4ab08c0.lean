import Solution
/-!
Kernel-checked refutations of the start candidate (`candidate/Solution.lean`, the same as
`attacks/deployed_4ab08c0.lean`): the token1 branches of `SwapMath.computeSwapStep` at commit
4ab08c0.
-/
open KyberSwapStep

/-- The exploit pattern: an exact input of 1816821696332 units of token1, one unit below the reach
amount, moves the price to 27180014754675749645719300096015422, above the target
27180014754403994732126507336932861. -/
theorem port_in_step :
    computeSwapStep 529700652 26908681593376338809905220921561871 27180014754403994732126507336932861 300
        1816821696332 true =
      some { usedAmount := 1816821696332, returnedAmount := -14, deltaL := 8023,
             nextSqrtP := 27180014754675749645719300096015422 } := by decide

theorem port_refuted_in_within_target : ¬ InWithinTarget computeSwapStep := fun h =>
  absurd (h _ _ _ _ _ _ (by unfold ExactIn InRange InWindow MIN_SQRT_RATIO MAX_SQRT_RATIO; decide)
    port_in_step).2 (by decide)

/-- Exact output: an output of 153872678 units of token1 ends at 312702477359235854013914346495714,
below the target 312702479284222327139907330712089; the fee liquidity 2 is above the smaller root
of the fee equation. -/
theorem port_out_step :
    computeSwapStep 3391575 316297169264893702192209790286789 312702479284222327139907330712089 10
        (-153872678) false =
      some { usedAmount := -153872678, returnedAmount := 11, deltaL := 2,
             nextSqrtP := 312702477359235854013914346495714 } := by decide

theorem port_refuted_out_within_target : ¬ OutWithinTarget computeSwapStep := fun h =>
  absurd (h _ _ _ _ _ _ (by unfold ExactOut InRange InWindow MIN_SQRT_RATIO MAX_SQRT_RATIO; decide)
    port_out_step).1 (by decide)
