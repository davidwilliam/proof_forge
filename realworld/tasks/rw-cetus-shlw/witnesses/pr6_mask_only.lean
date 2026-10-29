import Solution
/-!
Kernel-checked refutation of the port of `checked_shlw` after pull request 6
(`attacks/pr6_mask_only.lean`, integer-mate merge commit fc84a51c29fabfbfbdb8ed76506b61a07493d492):
the mask is `1 << 192` but the test is still `n > mask`, so `n = 2^192` passes and
`2^192 << 64` wraps to 0.
-/
open ClmmMath

/-- `checked_shlw(2^192)` returns 0 and reports no overflow. -/
theorem port_shift_output :
    checkedShlw 6277101735386680763835789423207666416102355444464034512896 = (0, false) := by decide

theorem port_refuted_exact : ¬ ShlwExact checkedShlw := fun h =>
  absurd (h _ (congrArg Prod.snd port_shift_output)) (by rw [port_shift_output]; decide)

/-- At the caller: liquidity 2^113 over the price range from 60257519765924248467716150 to
60257519765924248467716150 + 2^79 gives `liquidity * diff = 2^192` exactly, and the deposit is
charged 0 units of token A. -/
theorem port_deposit_output :
    getDeltaA checkedShlw 60257519765924248467716150 60861982675731563055069238
      10384593717069655257060992658440192 true = some 0 := by decide

theorem port_refuted_covers : ¬ DeltaACovers checkedShlw := fun h =>
  absurd (h _ _ _ _ port_deposit_output) (by decide)
