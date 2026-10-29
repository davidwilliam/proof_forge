import Solution
/-!
Kernel-checked refutation of the port of the original `checked_shlw`
(`attacks/buggy_original.lean`, integer-mate commit 4d09c8ba0527274983c6664a5d5def2e784d4692)
on the attack deposit of 2025-05-22 as given by Dedaub: sqrt prices
60257519765924248467716150 (tick 300000) and 60863087478126617965993239 (tick 300200),
liquidity 10365647984364446732462244378333008, rounding up.
-/
open ClmmMath

/-- `liquidity * (sqrt_price_1 - sqrt_price_0)` is 2^192 + 491983144293873864340816, a 193-bit
number, below the original mask `0xffffffffffffffff << 192`, so no overflow is reported and the
shift keeps only the low 256 bits. -/
theorem port_shift_output :
    checkedShlw (fullMul 10365647984364446732462244378333008
      (absDiff 60257519765924248467716150 60863087478126617965993239)) =
      (9075487151368008912317032979326758767558656, false) := by decide

theorem port_refuted_exact : ¬ ShlwExact checkedShlw := fun h =>
  absurd (h _ (congrArg Prod.snd port_shift_output)) (by rw [port_shift_output]; decide)

/-- The deposit is charged 1 unit of token A. -/
theorem port_attack_output :
    getDeltaA checkedShlw 60257519765924248467716150 60863087478126617965993239
      10365647984364446732462244378333008 true = some 1 := by decide

/-- The exact amount owed is above 3.157 * 10^25 units: 1 unit does not cover it. -/
theorem port_refuted_covers : ¬ DeltaACovers checkedShlw := fun h =>
  absurd (h _ _ _ _ port_attack_output) (by decide)
