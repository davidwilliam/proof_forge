# ProofForgeFin.Evm: EVM and machine arithmetic

`ProofForgeFin.Evm` (`lib/ProofForgeFin/Evm/`, root `lib/ProofForgeFin/Evm.lean`) states and proves
the arithmetic of smart-contract code: 256-bit words with wrapping and checked operations,
full-precision `mulDiv` (including a proof of the 512-bit algorithm of Uniswap's
`FullMath.mulDiv`), binary fixed-point formats, Uniswap v3 sqrt price math, signed integers with
Solidity's truncating division, exponentiation by squaring with rounding, and bit operations.
It has 231 theorems and 66 definitions in eight modules, depends on the Lean core library and on
`ProofForgeFin.Rounding`, `FixedPoint` and `Word`, and every theorem uses only `propext`,
`Classical.choice` and `Quot.sound`. Two demonstrations (24 theorems) re-prove requirements of
`rw-cetus-shlw` and `rw-gomoney-split` with it.

## The word model

A `uintW` (Solidity `uint256`, Move `u256`, `u128`, `u64`) is `BitVec w`, and its value is
`x.toNat`. `BitVec` was chosen over a natural number with a range hypothesis for three reasons:

1. its `+`, `-`, `*`, `<<<`, `>>>`, `&&&`, `|||`, `^^^` and `/` are the EVM's `ADD`, `SUB`, `MUL`,
   `SHL`, `SHR`, `AND`, `OR`, `XOR` and `DIV` (wrapping modulo `2^w`, `x / 0 = 0`), so a port of
   Solidity, Yul or Move is a line-by-line translation, as in the existing task
   `rw-cetus-shlw`, whose specification is written over `BitVec`;
2. the range `x.toNat < 2^w` is part of the type, so no lemma carries a bound hypothesis for its
   inputs;
3. Lean core already proves the `toNat` and `toInt` of every operation (`BitVec.toNat_add`,
   `BitVec.toInt_sdiv`, ...), and bit-level facts can be stated on `BitVec` and transported.

Every specification is stated through `toNat` (or `toInt`) in unbounded natural numbers (or
integers), so the bounds of `Rounding` and `FixedPoint` apply unchanged, and the statements are
the cross-multiplied forms the task specifications use. A revert (Solidity `require`, `Panic`,
a Move abort) is `none` in `Option`.

Two EVM operations differ from `BitVec`: `MOD` and `MULMOD` return 0 for a zero modulus where
`BitVec`'s `%` returns the dividend. They are `evmMod` and `mulmod`. `SMOD` is `BitVec.srem`
for a nonzero divisor (Solidity reverts on a zero divisor before reaching it).

## Contents

Statements are paraphrased; the Lean names are exact. `x` for a word means `x.toNat` in a
bound.

### `Evm.Uint`: wrapping and checked arithmetic

`U256`, `U160`, `U128`, `U64`; `fit w n` (the word with value `n` if `n < 2^w`, else `none`);
`checkedAdd`, `checkedSub`, `checkedMul`, `checkedDiv`, `checkedMod`, `checkedPow`
(Solidity 0.8 operators), `checkedCast v` (OpenZeppelin `SafeCast.toUint128`, Move
`(x as u64)`), `evmMod`, `absDiffW`.

* Each checked operation is the exact result if it fits: `checkedAdd_eq_fit : checkedAdd x y =
  fit w (x + y)`, `checkedMul_eq_fit`, `checkedSub_eq`.
* Iff characterizations: `checkedAdd_eq_some_iff : checkedAdd x y = some z ↔ x + y < 2^w ∧ z =
  x + y`, and the same for every operation; `checkedAdd_eq_none_iff : ... = none ↔ 2^w ≤ x + y`,
  `checkedMul_eq_none_iff`, `checkedSub_eq_none_iff : ... ↔ x < y`, `checkedDiv_eq_none_iff :
  ... ↔ y = 0`, `checkedCast_eq_none_iff`.
* Wrapping results: `toNat_add_of_le` (with overflow the sum loses exactly `2^w`),
  `toNat_sub_of_lt` (with underflow the difference gains `2^w`), `toNat_evmMod`.
* The overflow tests of deployed code, each proved equivalent to the overflow condition:
  `add_lt_left_iff : x + y < x ↔ 2^w ≤ x + y` (OpenZeppelin `tryAdd`, SafeMath, the 0.8 compiler's
  `checked_add`), `allOnes_sub_lt_iff : max - y < x ↔ 2^w ≤ x + y` (older compilers),
  `mul_div_ne_iff : x ≠ 0 → (x * y / x ≠ y ↔ 2^w ≤ x * y)` (`tryMul`, SafeMath, the compiler's
  `checked_mul`), `allOnes_div_lt_iff : (x ≠ 0 ∧ max / x < y) ↔ 2^w ≤ x * y`.

### `Evm.Bits`: shifts, logarithms, lowest set bit

`checkedShl x k`, `log2Ceil`, `mostSignificantBit` (port of Uniswap v3 `BitMath`),
`trailingZeros`.

* `mul_two_pow_lt_iff' : a * 2^k < 2^w ↔ a < 2^(w - k)` for every `k` (generalizes
  `Word.mul_two_pow_lt_iff`, which needs `k ≤ w`).
* `checkedShl_eq_some_iff : checkedShl x k = some z ↔ x < 2^(w - k) ∧ z = x * 2^k`, and three
  deployed overflow tests proved equal to that condition: `one_shiftLeft_le_iff` (the mask
  test `x >= 1 << j`, Cetus `checked_shlw` after pull request 7), `ushiftRight_eq_zero_iff :
  x >> j = 0 ↔ x < 2^j` (the high-bits test), `shiftLeft_ushiftRight_eq_iff : (x << k) >> k = x ↔
  x < 2^(w - k)` (the shift-back test); `toNat_shiftLeft_eq_iff` (a wrapping shift is exact
  exactly then).
* `mostSignificantBit_eq : x ≠ 0 → mostSignificantBit x = some (Nat.log2 x)` and
  `mostSignificantBit_spec : 2^r ≤ x < 2^(r+1)`; `mostSignificantBit_eq_none_iff`.
* `log2_eq_iff`, `log2_spec`, `log2_div_two_pow : log2 (n / 2^k) = log2 n - k`, `log2_mono`;
  ceiling: `log2Ceil_le_iff : log2Ceil n ≤ r ↔ n ≤ 2^r`, `two_pow_pred_log2Ceil_lt`,
  `log2_le_log2Ceil`, `log2Ceil_eq_log2_iff` (OpenZeppelin `Math.log2(x, Rounding.Ceil)`).
* `toNat_neg_and_self : x ≠ 0 → ((0 - x) & x) = 2^(trailingZeros x)` and
  `toNat_and_neg_self` (OpenZeppelin's operand order): the `twos` factor of `mulDiv`;
  `trailingZeros_spec` (a nonzero `n` is `2^tz` times an odd number).

### `Evm.MulDiv`: full-precision `mulDiv` (specification)

`fullMulDiv a b d` (`a * b / d` rounded down, `none` when `d = 0` or the quotient does not
fit), `fullMulDivUp`, `divRoundingUp` (Uniswap `UnsafeMath.divRoundingUp`), `ceilDivW`
(OpenZeppelin `Math.ceilDiv`), `divRound` (Move integer-mate `math_u256::div_round`).

* `fullMulDiv_isSome_iff : (fullMulDiv a b d).isSome ↔ 0 < d ∧ a * b < 2^w * d` (the
  `require(denominator > prod1)` of `FullMath`, stated on the inputs); `fullMulDiv_eq_none_iff`;
  `fullMulDivUp_isSome_iff : ... ↔ 0 < d ∧ a * b ≤ (2^w - 1) * d`.
* `fullMulDiv_spec : q * d ≤ a * b < (q + 1) * d`, `fullMulDivUp_spec : a * b ≤ q * d < a * b + d`;
  `toNat_of_fullMulDiv'` (the value is the library's `mulDiv`).
* `fullMulDiv_of_fullMulDivUp` (rounding up succeeding implies rounding down succeeds, one unit
  apart), `fullMulDivUp_eq_fullMulDiv_iff` (equal exactly when `d ∣ a * b`).
* `fullMulDiv_of_le_left : 0 < d → a ≤ d → ∃ q, fullMulDiv a b d = some q ∧ q ≤ b` (a fraction
  never reverts), `fullMulDiv_of_le_right`,
  `fullMulDiv_mono`, `fullMulDiv_anti`, `fullMulDivUp_mono`, `fullMulDivUp_anti`.
* `toNat_divRoundingUp : divRoundingUp x y = ceilDiv x y` (no revert, no overflow);
  `ceilDivW_eq_some_iff`; `divRound_eq_some_iff : divRound n d up = some q ↔ 0 < d ∧ q = (if up
  then ceilDiv n d else n / d)`, `divRound_up_spec`, `divRound_down_spec`.

### `Evm.FullMath`: the 512-bit algorithm

`mulmod` (EVM `MULMOD`), `mulDiv512` (line-by-line port of `FullMath.mulDiv`: the two-word
product from `mulmod(a, b, not(0))`, `require(denominator > prod1)`, remainder subtraction,
`twos = (0 - denominator) & denominator`, the shift of `prod1` into `prod0`, the inverse seed
`(3 * denominator) ^ 2` and six Newton steps), `mulDivRoundingUp512`.

* `mulDiv512_eq : mulDiv512 a b d = fullMulDiv a b d` for all 256-bit `a`, `b`, `d`.
* `mulDivRoundingUp512_eq : mulDivRoundingUp512 a b d = fullMulDivUp a b d`.
* The steps are separate lemmas: `toNat_prod1` (the high word is `a * b / 2^256`),
  `toNat_sub_remainder`, `toNat_flip_twos` (`2^k` becomes `2^(256 - k)`), `toNat_shift_in`,
  `seed_inv` (the seed inverts an odd number modulo `2^4`), `newton_step` and `newton_word`
  (Hensel lifting: each `inv *= 2 - d * inv` doubles the correct bits).

### `Evm.FixedQ`: binary fixed point

`Q64`, `Q96`, `Q128` (`Q96_eq : Q96 = 2^96`, the literal of `FixedPoint96.Q96`), `toQ`,
`floorQ`, `ceilQ`, `convertQ m n`, `convertQUp m n` (change the number of fractional bits),
`mulQ`, `mulQUp`, `divQ`, `divQUp`, `q128ToQ96Up`.

* `convertQ_spec : convertQ m n x * 2^m ≤ x * 2^n < (convertQ m n x + 1) * 2^m` (the rationals
  `y / 2^n` and `x / 2^m`, cross-multiplied) and `convertQUp_spec`; `convertQ_of_le` (adding
  fractional bits is exact), `convertQ_convertQ` (round trip), `convertQ_le_convertQUp`,
  monotonicity.
* `floorQ_toQ`, `ceilQ_toQ`, `floorQ_spec`, `ceilQ_spec`, `lt_two_pow_add_iff` (a `Qm.n` number fits
  in `m + n` bits exactly when its integer part fits in `m`).
* `mulQ_spec`, `mulQUp_spec`, `divQ_spec`, `divQUp_spec` (the `FixedPoint` bounds at
  `one = 2^n`), `mulQ_eq_shiftRight`, `toNat_fullMulDiv_two_pow` (`FullMath.mulDiv(a, b, Q96)` is
  `mulQ 96`).
* `toNat_q128ToQ96Up`: the last line of `TickMath.getSqrtRatioAtTick`,
  `uint160((ratio >> 32) + (ratio % (1 << 32) == 0 ? 0 : 1))`, is `convertQUp 128 96 ratio`.

### `Evm.SqrtPrice`: Uniswap v3 amounts and prices

`sortPrices`, `getAmount0Delta`, `getAmount1Delta`, `getNextSqrtPriceFromAmount0Add` (ports of
v3-core `SqrtPriceMath` calling `mulDiv512`, `mulDivRoundingUp512` and `divRoundingUp`);
`amount0Num L lo hi = L * (hi - lo) * 2^96` and `amount1Num L lo hi = L * (hi - lo)` (the exact
amounts times their denominators `lo * hi` and `2^96`).

* `getAmount0Delta_eq_none_iff : getAmount0Delta a b L up = none ↔ min a b = 0`.
* `getAmount0Delta_up_spec : amount0Num ≤ amt * (lo * hi) < amount0Num + lo * hi` (the trader
  pays at least the exact amount, by less than one unit), `getAmount0Delta_down_spec` (floor
  bounds), `toNat_getAmount0Delta` (the value is the exact quotient rounded once, although the
  code divides twice).
* `getAmount1Delta_isSome`, `getAmount1Delta_up_spec`, `getAmount1Delta_down_spec`,
  `toNat_getAmount1Delta`.
* `getNextSqrtPriceFromAmount0Add_spec : ... = some p → L * 2^96 * sqrtP ≤ p * (L * 2^96 +
  amount * sqrtP) ∧ p ≤ sqrtP`: the next price is at least the exact next price, on both code
  paths (the overflow-checked formula and the fallback `divRoundingUp(numerator1,
  numerator1 / sqrtP + amount)`), and the `uint160` truncation is exact.
* `ceilDiv_ceilDiv : ⌈⌈x / b⌉ / a⌉ = ⌈x / (a * b)⌉`, `div_div_eq_div_mul'`.

### `Evm.Signed`: `int256` and the three divisions

`cdiv` (ceiling division on `Int`), `I256`, `InRange n i` (`-2^n ≤ i < 2^n`), `checkedSAdd`,
`checkedSSub`, `checkedSMul`, `checkedSNeg`, `checkedSDiv` (Solidity 0.8: reverts on 0 and on
`type(int).min / -1`), `checkedSMod`, `toIntChecked` and `toUintChecked` (OpenZeppelin
`SafeCast.toInt256`, `toUint256`), `absW` (OpenZeppelin `SignedMath.abs`), `addDelta` (Uniswap v3
`LiquidityMath.addDelta`). Signed words are `BitVec (n + 1)`, so `int256` is `n = 255` and
`int24` (ticks) is `n = 23`.

* For `0 < b`: `fdiv_spec : fdiv a b * b ≤ a < (fdiv a b + 1) * b`, `cdiv_spec : a ≤ cdiv a b * b <
  a + b`, `le_fdiv_iff`, `cdiv_le_iff`, `fdiv_eq_of_bounds`, `cdiv_eq_of_bounds`,
  `fdiv_le_cdiv`, `fdiv_eq_cdiv_iff` (equal exactly when `b ∣ a`).
* Truncation: `tdiv_eq_fdiv_of_nonneg`, `tdiv_eq_cdiv_of_nonpos`, `fdiv_le_tdiv_le_cdiv`,
  `tdiv_spec`, `tmod_spec` (the remainder has the sign of the dividend), `tmod_eq_zero_iff`,
  `natAbs_tdiv'`.
* `fdiv_eq_tdiv_sub : fdiv a b = tdiv a b - (if a < 0 ∧ tmod a b ≠ 0 then 1 else 0)` (the floor
  as Uniswap's `TickBitmap` callers compute it: `compressed--` for a negative inexact tick) and
  `cdiv_eq_tdiv_add`.
* `checkedSAdd_eq_some_iff : ... = some z ↔ InRange n (x + y) ∧ z = x + y` (over `toInt`), the
  same for subtraction, multiplication and negation; `checkedSDiv_eq_some_iff : ... ↔ (y ≠ 0 ∧
  ¬(x = -2^n ∧ y = -1)) ∧ z = tdiv x y`, `checkedSDiv_eq_none_iff`, `tdiv_inRange`,
  `checkedSMod_eq_some_iff`.
* `toIntChecked_eq_some_iff`, `toUintChecked_eq_some_iff`, `toInt_of_lt`, `toInt_of_le`,
  `toNat_absW : absW x = natAbs x` on every input (including `type(int256).min`).
* `addDelta_eq_some_iff : addDelta x y = some z ↔ 0 ≤ x + y < 2^128 ∧ z = x + y` (signed `y`).

### `Evm.Pow`: exponentiation by squaring

`rpowLoop`, `rpowWith mul s x n` (the loop of DSMath and Solmate `rpow` with any product),
`mulHalf` (`(a * b + s / 2) / s`), `rpowDown`, `rpowUp`, `rpowHalf`.

* `rpowWith_invariant`: a property of (value, exponent) pairs true of `s` with exponent 0 and `x`
  with exponent 1 and preserved by `mul` holds for `rpowWith mul s x n` with exponent `n`. Every
  bound is an instance; `rpowWith_le` compares two products.
* `rpowDown_le : rpowDown s x n * s^n ≤ x^n * s` and `le_rpowUp : x^n * s ≤ rpowUp s x n * s^n`
  (for every base: rounding down never exceeds `s * (x / s)^n`, rounding up never falls below it).
* For `s ≤ x` (a rate at least one, as in interest accrual): `rpowDown_ge : x^n * (s - 1)^(n-1) *
  s ≤ rpowDown s x n * s^n * s^(n-1)`, `rpowDown_ge_bernoulli : x^n * (s - (n - 1)) ≤
  rpowDown s x n * s^n` (relative error below `(n - 1) / s`), `rpowUp_le : rpowUp s x n * s^n *
  s^(n-1) ≤ x^n * (s + 1)^(n-1) * s`.
* `rpowDown_le_rpowHalf`, `rpowHalf_le_rpowUp`, `rpowHalf_bounds` (both bounds for the
  half-up rounding of the deployed code); `bernoulli`, `mul_pred_le_mulDown`, `mulUp_le_mul_succ`.

## Real code modeled

| Library | Real function | Where |
|---|---|---|
| `Bits.checkedShl`, `one_shiftLeft_le_iff`, `ushiftRight_eq_zero_iff` | `checked_shlw` (integer-mate `math_u256.move`) | `realworld/tasks/rw-cetus-shlw/spec/ClmmMath/Spec.lean` (`Shlw`, `ShlwExact`), `reference/SolutionA.lean` (mask `1 << 192`), `reference/SolutionB.lean` (`n >> 192 == 0`), `attacks/*.lean` |
| `MulDiv.divRound` | `math_u256::div_round` | `rw-cetus-shlw/spec/ClmmMath/Spec.lean` (`divRound`, equal by `rfl`) |
| `Word.toNat_fullMul`, `Uint.absDiffW`, `Uint.checkedCast 64`, `FixedQ.Q64` | `full_math_u128::full_mul`, `sqrt_price_diff` and `(quotient as u64)` of `clmm_math::get_delta_a` | `rw-cetus-shlw/spec/ClmmMath/Spec.lean` (`fullMul`, `absDiff`, `getDeltaA`) |
| `Signed.tdiv_spec`, `tmod_spec`, `fdiv_spec`, `le_fdiv_iff` | `Money.Split` of Rhymond/go-money (Go's truncating `/` and `%`) | `realworld/tasks/rw-gomoney-split/attacks/buggy_original.lean`, `attacks/v1_0_5_sign_from_quotient.lean`, `reference/SolutionA.lean` |
| `FullMath.mulDiv512`, `mulDivRoundingUp512` | Uniswap v4-core and v3-core `FullMath.mulDiv`, `mulDivRoundingUp`; OpenZeppelin `Math.mulDiv`; Solady `fullMulDiv` | not in the task set |
| `SqrtPrice.*` | v3-core `SqrtPriceMath.getAmount0Delta`, `getAmount1Delta`, `getNextSqrtPriceFromAmount0RoundingUp`; `UnsafeMath.divRoundingUp` | not in the task set |
| `FixedQ.q128ToQ96Up`, `Q96`, `Q128` | v3-core `TickMath.getSqrtRatioAtTick` (last line), `FixedPoint96`, `FixedPoint128` | not in the task set |
| `Bits.mostSignificantBit`, `log2Ceil` | v3-core `BitMath.mostSignificantBit`; OpenZeppelin `Math.log2` | not in the task set |
| `Signed.addDelta`, `fdiv_eq_tdiv_sub` | v3-core `LiquidityMath.addDelta`; the tick compression of `TickBitmap.nextInitializedTickWithinOneWord` | not in the task set |
| `Uint.add_lt_left_iff`, `mul_div_ne_iff`, `Signed.toIntChecked`, `absW` | OpenZeppelin `Math.tryAdd`, `tryMul`, SafeMath, `SafeCast`, `SignedMath.abs`; the checks the Solidity compiler emits | not in the task set |
| `Pow.rpowHalf` | DSMath `rpow`, Solmate `FixedPointMathLib.rpow`, MakerDAO `Jug` `rpow` | not in the task set |

## Demonstrations

`lib/ProofForgeFinDemo/Evm/` (root `lib/ProofForgeFinDemo/Evm.lean`) copies task definitions
verbatim from the files named in each header; no task file is imported or modified. Sizes are
lines of theorem statements and proofs, without blank lines and comments.

### `Cetus.lean` (`rw-cetus-shlw`)

All five requirements (REQ-SHLW-EXACT, REQ-SHLW-COMPLETE, REQ-DELTA-A-COVERS, REQ-DELTA-A-TIGHT,
REQ-DELTA-A-FLOOR) for both reference routines. `deltaA_of_exact` proves the three requirements
on `get_delta_a` for every shift routine that meets REQ-SHLW-EXACT, from
`Evm.divRound_eq_some_iff`, `Evm.toNat_absDiffW`, `Word.toNat_fullMul`, `Evm.checkedCast_eq_some_iff`
and the `Rounding` bounds; the task's `divRound` and `absDiff` are the library's by `rfl`.

| Part | Task proof | Library-based proof |
|---|---|---|
| Helper lemmas of `spec/ClmmMath/Lemmas.lean` used by the references (`toNat_fullMul`, `toNat_absDiff`, `absDiff_eq_zero`, `divRound_up`, `divRound_down`, `getDeltaA_cases`, `two_pow_128_mul`) | 114 lines | replaced by library lemmas |
| The three `get_delta_a` requirements given an exact shift | 33 lines per solution (`numerator_exact`, `exact_zero`, three requirement proofs), plus the 114 | 54 lines once for every exact routine (`getDeltaA_value` 31, `deltaA_of_exact` 17, bridges 6), plus 3 per solution |
| Shift requirements, solution A (mask) | 31 lines (`mask_toNat`, `flag_false_iff`, `value_of_flag`, two requirements) | 12 lines |
| Shift requirements, solution B (`n >> 192`) | 31 lines (`top_zero_iff`, `flag_false_iff`, `value_of_flag`, two requirements) | 14 lines |
| Total for both solutions | 242 lines | 86 lines |

### `GoMoney.lean` (`rw-gomoney-split`)

| Part | Task proof | Library-based proof |
|---|---|---|
| Reference: REQ-WITHIN-ONE-UNIT and REQ-SIGN (`split_some`, `mem_shares`, two requirement proofs) | 56 lines | 42 lines (`fdiv_spec`, `le_fdiv_iff`) |
| go-money 1.0.3 port (`attacks/buggy_original.lean`, truncating division): REQ-WITHIN-ONE-UNIT and REQ-SIGN | `sorry` in the task | 44 lines (`tdiv_spec`, `tmod_spec`, `tdiv_eq_cdiv_of_nonpos`, `cdiv_le_iff`) |

The second row shows with the truncated-division lemmas that the 1.0.3 code is correct
whenever it returns; its only failure is the panic on a negative remainder (REQ-VALID-SUCCEEDS,
refuted by the task's witness).

## Limits

* The ports are hand translations of Solidity, Yul and Move into `BitVec` and `Option`. The
  translation is reviewed, not machine-checked against source or bytecode. Gas, memory and
  revert data are not modeled; every revert is `none`.
* `mulDiv512` follows Uniswap v4-core. Uniswap v3-core (Solidity 0.7) writes
  `-denominator & denominator` and `require(result < type(uint256).max)` in `mulDivRoundingUp`,
  the same operations; OpenZeppelin `Math.mulDiv` uses the same steps with the operands of
  `twos` swapped (`toNat_and_neg_self`), but is not ported separately.
* The `SqrtPrice` ports follow v3-core (Solidity 0.7.6, no implicit overflow checks); only the
  `add = true` branch of `getNextSqrtPriceFromAmount0RoundingUp` is ported. Not covered:
  `getNextSqrtPriceFromAmount1RoundingDown`, `getNextSqrtPriceFromInput` and `FromOutput`,
  `TickMath` except its final conversion, `SwapMath`, `BitMath.leastSignificantBit` (its
  specification, `trailingZeros`, and the `x & (0 - x)` lemma are proved).
* `Pow` models the natural-number computation; the overflow reverts of the EVM versions (Solmate
  checks `x < 2^128` and the rounding additions) are not modeled. The multiplicative error bounds
  need a base at least one (`s ≤ x`); for a base below one only the one-sided bounds
  `rpowDown_le` and `le_rpowUp` are proved.
* `checkedSMod` uses `BitVec.srem`, which differs from the EVM's `SMOD` only for a zero divisor,
  where Solidity reverts first.
* `fit`, `checkedAdd` and the other checked operations are proved for every width; the 512-bit
  algorithm and the sqrt price ports are for the deployed widths (256, 160, 128).
