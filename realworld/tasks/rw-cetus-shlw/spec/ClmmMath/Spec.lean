/-!
# Checked shift and token-A amount of a concentrated-liquidity pool (protected)

Owner-reviewed definitions for two Move routines of the Cetus CLMM on Sui:

* `integer_mate::math_u256::checked_shlw(n: u256): (u256, bool)`, which shifts `n` left by
  64 bits and reports whether the shift would overflow;
* `cetusclmm::clmm_math::get_delta_a(sqrt_price_0, sqrt_price_1, liquidity, round_up): u64`,
  which computes the amount of token A owed for `liquidity` over a price range,
  `liquidity * |sqrt_price_1 - sqrt_price_0| * 2^64 / (sqrt_price_0 * sqrt_price_1)`, rounded
  up when a depositor pays and down when the pool pays.

Move integers are modeled with `BitVec`: a `u128` is `BitVec 128` and a `u256` is
`BitVec 256`. Move's `<<` does not abort; it drops the bits shifted past the top, which is
exactly `BitVec`'s `<<<`. Move's `*`, `+`, `-` and `/` abort on overflow, underflow or a zero
divisor, and `(x as u64)` aborts when `x` does not fit; an abort is modeled as `none`.

`checkedShlw` is the definition hole. `getDeltaA` is the caller, ported line by line from
`clmm_math.move` and parameterized by the shift routine it calls, so that every requirement
on the caller is a requirement on the shift routine it is given.

Candidates may not edit this file. Every requirement is a predicate over an implementation
`shlw : Shlw`; the locked challenge (`ClmmMath/Challenge.lean`) applies each one to the
definition hole `ClmmMath.checkedShlw`.
-/

namespace ClmmMath

/-- A port of `checked_shlw(n: u256): (u256, bool)`: the shifted value and the overflow flag. -/
abbrev Shlw := BitVec 256 → BitVec 256 × Bool

/-- `integer_mate::full_math_u128::full_mul(num1: u128, num2: u128): u256`, which is
`(num1 as u256) * (num2 as u256)`. The product of two values below `2^128` is below `2^256`,
so this multiplication never aborts in Move and never wraps here. -/
def fullMul (a b : BitVec 128) : BitVec 256 :=
  a.setWidth 256 * b.setWidth 256

/-- `integer_mate::math_u256::div_round(num, denom, round_up)`:
`let p = num / denom; if (round_up && ((p * denom) != num)) { p + 1 } else { p }`.
Move's `/` aborts when `denom = 0` (`none`). Neither `p * denom` (at most `num`) nor `p + 1`
(reached only when `p * denom < num`, so `p < 2^256 - 1`) can overflow, so `BitVec`'s
wrapping operations agree with Move's aborting ones on every input. -/
def divRound (num denom : BitVec 256) (roundUp : Bool) : Option (BitVec 256) :=
  if denom = 0 then none
  else
    let p := num / denom
    if roundUp && p * denom != num then some (p + 1) else some p

/-- `sqrt_price_diff` in `get_delta_a`: `if (sqrt_price_0 > sqrt_price_1) { sqrt_price_0 -
sqrt_price_1 } else { sqrt_price_1 - sqrt_price_0 }`; neither subtraction underflows. -/
def absDiff (sqrtPrice0 sqrtPrice1 : BitVec 128) : BitVec 128 :=
  if sqrtPrice0 > sqrtPrice1 then sqrtPrice0 - sqrtPrice1 else sqrtPrice1 - sqrtPrice0

/-- `cetusclmm::clmm_math::get_delta_a`, with the shift routine as a parameter:

```
let sqrt_price_diff = if (sqrt_price_0 > sqrt_price_1) { sqrt_price_0 - sqrt_price_1 }
                      else { sqrt_price_1 - sqrt_price_0 };
if (sqrt_price_diff == 0 || liquidity == 0) { return 0 };
let (numberator, overflowing) = math_u256::checked_shlw(full_math_u128::full_mul(liquidity, sqrt_price_diff));
if (overflowing) { abort EMULTIPLICATION_OVERFLOW };
let denominator = full_math_u128::full_mul(sqrt_price_0, sqrt_price_1);
let quotient = math_u256::div_round(numberator, denominator, round_up);
(quotient as u64)
```
-/
def getDeltaA (shlw : Shlw) (sqrtPrice0 sqrtPrice1 liquidity : BitVec 128) (roundUp : Bool) :
    Option (BitVec 64) :=
  let diff := absDiff sqrtPrice0 sqrtPrice1
  if diff = 0 ∨ liquidity = 0 then some 0
  else
    let r := shlw (fullMul liquidity diff)
    if r.2 then none
    else
      match divRound r.1 (fullMul sqrtPrice0 sqrtPrice1) roundUp with
      | none => none
      | some q => if q.toNat < 2 ^ 64 then some (q.setWidth 64) else none

/-! ## Exact amounts, in unbounded natural numbers -/

/-- `|sqrt_price_1 - sqrt_price_0|` as a natural number. -/
def priceDiff (sqrtPrice0 sqrtPrice1 : BitVec 128) : Nat :=
  if sqrtPrice1.toNat ≤ sqrtPrice0.toNat then sqrtPrice0.toNat - sqrtPrice1.toNat
  else sqrtPrice1.toNat - sqrtPrice0.toNat

/-- The exact token-A amount times the denominator: `liquidity * |sqrt_price_1 - sqrt_price_0| * 2^64`.
The exact amount owed is this divided by `sqrt_price_0 * sqrt_price_1`. -/
def exactNumerator (sqrtPrice0 sqrtPrice1 liquidity : BitVec 128) : Nat :=
  liquidity.toNat * priceDiff sqrtPrice0 sqrtPrice1 * 2 ^ 64

/-- The denominator `sqrt_price_0 * sqrt_price_1` as a natural number. -/
def denominator (sqrtPrice0 sqrtPrice1 : BitVec 128) : Nat :=
  sqrtPrice0.toNat * sqrtPrice1.toNat

/-! ## Requirements on the shift routine -/

/-- REQ-SHLW-EXACT: when the shift reports no overflow, its result is exactly `n * 2^64`:
no bit is lost. -/
def ShlwExact (shlw : Shlw) : Prop :=
  ∀ n : BitVec 256, (shlw n).2 = false → (shlw n).1.toNat = n.toNat * 2 ^ 64

/-- REQ-SHLW-COMPLETE: when `n * 2^64` fits in 256 bits, the shift does not report overflow,
so no valid position is refused. -/
def ShlwComplete (shlw : Shlw) : Prop :=
  ∀ n : BitVec 256, n.toNat * 2 ^ 64 < 2 ^ 256 → (shlw n).2 = false

/-! ## Requirements on the token-A amount computed with the shift routine -/

/-- REQ-DELTA-A-COVERS: rounding up (a deposit), the amount returned is at least the exact
amount owed for the liquidity: `amount * (sqrt_price_0 * sqrt_price_1) >=
liquidity * |sqrt_price_1 - sqrt_price_0| * 2^64`. The depositor always pays at least the
exact amount for the liquidity received. -/
def DeltaACovers (shlw : Shlw) : Prop :=
  ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64,
    getDeltaA shlw sp0 sp1 liquidity true = some amount →
    exactNumerator sp0 sp1 liquidity ≤ amount.toNat * denominator sp0 sp1

/-- REQ-DELTA-A-TIGHT: rounding up, the amount is less than one unit above the exact amount:
one unit less would not cover it. -/
def DeltaATight (shlw : Shlw) : Prop :=
  ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64,
    getDeltaA shlw sp0 sp1 liquidity true = some amount → 0 < amount.toNat →
    (amount.toNat - 1) * denominator sp0 sp1 < exactNumerator sp0 sp1 liquidity

/-- REQ-DELTA-A-FLOOR: rounding down (the pool pays), the amount returned is at most the exact
amount: `amount * (sqrt_price_0 * sqrt_price_1) <= liquidity * |sqrt_price_1 - sqrt_price_0| * 2^64`. -/
def DeltaAFloor (shlw : Shlw) : Prop :=
  ∀ sp0 sp1 liquidity : BitVec 128, ∀ amount : BitVec 64,
    getDeltaA shlw sp0 sp1 liquidity false = some amount →
    amount.toNat * denominator sp0 sp1 ≤ exactNumerator sp0 sp1 liquidity

end ClmmMath
