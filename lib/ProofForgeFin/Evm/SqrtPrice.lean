import ProofForgeFin.Evm.FullMath
import ProofForgeFin.Evm.FixedQ
/-!
# Uniswap v3 sqrt price math

Ports of three functions of Uniswap v3-core `SqrtPriceMath` (Solidity 0.7.6), over the proved
`FullMath` port `mulDiv512` and `UnsafeMath.divRoundingUp`:

* `getAmount0Delta(sqrtA, sqrtB, liquidity, roundUp)`: the amount of token0 for `liquidity` over
  the price range, `liquidity * (sqrtB - sqrtA) * 2^96 / (sqrtA * sqrtB)`;
* `getAmount1Delta(sqrtA, sqrtB, liquidity, roundUp)`: the amount of token1,
  `liquidity * (sqrtB - sqrtA) / 2^96`;
* `getNextSqrtPriceFromAmount0RoundingUp(sqrtP, liquidity, amount, true)`: the price after
  `amount` of token0 is added, `liquidity * 2^96 * sqrtP / (liquidity * 2^96 + amount * sqrtP)`.

Each amount is proved to be the exact amount rounded in the stated direction, stated by
cross-multiplication over natural numbers: rounded up, `exactNumerator ≤ amount * denominator`
(the trader pays at least the exact amount) and `amount * denominator < exactNumerator +
denominator` (less than one unit more); rounded down, the two floor bounds. The amount
functions never revert for a positive lower price. The next price rounded up is at least the
exact next price and at most the current price.

The amount of token0 divides twice (by `sqrtB`, then by `sqrtA`); `ceilDiv_ceilDiv` and
`Nat.div_div_eq_div_mul` show that two roundings in the same direction are one rounding of the
exact quotient, so no precision is lost by the two-step division.
-/

namespace ProofForgeFin.Evm

/-- Rounding up twice is rounding up once: `⌈⌈x / b⌉ / a⌉ = ⌈x / (a * b)⌉`. -/
theorem ceilDiv_ceilDiv (x : Nat) {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    ceilDiv (ceilDiv x b) a = ceilDiv x (a * b) := by
  apply Nat.le_antisymm
  · rw [ceilDiv_le_iff ha, ceilDiv_le_iff hb, Nat.mul_assoc]
    exact le_ceilDiv_mul x _ (Nat.mul_pos ha hb)
  · rw [ceilDiv_le_iff (Nat.mul_pos ha hb), ← Nat.mul_assoc]
    exact Nat.le_trans (le_ceilDiv_mul x b hb)
      (Nat.mul_le_mul_right b (le_ceilDiv_mul _ a ha))

/-- Rounding down twice is rounding down once: `⌊⌊x / b⌋ / a⌋ = ⌊x / (a * b)⌋`. -/
theorem div_div_eq_div_mul' (x a b : Nat) : x / b / a = x / (a * b) := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- `if (sqrtRatioAX96 > sqrtRatioBX96) (sqrtRatioAX96, sqrtRatioBX96) = (sqrtRatioBX96,
sqrtRatioAX96)`. -/
def sortPrices (a b : U160) : U160 × U160 := if a > b then (b, a) else (a, b)

/-- The sorted prices are the minimum and the maximum. -/
theorem toNat_sortPrices (a b : U160) :
    (sortPrices a b).1.toNat = min a.toNat b.toNat ∧ (sortPrices a b).2.toNat = max a.toNat b.toNat := by
  unfold sortPrices
  by_cases h : a > b
  · rw [ite_eq_left h]; rw [GT.gt, BitVec.lt_def] at h; simp only; omega
  · rw [ite_eq_right h]; rw [GT.gt, BitVec.lt_def] at h; simp only; omega

/-- The exact amount of token0 times its denominator: `liquidity * (hi - lo) * 2^96`. -/
def amount0Num (L lo hi : Nat) : Nat := L * (hi - lo) * 2 ^ 96

/-- The exact amount of token1 times its denominator `2^96`: `liquidity * (hi - lo)`. -/
def amount1Num (L lo hi : Nat) : Nat := L * (hi - lo)

/-- Uniswap v3 `SqrtPriceMath.getAmount0Delta`:

```
if (sqrtRatioAX96 > sqrtRatioBX96) (sqrtRatioAX96, sqrtRatioBX96) = (sqrtRatioBX96, sqrtRatioAX96);
uint256 numerator1 = uint256(liquidity) << FixedPoint96.RESOLUTION;
uint256 numerator2 = sqrtRatioBX96 - sqrtRatioAX96;
require(sqrtRatioAX96 > 0);
return roundUp
    ? UnsafeMath.divRoundingUp(FullMath.mulDivRoundingUp(numerator1, numerator2, sqrtRatioBX96), sqrtRatioAX96)
    : FullMath.mulDiv(numerator1, numerator2, sqrtRatioBX96) / sqrtRatioAX96;
```
-/
def getAmount0Delta (sqrtRatioAX96 sqrtRatioBX96 : U160) (liquidity : U128) (roundUp : Bool) :
    Option U256 :=
  let s := sortPrices sqrtRatioAX96 sqrtRatioBX96
  let numerator1 : U256 := liquidity.setWidth 256 <<< 96
  let numerator2 : U256 := (s.2 - s.1).setWidth 256
  if s.1 = 0 then none
  else if roundUp then
    (mulDivRoundingUp512 numerator1 numerator2 (s.2.setWidth 256)).map
      (fun x => divRoundingUp x (s.1.setWidth 256))
  else
    (mulDiv512 numerator1 numerator2 (s.2.setWidth 256)).map (fun x => x / s.1.setWidth 256)

/-- Uniswap v3 `SqrtPriceMath.getAmount1Delta`:

```
if (sqrtRatioAX96 > sqrtRatioBX96) (sqrtRatioAX96, sqrtRatioBX96) = (sqrtRatioBX96, sqrtRatioAX96);
return roundUp
    ? FullMath.mulDivRoundingUp(liquidity, sqrtRatioBX96 - sqrtRatioAX96, FixedPoint96.Q96)
    : FullMath.mulDiv(liquidity, sqrtRatioBX96 - sqrtRatioAX96, FixedPoint96.Q96);
```
-/
def getAmount1Delta (sqrtRatioAX96 sqrtRatioBX96 : U160) (liquidity : U128) (roundUp : Bool) :
    Option U256 :=
  let s := sortPrices sqrtRatioAX96 sqrtRatioBX96
  if roundUp then
    mulDivRoundingUp512 (liquidity.setWidth 256) ((s.2 - s.1).setWidth 256) (BitVec.ofNat 256 Q96)
  else mulDiv512 (liquidity.setWidth 256) ((s.2 - s.1).setWidth 256) (BitVec.ofNat 256 Q96)

/-- The value of a widened word. -/
theorem toNat_setWidth_256 {w : Nat} (x : BitVec w) (h : w ≤ 256) : (x.setWidth 256).toNat = x.toNat :=
  toNat_setWidth_of_le x h

/-- The value of `uint256(liquidity) << 96`: no bit is lost. -/
theorem toNat_liquidity_shl (L : U128) : (L.setWidth 256 <<< 96).toNat = L.toNat * 2 ^ 96 := by
  have hL := L.isLt
  rw [toNat_shiftLeft_of_lt _ _ (by rw [toNat_setWidth_256 L (by decide)]; omega),
    toNat_setWidth_256 L (by decide)]

/-- The value of `sqrtRatioBX96 - sqrtRatioAX96` after sorting. -/
theorem toNat_sorted_diff (a b : U160) :
    (((sortPrices a b).2 - (sortPrices a b).1).setWidth 256).toNat =
      max a.toNat b.toNat - min a.toNat b.toNat := by
  have ⟨h1, h2⟩ := toNat_sortPrices a b
  rw [toNat_setWidth_256 _ (by decide), toNat_sub_of_le _ _ (by rw [h1, h2]; omega), h1, h2]

/-- `getAmount0Delta` reverts exactly when the lower sqrt price is zero. -/
theorem getAmount0Delta_eq_none_iff (a b : U160) (L : U128) (up : Bool) :
    getAmount0Delta a b L up = none ↔ min a.toNat b.toNat = 0 := by
  have ⟨h1, h2⟩ := toNat_sortPrices a b
  have hL := L.isLt
  have hn1 := toNat_liquidity_shl L
  have hn2 := toNat_sorted_diff a b
  unfold getAmount0Delta
  dsimp only
  by_cases hz : (sortPrices a b).1 = 0
  · rw [ite_eq_left hz]; rw [eq_zero_iff_toNat, h1] at hz; simp [hz]
  · rw [ite_eq_right hz]
    have hlo : min a.toNat b.toNat ≠ 0 := by rw [← h1]; exact fun e => hz (eq_zero_iff_toNat.2 e)
    simp only [hlo, iff_false]
    have hhi : 0 < ((sortPrices a b).2.setWidth 256).toNat := by
      rw [toNat_setWidth_256 _ (by decide), h2]; omega
    cases up with
    | true =>
      rw [ite_eq_left rfl, mulDivRoundingUp512_eq]
      intro h
      rw [Option.map_eq_none_iff, fullMulDivUp_eq_none_iff] at h
      rcases h with h | h
      · omega
      · rw [hn1, hn2, toNat_setWidth_256 _ (by decide), h2] at h
        have : L.toNat * 2 ^ 96 * (max a.toNat b.toNat - min a.toNat b.toNat) ≤
            (2 ^ 256 - 1) * max a.toNat b.toNat :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
    | false =>
      rw [ite_eq_right (by decide), mulDiv512_eq]
      intro h
      rw [Option.map_eq_none_iff, fullMulDiv_eq_none_iff] at h
      rcases h with h | h
      · omega
      · rw [hn1, hn2, toNat_setWidth_256 _ (by decide), h2] at h
        have : L.toNat * 2 ^ 96 * (max a.toNat b.toNat - min a.toNat b.toNat) <
            2 ^ 256 * max a.toNat b.toNat :=
          Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega)
        omega

/-- The value of `getAmount0Delta`: the exact amount of token0,
`liquidity * (hi - lo) * 2^96 / (lo * hi)`, rounded up when `roundUp` holds and down otherwise. -/
theorem toNat_getAmount0Delta {a b : U160} {L : U128} {up : Bool} {amt : U256}
    (h : getAmount0Delta a b L up = some amt) :
    amt.toNat = if up then
        ceilDiv (amount0Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat))
          (min a.toNat b.toNat * max a.toNat b.toNat)
      else amount0Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) /
          (min a.toNat b.toNat * max a.toNat b.toNat) := by
  have ⟨h1, h2⟩ := toNat_sortPrices a b
  have hn1 := toNat_liquidity_shl L
  have hn2 := toNat_sorted_diff a b
  have hlo : min a.toNat b.toNat ≠ 0 := by
    intro e; rw [← getAmount0Delta_eq_none_iff a b L up] at e; rw [e] at h; cases h
  unfold getAmount0Delta at h
  dsimp only at h
  have hz : (sortPrices a b).1 ≠ 0 := by
    intro e; rw [eq_zero_iff_toNat, h1] at e; exact hlo e
  rw [ite_eq_right hz] at h
  have hA : ((sortPrices a b).1.setWidth 256).toNat = min a.toNat b.toNat := by
    rw [toNat_setWidth_256 _ (by decide), h1]
  have hB : ((sortPrices a b).2.setWidth 256).toNat = max a.toNat b.toNat := by
    rw [toNat_setWidth_256 _ (by decide), h2]
  have hlo' : 0 < min a.toNat b.toNat := Nat.pos_of_ne_zero hlo
  have hhi' : 0 < max a.toNat b.toNat := by omega
  have hnum : L.toNat * 2 ^ 96 * (max a.toNat b.toNat - min a.toNat b.toNat) =
      amount0Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) := by
    unfold amount0Num; rw [Nat.mul_right_comm]
  cases up with
  | true =>
    rw [ite_eq_left rfl, mulDivRoundingUp512_eq] at h
    rw [ite_eq_left rfl]
    cases hx : fullMulDivUp (L.setWidth 256 <<< 96) (((sortPrices a b).2 - (sortPrices a b).1).setWidth 256)
        ((sortPrices a b).2.setWidth 256) with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rw [toNat_divRoundingUp, toNat_of_fullMulDivUp hx, hn1, hn2, hA, hB, hnum,
        ceilDiv_ceilDiv _ hlo' hhi']
  | false =>
    rw [ite_eq_right (by decide), mulDiv512_eq] at h
    rw [ite_eq_right (by decide)]
    cases hx : fullMulDiv (L.setWidth 256 <<< 96) (((sortPrices a b).2 - (sortPrices a b).1).setWidth 256)
        ((sortPrices a b).2.setWidth 256) with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      rw [BitVec.toNat_udiv, toNat_of_fullMulDiv hx, hn1, hn2, hA, hB, hnum, div_div_eq_div_mul']

/-- Rounded up, the amount of token0 covers the exact amount, by less than one unit:
`exact ≤ amount * (lo * hi) < exact + lo * hi`. -/
theorem getAmount0Delta_up_spec {a b : U160} {L : U128} {amt : U256}
    (h : getAmount0Delta a b L true = some amt) :
    amount0Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) ≤
        amt.toNat * (min a.toNat b.toNat * max a.toNat b.toNat) ∧
      amt.toNat * (min a.toNat b.toNat * max a.toNat b.toNat) <
        amount0Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) +
          min a.toNat b.toNat * max a.toNat b.toNat := by
  have hlo : min a.toNat b.toNat ≠ 0 := by
    intro e; rw [← getAmount0Delta_eq_none_iff a b L true] at e; rw [e] at h; cases h
  rw [toNat_getAmount0Delta h, ite_eq_left rfl]
  exact ceilDiv_spec _ _ (Nat.mul_pos (Nat.pos_of_ne_zero hlo) (by omega))

/-- Rounded down, the amount of token0 is at most the exact amount, by less than one unit. -/
theorem getAmount0Delta_down_spec {a b : U160} {L : U128} {amt : U256}
    (h : getAmount0Delta a b L false = some amt) :
    amt.toNat * (min a.toNat b.toNat * max a.toNat b.toNat) ≤
        amount0Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) ∧
      amount0Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) <
        (amt.toNat + 1) * (min a.toNat b.toNat * max a.toNat b.toNat) := by
  have hlo : min a.toNat b.toNat ≠ 0 := by
    intro e; rw [← getAmount0Delta_eq_none_iff a b L false] at e; rw [e] at h; cases h
  rw [toNat_getAmount0Delta h, ite_eq_right (by decide)]
  exact floor_spec _ _ (Nat.mul_pos (Nat.pos_of_ne_zero hlo) (by omega))

/-- `getAmount1Delta` never reverts. -/
theorem getAmount1Delta_isSome (a b : U160) (L : U128) (up : Bool) :
    (getAmount1Delta a b L up).isSome := by
  have hn2 := toNat_sorted_diff a b
  have hL := L.isLt
  have ha := a.isLt; have hb := b.isLt
  have hq : (BitVec.ofNat 256 Q96).toNat = 2 ^ 96 := by rw [Q96_eq]; exact toNat_ofNat_of_lt (by decide)
  have hprod : L.toNat * (max a.toNat b.toNat - min a.toNat b.toNat) < 2 ^ 128 * 2 ^ 160 :=
    Nat.mul_lt_mul_of_lt_of_le hL (by omega) (by decide)
  unfold getAmount1Delta
  cases up with
  | true =>
    rw [ite_eq_left rfl, mulDivRoundingUp512_eq, fullMulDivUp_isSome_iff, hn2, hq,
      toNat_setWidth_256 L (by decide)]
    exact ⟨by decide, by omega⟩
  | false =>
    rw [ite_eq_right (by decide), mulDiv512_eq, fullMulDiv_isSome_iff, hn2, hq,
      toNat_setWidth_256 L (by decide)]
    exact ⟨by decide, by omega⟩

/-- The value of `getAmount1Delta`: the exact amount of token1, `liquidity * (hi - lo) / 2^96`,
rounded up when `roundUp` holds and down otherwise. -/
theorem toNat_getAmount1Delta {a b : U160} {L : U128} {up : Bool} {amt : U256}
    (h : getAmount1Delta a b L up = some amt) :
    amt.toNat = if up then ceilDiv (amount1Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat)) (2 ^ 96)
      else amount1Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) / 2 ^ 96 := by
  have hn2 := toNat_sorted_diff a b
  have hq : (BitVec.ofNat 256 Q96).toNat = 2 ^ 96 := by rw [Q96_eq]; exact toNat_ofNat_of_lt (by decide)
  unfold getAmount1Delta at h
  cases up with
  | true =>
    rw [ite_eq_left rfl, mulDivRoundingUp512_eq] at h
    rw [ite_eq_left rfl, toNat_of_fullMulDivUp h, hn2, hq, toNat_setWidth_256 L (by decide)]; rfl
  | false =>
    rw [ite_eq_right (by decide), mulDiv512_eq] at h
    rw [ite_eq_right (by decide), toNat_of_fullMulDiv h, hn2, hq, toNat_setWidth_256 L (by decide)]; rfl

/-- Rounded up, the amount of token1 covers the exact amount, by less than one unit. -/
theorem getAmount1Delta_up_spec {a b : U160} {L : U128} {amt : U256}
    (h : getAmount1Delta a b L true = some amt) :
    amount1Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) ≤ amt.toNat * 2 ^ 96 ∧
      amt.toNat * 2 ^ 96 < amount1Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) + 2 ^ 96 := by
  rw [toNat_getAmount1Delta h, ite_eq_left rfl]; exact ceilDiv_spec _ _ (Nat.two_pow_pos 96)

/-- Rounded down, the amount of token1 is at most the exact amount, by less than one unit. -/
theorem getAmount1Delta_down_spec {a b : U160} {L : U128} {amt : U256}
    (h : getAmount1Delta a b L false = some amt) :
    amt.toNat * 2 ^ 96 ≤ amount1Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) ∧
      amount1Num L.toNat (min a.toNat b.toNat) (max a.toNat b.toNat) < (amt.toNat + 1) * 2 ^ 96 := by
  rw [toNat_getAmount1Delta h, ite_eq_right (by decide)]; exact floor_spec _ _ (Nat.two_pow_pos 96)

/-! ## The next price after adding token0 -/

/-- Uniswap v3 `SqrtPriceMath.getNextSqrtPriceFromAmount0RoundingUp` for `add = true` (a swap
of token0 in):

```
if (amount == 0) return sqrtPX96;
uint256 numerator1 = uint256(liquidity) << FixedPoint96.RESOLUTION;
uint256 product;
if ((product = amount * sqrtPX96) / amount == sqrtPX96) {
    uint256 denominator = numerator1 + product;
    if (denominator >= numerator1)
        return uint160(FullMath.mulDivRoundingUp(numerator1, sqrtPX96, denominator));
}
return uint160(UnsafeMath.divRoundingUp(numerator1, (numerator1 / sqrtPX96).add(amount)));
```

`LowGasSafeMath.add` reverts on overflow (`checkedAdd`); the conversions to `uint160` truncate. -/
def getNextSqrtPriceFromAmount0Add (sqrtPX96 : U160) (liquidity : U128) (amount : U256) :
    Option U160 :=
  if amount = 0 then some sqrtPX96
  else
    let numerator1 : U256 := liquidity.setWidth 256 <<< 96
    let sp : U256 := sqrtPX96.setWidth 256
    let product := amount * sp
    let fallback := (checkedAdd (numerator1 / sp) amount).map
      (fun d => (divRoundingUp numerator1 d).setWidth 160)
    if product / amount = sp then
      let denominator := numerator1 + product
      if denominator ≥ numerator1 then
        (mulDivRoundingUp512 numerator1 sp denominator).map (fun x => x.setWidth 160)
      else fallback
    else fallback

/-- The next price after adding token0 is at least the exact next price
`liquidity * 2^96 * sqrtP / (liquidity * 2^96 + amount * sqrtP)` (the price moves less than
exactly, in the pool's favour) and at most the current price. -/
theorem getNextSqrtPriceFromAmount0Add_spec {sp : U160} {L : U128} {amount : U256} {p : U160}
    (h : getNextSqrtPriceFromAmount0Add sp L amount = some p) :
    L.toNat * 2 ^ 96 * sp.toNat ≤ p.toNat * (L.toNat * 2 ^ 96 + amount.toNat * sp.toNat) ∧
      p.toNat ≤ sp.toNat := by
  unfold getNextSqrtPriceFromAmount0Add at h
  by_cases h0 : amount = 0
  · rw [ite_eq_left h0, Option.some.injEq] at h
    subst h
    refine ⟨?_, Nat.le_refl _⟩
    rw [eq_zero_iff_toNat.1 h0, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_of_eq (Nat.mul_comm _ _)
  rw [ite_eq_right h0] at h
  dsimp only at h
  have hn1 := toNat_liquidity_shl L
  have hsp : (sp.setWidth 256).toNat = sp.toNat := toNat_setWidth_256 sp (by decide)
  have hspl := sp.isLt
  have hA : 0 < amount.toNat := toNat_pos_of_ne_zero h0
  -- the fallback branch, reached only with a positive price
  have hfb : ∀ q, sp.toNat ≠ 0 →
      (checkedAdd ((L.setWidth 256 <<< 96) / sp.setWidth 256) amount).map
        (fun d => (divRoundingUp (L.setWidth 256 <<< 96) d).setWidth 160) = some q →
      L.toNat * 2 ^ 96 * sp.toNat ≤ q.toNat * (L.toNat * 2 ^ 96 + amount.toNat * sp.toNat) ∧
        q.toNat ≤ sp.toNat := by
    intro q hs0 hq
    cases hd : checkedAdd ((L.setWidth 256 <<< 96) / sp.setWidth 256) amount with
    | none => rw [hd] at hq; cases hq
    | some d =>
      rw [hd] at hq
      simp only [Option.map_some, Option.some.injEq] at hq
      subst hq
      have hdv := toNat_of_checkedAdd hd
      rw [BitVec.toNat_udiv, hn1, hsp] at hdv
      have hdpos : 0 < d.toNat := by rw [hdv]; exact Nat.lt_of_lt_of_le hA (Nat.le_add_left _ _)
      have hc := toNat_divRoundingUp (L.setWidth 256 <<< 96) d
      rw [hn1] at hc
      have hsp0 : 0 < sp.toNat := Nat.pos_of_ne_zero hs0
      -- `d > numerator1 / sqrtP`, so `numerator1 / d < sqrtP`
      have hlt : L.toNat * 2 ^ 96 < sp.toNat * d.toNat := by
        have h1 := lt_div_add_one_mul (L.toNat * 2 ^ 96) sp.toNat hsp0
        have h2 : (L.toNat * 2 ^ 96 / sp.toNat + 1) * sp.toNat ≤ d.toNat * sp.toNat :=
          Nat.mul_le_mul_right _ (by rw [hdv]; exact Nat.add_le_add_left hA _)
        rw [Nat.mul_comm sp.toNat]; exact Nat.lt_of_lt_of_le h1 h2
      have hle : ceilDiv (L.toNat * 2 ^ 96) d.toNat ≤ sp.toNat := by
        rw [ceilDiv_le_iff hdpos]; exact Nat.le_of_lt hlt
      have hfit : ceilDiv (L.toNat * 2 ^ 96) d.toNat < 2 ^ 160 := Nat.lt_of_le_of_lt hle hspl
      rw [BitVec.toNat_setWidth, hc, Nat.mod_eq_of_lt hfit]
      refine ⟨?_, hle⟩
      have hcv := le_ceilDiv_mul (L.toNat * 2 ^ 96) d.toNat hdpos
      have hdd : d.toNat * sp.toNat ≤ L.toNat * 2 ^ 96 + amount.toNat * sp.toNat := by
        rw [hdv, Nat.add_mul]
        exact Nat.add_le_add_right (div_mul_le _ _) _
      calc L.toNat * 2 ^ 96 * sp.toNat
          ≤ ceilDiv (L.toNat * 2 ^ 96) d.toNat * d.toNat * sp.toNat := Nat.mul_le_mul_right _ hcv
        _ = ceilDiv (L.toNat * 2 ^ 96) d.toNat * (d.toNat * sp.toNat) := Nat.mul_assoc _ _ _
        _ ≤ _ := Nat.mul_le_mul_left _ hdd
  by_cases hm : amount * sp.setWidth 256 / amount = sp.setWidth 256
  · rw [ite_eq_left hm] at h
    have hnof : amount.toNat * sp.toNat < 2 ^ 256 := by
      refine Nat.lt_of_not_le fun h' => ?_
      have := (mul_div_ne_iff (x := amount) (y := sp.setWidth 256) h0).2 (by rw [hsp]; exact h')
      exact this hm
    have hprod : (amount * sp.setWidth 256).toNat = amount.toNat * sp.toNat := by
      rw [toNat_mul_of_lt _ _ (by rw [hsp]; exact hnof), hsp]
    by_cases hd : L.setWidth 256 <<< 96 + amount * sp.setWidth 256 ≥ L.setWidth 256 <<< 96
    · rw [ite_eq_left hd] at h
      have hdnof : L.toNat * 2 ^ 96 + amount.toNat * sp.toNat < 2 ^ 256 := by
        refine Nat.lt_of_not_le fun h' => ?_
        have := (add_lt_left_iff (x := L.setWidth 256 <<< 96) (y := amount * sp.setWidth 256)).2
          (by rw [hn1, hprod]; exact h')
        rw [GE.ge, BitVec.le_def] at hd
        rw [BitVec.lt_def] at this
        omega
      have hden : (L.setWidth 256 <<< 96 + amount * sp.setWidth 256).toNat =
          L.toNat * 2 ^ 96 + amount.toNat * sp.toNat := by
        rw [toNat_add_of_lt _ _ (by rw [hn1, hprod]; exact hdnof), hn1, hprod]
      rw [mulDivRoundingUp512_eq] at h
      cases hx : fullMulDivUp (L.setWidth 256 <<< 96) (sp.setWidth 256)
          (L.setWidth 256 <<< 96 + amount * sp.setWidth 256) with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have ⟨hdpos, _, hxv⟩ := fullMulDivUp_eq_some_iff.1 hx
        rw [hn1, hsp, hden] at hxv
        rw [hden] at hdpos
        have hle : ceilDiv (L.toNat * 2 ^ 96 * sp.toNat)
            (L.toNat * 2 ^ 96 + amount.toNat * sp.toNat) ≤ sp.toNat := by
          rw [ceilDiv_le_iff hdpos, Nat.mul_comm sp.toNat]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        have hfit := Nat.lt_of_le_of_lt hle hspl
        rw [BitVec.toNat_setWidth, hxv, Nat.mod_eq_of_lt hfit]
        exact ⟨le_ceilDiv_mul _ _ hdpos, hle⟩
    · rw [ite_eq_right hd] at h
      refine hfb p (fun e => hd ?_) h
      have : (amount * sp.setWidth 256).toNat = 0 := by rw [hprod, e, Nat.mul_zero]
      rw [GE.ge, BitVec.le_def, toNat_add_of_lt _ _ (by rw [this, Nat.add_zero]; exact BitVec.isLt _),
        this, Nat.add_zero]
      exact Nat.le_refl _
  · rw [ite_eq_right hm] at h
    refine hfb p (fun e => hm ?_) h
    have hz : sp.setWidth 256 = 0 := by rw [eq_zero_iff_toNat, hsp, e]
    rw [hz]
    simp

end ProofForgeFin.Evm
