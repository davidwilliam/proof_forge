import ProofForgeFin.Evm.MulDiv
import ProofForgeFin.Evm.Bits
/-!
# The 512-bit algorithm of `FullMath.mulDiv`

`mulDiv512` is a line-by-line port of `FullMath.mulDiv` of Uniswap v4-core (Solidity 0.8, the
same algorithm as Uniswap v3-core's `FullMath.mulDiv` and OpenZeppelin's `Math.mulDiv`, by Remco
Bloemen): it computes `a * b / denominator` with a 512-bit intermediate product held in two
words `[prod1 prod0]`, without any 512-bit division:

1. `prod0 = a * b mod 2^256` and `prod1 = (mulmod(a, b, 2^256 - 1) - prod0 - borrow) mod 2^256`
   are the two halves of the product (Chinese remainder theorem);
2. `require(denominator > prod1)` reverts exactly when the quotient does not fit (or the
   denominator is zero);
3. if `prod1 = 0` the product fits and the result is `prod0 / denominator`;
4. otherwise the remainder `mulmod(a, b, denominator)` is subtracted so that the division is
   exact, the largest power of two dividing the denominator (`twos`) is divided out of both, the
   odd part of the denominator is inverted modulo `2^256` by a seed correct to 4 bits and six
   Newton steps (each doubles the number of correct bits: 8, 16, ..., 256), and the quotient is
   the low half times the inverse.

`mulDiv512_eq` proves that the port returns `fullMulDiv a b d` on every input: the exact floor
quotient when it fits, and a revert exactly when `d = 0` or the quotient does not fit.
`mulDivRoundingUp512` (`FullMath.mulDivRoundingUp`) is proved equal to `fullMulDivUp`.

The EVM's `MULMOD` is `mulmod` (0 for a zero modulus); its `LT` and `GT`, which return 1 or 0, are
`if _ then 1 else 0`.
-/

namespace ProofForgeFin.Evm

/-- The EVM's `MULMOD`: `a * b % m` computed with unbounded precision, and 0 for `m = 0`. -/
def mulmod (a b m : U256) : U256 :=
  if m = 0 then 0 else BitVec.ofNat 256 (a.toNat * b.toNat % m.toNat)

/-- The value of `MULMOD`. -/
theorem toNat_mulmod (a b m : U256) :
    (mulmod a b m).toNat = if m.toNat = 0 then 0 else a.toNat * b.toNat % m.toNat := by
  unfold mulmod
  by_cases h : m = 0
  · subst h; simp
  · have hm : m.toNat ≠ 0 := fun e => h (eq_zero_iff_toNat.2 e)
    rw [ite_eq_right h, ite_eq_right hm, toNat_ofNat_of_lt]
    exact Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hm)) m.isLt

/-! ## Congruences modulo `2^256` -/

/-- A wrapped product is congruent to the product modulo `2^256`. -/
theorem dvd_toNat_mul_sub (x y : U256) :
    (2 ^ 256 : Int) ∣ ((x * y).toNat : Int) - (x.toNat : Int) * (y.toNat : Int) := by
  rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul]
  generalize (x.toNat : Int) * (y.toNat : Int) = P
  have : ((2 ^ 256 : Nat) : Int) = 2 ^ 256 := by simp
  rw [this]
  omega

/-- A wrapped difference is congruent to the difference modulo `2^256`. -/
theorem dvd_toNat_sub_sub (x y : U256) :
    (2 ^ 256 : Int) ∣ ((x - y).toNat : Int) - ((x.toNat : Int) - (y.toNat : Int)) := by
  rw [BitVec.toNat_sub]
  have := x.isLt; have := y.isLt
  omega

/-- Congruence is compatible with products. -/
theorem dvd_mul_sub_mul {N A a B b : Int} (h1 : N ∣ A - a) (h2 : N ∣ B - b) :
    N ∣ A * B - a * b := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  exact ⟨A * c2 + b * c1, by grind⟩

/-! ## The inverse modulo `2^256` -/

/-- Hensel lifting in one Newton step: if `d * x ≡ 1 (mod 2^j)` and `y ≡ x * (2 - d * x)
(mod N)` for a multiple `N` of `2^(2j)`, then `d * y ≡ 1 (mod 2^(2j))`. -/
theorem newton_step {N d x y : Int} {j : Nat} (hN : (2 : Int) ^ (2 * j) ∣ N)
    (hx : (2 : Int) ^ j ∣ d * x - 1) (hy : N ∣ y - x * (2 - d * x)) :
    (2 : Int) ^ (2 * j) ∣ d * y - 1 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨s, hs⟩ := hy
  obtain ⟨u, hu⟩ := hN
  refine ⟨d * u * s - t * t, ?_⟩
  have hy' : y = N * s + x * (2 - d * x) := by omega
  have h2 : (2 : Int) ^ (2 * j) = 2 ^ j * 2 ^ j := by rw [Nat.two_mul, Int.pow_add]
  subst hy'
  rw [hu, h2]
  have hdx : d * x = 2 ^ j * t + 1 := by omega
  grind

/-- One line `inv *= 2 - denominator * inv` of `FullMath.mulDiv` doubles the number of correct
bits of the inverse, up to 256. -/
theorem newton_word {d x : U256} {j : Nat} (hj : 2 * j ≤ 256)
    (hx : (2 : Int) ^ j ∣ (d.toNat : Int) * (x.toNat : Int) - 1) :
    (2 : Int) ^ (2 * j) ∣ (d.toNat : Int) * ((x * (2 - d * x)).toNat : Int) - 1 := by
  have hN : (2 : Int) ^ (2 * j) ∣ 2 ^ 256 := by
    refine ⟨2 ^ (256 - 2 * j), ?_⟩
    rw [← Int.pow_add]; congr 1; omega
  apply newton_step hN hx
  have h1 := dvd_toNat_mul_sub x (2 - d * x)
  have h2 := dvd_toNat_sub_sub 2 (d * x)
  have h3 := dvd_toNat_mul_sub d x
  have h22 : (2 : U256).toNat = 2 := rfl
  rw [h22] at h2
  have h4 : (2 ^ 256 : Int) ∣ ((2 - d * x).toNat : Int) - (2 - (d.toNat : Int) * (x.toNat : Int)) := by
    omega
  have h5 := dvd_mul_sub_mul (⟨0, by simp⟩ : (2 ^ 256 : Int) ∣ (x.toNat : Int) - x.toNat) h4
  have h6 := Int.dvd_add h1 h5
  have e : ((x * (2 - d * x)).toNat : Int) - (x.toNat : Int) * (2 - (d.toNat : Int) * (x.toNat : Int)) =
      ((x * (2 - d * x)).toNat : Int) - (x.toNat : Int) * ((2 - d * x).toNat : Int) +
      ((x.toNat : Int) * ((2 - d * x).toNat : Int) -
        (x.toNat : Int) * (2 - (d.toNat : Int) * (x.toNat : Int))) := by omega
  rw [e]; exact h6

/-- The seed `inv = (3 * denominator) ^ 2` is an inverse of an odd `denominator` modulo `2^4`. -/
theorem seed_inv {d : U256} (hd : d.toNat % 2 = 1) :
    (2 : Int) ^ 4 ∣ (d.toNat : Int) * (((3 * d) ^^^ 2).toNat : Int) - 1 := by
  have key : ∀ r < 16, r % 2 = 1 → r * ((3 * r % 16) ^^^ 2) % 16 = 1 := by decide
  have hx : ((3 * d) ^^^ 2).toNat % 16 = (3 * (d.toNat % 16) % 16) ^^^ 2 := by
    rw [BitVec.toNat_xor, BitVec.toNat_mul]
    have h3 : (3 : U256).toNat = 3 := rfl
    have h2 : (2 : U256).toNat = 2 := rfl
    rw [h3, h2, show (16 : Nat) = 2 ^ 4 from rfl, Nat.xor_mod_two_pow,
      Nat.mod_mod_of_dvd _ (by decide : 2 ^ 4 ∣ 2 ^ 256), ← Nat.mul_mod_mod]
  have hm : d.toNat * ((3 * d) ^^^ 2).toNat % 16 = 1 := by
    rw [Nat.mul_mod, hx]
    exact key _ (Nat.mod_lt _ (by decide)) (by omega)
  have : ((d.toNat * ((3 * d) ^^^ 2).toNat : Nat) : Int) =
      (d.toNat : Int) * (((3 * d) ^^^ 2).toNat : Int) := by simp
  rw [← this]
  generalize d.toNat * ((3 * d) ^^^ 2).toNat = m at hm
  omega

/-! ## The port -/

/-- Uniswap v4-core `FullMath.mulDiv(uint256 a, uint256 b, uint256 denominator)`, line by line
(every operation is in an `unchecked` block or in assembly, so it wraps):

```
uint256 prod0 = a * b;
uint256 prod1;
assembly { let mm := mulmod(a, b, not(0)) prod1 := sub(sub(mm, prod0), lt(mm, prod0)) }
require(denominator > prod1);
if (prod1 == 0) { assembly { result := div(prod0, denominator) } return result; }
uint256 remainder;
assembly { remainder := mulmod(a, b, denominator) }
assembly { prod1 := sub(prod1, gt(remainder, prod0)) prod0 := sub(prod0, remainder) }
uint256 twos = (0 - denominator) & denominator;
assembly { denominator := div(denominator, twos) }
assembly { prod0 := div(prod0, twos) }
assembly { twos := add(div(sub(0, twos), twos), 1) }
prod0 |= prod1 * twos;
uint256 inv = (3 * denominator) ^ 2;
inv *= 2 - denominator * inv; // six times
result = prod0 * inv;
```

The `require` is `none`. -/
def mulDiv512 (a b denominator : U256) : Option U256 :=
  let prod0 := a * b
  let mm := mulmod a b (BitVec.allOnes 256)
  let prod1 := mm - prod0 - (if mm < prod0 then 1 else 0)
  if prod1 < denominator then
    if prod1 = 0 then some (prod0 / denominator)
    else
      let remainder := mulmod a b denominator
      let prod1 := prod1 - (if prod0 < remainder then 1 else 0)
      let prod0 := prod0 - remainder
      let twos := (0 - denominator) &&& denominator
      let denominator := denominator / twos
      let prod0 := prod0 / twos
      let twos := (0 - twos) / twos + 1
      let prod0 := prod0 ||| prod1 * twos
      let inv := (3 * denominator) ^^^ 2
      let inv := inv * (2 - denominator * inv)
      let inv := inv * (2 - denominator * inv)
      let inv := inv * (2 - denominator * inv)
      let inv := inv * (2 - denominator * inv)
      let inv := inv * (2 - denominator * inv)
      let inv := inv * (2 - denominator * inv)
      some (prod0 * inv)
  else none

/-! ## Correctness -/

/-- The high word: `mulmod(a, b, 2^256 - 1)` minus the low word, with a borrow, is
`a * b / 2^256` (the product modulo `2^256 - 1` and modulo `2^256` determine it). -/
theorem toNat_prod1 (a b : U256) :
    (mulmod a b (BitVec.allOnes 256) - a * b -
      (if mulmod a b (BitVec.allOnes 256) < a * b then 1 else 0)).toNat =
      a.toNat * b.toNat / 2 ^ 256 := by
  have ha := a.isLt; have hb := b.isLt
  have hP : a.toNat * b.toNat ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmm : (mulmod a b (BitVec.allOnes 256)).toNat = a.toNat * b.toNat % (2 ^ 256 - 1) := by
    rw [toNat_mulmod, BitVec.toNat_allOnes, ite_eq_right (by decide)]
  have hp0 : (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := BitVec.toNat_mul a b
  generalize mulmod a b (BitVec.allOnes 256) = mm at hmm ⊢
  generalize a * b = p0 at hp0 ⊢
  generalize a.toNat * b.toNat = P at hP hmm hp0 ⊢
  have hdm := Nat.div_add_mod P (2 ^ 256)
  have hL := Nat.mod_lt P (Nat.two_pow_pos 256)
  generalize P / 2 ^ 256 = H at hdm ⊢
  generalize P % 2 ^ 256 = L at hdm hL hp0
  have hHb : H ≤ 2 ^ 256 - 2 := by omega
  have hM : P % (2 ^ 256 - 1) = (H + L) % (2 ^ 256 - 1) := by
    have : P = (H + L) + (2 ^ 256 - 1) * H := by omega
    rw [this, Nat.add_mul_mod_self_left]
  rw [hM] at hmm
  have h1 : (1 : U256).toNat = 1 := rfl
  have h0 : (0 : U256).toNat = 0 := rfl
  by_cases hc : H + L < 2 ^ 256 - 1
  · rw [Nat.mod_eq_of_lt hc] at hmm
    have hge : ¬ mm < p0 := by rw [BitVec.lt_def, hmm, hp0]; omega
    rw [ite_eq_right hge, toNat_sub_of_le _ _ (by rw [h0]; omega), h0, Nat.sub_zero,
      toNat_sub_of_le _ _ (by rw [hmm, hp0]; omega), hmm, hp0]
    omega
  · have hm2 : (H + L) % (2 ^ 256 - 1) = H + L - (2 ^ 256 - 1) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm2] at hmm
    have hlt' : mm.toNat < p0.toNat := by rw [hmm, hp0]; omega
    have hlt : mm < p0 := BitVec.lt_def.2 hlt'
    rw [ite_eq_left hlt]
    have e2 : (mm - p0).toNat = 2 ^ 256 + mm.toNat - p0.toNat := toNat_sub_of_lt hlt'
    rw [toNat_sub_of_le _ _ (by rw [e2, h1, hmm, hp0]; omega), e2, h1, hmm, hp0]
    omega

/-- After the remainder is subtracted, `[prod1 prod0]` is the exact multiple
`a * b - a * b % d` of the denominator. -/
theorem toNat_sub_remainder {prod0 prod1 r : U256} {P D : Nat}
    (e0 : prod0.toNat = P % 2 ^ 256) (e1 : prod1.toNat = P / 2 ^ 256) (h1 : prod1 ≠ 0)
    (er : r.toNat = P % D) (hD : 0 < D) (hDN : D < 2 ^ 256) :
    (prod1 - (if prod0 < r then 1 else 0)).toNat * 2 ^ 256 + (prod0 - r).toNat = P - P % D := by
  have hdm := Nat.div_add_mod P (2 ^ 256)
  have hr1 := Nat.mod_lt P hD
  have hr2 := Nat.mod_le P D
  have hne : prod1.toNat ≠ 0 := fun e => h1 (eq_zero_iff_toNat.2 e)
  have hL := Nat.mod_lt P (Nat.two_pow_pos 256)
  have h1' : (1 : U256).toNat = 1 := rfl
  have h0' : (0 : U256).toNat = 0 := rfl
  by_cases hlt : prod0 < r
  · rw [ite_eq_left hlt]
    have hlt' := BitVec.lt_def.1 hlt
    rw [toNat_sub_of_le _ _ (by rw [h1']; omega), h1', toNat_sub_of_lt hlt', e0, e1, er]
    rw [e0, er] at hlt'
    rw [e1] at hne
    have : (P / 2 ^ 256 - 1) * 2 ^ 256 = P / 2 ^ 256 * 2 ^ 256 - 2 ^ 256 := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [this]
    generalize P / 2 ^ 256 = H at hdm hne ⊢
    generalize P % 2 ^ 256 = L at hdm hlt' hL ⊢
    generalize P % D = R at hr1 hr2 hlt' ⊢
    have : 2 ^ 256 ≤ H * 2 ^ 256 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    omega
  · rw [ite_eq_right hlt]
    have hge : r.toNat ≤ prod0.toNat := Nat.le_of_not_lt (fun h => hlt (BitVec.lt_def.2 h))
    rw [toNat_sub_of_le _ _ (by rw [h0']; omega), h0', Nat.sub_zero, toNat_sub_of_le _ _ hge,
      e0, e1, er]
    rw [e0, er] at hge
    generalize P / 2 ^ 256 = H at hdm ⊢
    generalize P % 2 ^ 256 = L at hdm hge hL ⊢
    generalize P % D = R at hr1 hr2 hge ⊢
    rw [Nat.mul_comm]
    omega

/-- The value modulo `2^256` of a natural number, cast to `Int`, is congruent to it. -/
theorem dvd_natCast_mod_sub (m : Nat) : (2 ^ 256 : Int) ∣ ((m % 2 ^ 256 : Nat) : Int) - (m : Int) := by
  rw [Int.natCast_emod]
  have : ((2 ^ 256 : Nat) : Int) = 2 ^ 256 := by simp
  rw [this]
  generalize (m : Int) = x
  omega

/-- `twos := add(div(sub(0, twos), twos), 1)` turns `2^k` into `2^(256 - k)` (into 0 for
`k = 0`). -/
theorem toNat_flip_twos {t : U256} {k : Nat} (et : t.toNat = 2 ^ k) (hk : k < 256) :
    ((0 - t) / t + 1).toNat = 2 ^ (256 - k) % 2 ^ 256 := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hw : 2 ^ 256 = 2 ^ (256 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hlt : 2 ^ k < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) hk
  have hneg : (0 - t).toNat = 2 ^ 256 - 2 ^ k := by
    rw [BitVec.toNat_sub, et]
    have : (0 : U256).toNat = 0 := rfl
    rw [this, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  have hq : (2 ^ 256 - 2 ^ k) / 2 ^ k = 2 ^ (256 - k) - 1 := by
    rw [hw, show 2 ^ (256 - k) * 2 ^ k - 2 ^ k = (2 ^ (256 - k) - 1) * 2 ^ k by
      rw [Nat.sub_mul, Nat.one_mul]]
    exact Nat.mul_div_cancel _ hpos
  have h1 : (1 : U256).toNat = 1 := rfl
  have hp : 0 < 2 ^ (256 - k) := Nat.two_pow_pos _
  rw [BitVec.toNat_add, BitVec.toNat_udiv, hneg, et, hq, h1, Nat.sub_add_cancel hp]

/-- Shifting the high word into the low word: with `twos = 2^(256 - k)`, `prod0 / 2^k |
prod1 * twos` is the exact quotient `[prod1 prod0] / 2^k` modulo `2^256`. -/
theorem toNat_shift_in {p0 p1 t' : U256} {k : Nat} (hk : k < 256)
    (et' : t'.toNat = 2 ^ (256 - k) % 2 ^ 256) :
    (p0 / BitVec.ofNat 256 (2 ^ k) ||| p1 * t').toNat =
      (p1.toNat * 2 ^ 256 + p0.toNat) / 2 ^ k % 2 ^ 256 := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hw : 2 ^ 256 = 2 ^ k * 2 ^ (256 - k) := by rw [← Nat.pow_add]; congr 1; omega
  have hlt : 2 ^ k < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) hk
  have hc : (BitVec.ofNat 256 (2 ^ k)).toNat = 2 ^ k := toNat_ofNat_of_lt hlt
  have hl := p0.isLt
  have hsmall : p0.toNat / 2 ^ k < 2 ^ (256 - k) := by
    rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm, ← hw]; exact hl
  have hhigh : (p1 * t').toNat = p1.toNat % 2 ^ k * 2 ^ (256 - k) := by
    rw [BitVec.toNat_mul, et', Nat.mul_mod_mod, hw, Nat.mul_mod_mul_right]
  rw [BitVec.toNat_or, BitVec.toNat_udiv, hc, hhigh, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt hsmall, Nat.shiftLeft_eq]
  have hsplit : p1.toNat * 2 ^ 256 + p0.toNat =
      p0.toNat + (p1.toNat * 2 ^ (256 - k)) * 2 ^ k := by
    rw [hw, Nat.mul_comm (2 ^ k), ← Nat.mul_assoc]; omega
  rw [hsplit, Nat.add_mul_div_right _ _ hpos]
  have hm := Nat.mod_add_div p1.toNat (2 ^ k)
  have hbound : p1.toNat % 2 ^ k * 2 ^ (256 - k) + p0.toNat / 2 ^ k < 2 ^ 256 := by
    have h1 : p1.toNat % 2 ^ k + 1 ≤ 2 ^ k := Nat.mod_lt _ hpos
    have h2 : (p1.toNat % 2 ^ k + 1) * 2 ^ (256 - k) ≤ 2 ^ k * 2 ^ (256 - k) :=
      Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul, ← hw] at h2
    omega
  have e : p0.toNat / 2 ^ k + p1.toNat * 2 ^ (256 - k) =
      (p1.toNat % 2 ^ k * 2 ^ (256 - k) + p0.toNat / 2 ^ k) +
        2 ^ 256 * (p1.toNat / 2 ^ k) := by
    rw [hw]
    have : p1.toNat * 2 ^ (256 - k) =
        (p1.toNat % 2 ^ k + 2 ^ k * (p1.toNat / 2 ^ k)) * 2 ^ (256 - k) := by rw [hm]
    rw [this, Nat.add_mul]
    have : 2 ^ k * (p1.toNat / 2 ^ k) * 2 ^ (256 - k) =
        2 ^ k * 2 ^ (256 - k) * (p1.toNat / 2 ^ k) := by
      rw [Nat.mul_right_comm]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]

/-- `FullMath.mulDiv` returns the full-precision floor quotient `a * b / d` when it fits in 256
bits, and reverts exactly when `d = 0` or the quotient does not fit. -/
theorem mulDiv512_eq (a b d : U256) : mulDiv512 a b d = fullMulDiv a b d := by
  have ha := a.isLt; have hb := b.isLt; have hdl := d.isLt
  have e0 : (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := BitVec.toNat_mul a b
  have e1 := toNat_prod1 a b
  unfold mulDiv512
  dsimp only
  generalize hprod0 : a * b = prod0 at e0 e1 ⊢
  generalize hprod1 : mulmod a b (BitVec.allOnes 256) - prod0 -
    (if mulmod a b (BitVec.allOnes 256) < prod0 then 1 else 0) = prod1 at e1 ⊢
  by_cases hreq : prod1 < d
  case neg =>
    rw [ite_eq_right hreq]
    symm
    rw [fullMulDiv_eq_none_iff]
    rw [BitVec.lt_def, e1] at hreq
    by_cases hd : d.toNat = 0
    · exact Or.inl hd
    · right
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 256)).1 (Nat.le_of_not_lt hreq)
      rw [Nat.mul_comm]; exact this
  case pos =>
  rw [ite_eq_left hreq]
  rw [BitVec.lt_def, e1] at hreq
  have hD : 0 < d.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hreq
  have hfit : a.toNat * b.toNat < 2 ^ 256 * d.toNat := by
    have := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 256)).1 hreq
    rw [Nat.mul_comm (2 ^ 256)]; exact this
  have hq : a.toNat * b.toNat / d.toNat < 2 ^ 256 := (div_lt_two_pow_iff hD).2 hfit
  rw [fullMulDiv_of_lt hD hfit]
  by_cases hz : prod1 = 0
  · rw [ite_eq_left hz, Option.some.injEq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, toNat_ofNat_of_lt hq, e0]
    have : a.toNat * b.toNat / 2 ^ 256 = 0 := by rw [← e1, hz]; rfl
    have hP : a.toNat * b.toNat < 2 ^ 256 := by
      have := Nat.div_add_mod (a.toNat * b.toNat) (2 ^ 256); omega
    rw [Nat.mod_eq_of_lt hP]
  rw [ite_eq_right hz, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_of_lt hq]
  -- the exact multiple of the denominator
  have hd0 : d ≠ 0 := fun e => by rw [eq_zero_iff_toNat.1 e] at hD; exact absurd hD (by decide)
  have er : (mulmod a b d).toNat = a.toNat * b.toNat % d.toNat := by
    rw [toNat_mulmod, ite_eq_right (by omega)]
  have esplit := toNat_sub_remainder e0 e1 hz er hD hdl
  generalize mulmod a b d = r at esplit ⊢
  generalize prod1 - (if prod0 < r then 1 else 0) = p1 at esplit ⊢
  generalize prod0 - r = p0 at esplit ⊢
  -- the power of two in the denominator
  have et := toNat_neg_and_self hd0
  have hdn : d.toNat ≠ 0 := by omega
  have ⟨hk1, hk2⟩ := trailingZeros_spec hdn
  have hk : trailingZeros d.toNat < 256 := trailingZeros_lt hdn hdl
  generalize trailingZeros d.toNat = k at et hk1 hk2 hk
  have htw : (0 - d) &&& d = BitVec.ofNat 256 (2 ^ k) := by
    apply BitVec.eq_of_toNat_eq
    rw [et, toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  rw [htw]
  have et' := toNat_flip_twos (t := BitVec.ofNat 256 (2 ^ k))
    (toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hk)) hk
  generalize (0 - BitVec.ofNat 256 (2 ^ k)) / BitVec.ofNat 256 (2 ^ k) + 1 = t' at et' ⊢
  have ep := toNat_shift_in (p0 := p0) (p1 := p1) hk et'
  generalize p0 / BitVec.ofNat 256 (2 ^ k) ||| p1 * t' = pf at ep ⊢
  rw [esplit] at ep
  -- the odd part of the denominator
  have hc : (BitVec.ofNat 256 (2 ^ k)).toNat = 2 ^ k :=
    toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hk)
  have eo : (d / BitVec.ofNat 256 (2 ^ k)).toNat = d.toNat / 2 ^ k := by
    rw [BitVec.toNat_udiv, hc]
  generalize d / BitVec.ofNat 256 (2 ^ k) = o at eo ⊢
  have hodd : o.toNat % 2 = 1 := by rw [eo]; exact hk2
  -- the exact quotient of the low word
  have hdo : d.toNat = 2 ^ k * o.toNat := by
    have := Nat.div_add_mod d.toNat (2 ^ k); rw [hk1, ← eo] at this; omega
  have hmul : a.toNat * b.toNat - a.toNat * b.toNat % d.toNat =
      d.toNat * (a.toNat * b.toNat / d.toNat) := by
    have := Nat.div_add_mod (a.toNat * b.toNat) d.toNat; omega
  rw [hmul] at ep
  generalize a.toNat * b.toNat / d.toNat = q at ep hq ⊢
  rw [hdo, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)] at ep
  -- the inverse
  have i0 := seed_inv hodd
  have i1 := newton_word (j := 4) (by decide) i0
  have i2 := newton_word (j := 8) (by decide) i1
  have i3 := newton_word (j := 16) (by decide) i2
  have i4 := newton_word (j := 32) (by decide) i3
  have i5 := newton_word (j := 64) (by decide) i4
  have i6 := newton_word (j := 128) (by decide) i5
  generalize (3 * o) ^^^ 2 = x0 at i0 i1 i2 i3 i4 i5 i6 ⊢
  generalize x0 * (2 - o * x0) = x1 at i1 i2 i3 i4 i5 i6 ⊢
  generalize x1 * (2 - o * x1) = x2 at i2 i3 i4 i5 i6 ⊢
  generalize x2 * (2 - o * x2) = x3 at i3 i4 i5 i6 ⊢
  generalize x3 * (2 - o * x3) = x4 at i4 i5 i6 ⊢
  generalize x4 * (2 - o * x4) = x5 at i5 i6 ⊢
  generalize x5 * (2 - o * x5) = x6 at i6 ⊢
  -- the result
  have hr := dvd_toNat_mul_sub pf x6
  have hpf : (2 ^ 256 : Int) ∣ (pf.toNat : Int) - (o.toNat : Int) * (q : Int) := by
    rw [ep, ← Int.natCast_mul]
    exact dvd_natCast_mod_sub _
  have h7 := dvd_mul_sub_mul hpf (⟨0, by simp⟩ : (2 ^ 256 : Int) ∣ (x6.toNat : Int) - x6.toNat)
  have h8 := dvd_mul_sub_mul (⟨0, by simp⟩ : (2 ^ 256 : Int) ∣ (q : Int) - q) i6
  have hfin : (2 ^ 256 : Int) ∣ ((pf * x6).toNat : Int) - (q : Int) := by
    obtain ⟨c1, hc1⟩ := hr
    obtain ⟨c2, hc2⟩ := h7
    obtain ⟨c3, hc3⟩ := h8
    exact ⟨c1 + c2 + c3, by grind⟩
  have := (pf * x6).isLt
  omega

/-- Uniswap `FullMath.mulDivRoundingUp`:

```
result = mulDiv(a, b, denominator);
if (mulmod(a, b, denominator) > 0) { require(result < type(uint256).max); result++; }
```
-/
def mulDivRoundingUp512 (a b denominator : U256) : Option U256 :=
  match mulDiv512 a b denominator with
  | none => none
  | some result =>
    if mulmod a b denominator > 0 then
      if result < BitVec.allOnes 256 then some (result + 1) else none
    else some result

/-- `FullMath.mulDivRoundingUp` returns the full-precision rounded-up quotient when it fits,
and reverts exactly when `d = 0` or that quotient does not fit. -/
theorem mulDivRoundingUp512_eq (a b d : U256) :
    mulDivRoundingUp512 a b d = fullMulDivUp a b d := by
  unfold mulDivRoundingUp512
  rw [mulDiv512_eq]
  have hm := toNat_mulmod a b d
  by_cases hd : d.toNat = 0
  · have : d = 0 := eq_zero_iff_toNat.2 hd
    subst this
    simp [fullMulDiv, fullMulDivUp]
  have hd0 : 0 < d.toNat := Nat.pos_of_ne_zero hd
  rw [ite_eq_right hd] at hm
  cases h : fullMulDiv a b d with
  | none =>
    simp only
    symm
    rw [fullMulDivUp_eq_none_iff]
    rw [fullMulDiv_eq_none_iff] at h
    have := Nat.two_pow_pos 256
    rcases h with h | h
    · exact Or.inl h
    · right
      have : (2 ^ 256 - 1) * d.toNat < 2 ^ 256 * d.toNat := by
        rw [Nat.sub_mul, Nat.one_mul]; omega
      omega
  | some q =>
    simp only
    have ⟨_, hfit, hq⟩ := fullMulDiv_eq_some_iff.1 h
    have hfit' : a.toNat * b.toNat < 2 ^ 256 * d.toNat := (div_lt_two_pow_iff hd0).1 hfit
    by_cases hr : mulmod a b d > 0
    · rw [ite_eq_left hr]
      have hr' : a.toNat * b.toNat % d.toNat ≠ 0 := by
        rw [GT.gt, BitVec.lt_def, hm] at hr; simp at hr; omega
      have hc := ceilDiv_eq_div_add_one _ _ hd0 hr'
      by_cases hmax : q < BitVec.allOnes 256
      · rw [ite_eq_left hmax]
        rw [BitVec.lt_def, BitVec.toNat_allOnes] at hmax
        symm
        rw [fullMulDivUp_eq_some_iff, hc]
        have h1 : (1 : U256).toNat = 1 := rfl
        refine ⟨hd0, by omega, ?_⟩
        rw [toNat_add_of_lt _ _ (by rw [h1]; omega), h1, hq]
      · rw [ite_eq_right hmax]
        rw [BitVec.lt_def, BitVec.toNat_allOnes] at hmax
        symm
        rw [← Option.not_isSome_iff_eq_none, fullMulDivUp_isSome_iff]
        rw [← ceilDiv_lt_two_pow_iff hd0, hc]
        omega
    · rw [ite_eq_right hr]
      have hr' : a.toNat * b.toNat % d.toNat = 0 := by
        rw [GT.gt, BitVec.lt_def, hm] at hr; simp at hr; omega
      rw [← h]
      exact ((fullMulDivUp_eq_fullMulDiv_iff hd0 hfit').2 hr').symm

end ProofForgeFin.Evm
