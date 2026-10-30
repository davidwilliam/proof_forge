import ProofForgeFin.FixedPoint
import ProofForgeFin.Evm.Bits
import ProofForgeFin.Evm.MulDiv
/-!
# Binary fixed-point formats: Q64.64, Q64.96, Q128.128

A number in the binary format `Qm.n` is stored as a natural number `x` below `2^(m + n)` and
represents the rational `x / 2^n`: `n` fractional bits and `m` integer bits. Uniswap v3 stores
sqrt prices as Q64.96 in a `uint160` (`sqrtPriceX96`, `FixedPoint96.Q96 = 2^96`), fee growth
and the tick math ratio as Q128.128 (`FixedPoint128.Q128 = 2^128`); Cetus and other Move pools
store sqrt prices as Q64.64 in a `u128`.

* `toQ n a` encodes an integer, `floorQ n x` and `ceilQ n x` decode with rounding down and up.
* `convertQ m n x` and `convertQUp m n x` change the number of fractional bits from `m` to `n`,
  rounding down and up; every bound is stated as an order between the rationals `x / 2^m` and
  `y / 2^n`, cross-multiplied: `y * 2^m ≤ x * 2^n` reads "`y / 2^n` is at most `x / 2^m`".
* `mulQ`, `mulQUp`, `divQ`, `divQUp` are the fixed-point products and quotients at scale
  `2^n`; their bounds are those of `FixedPoint` with `one = 2^n`.
* `q128ToQ96Up` is the conversion at the end of Uniswap v3 `TickMath.getSqrtRatioAtTick`,
  `uint160((ratio >> 32) + (ratio % (1 << 32) == 0 ? 0 : 1))`, proved to be `convertQUp 128 96`.
-/

namespace ProofForgeFin.Evm

/-! ## Resolutions -/

/-- `FixedPoint96.Q96` of Uniswap v3. -/
def Q96 : Nat := 0x1000000000000000000000000

/-- `FixedPoint128.Q128` of Uniswap v3. -/
def Q128 : Nat := 0x100000000000000000000000000000000

/-- The Q64.64 resolution of Move pools (`1 << 64`). -/
def Q64 : Nat := 0x10000000000000000

/-- `Q96 = 2^96`. -/
theorem Q96_eq : Q96 = 2 ^ 96 := by decide

/-- `Q128 = 2^128`. -/
theorem Q128_eq : Q128 = 2 ^ 128 := by decide

/-- `Q64 = 2^64`. -/
theorem Q64_eq : Q64 = 2 ^ 64 := by decide

/-! ## Encoding and decoding -/

/-- The integer `a` in a format with `n` fractional bits: `a << n`. -/
def toQ (n a : Nat) : Nat := a * 2 ^ n

/-- The integer part of a number with `n` fractional bits (rounded down): `x >> n`. -/
def floorQ (n x : Nat) : Nat := x / 2 ^ n

/-- The value of a number with `n` fractional bits, rounded up to an integer. -/
def ceilQ (n x : Nat) : Nat := ceilDiv x (2 ^ n)

/-- Decoding an encoded integer returns it. -/
@[simp] theorem floorQ_toQ (n a : Nat) : floorQ n (toQ n a) = a :=
  Nat.mul_div_cancel a (Nat.two_pow_pos n)

/-- Decoding an encoded integer with rounding up returns it. -/
@[simp] theorem ceilQ_toQ (n a : Nat) : ceilQ n (toQ n a) = a := ceilDiv_mul_cancel a (Nat.two_pow_pos n)

/-- The integer part is within one unit below the value: `floorQ n x * 2^n ≤ x <
(floorQ n x + 1) * 2^n`. -/
theorem floorQ_spec (n x : Nat) : floorQ n x * 2 ^ n ≤ x ∧ x < (floorQ n x + 1) * 2 ^ n :=
  floor_spec x _ (Nat.two_pow_pos n)

/-- Rounding up is within one unit above the value: `x ≤ ceilQ n x * 2^n < x + 2^n`. -/
theorem ceilQ_spec (n x : Nat) : x ≤ ceilQ n x * 2 ^ n ∧ ceilQ n x * 2 ^ n < x + 2 ^ n :=
  ceilDiv_spec x _ (Nat.two_pow_pos n)

/-- A number of the format `Qm.n` fits in `m + n` bits exactly when its integer part fits in `m`
bits. -/
theorem lt_two_pow_add_iff (m n x : Nat) : x < 2 ^ (m + n) ↔ floorQ n x < 2 ^ m := by
  unfold floorQ
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n), Nat.pow_add]

/-- The word-level decoding: a right shift by `n` is `floorQ n`. -/
theorem toNat_ushiftRight_eq_floorQ {w : Nat} (x : BitVec w) (n : Nat) :
    (x >>> n).toNat = floorQ n x.toNat := toNat_ushiftRight x n

/-- The word-level encoding: a checked left shift by `n` succeeds exactly when the integer fits
in `w - n` bits, and then is `toQ n`. -/
theorem checkedShl_eq_some_iff_toQ {w : Nat} {x z : BitVec w} {n : Nat} :
    checkedShl x n = some z ↔ x.toNat < 2 ^ (w - n) ∧ z.toNat = toQ n x.toNat :=
  checkedShl_eq_some_iff

/-! ## Changing the number of fractional bits -/

/-- From `m` to `n` fractional bits, rounded down (exact when `m ≤ n`). -/
def convertQ (m n x : Nat) : Nat := if m ≤ n then x * 2 ^ (n - m) else x / 2 ^ (m - n)

/-- From `m` to `n` fractional bits, rounded up (exact when `m ≤ n`). -/
def convertQUp (m n x : Nat) : Nat := if m ≤ n then x * 2 ^ (n - m) else ceilDiv x (2 ^ (m - n))

/-- `2^m = 2^(m - n) * 2^n` for `n ≤ m`. -/
theorem two_pow_sub_mul {m n : Nat} (h : n ≤ m) : 2 ^ m = 2 ^ (m - n) * 2 ^ n := by
  rw [← Nat.pow_add]; congr 1; omega

/-- Rounding down: `convertQ m n x / 2^n ≤ x / 2^m < (convertQ m n x + 1) / 2^n`. -/
theorem convertQ_spec (m n x : Nat) :
    convertQ m n x * 2 ^ m ≤ x * 2 ^ n ∧ x * 2 ^ n < (convertQ m n x + 1) * 2 ^ m := by
  unfold convertQ
  by_cases h : m ≤ n
  · rw [ite_eq_left h, two_pow_sub_mul h]
    have hp := Nat.two_pow_pos m
    refine ⟨by rw [Nat.mul_assoc]; exact Nat.le_refl _, ?_⟩
    rw [← Nat.mul_assoc, Nat.add_mul, Nat.one_mul]; omega
  · rw [ite_eq_right h]
    have h' : n ≤ m := by omega
    have ⟨h1, h2⟩ := floor_spec x (2 ^ (m - n)) (Nat.two_pow_pos _)
    rw [two_pow_sub_mul h']
    constructor
    · rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h1
    · rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos n)

/-- Rounding up: `x / 2^m ≤ convertQUp m n x / 2^n < x / 2^m + 1 / 2^n`. -/
theorem convertQUp_spec (m n x : Nat) :
    x * 2 ^ n ≤ convertQUp m n x * 2 ^ m ∧ convertQUp m n x * 2 ^ m < x * 2 ^ n + 2 ^ m := by
  unfold convertQUp
  by_cases h : m ≤ n
  · rw [ite_eq_left h, two_pow_sub_mul h]
    have hp := Nat.two_pow_pos m
    refine ⟨by rw [Nat.mul_assoc]; exact Nat.le_refl _, ?_⟩
    rw [Nat.mul_assoc]; omega
  · rw [ite_eq_right h]
    have h' : n ≤ m := by omega
    have ⟨h1, h2⟩ := ceilDiv_spec x (2 ^ (m - n)) (Nat.two_pow_pos _)
    rw [two_pow_sub_mul h']
    constructor
    · rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h1
    · rw [← Nat.mul_assoc]
      have := Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos n)
      rw [Nat.add_mul] at this; exact this

/-- Adding fractional bits is exact. -/
theorem convertQ_of_le {m n : Nat} (h : m ≤ n) (x : Nat) : convertQ m n x * 2 ^ m = x * 2 ^ n := by
  unfold convertQ; rw [ite_eq_left h, two_pow_sub_mul h, Nat.mul_assoc]

/-- Adding fractional bits and removing them again returns the number. -/
theorem convertQ_convertQ {m n : Nat} (h : m ≤ n) (x : Nat) : convertQ n m (convertQ m n x) = x := by
  unfold convertQ
  rw [ite_eq_left h]
  by_cases h' : n ≤ m
  · have : n = m := by omega
    subst this; simp
  · rw [ite_eq_right h']; exact Nat.mul_div_cancel x (Nat.two_pow_pos _)

/-- The two roundings differ by at most one unit. -/
theorem convertQ_le_convertQUp (m n x : Nat) :
    convertQ m n x ≤ convertQUp m n x ∧ convertQUp m n x ≤ convertQ m n x + 1 := by
  unfold convertQ convertQUp
  split
  · omega
  · exact ⟨div_le_ceilDiv _ _, ceilDiv_le_div_add_one _ _⟩

/-- Changing the number of fractional bits is monotone. -/
theorem convertQ_mono (m n : Nat) {x y : Nat} (h : x ≤ y) : convertQ m n x ≤ convertQ m n y := by
  unfold convertQ
  split
  · exact Nat.mul_le_mul_right _ h
  · exact Nat.div_le_div_right h

/-- Changing the number of fractional bits rounded up is monotone. -/
theorem convertQUp_mono (m n : Nat) {x y : Nat} (h : x ≤ y) : convertQUp m n x ≤ convertQUp m n y := by
  unfold convertQUp
  split
  · exact Nat.mul_le_mul_right _ h
  · exact ceilDiv_mono_left _ h

/-! ## Products and quotients -/

/-- The product of two numbers with `n` fractional bits, rounded down: `a * b >> n`. -/
def mulQ (n a b : Nat) : Nat := mulDown (2 ^ n) a b

/-- The product of two numbers with `n` fractional bits, rounded up. -/
def mulQUp (n a b : Nat) : Nat := mulUp (2 ^ n) a b

/-- The quotient of two numbers with `n` fractional bits, rounded down: `(a << n) / b`. -/
def divQ (n a b : Nat) : Nat := divDown (2 ^ n) a b

/-- The quotient of two numbers with `n` fractional bits, rounded up. -/
def divQUp (n a b : Nat) : Nat := divUp (2 ^ n) a b

/-- `mulQ` is within one unit below the exact product: `mulQ n a b * 2^n ≤ a * b <
(mulQ n a b + 1) * 2^n`. -/
theorem mulQ_spec (n a b : Nat) : mulQ n a b * 2 ^ n ≤ a * b ∧ a * b < (mulQ n a b + 1) * 2 ^ n :=
  mulDown_spec _ a b (Nat.two_pow_pos n)

/-- `mulQUp` is within one unit above the exact product. -/
theorem mulQUp_spec (n a b : Nat) :
    a * b ≤ mulQUp n a b * 2 ^ n ∧ mulQUp n a b * 2 ^ n < a * b + 2 ^ n :=
  mulUp_spec _ a b (Nat.two_pow_pos n)

/-- `divQ` is within one unit below the exact quotient, for `0 < b`. -/
theorem divQ_spec (n a b : Nat) (hb : 0 < b) :
    divQ n a b * b ≤ a * 2 ^ n ∧ a * 2 ^ n < (divQ n a b + 1) * b :=
  divDown_spec _ a b hb

/-- `divQUp` is within one unit above the exact quotient, for `0 < b`. -/
theorem divQUp_spec (n a b : Nat) (hb : 0 < b) :
    a * 2 ^ n ≤ divQUp n a b * b ∧ divQUp n a b * b < a * 2 ^ n + b :=
  divUp_spec _ a b hb

/-- The fixed-point product is a right shift of the product. -/
theorem mulQ_eq_shiftRight (n a b : Nat) : mulQ n a b = (a * b) >>> n := by
  unfold mulQ mulDown mulDiv; rw [Nat.shiftRight_eq_div_pow]

/-- The fixed-point quotient is a left shift divided. -/
theorem divQ_eq_shiftLeft (n a b : Nat) : divQ n a b = (a <<< n) / b := by
  unfold divQ divDown mulDiv; rw [Nat.shiftLeft_eq]

/-- A word-level fixed-point product with a full-precision `mulDiv` (`FullMath.mulDiv(a, b,
Q96)`) returns `mulQ`. -/
theorem toNat_fullMulDiv_two_pow {w n : Nat} {a b d q : BitVec w} (hd : d.toNat = 2 ^ n)
    (h : fullMulDiv a b d = some q) : q.toNat = mulQ n a.toNat b.toNat := by
  rw [toNat_of_fullMulDiv h, hd]; rfl

/-- A word-level fixed-point product rounded up with a full-precision `mulDivRoundingUp`
returns `mulQUp`. -/
theorem toNat_fullMulDivUp_two_pow {w n : Nat} {a b d q : BitVec w} (hd : d.toNat = 2 ^ n)
    (h : fullMulDivUp a b d = some q) : q.toNat = mulQUp n a.toNat b.toNat := by
  rw [toNat_of_fullMulDivUp h, hd]; rfl

/-! ## The conversion of `TickMath.getSqrtRatioAtTick` -/

/-- The end of Uniswap v3 `TickMath.getSqrtRatioAtTick`: a Q128.128 ratio converted to a Q64.96
sqrt price rounded up, `uint160((ratio >> 32) + (ratio % (1 << 32) == 0 ? 0 : 1))`. The
conversion to `uint160` truncates. -/
def q128ToQ96Up (ratio : U256) : U160 :=
  ((ratio >>> 32) + (if evmMod ratio ((1 : U256) <<< 32) = 0 then 0 else 1)).setWidth 160

/-- The conversion is `convertQUp 128 96` (the ratio rounded up to 96 fractional bits) whenever
the result fits in 160 bits, which holds for every ratio of a tick in range. -/
theorem toNat_q128ToQ96Up (ratio : U256) (h : convertQUp 128 96 ratio.toNat < 2 ^ 160) :
    (q128ToQ96Up ratio).toNat = convertQUp 128 96 ratio.toNat := by
  unfold q128ToQ96Up
  have hm : ((1 : U256) <<< 32).toNat = 2 ^ 32 := toNat_one_shiftLeft (by decide)
  have hmod := toNat_evmMod ratio ((1 : U256) <<< 32)
  rw [hm, ite_eq_right (by decide)] at hmod
  have hcu : convertQUp 128 96 ratio.toNat = ceilDiv ratio.toNat (2 ^ 32) := by
    unfold convertQUp; rw [ite_eq_right (by decide)]
  rw [hcu] at h ⊢
  have hshift : (ratio >>> 32).toNat = ratio.toNat / 2 ^ 32 := toNat_ushiftRight ratio 32
  have hq : ratio.toNat / 2 ^ 32 < 2 ^ 224 := by
    have := ratio.isLt
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32)]; exact this
  have hp : 0 < 2 ^ 32 := Nat.two_pow_pos 32
  by_cases hz : evmMod ratio ((1 : U256) <<< 32) = 0
  · rw [ite_eq_left hz]
    have hz' : ratio.toNat % 2 ^ 32 = 0 := by rw [← hmod, hz]; rfl
    rw [BitVec.toNat_setWidth, toNat_add_of_lt _ _ (by rw [hshift]; simp; omega), hshift]
    rw [(ceilDiv_eq_div_iff _ _ hp).2 hz'] at h ⊢
    simp only [show (0 : U256).toNat = 0 from rfl, Nat.add_zero]
    exact Nat.mod_eq_of_lt h
  · rw [ite_eq_right hz]
    have hz' : ratio.toNat % 2 ^ 32 ≠ 0 := fun e => hz (by
      apply BitVec.eq_of_toNat_eq; rw [hmod, e]; rfl)
    rw [ceilDiv_eq_div_add_one _ _ hp hz'] at h ⊢
    have h1 : (1 : U256).toNat = 1 := rfl
    rw [BitVec.toNat_setWidth, toNat_add_of_lt _ _ (by rw [hshift, h1]; omega), hshift, h1]
    exact Nat.mod_eq_of_lt h

end ProofForgeFin.Evm
