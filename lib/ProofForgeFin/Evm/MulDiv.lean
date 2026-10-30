import ProofForgeFin.FixedPoint
import ProofForgeFin.Evm.Uint
/-!
# Full-precision `mulDiv` on machine words

`fullMulDiv a b d` is the result of Uniswap v3 `FullMath.mulDiv`, OpenZeppelin `Math.mulDiv`
and Solady `FixedPointMathLib.fullMulDiv`: `a * b / d` rounded down, computed as if the product
`a * b` had unbounded precision (the deployed code uses a 512-bit intermediate), reverting
exactly when `d = 0` or the quotient does not fit in a word. `fullMulDivUp` is the same rounded
up (`FullMath.mulDivRoundingUp`, `Math.mulDiv(a, b, d, Rounding.Ceil)`, `fullMulDivUp`).

These are the specifications; `ProofForgeFin.Evm.FullMath` proves the 512-bit algorithm of
`FullMath.mulDiv` equal to `fullMulDiv` on every input.

The module also gives the word-level rounding helpers deployed code calls next to them:
`divRoundingUp` (Uniswap v3 `UnsafeMath.divRoundingUp`, which never reverts), `ceilDivW`
(OpenZeppelin `Math.ceilDiv`) and `divRound` (Move integer-mate `math_u256::div_round`, called
by Cetus `get_delta_a`).

Every result is characterized through `toNat` by the `Rounding` lemmas: the floor and ceiling
bounds, the exact conditions under which the call reverts, the order between the two
roundings and monotonicity.
-/

namespace ProofForgeFin.Evm

variable {w : Nat}

/-! ## Specification of `mulDiv` -/

/-- Full-precision `a * b / d`, rounded down, reverting (`none`) when `d = 0` or the quotient
does not fit (`FullMath.mulDiv`). -/
def fullMulDiv (a b d : BitVec w) : Option (BitVec w) :=
  if d = 0 then none else fit w (a.toNat * b.toNat / d.toNat)

/-- Full-precision `a * b / d`, rounded up, reverting when `d = 0` or the quotient does not fit
(`FullMath.mulDivRoundingUp`). -/
def fullMulDivUp (a b d : BitVec w) : Option (BitVec w) :=
  if d = 0 then none else fit w (ceilDiv (a.toNat * b.toNat) d.toNat)

/-- `fullMulDiv a b d = some q` exactly when `d ≠ 0`, the quotient fits and `q` is the floor
quotient. -/
theorem fullMulDiv_eq_some_iff {a b d q : BitVec w} :
    fullMulDiv a b d = some q ↔
      0 < d.toNat ∧ a.toNat * b.toNat / d.toNat < 2 ^ w ∧
        q.toNat = a.toNat * b.toNat / d.toNat := by
  unfold fullMulDiv
  by_cases h : d = 0
  · simp [h]
  · rw [ite_eq_right h, fit_eq_some_iff]
    simp [toNat_pos_of_ne_zero h]

/-- `fullMulDivUp a b d = some q` exactly when `d ≠ 0`, the rounded-up quotient fits and `q` is
the rounded-up quotient. -/
theorem fullMulDivUp_eq_some_iff {a b d q : BitVec w} :
    fullMulDivUp a b d = some q ↔
      0 < d.toNat ∧ ceilDiv (a.toNat * b.toNat) d.toNat < 2 ^ w ∧
        q.toNat = ceilDiv (a.toNat * b.toNat) d.toNat := by
  unfold fullMulDivUp
  by_cases h : d = 0
  · simp [h]
  · rw [ite_eq_right h, fit_eq_some_iff]
    simp [toNat_pos_of_ne_zero h]

/-- The floor quotient fits exactly when `a * b < 2^w * d`: this is the `require(denominator >
prod1)` of `FullMath.mulDiv`, stated on the inputs. -/
theorem div_lt_two_pow_iff {p d : Nat} (hd : 0 < d) : p / d < 2 ^ w ↔ p < 2 ^ w * d := by
  rw [Nat.div_lt_iff_lt_mul hd]

/-- The rounded-up quotient fits exactly when `a * b ≤ (2^w - 1) * d`. -/
theorem ceilDiv_lt_two_pow_iff {p d : Nat} (hd : 0 < d) :
    ceilDiv p d < 2 ^ w ↔ p ≤ (2 ^ w - 1) * d := by
  rw [← ceilDiv_le_iff hd]
  have := Nat.two_pow_pos w
  omega

/-- `fullMulDiv` succeeds exactly when `d ≠ 0` and `a * b < 2^w * d`. -/
theorem fullMulDiv_isSome_iff {a b d : BitVec w} :
    (fullMulDiv a b d).isSome ↔ 0 < d.toNat ∧ a.toNat * b.toNat < 2 ^ w * d.toNat := by
  unfold fullMulDiv
  by_cases h : d = 0
  · simp [h]
  · have hd := toNat_pos_of_ne_zero h
    rw [ite_eq_right h, fit_isSome_iff, div_lt_two_pow_iff hd]
    simp [hd]

/-- `fullMulDiv` reverts exactly when `d = 0` or `2^w * d ≤ a * b`. -/
theorem fullMulDiv_eq_none_iff {a b d : BitVec w} :
    fullMulDiv a b d = none ↔ d.toNat = 0 ∨ 2 ^ w * d.toNat ≤ a.toNat * b.toNat := by
  rw [← Option.not_isSome_iff_eq_none, fullMulDiv_isSome_iff]
  omega

/-- `fullMulDivUp` succeeds exactly when `d ≠ 0` and `a * b ≤ (2^w - 1) * d`. -/
theorem fullMulDivUp_isSome_iff {a b d : BitVec w} :
    (fullMulDivUp a b d).isSome ↔
      0 < d.toNat ∧ a.toNat * b.toNat ≤ (2 ^ w - 1) * d.toNat := by
  unfold fullMulDivUp
  by_cases h : d = 0
  · simp [h]
  · have hd := toNat_pos_of_ne_zero h
    rw [ite_eq_right h, fit_isSome_iff, ceilDiv_lt_two_pow_iff hd]
    simp [hd]

/-- `fullMulDivUp` reverts exactly when `d = 0` or `(2^w - 1) * d < a * b`. -/
theorem fullMulDivUp_eq_none_iff {a b d : BitVec w} :
    fullMulDivUp a b d = none ↔ d.toNat = 0 ∨ (2 ^ w - 1) * d.toNat < a.toNat * b.toNat := by
  rw [← Option.not_isSome_iff_eq_none, fullMulDivUp_isSome_iff]
  omega

/-- When the quotient fits, `fullMulDiv` returns it. -/
theorem fullMulDiv_of_lt {a b d : BitVec w} (hd : 0 < d.toNat)
    (h : a.toNat * b.toNat < 2 ^ w * d.toNat) :
    fullMulDiv a b d = some (BitVec.ofNat w (a.toNat * b.toNat / d.toNat)) := by
  have hd' : d ≠ 0 := fun e => by rw [eq_zero_iff_toNat.1 e] at hd; exact absurd hd (by decide)
  unfold fullMulDiv fit
  rw [ite_eq_right hd', ite_eq_left ((div_lt_two_pow_iff hd).2 h)]

/-- The value of a successful `fullMulDiv` is the floor quotient. -/
theorem toNat_of_fullMulDiv {a b d q : BitVec w} (h : fullMulDiv a b d = some q) :
    q.toNat = a.toNat * b.toNat / d.toNat := (fullMulDiv_eq_some_iff.1 h).2.2

/-- The value of a successful `fullMulDivUp` is the rounded-up quotient. -/
theorem toNat_of_fullMulDivUp {a b d q : BitVec w} (h : fullMulDivUp a b d = some q) :
    q.toNat = ceilDiv (a.toNat * b.toNat) d.toNat := (fullMulDivUp_eq_some_iff.1 h).2.2

/-- `fullMulDiv` is the library's `mulDiv` on the values, when it succeeds. -/
theorem toNat_of_fullMulDiv' {a b d q : BitVec w} (h : fullMulDiv a b d = some q) :
    q.toNat = mulDiv a.toNat b.toNat d.toNat := toNat_of_fullMulDiv h

/-- `fullMulDivUp` is the library's `mulDivUp` on the values, when it succeeds. -/
theorem toNat_of_fullMulDivUp' {a b d q : BitVec w} (h : fullMulDivUp a b d = some q) :
    q.toNat = mulDivUp a.toNat b.toNat d.toNat := toNat_of_fullMulDivUp h

/-- Floor bounds: `q * d ≤ a * b < (q + 1) * d`. -/
theorem fullMulDiv_spec {a b d q : BitVec w} (h : fullMulDiv a b d = some q) :
    q.toNat * d.toNat ≤ a.toNat * b.toNat ∧ a.toNat * b.toNat < (q.toNat + 1) * d.toNat := by
  have ⟨hd, _, hq⟩ := fullMulDiv_eq_some_iff.1 h
  rw [hq]; exact floor_spec _ _ hd

/-- Ceiling bounds: `a * b ≤ q * d < a * b + d`. -/
theorem fullMulDivUp_spec {a b d q : BitVec w} (h : fullMulDivUp a b d = some q) :
    a.toNat * b.toNat ≤ q.toNat * d.toNat ∧ q.toNat * d.toNat < a.toNat * b.toNat + d.toNat := by
  have ⟨hd, _, hq⟩ := fullMulDivUp_eq_some_iff.1 h
  rw [hq]; exact ceilDiv_spec _ _ hd

/-- If rounding up succeeds, rounding down succeeds, and the two differ by at most one unit:
`q ≤ q' ≤ q + 1`. -/
theorem fullMulDiv_of_fullMulDivUp {a b d q' : BitVec w} (h : fullMulDivUp a b d = some q') :
    ∃ q, fullMulDiv a b d = some q ∧ q.toNat ≤ q'.toNat ∧ q'.toNat ≤ q.toNat + 1 := by
  have ⟨hd, hfit, hq⟩ := fullMulDivUp_eq_some_iff.1 h
  have h1 := div_le_ceilDiv (a.toNat * b.toNat) d.toNat
  have h2 := ceilDiv_le_div_add_one (a.toNat * b.toNat) d.toNat
  have hfit' : a.toNat * b.toNat / d.toNat < 2 ^ w := by omega
  refine ⟨BitVec.ofNat w (a.toNat * b.toNat / d.toNat), ?_, ?_⟩
  · exact fullMulDiv_of_lt hd ((div_lt_two_pow_iff hd).1 hfit')
  · rw [toNat_ofNat_of_lt hfit', hq]; exact ⟨h1, h2⟩

/-- When rounding down succeeds, the two roundings return the same result exactly when `d`
divides `a * b` (the `mulmod(a, b, d) > 0` test of `FullMath.mulDivRoundingUp`). -/
theorem fullMulDivUp_eq_fullMulDiv_iff {a b d : BitVec w} (hd : 0 < d.toNat)
    (hfit : a.toNat * b.toNat < 2 ^ w * d.toNat) :
    fullMulDivUp a b d = fullMulDiv a b d ↔ a.toNat * b.toNat % d.toNat = 0 := by
  have hd' : d ≠ 0 := fun e => by rw [eq_zero_iff_toNat.1 e] at hd; exact absurd hd (by decide)
  have hq : a.toNat * b.toNat / d.toNat < 2 ^ w := (div_lt_two_pow_iff hd).2 hfit
  unfold fullMulDivUp fullMulDiv
  rw [ite_eq_right hd', ite_eq_right hd']
  constructor
  · intro h
    refine Classical.byContradiction fun hm => ?_
    rw [ceilDiv_eq_div_add_one _ _ hd hm] at h
    unfold fit at h
    rw [ite_eq_left hq] at h
    by_cases h1 : a.toNat * b.toNat / d.toNat + 1 < 2 ^ w
    · rw [ite_eq_left h1, Option.some.injEq, BitVec.toNat_eq, toNat_ofNat_of_lt h1,
        toNat_ofNat_of_lt hq] at h
      omega
    · rw [ite_eq_right h1] at h; cases h
  · intro h
    rw [(ceilDiv_eq_div_iff _ _ hd).2 h]

/-! ## Sufficient conditions and monotonicity -/

/-- `mulDiv(a, b, d)` with `a ≤ d` (a fraction of `b`) never reverts for `d ≠ 0`, and returns
at most `b`. -/
theorem fullMulDiv_of_le_left {a b d : BitVec w} (hd : 0 < d.toNat) (h : a.toNat ≤ d.toNat) :
    ∃ q, fullMulDiv a b d = some q ∧ q.toNat ≤ b.toNat := by
  have hb := b.isLt
  have hlt : a.toNat * b.toNat < 2 ^ w * d.toNat := by
    calc a.toNat * b.toNat ≤ d.toNat * b.toNat := Nat.mul_le_mul_right _ h
      _ < d.toNat * 2 ^ w := Nat.mul_lt_mul_of_pos_left hb hd
      _ = 2 ^ w * d.toNat := Nat.mul_comm _ _
  refine ⟨_, fullMulDiv_of_lt hd hlt, ?_⟩
  rw [toNat_ofNat_of_lt ((div_lt_two_pow_iff hd).2 hlt)]
  exact mul_div_le_of_le h

/-- `mulDiv(a, b, d)` with `b ≤ d` never reverts for `d ≠ 0`, and returns at most `a`. -/
theorem fullMulDiv_of_le_right {a b d : BitVec w} (hd : 0 < d.toNat) (h : b.toNat ≤ d.toNat) :
    ∃ q, fullMulDiv a b d = some q ∧ q.toNat ≤ a.toNat := by
  have ⟨q, hq, hle⟩ := fullMulDiv_of_le_left (b := a) hd h
  refine ⟨q, ?_, hle⟩
  unfold fullMulDiv at *
  rw [Nat.mul_comm]; exact hq

/-- Monotonicity in the factors: if `fullMulDiv a' b' d` succeeds and `a ≤ a'`, `b ≤ b'`, then
`fullMulDiv a b d` succeeds with a result at most as large. -/
theorem fullMulDiv_mono {a a' b b' d q' : BitVec w} (ha : a.toNat ≤ a'.toNat)
    (hb : b.toNat ≤ b'.toNat) (h : fullMulDiv a' b' d = some q') :
    ∃ q, fullMulDiv a b d = some q ∧ q.toNat ≤ q'.toNat := by
  have ⟨hd, hfit, hq⟩ := fullMulDiv_eq_some_iff.1 h
  have hle : a.toNat * b.toNat / d.toNat ≤ a'.toNat * b'.toNat / d.toNat :=
    Nat.div_le_div_right (Nat.mul_le_mul ha hb)
  have hfit2 : a.toNat * b.toNat / d.toNat < 2 ^ w := Nat.lt_of_le_of_lt hle hfit
  refine ⟨_, fullMulDiv_of_lt hd ((div_lt_two_pow_iff hd).1 hfit2), ?_⟩
  rw [toNat_ofNat_of_lt hfit2, hq]; exact hle

/-- Antitonicity in the divisor: if `fullMulDiv a b d` succeeds and `d ≤ d'`, then
`fullMulDiv a b d'` succeeds with a result at most as large. -/
theorem fullMulDiv_anti {a b d d' q : BitVec w} (hdd : d.toNat ≤ d'.toNat)
    (h : fullMulDiv a b d = some q) :
    ∃ q', fullMulDiv a b d' = some q' ∧ q'.toNat ≤ q.toNat := by
  have ⟨hd, hfit, hq⟩ := fullMulDiv_eq_some_iff.1 h
  have hd' : 0 < d'.toNat := Nat.lt_of_lt_of_le hd hdd
  have hle : a.toNat * b.toNat / d'.toNat ≤ a.toNat * b.toNat / d.toNat :=
    Nat.div_le_div_left hdd hd
  have hfit2 := Nat.lt_of_le_of_lt hle hfit
  refine ⟨_, fullMulDiv_of_lt hd' ((div_lt_two_pow_iff hd').1 hfit2), ?_⟩
  rw [toNat_ofNat_of_lt hfit2, hq]; exact hle

/-- Monotonicity of the rounded-up quotient in the factors. -/
theorem fullMulDivUp_mono {a a' b b' d q' : BitVec w} (ha : a.toNat ≤ a'.toNat)
    (hb : b.toNat ≤ b'.toNat) (h : fullMulDivUp a' b' d = some q') :
    ∃ q, fullMulDivUp a b d = some q ∧ q.toNat ≤ q'.toNat := by
  have ⟨hd, hfit, hq⟩ := fullMulDivUp_eq_some_iff.1 h
  have hle : ceilDiv (a.toNat * b.toNat) d.toNat ≤ ceilDiv (a'.toNat * b'.toNat) d.toNat :=
    ceilDiv_mono_left _ (Nat.mul_le_mul ha hb)
  have hfit2 := Nat.lt_of_le_of_lt hle hfit
  have hd' : d ≠ 0 := fun e => by rw [eq_zero_iff_toNat.1 e] at hd; exact absurd hd (by decide)
  refine ⟨BitVec.ofNat w (ceilDiv (a.toNat * b.toNat) d.toNat), ?_, ?_⟩
  · unfold fullMulDivUp fit; rw [ite_eq_right hd', ite_eq_left hfit2]
  · rw [toNat_ofNat_of_lt hfit2, hq]; exact hle

/-- Antitonicity of the rounded-up quotient in the divisor. -/
theorem fullMulDivUp_anti {a b d d' q : BitVec w} (hdd : d.toNat ≤ d'.toNat)
    (h : fullMulDivUp a b d = some q) :
    ∃ q', fullMulDivUp a b d' = some q' ∧ q'.toNat ≤ q.toNat := by
  have ⟨hd, hfit, hq⟩ := fullMulDivUp_eq_some_iff.1 h
  have hd' : 0 < d'.toNat := Nat.lt_of_lt_of_le hd hdd
  have hle : ceilDiv (a.toNat * b.toNat) d'.toNat ≤ ceilDiv (a.toNat * b.toNat) d.toNat :=
    ceilDiv_anti_right _ hd hdd
  have hfit2 := Nat.lt_of_le_of_lt hle hfit
  have hne : d' ≠ 0 := fun e => by rw [eq_zero_iff_toNat.1 e] at hd'; exact absurd hd' (by decide)
  refine ⟨BitVec.ofNat w (ceilDiv (a.toNat * b.toNat) d'.toNat), ?_, ?_⟩
  · unfold fullMulDivUp fit; rw [ite_eq_right hne, ite_eq_left hfit2]
  · rw [toNat_ofNat_of_lt hfit2, hq]; exact hle

/-! ## Rounding helpers of deployed code -/

/-- Uniswap v3 `UnsafeMath.divRoundingUp(x, y)`: `z := add(div(x, y), gt(mod(x, y), 0))`.
It never reverts; for `y = 0` the EVM's `DIV` and `MOD` return 0, and so does this. -/
def divRoundingUp (x y : BitVec w) : BitVec w :=
  x / y + (if evmMod x y > 0 then 1 else 0)

/-- The word `1` has value 1 when some word is positive (so `w > 0`). -/
theorem toNat_one_of_pos {x : BitVec w} (h : 0 < x.toNat) : (1 : BitVec w).toNat = 1 := by
  show (BitVec.ofNat w 1).toNat = 1
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h x.isLt)

/-- `divRoundingUp` is the ceiling quotient, and never overflows. -/
theorem toNat_divRoundingUp (x y : BitVec w) : (divRoundingUp x y).toNat = ceilDiv x.toNat y.toNat := by
  unfold divRoundingUp
  have hm := toNat_evmMod x y
  by_cases hy : y.toNat = 0
  · have : y = 0 := eq_zero_iff_toNat.2 hy
    subst this
    have : ¬ (evmMod x 0 > 0) := by rw [GT.gt, BitVec.lt_def, hm]; simp
    rw [ite_eq_right this]
    simp [ceilDiv]
  · have hy0 : 0 < y.toNat := Nat.pos_of_ne_zero hy
    rw [ite_eq_right hy] at hm
    by_cases hr : x.toNat % y.toNat = 0
    · have : ¬ (evmMod x y > 0) := by rw [GT.gt, BitVec.lt_def, hm]; simp [hr]
      rw [ite_eq_right this, toNat_add_of_lt] <;> simp [BitVec.toNat_udiv, (ceilDiv_eq_div_iff _ _ hy0).2 hr]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
    · have : evmMod x y > 0 := by rw [GT.gt, BitVec.lt_def, hm]; simp; omega
      rw [ite_eq_left this, ceilDiv_eq_div_add_one _ _ hy0 hr]
      have hy2 : 2 ≤ y.toNat := by
        refine Nat.lt_of_not_le fun h => hr ?_
        have : y.toNat = 1 := by omega
        rw [this, Nat.mod_one]
      have hxpos : 0 < x.toNat := Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hr) (Nat.mod_le _ _)
      have hq : x.toNat / y.toNat < x.toNat := Nat.div_lt_self hxpos (by omega)
      have h1 := toNat_one_of_pos hxpos
      have hx := x.isLt
      rw [toNat_add_of_lt, BitVec.toNat_udiv, h1]
      rw [BitVec.toNat_udiv, h1]; omega

/-- OpenZeppelin `Math.ceilDiv(a, b)`: `if (b == 0) panic; return a == 0 ? 0 : (a - 1) / b + 1`. -/
def ceilDivW (a b : BitVec w) : Option (BitVec w) :=
  if b = 0 then none else some (if a = 0 then 0 else (a - 1) / b + 1)

/-- `Math.ceilDiv` reverts exactly on a zero divisor and otherwise returns the ceiling quotient. -/
theorem ceilDivW_eq_some_iff {a b q : BitVec w} :
    ceilDivW a b = some q ↔ 0 < b.toNat ∧ q.toNat = ceilDiv a.toNat b.toNat := by
  unfold ceilDivW
  by_cases hb : b = 0
  · simp [hb]
  · have hb0 := toNat_pos_of_ne_zero hb
    rw [ite_eq_right hb, Option.some.injEq]
    simp only [hb0, true_and]
    rw [ceilDiv_eq_ite _ _ hb0, eq_comm, BitVec.toNat_eq]
    by_cases ha : a = 0
    · subst ha; simp
    · have ha0 := toNat_pos_of_ne_zero ha
      have hx := a.isLt
      rw [ite_eq_right ha, ite_eq_right (by omega)]
      have h1 := toNat_one_of_pos ha0
      have hsub : (a - 1).toNat = a.toNat - 1 := by rw [toNat_sub_of_le _ _ (by omega), h1]
      have hq : (a.toNat - 1) / b.toNat ≤ a.toNat - 1 := Nat.div_le_self _ _
      rw [toNat_add_of_lt, BitVec.toNat_udiv, hsub, h1]
      rw [BitVec.toNat_udiv, hsub, h1]; omega

/-- Move integer-mate `math_u256::div_round(num, denom, round_up)`:
`let p = num / denom; if (round_up && ((p * denom) != num)) { p + 1 } else { p }`, aborting on a
zero divisor. Neither `p * denom` nor `p + 1` can overflow. -/
def divRound (num denom : BitVec w) (roundUp : Bool) : Option (BitVec w) :=
  if denom = 0 then none
  else
    let p := num / denom
    if roundUp && p * denom != num then some (p + 1) else some p

/-- `div_round` aborts exactly on a zero divisor and otherwise returns the quotient rounded up
when `roundUp` holds and rounded down otherwise. -/
theorem divRound_eq_some_iff {num denom q : BitVec w} {roundUp : Bool} :
    divRound num denom roundUp = some q ↔
      0 < denom.toNat ∧
        q.toNat = if roundUp then ceilDiv num.toNat denom.toNat else num.toNat / denom.toNat := by
  unfold divRound
  by_cases h0 : denom = 0
  · simp [h0]
  have hd := toNat_pos_of_ne_zero h0
  have hn := num.isLt
  rw [ite_eq_right h0]
  simp only [hd, true_and]
  have hdiv : (num / denom).toNat = num.toNat / denom.toNat := BitVec.toNat_udiv
  have hle : num.toNat / denom.toNat * denom.toNat ≤ num.toNat := Nat.div_mul_le_self _ _
  have hmul : (num / denom * denom).toNat = num.toNat / denom.toNat * denom.toNat := by
    rw [BitVec.toNat_mul, hdiv, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hn)]
  have hmod : num.toNat / denom.toNat * denom.toNat = num.toNat ↔ num.toNat % denom.toNat = 0 := by
    have := Nat.div_add_mod num.toNat denom.toNat
    rw [Nat.mul_comm] at this; omega
  cases roundUp with
  | false =>
    simp only [Bool.false_and, Bool.false_eq_true, ite_false, Option.some.injEq]
    rw [eq_comm, BitVec.toNat_eq, hdiv]
  | true =>
    simp only [Bool.true_and, ite_true]
    by_cases he : num / denom * denom = num
    · have he' : num.toNat % denom.toNat = 0 := hmod.1 (by rw [← hmul, he])
      simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false, Option.some.injEq]
      rw [eq_comm, BitVec.toNat_eq, hdiv, (ceilDiv_eq_div_iff _ _ hd).2 he']
    · have hne : (num / denom * denom != num) = true := by simpa using he
      have he' : num.toNat % denom.toNat ≠ 0 := fun e =>
        he (BitVec.eq_of_toNat_eq (hmul.trans (hmod.2 e)))
      rw [ite_eq_left hne, Option.some.injEq, eq_comm, BitVec.toNat_eq,
        ceilDiv_eq_div_add_one _ _ hd he']
      have hq : num.toNat / denom.toNat < num.toNat := by
        have hd2 : 2 ≤ denom.toNat := by
          refine Nat.lt_of_not_le fun h => he' ?_
          have : denom.toNat = 1 := by omega
          rw [this, Nat.mod_one]
        exact Nat.div_lt_self (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero he') (Nat.mod_le _ _)) (by omega)
      have hnpos : 0 < num.toNat := Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero he') (Nat.mod_le _ _)
      have h1 := toNat_one_of_pos hnpos
      rw [toNat_add_of_lt, hdiv, h1]
      rw [hdiv, h1]; omega

/-- Rounding up with `div_round`: the result covers `num`, and one unit less does not. -/
theorem divRound_up_spec {num denom q : BitVec w} (h : divRound num denom true = some q) :
    num.toNat ≤ q.toNat * denom.toNat ∧ q.toNat * denom.toNat < num.toNat + denom.toNat := by
  have ⟨hd, hq⟩ := divRound_eq_some_iff.1 h
  rw [ite_eq_left rfl] at hq
  rw [hq]; exact ceilDiv_spec _ _ hd

/-- Rounding down with `div_round`: the result times `denom` is at most `num`, and one unit more
exceeds it. -/
theorem divRound_down_spec {num denom q : BitVec w} (h : divRound num denom false = some q) :
    q.toNat * denom.toNat ≤ num.toNat ∧ num.toNat < (q.toNat + 1) * denom.toNat := by
  have ⟨hd, hq⟩ := divRound_eq_some_iff.1 h
  rw [ite_eq_right (by decide)] at hq
  rw [hq]; exact floor_spec _ _ hd

/-- `div_round` aborts exactly on a zero divisor. -/
@[simp] theorem divRound_eq_none_iff {num denom : BitVec w} {roundUp : Bool} :
    divRound num denom roundUp = none ↔ denom = 0 := by
  unfold divRound
  by_cases h : denom = 0
  · simp [h]
  · simp only [h, ite_false, iff_false]
    split <;> simp

end ProofForgeFin.Evm
