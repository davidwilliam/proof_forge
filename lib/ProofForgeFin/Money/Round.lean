import ProofForgeFin.Rounding
/-!
# Rounding modes on integer fractions

Money code rounds the rational `n / d` (an amount times a rate, divided by a scale) to an
integer number of minor units, and the rounding mode is part of its contract. This module
defines the modes in common use on `Int` numerators with a positive `Int` denominator and
proves, for each, the exact two-sided bound that characterizes it:

| mode | result `q` is the unique integer with |
|------|----------------------------------------|
| `floor` | `q * d ≤ n < q * d + d` |
| `ceil` | `q * d - d < n ≤ q * d` |
| `towardZero` | `floor` for `0 ≤ n`, `ceil` for `n < 0` |
| `awayFromZero` | `ceil` for `0 ≤ n`, `floor` for `n < 0` |
| `halfCeil` | `-d < 2 * (q * d - n) ≤ d` (ties toward positive infinity) |
| `halfFloor` | `-d ≤ 2 * (q * d - n) < d` (ties toward negative infinity) |
| `halfUp` | `halfCeil` for `0 ≤ n`, `halfFloor` for `n < 0` (ties away from zero) |
| `halfDown` | `halfFloor` for `0 ≤ n`, `halfCeil` for `n < 0` (ties toward zero) |
| `halfEven` | `-d ≤ 2 * (q * d - n) ≤ d`, and `q` even on a tie (banker's rounding) |

The names follow Java's `RoundingMode` and moneyphp's `Money::ROUND_*` constants: `halfUp` is
`ROUND_HALF_UP` (a tie goes away from zero), `halfCeil` is `ROUND_HALF_POSITIVE_INFINITY` and
JavaScript's `Math.round`, `towardZero` is `ROUND_DOWN` and Go's integer division,
`awayFromZero` is `ROUND_UP`.

The error of a result `q` is `q * d - n` (the result minus the exact value, in units of
`1 / d`). Every statement is linear in `q * d`, so `omega` combines them.

Proved relations: every mode lies between `floor` and `ceil`, which differ by at most one and
agree exactly on multiples; every mode is within one unit of the exact value; the half modes
lie between `halfFloor` and `halfCeil`, are within half a unit and give a nearest integer;
every mode is monotone in the numerator, depends only on the value of the fraction, maps exact
multiples to the multiplier and commutes with negation up to the mirrored mode; `towardZero`
has the least magnitude and `awayFromZero` the largest. For a list of numerators, rounding the
sum and summing the rounded parts differ by at most the number of parts (half of that, plus a
half, for the half modes), and `floor` (`ceil`) of the sum is at least (at most) the sum of
the floors (ceilings).
-/

namespace ProofForgeFin.Money

/-! ## Cancellation by a positive factor -/

/-- `q * d < q' * d + d` with `0 < d` gives `q ≤ q'`: two multiples of `d` closer than `d`
come from integers in the same order. -/
theorem le_of_mul_lt_mul_add {q q' d : Int} (hd : 0 < d) (h : q * d < q' * d + d) : q ≤ q' := by
  have h' : q * d < (q' + 1) * d := by rw [Int.add_mul, Int.one_mul]; exact h
  have := Int.lt_of_mul_lt_mul_right h' (Int.le_of_lt hd)
  omega

/-- `q ≤ q'` and `0 ≤ d` give `q * d ≤ q' * d`. -/
theorem mul_le_mul_of_le {q q' d : Int} (hd : 0 ≤ d) (h : q ≤ q') : q * d ≤ q' * d :=
  Int.mul_le_mul_of_nonneg_right h hd

/-- Two integers whose multiples of `d > 0` are less than `d` apart are equal. -/
theorem eq_of_mul_lt_mul_add {q q' d : Int} (hd : 0 < d) (h1 : q * d < q' * d + d)
    (h2 : q' * d < q * d + d) : q = q' :=
  Int.le_antisymm (le_of_mul_lt_mul_add hd h1) (le_of_mul_lt_mul_add hd h2)

/-! ## The four base operations -/

/-- Floor division on `Int` (`Int.ediv`, Lean's `/`) is characterized by its two bounds: for
`0 < d`, `n / d = q` exactly when `q * d ≤ n < q * d + d`. -/
theorem ediv_eq_iff {n d q : Int} (hd : 0 < d) : n / d = q ↔ q * d ≤ n ∧ n < q * d + d := by
  have a1 := Int.ediv_mul_le n (show d ≠ 0 by omega)
  have a2 := Int.lt_ediv_add_one_mul_self n hd
  rw [Int.add_mul, Int.one_mul] at a2
  constructor
  · rintro rfl; exact ⟨a1, a2⟩
  · rintro ⟨h1, h2⟩
    exact eq_of_mul_lt_mul_add hd (by omega) (by omega)

/-- The floor bounds: `n / d * d ≤ n < n / d * d + d`. -/
theorem ediv_bounds (n : Int) {d : Int} (hd : 0 < d) : n / d * d ≤ n ∧ n < n / d * d + d :=
  (ediv_eq_iff hd).1 rfl

/-- `n / d` rounded toward positive infinity: `-((-n) / d)`. -/
def divCeil (n d : Int) : Int := -((-n) / d)

/-- Ceiling division is characterized by its two bounds: `divCeil n d = q` exactly when
`q * d - d < n ≤ q * d`. -/
theorem divCeil_eq_iff {n d q : Int} (hd : 0 < d) :
    divCeil n d = q ↔ q * d - d < n ∧ n ≤ q * d := by
  have key := ediv_eq_iff (n := -n) (q := -q) hd
  rw [Int.neg_mul] at key
  unfold divCeil
  constructor
  · intro h
    have := key.1 (by omega)
    omega
  · intro h
    have := key.2 (by omega)
    omega

/-- The ceiling bounds: `divCeil n d * d - d < n ≤ divCeil n d * d`. -/
theorem divCeil_bounds (n : Int) {d : Int} (hd : 0 < d) :
    divCeil n d * d - d < n ∧ n ≤ divCeil n d * d :=
  (divCeil_eq_iff hd).1 rfl

/-- `n / d` rounded to the nearest integer, ties toward positive infinity:
`(2 * n + d) / (2 * d)`, the floor of `n / d + 1 / 2` (JavaScript's `Math.round`). -/
def divHalfCeil (n d : Int) : Int := (2 * n + d) / (2 * d)

/-- `divHalfCeil n d = q` exactly when `-d < 2 * (q * d - n) ≤ d`: the result is within half a
unit of the exact value, and a tie (error exactly `-1/2` or `+1/2`) resolves to `+1/2`. -/
theorem divHalfCeil_eq_iff {n d q : Int} (hd : 0 < d) :
    divHalfCeil n d = q ↔ -d < 2 * (q * d - n) ∧ 2 * (q * d - n) ≤ d := by
  have key := ediv_eq_iff (n := 2 * n + d) (q := q) (show 0 < 2 * d by omega)
  have e : q * (2 * d) = 2 * (q * d) := Int.mul_left_comm q 2 d
  rw [e] at key
  unfold divHalfCeil
  rw [key]
  omega

/-- The bounds of `divHalfCeil`. -/
theorem divHalfCeil_bounds (n : Int) {d : Int} (hd : 0 < d) :
    -d < 2 * (divHalfCeil n d * d - n) ∧ 2 * (divHalfCeil n d * d - n) ≤ d :=
  (divHalfCeil_eq_iff hd).1 rfl

/-- `n / d` rounded to the nearest integer, ties toward negative infinity:
`-((d - 2 * n) / (2 * d))`, the ceiling of `n / d - 1 / 2`. -/
def divHalfFloor (n d : Int) : Int := -((d - 2 * n) / (2 * d))

/-- `divHalfFloor n d = q` exactly when `-d ≤ 2 * (q * d - n) < d`. -/
theorem divHalfFloor_eq_iff {n d q : Int} (hd : 0 < d) :
    divHalfFloor n d = q ↔ -d ≤ 2 * (q * d - n) ∧ 2 * (q * d - n) < d := by
  have key := ediv_eq_iff (n := d - 2 * n) (q := -q) (show 0 < 2 * d by omega)
  have e : -q * (2 * d) = -(2 * (q * d)) := by rw [Int.neg_mul, Int.mul_left_comm]
  rw [e] at key
  unfold divHalfFloor
  constructor
  · intro h
    have := key.1 (by omega)
    omega
  · intro h
    have := key.2 (by omega)
    omega

/-- The bounds of `divHalfFloor`. -/
theorem divHalfFloor_bounds (n : Int) {d : Int} (hd : 0 < d) :
    -d ≤ 2 * (divHalfFloor n d * d - n) ∧ 2 * (divHalfFloor n d * d - n) < d :=
  (divHalfFloor_eq_iff hd).1 rfl

/-- `n / d` rounded to the nearest integer, ties to the even neighbour (banker's rounding,
`ROUND_HALF_EVEN`). -/
def divHalfEven (n d : Int) : Int :=
  if 2 * (n % d) < d then n / d
  else if d < 2 * (n % d) then n / d + 1
  else if n / d % 2 = 0 then n / d else n / d + 1

/-- `divHalfEven` is within half a unit of the exact value and is even on a tie. -/
theorem divHalfEven_spec (n : Int) {d : Int} (hd : 0 < d) :
    -d ≤ 2 * (divHalfEven n d * d - n) ∧ 2 * (divHalfEven n d * d - n) ≤ d ∧
      (2 * (divHalfEven n d * d - n) = d ∨ 2 * (divHalfEven n d * d - n) = -d →
        divHalfEven n d % 2 = 0) := by
  have h1 : n % d = n - n / d * d := by rw [Int.emod_def, Int.mul_comm]
  have h2 := Int.emod_nonneg n (show d ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos n hd
  have e : (n / d + 1) * d = n / d * d + d := by rw [Int.add_mul, Int.one_mul]
  unfold divHalfEven
  generalize n % d = r at *
  generalize n / d = f at *
  by_cases ha : 2 * r < d
  · simp only [ha, ↓reduceIte]; omega
  · simp only [ha, ↓reduceIte]
    by_cases hb : d < 2 * r
    · simp only [hb, ↓reduceIte]; rw [e]; omega
    · simp only [hb, ↓reduceIte]
      by_cases hc : f % 2 = 0
      · simp only [hc, ↓reduceIte]
        exact ⟨by omega, by omega, fun _ => trivial⟩
      · simp only [hc, ↓reduceIte]; rw [e]
        refine ⟨by omega, by omega, fun _ => by omega⟩

/-- `divHalfEven n d = q` exactly when `-d ≤ 2 * (q * d - n) ≤ d` and `q` is even whenever
the error is exactly half a unit. -/
theorem divHalfEven_eq_iff {n d q : Int} (hd : 0 < d) :
    divHalfEven n d = q ↔ -d ≤ 2 * (q * d - n) ∧ 2 * (q * d - n) ≤ d ∧
      (2 * (q * d - n) = d ∨ 2 * (q * d - n) = -d → q % 2 = 0) := by
  constructor
  · rintro rfl; exact divHalfEven_spec n hd
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨g1, g2, g3⟩ := divHalfEven_spec n hd
    generalize divHalfEven n d = p at g1 g2 g3 ⊢
    rcases Int.lt_trichotomy p q with h | h | h
    · have m := mul_le_mul_of_le (Int.le_of_lt hd) (show p + 1 ≤ q by omega)
      rw [Int.add_mul, Int.one_mul] at m
      have e : q * d = (p + 1) * d := by rw [Int.add_mul, Int.one_mul]; omega
      have := Int.eq_of_mul_eq_mul_right (show d ≠ 0 by omega) e
      have := g3 (by omega)
      have := h3 (by omega)
      omega
    · exact h
    · have m := mul_le_mul_of_le (Int.le_of_lt hd) (show q + 1 ≤ p by omega)
      rw [Int.add_mul, Int.one_mul] at m
      have e : p * d = (q + 1) * d := by rw [Int.add_mul, Int.one_mul]; omega
      have := Int.eq_of_mul_eq_mul_right (show d ≠ 0 by omega) e
      have := g3 (by omega)
      have := h3 (by omega)
      omega

/-! ## Rounding modes -/

/-- A rounding mode for the quotient of two integers. -/
inductive RoundingMode where
  /-- Toward negative infinity (`FLOOR`). -/
  | floor
  /-- Toward positive infinity (`CEILING`). -/
  | ceil
  /-- Toward zero (`DOWN`, `ROUND_DOWN`, truncating integer division). -/
  | towardZero
  /-- Away from zero (`UP`, `ROUND_UP`). -/
  | awayFromZero
  /-- To the nearest integer, ties away from zero (`HALF_UP`, `ROUND_HALF_UP`). -/
  | halfUp
  /-- To the nearest integer, ties toward zero (`HALF_DOWN`, `ROUND_HALF_DOWN`). -/
  | halfDown
  /-- To the nearest integer, ties to the even neighbour (`HALF_EVEN`, banker's rounding). -/
  | halfEven
  /-- To the nearest integer, ties toward positive infinity (`ROUND_HALF_POSITIVE_INFINITY`,
  JavaScript's `Math.round`). -/
  | halfCeil
  /-- To the nearest integer, ties toward negative infinity
  (`ROUND_HALF_NEGATIVE_INFINITY`). -/
  | halfFloor
  deriving DecidableEq, Repr, Inhabited

namespace RoundingMode

/-- The modes that round to a nearest integer. -/
def isHalf : RoundingMode → Bool
  | floor => false
  | ceil => false
  | towardZero => false
  | awayFromZero => false
  | halfUp => true
  | halfDown => true
  | halfEven => true
  | halfCeil => true
  | halfFloor => true

/-- The mirrored mode: rounding `-n` with `m` is the negation of rounding `n` with `m.neg`
(`rdiv_neg`). -/
def neg : RoundingMode → RoundingMode
  | floor => ceil
  | ceil => floor
  | halfCeil => halfFloor
  | halfFloor => halfCeil
  | towardZero => towardZero
  | awayFromZero => awayFromZero
  | halfUp => halfUp
  | halfDown => halfDown
  | halfEven => halfEven

/-- Mirroring twice is the identity. -/
@[simp] theorem neg_neg (m : RoundingMode) : m.neg.neg = m := by cases m <;> rfl

end RoundingMode

open RoundingMode

/-- `n / d` rounded with mode `m` (for `0 < d`). -/
def rdiv : RoundingMode → Int → Int → Int
  | .floor, n, d => n / d
  | .ceil, n, d => divCeil n d
  | .towardZero, n, d => if 0 ≤ n then n / d else divCeil n d
  | .awayFromZero, n, d => if 0 ≤ n then divCeil n d else n / d
  | .halfUp, n, d => if 0 ≤ n then divHalfCeil n d else divHalfFloor n d
  | .halfDown, n, d => if 0 ≤ n then divHalfFloor n d else divHalfCeil n d
  | .halfEven, n, d => divHalfEven n d
  | .halfCeil, n, d => divHalfCeil n d
  | .halfFloor, n, d => divHalfFloor n d

@[simp] theorem rdiv_floor (n d : Int) : rdiv .floor n d = n / d := rfl
@[simp] theorem rdiv_ceil (n d : Int) : rdiv .ceil n d = divCeil n d := rfl
@[simp] theorem rdiv_halfEven (n d : Int) : rdiv .halfEven n d = divHalfEven n d := rfl
@[simp] theorem rdiv_halfCeil (n d : Int) : rdiv .halfCeil n d = divHalfCeil n d := rfl
@[simp] theorem rdiv_halfFloor (n d : Int) : rdiv .halfFloor n d = divHalfFloor n d := rfl

/-- `towardZero` is `floor` on a nonnegative numerator. -/
theorem rdiv_towardZero_of_nonneg {n : Int} (d : Int) (h : 0 ≤ n) :
    rdiv .towardZero n d = n / d := by simp [rdiv, h]

/-- `towardZero` is `ceil` on a negative numerator. -/
theorem rdiv_towardZero_of_neg {n : Int} (d : Int) (h : n < 0) :
    rdiv .towardZero n d = divCeil n d := by simp [rdiv, show ¬ 0 ≤ n by omega]

/-- `awayFromZero` is `ceil` on a nonnegative numerator. -/
theorem rdiv_awayFromZero_of_nonneg {n : Int} (d : Int) (h : 0 ≤ n) :
    rdiv .awayFromZero n d = divCeil n d := by simp [rdiv, h]

/-- `awayFromZero` is `floor` on a negative numerator. -/
theorem rdiv_awayFromZero_of_neg {n : Int} (d : Int) (h : n < 0) :
    rdiv .awayFromZero n d = n / d := by simp [rdiv, show ¬ 0 ≤ n by omega]

/-- `halfUp` is `halfCeil` on a nonnegative numerator. -/
theorem rdiv_halfUp_of_nonneg {n : Int} (d : Int) (h : 0 ≤ n) :
    rdiv .halfUp n d = divHalfCeil n d := by simp [rdiv, h]

/-- `halfUp` is `halfFloor` on a negative numerator. -/
theorem rdiv_halfUp_of_neg {n : Int} (d : Int) (h : n < 0) :
    rdiv .halfUp n d = divHalfFloor n d := by simp [rdiv, show ¬ 0 ≤ n by omega]

/-- `halfDown` is `halfFloor` on a nonnegative numerator. -/
theorem rdiv_halfDown_of_nonneg {n : Int} (d : Int) (h : 0 ≤ n) :
    rdiv .halfDown n d = divHalfFloor n d := by simp [rdiv, h]

/-- `halfDown` is `halfCeil` on a negative numerator. -/
theorem rdiv_halfDown_of_neg {n : Int} (d : Int) (h : n < 0) :
    rdiv .halfDown n d = divHalfCeil n d := by simp [rdiv, show ¬ 0 ≤ n by omega]

/-! ## Order between the base operations -/

/-- Rounding down is at most rounding up. -/
theorem ediv_le_divCeil (n : Int) {d : Int} (hd : 0 < d) : n / d ≤ divCeil n d := by
  have := ediv_bounds n hd
  have := divCeil_bounds n hd
  exact le_of_mul_lt_mul_add hd (by omega)

/-- Rounding up is at most one unit above rounding down. -/
theorem divCeil_le_ediv_add_one (n : Int) {d : Int} (hd : 0 < d) : divCeil n d ≤ n / d + 1 := by
  have := ediv_bounds n hd
  have := divCeil_bounds n hd
  have e : (n / d + 1) * d = n / d * d + d := by rw [Int.add_mul, Int.one_mul]
  exact le_of_mul_lt_mul_add hd (by omega)

/-- Rounding up equals rounding down exactly when `d` divides `n`. -/
theorem divCeil_eq_ediv_iff (n : Int) {d : Int} (hd : 0 < d) : divCeil n d = n / d ↔ n % d = 0 := by
  have h1 : n % d = n - n / d * d := by rw [Int.emod_def, Int.mul_comm]
  have := ediv_bounds n hd
  rw [divCeil_eq_iff hd]
  omega

/-- With a nonzero remainder, rounding up is rounding down plus one. -/
theorem divCeil_eq_ediv_add_one (n : Int) {d : Int} (hd : 0 < d) (h : n % d ≠ 0) :
    divCeil n d = n / d + 1 := by
  have := mt (divCeil_eq_ediv_iff n hd).1 h
  have := ediv_le_divCeil n hd
  have := divCeil_le_ediv_add_one n hd
  omega

/-- `floor ≤ halfFloor`. -/
theorem ediv_le_divHalfFloor (n : Int) {d : Int} (hd : 0 < d) : n / d ≤ divHalfFloor n d := by
  have := ediv_bounds n hd
  have := divHalfFloor_bounds n hd
  exact le_of_mul_lt_mul_add hd (by omega)

/-- `halfFloor ≤ halfCeil`. -/
theorem divHalfFloor_le_divHalfCeil (n : Int) {d : Int} (hd : 0 < d) :
    divHalfFloor n d ≤ divHalfCeil n d := by
  have := divHalfFloor_bounds n hd
  have := divHalfCeil_bounds n hd
  exact le_of_mul_lt_mul_add hd (by omega)

/-- `halfCeil ≤ halfFloor + 1`. -/
theorem divHalfCeil_le_divHalfFloor_add_one (n : Int) {d : Int} (hd : 0 < d) :
    divHalfCeil n d ≤ divHalfFloor n d + 1 := by
  have := divHalfFloor_bounds n hd
  have := divHalfCeil_bounds n hd
  have e : (divHalfFloor n d + 1) * d = divHalfFloor n d * d + d := by
    rw [Int.add_mul, Int.one_mul]
  exact le_of_mul_lt_mul_add hd (by omega)

/-- `halfCeil ≤ ceil`. -/
theorem divHalfCeil_le_divCeil (n : Int) {d : Int} (hd : 0 < d) : divHalfCeil n d ≤ divCeil n d := by
  have := divCeil_bounds n hd
  have := divHalfCeil_bounds n hd
  exact le_of_mul_lt_mul_add hd (by omega)

/-- `halfFloor ≤ halfEven`. -/
theorem divHalfFloor_le_divHalfEven (n : Int) {d : Int} (hd : 0 < d) :
    divHalfFloor n d ≤ divHalfEven n d := by
  have := divHalfFloor_bounds n hd
  have := divHalfEven_spec n hd
  exact le_of_mul_lt_mul_add hd (by omega)

/-- `halfEven ≤ halfCeil`. -/
theorem divHalfEven_le_divHalfCeil (n : Int) {d : Int} (hd : 0 < d) :
    divHalfEven n d ≤ divHalfCeil n d := by
  have := divHalfCeil_bounds n hd
  have := divHalfEven_spec n hd
  exact le_of_mul_lt_mul_add hd (by omega)

/-- The two nearest-integer roundings agree exactly when the fraction is not a tie, that is,
when twice the remainder is not the divisor. -/
theorem divHalfFloor_eq_divHalfCeil_iff (n : Int) {d : Int} (hd : 0 < d) :
    divHalfFloor n d = divHalfCeil n d ↔ 2 * (n % d) ≠ d := by
  have h1 : n % d = n - n / d * d := by rw [Int.emod_def, Int.mul_comm]
  have h2 := Int.emod_nonneg n (show d ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos n hd
  have e : (n / d + 1) * d = n / d * d + d := by rw [Int.add_mul, Int.one_mul]
  have hf := divHalfFloor_bounds n hd
  have hc := divHalfCeil_bounds n hd
  constructor
  · intro h htie
    rw [h] at hf
    have a1 : divHalfCeil n d ≤ n / d := le_of_mul_lt_mul_add hd (by omega)
    have a2 : n / d < divHalfCeil n d := Int.lt_of_mul_lt_mul_right (by omega) (Int.le_of_lt hd)
    omega
  · intro h
    by_cases hlt : 2 * (n % d) < d
    · rw [(divHalfFloor_eq_iff hd).2 (show -d ≤ 2 * (n / d * d - n) ∧ 2 * (n / d * d - n) < d by omega),
        (divHalfCeil_eq_iff hd).2 (show -d < 2 * (n / d * d - n) ∧ 2 * (n / d * d - n) ≤ d by omega)]
    · rw [(divHalfFloor_eq_iff hd).2
          (show -d ≤ 2 * ((n / d + 1) * d - n) ∧ 2 * ((n / d + 1) * d - n) < d by rw [e]; omega),
        (divHalfCeil_eq_iff hd).2
          (show -d < 2 * ((n / d + 1) * d - n) ∧ 2 * ((n / d + 1) * d - n) ≤ d by rw [e]; omega)]

/-! ## Every mode between floor and ceiling -/

/-- Every mode rounds to at least the floor and at most the ceiling. -/
theorem ediv_le_rdiv_le_divCeil (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    n / d ≤ rdiv m n d ∧ rdiv m n d ≤ divCeil n d := by
  have a := ediv_le_divCeil n hd
  have b := ediv_le_divHalfFloor n hd
  have c := divHalfFloor_le_divHalfCeil n hd
  have e := divHalfCeil_le_divCeil n hd
  have f := divHalfFloor_le_divHalfEven n hd
  have g := divHalfEven_le_divHalfCeil n hd
  cases m <;> simp only [rdiv] <;> (try split) <;> omega

/-- Every mode rounds to at least the floor. -/
theorem ediv_le_rdiv (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) : n / d ≤ rdiv m n d :=
  (ediv_le_rdiv_le_divCeil m n hd).1

/-- Every mode rounds to at most the ceiling. -/
theorem rdiv_le_divCeil (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    rdiv m n d ≤ divCeil n d :=
  (ediv_le_rdiv_le_divCeil m n hd).2

/-- Every mode returns the floor or the ceiling. -/
theorem rdiv_eq_ediv_or_divCeil (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    rdiv m n d = n / d ∨ rdiv m n d = divCeil n d := by
  have := ediv_le_rdiv_le_divCeil m n hd
  have := divCeil_le_ediv_add_one n hd
  omega

/-- Every mode is within one unit of the exact value: `-d < rdiv m n d * d - n < d`. -/
theorem rdiv_bounds (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    -d < rdiv m n d * d - n ∧ rdiv m n d * d - n < d := by
  obtain ⟨h1, h2⟩ := ediv_le_rdiv_le_divCeil m n hd
  have a := mul_le_mul_of_le (Int.le_of_lt hd) h1
  have b := mul_le_mul_of_le (Int.le_of_lt hd) h2
  have := ediv_bounds n hd
  have := divCeil_bounds n hd
  omega

/-- On an exact multiple every mode returns the multiplier. -/
@[simp] theorem rdiv_mul_self (m : RoundingMode) (k : Int) {d : Int} (hd : 0 < d) :
    rdiv m (k * d) d = k := by
  have h1 : k * d / d = k := Int.mul_ediv_cancel k (show d ≠ 0 by omega)
  have h2 : divCeil (k * d) d = k := (divCeil_eq_iff hd).2 (by omega)
  have := ediv_le_rdiv_le_divCeil m (k * d) hd
  omega

/-- Zero rounds to zero in every mode. -/
@[simp] theorem rdiv_zero_left (m : RoundingMode) {d : Int} (hd : 0 < d) : rdiv m 0 d = 0 := by
  have := rdiv_mul_self m 0 hd
  rwa [Int.zero_mul] at this

/-- When `d` divides `n` every mode returns `n / d`. -/
theorem rdiv_of_emod_eq_zero (m : RoundingMode) {n d : Int} (hd : 0 < d) (h : n % d = 0) :
    rdiv m n d = n / d := by
  have := (divCeil_eq_ediv_iff n hd).2 h
  have := ediv_le_rdiv_le_divCeil m n hd
  omega

/-- A nonnegative numerator rounds to a nonnegative result in every mode. -/
theorem rdiv_nonneg (m : RoundingMode) {n d : Int} (hd : 0 < d) (hn : 0 ≤ n) : 0 ≤ rdiv m n d :=
  Int.le_trans (Int.ediv_nonneg hn (Int.le_of_lt hd)) (ediv_le_rdiv m n hd)

/-- A nonpositive numerator rounds to a nonpositive result in every mode. -/
theorem rdiv_nonpos (m : RoundingMode) {n d : Int} (hd : 0 < d) (hn : n ≤ 0) : rdiv m n d ≤ 0 := by
  have := divCeil_bounds n hd
  have : divCeil n d ≤ 0 := le_of_mul_lt_mul_add hd (by rw [Int.zero_mul]; omega)
  have := rdiv_le_divCeil m n hd
  omega

/-! ## The nearest-integer modes -/

/-- The nearest-integer modes are within half a unit of the exact value:
`-d ≤ 2 * (rdiv m n d * d - n) ≤ d`. -/
theorem rdiv_half_bounds {m : RoundingMode} (hm : m.isHalf = true) (n : Int) {d : Int}
    (hd : 0 < d) : -d ≤ 2 * (rdiv m n d * d - n) ∧ 2 * (rdiv m n d * d - n) ≤ d := by
  have := divHalfCeil_bounds n hd
  have := divHalfFloor_bounds n hd
  have := divHalfEven_spec n hd
  cases m <;> simp only [isHalf, Bool.false_eq_true] at hm <;> simp only [rdiv] <;> (try split) <;> omega

/-- The nearest-integer modes lie between `halfFloor` and `halfCeil`. -/
theorem divHalfFloor_le_rdiv_le_divHalfCeil {m : RoundingMode} (hm : m.isHalf = true) (n : Int)
    {d : Int} (hd : 0 < d) : divHalfFloor n d ≤ rdiv m n d ∧ rdiv m n d ≤ divHalfCeil n d := by
  have := divHalfFloor_le_divHalfCeil n hd
  have := divHalfFloor_le_divHalfEven n hd
  have := divHalfEven_le_divHalfCeil n hd
  cases m <;> simp only [isHalf, Bool.false_eq_true] at hm <;> simp only [rdiv] <;> (try split) <;> omega

/-- Off a tie every nearest-integer mode gives the same result. -/
theorem rdiv_half_eq_of_not_tie {m m' : RoundingMode} (hm : m.isHalf = true)
    (hm' : m'.isHalf = true) {n d : Int} (hd : 0 < d) (h : 2 * (n % d) ≠ d) :
    rdiv m n d = rdiv m' n d := by
  have := (divHalfFloor_eq_divHalfCeil_iff n hd).2 h
  have := divHalfFloor_le_rdiv_le_divHalfCeil hm n hd
  have := divHalfFloor_le_rdiv_le_divHalfCeil hm' n hd
  omega

/-- The nearest-integer modes give a nearest integer: no integer `z` has a smaller error. -/
theorem rdiv_half_nearest {m : RoundingMode} (hm : m.isHalf = true) (n : Int) {d : Int}
    (hd : 0 < d) (z : Int) : (rdiv m n d * d - n).natAbs ≤ (z * d - n).natAbs := by
  have hb := rdiv_half_bounds hm n hd
  generalize rdiv m n d = q at hb ⊢
  rcases Int.lt_trichotomy z q with h | h | h
  · have := mul_le_mul_of_le (Int.le_of_lt hd) (show z + 1 ≤ q by omega)
    rw [Int.add_mul, Int.one_mul] at this
    omega
  · subst h; exact Nat.le_refl _
  · have := mul_le_mul_of_le (Int.le_of_lt hd) (show q + 1 ≤ z by omega)
    rw [Int.add_mul, Int.one_mul] at this
    omega

/-! ## Magnitudes -/

/-- Rounding toward zero gives the least magnitude of all modes. -/
theorem natAbs_towardZero_le (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    (rdiv .towardZero n d).natAbs ≤ (rdiv m n d).natAbs := by
  have := ediv_le_rdiv_le_divCeil m n hd
  by_cases hn : 0 ≤ n
  · rw [rdiv_towardZero_of_nonneg d hn]
    have := Int.ediv_nonneg hn (Int.le_of_lt hd)
    omega
  · rw [rdiv_towardZero_of_neg d (by omega)]
    have := rdiv_nonpos .ceil hd (show n ≤ 0 by omega)
    simp only [rdiv_ceil] at this
    omega

/-- Rounding away from zero gives the largest magnitude of all modes. -/
theorem natAbs_le_awayFromZero (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    (rdiv m n d).natAbs ≤ (rdiv .awayFromZero n d).natAbs := by
  have := ediv_le_rdiv_le_divCeil m n hd
  by_cases hn : 0 ≤ n
  · rw [rdiv_awayFromZero_of_nonneg d hn]
    have := Int.ediv_nonneg hn (Int.le_of_lt hd)
    omega
  · rw [rdiv_awayFromZero_of_neg d (by omega)]
    have := rdiv_nonpos .ceil hd (show n ≤ 0 by omega)
    simp only [rdiv_ceil] at this
    omega

/-- Rounding toward zero never exceeds the exact magnitude:
`|rdiv .towardZero n d| * d ≤ |n|`. -/
theorem natAbs_towardZero_mul_le (n : Int) {d : Int} (hd : 0 < d) :
    ((rdiv .towardZero n d).natAbs : Int) * d ≤ n.natAbs := by
  by_cases hn : 0 ≤ n
  · rw [rdiv_towardZero_of_nonneg d hn]
    have := Int.ediv_nonneg hn (Int.le_of_lt hd)
    have := ediv_bounds n hd
    have e : ((n / d).natAbs : Int) = n / d := by omega
    rw [e]; omega
  · rw [rdiv_towardZero_of_neg d (by omega)]
    have := rdiv_nonpos .ceil hd (show n ≤ 0 by omega)
    simp only [rdiv_ceil] at this
    have := divCeil_bounds n hd
    have e : ((divCeil n d).natAbs : Int) = -divCeil n d := by omega
    rw [e, Int.neg_mul]; omega

/-! ## Negation -/

/-- `floor (-n) = -ceil n`. -/
theorem neg_ediv_eq_neg_divCeil (n d : Int) : (-n) / d = -divCeil n d := by
  unfold divCeil; omega

/-- `ceil (-n) = -floor n`. -/
theorem divCeil_neg (n d : Int) : divCeil (-n) d = -(n / d) := by
  unfold divCeil; rw [Int.neg_neg]

/-- `halfCeil (-n) = -halfFloor n`. -/
theorem divHalfCeil_neg (n d : Int) : divHalfCeil (-n) d = -divHalfFloor n d := by
  unfold divHalfCeil divHalfFloor
  rw [Int.neg_neg, show 2 * -n + d = d - 2 * n by omega]

/-- `halfFloor (-n) = -halfCeil n`. -/
theorem divHalfFloor_neg (n d : Int) : divHalfFloor (-n) d = -divHalfCeil n d := by
  unfold divHalfCeil divHalfFloor
  rw [show d - 2 * -n = 2 * n + d by omega]

/-- `halfEven (-n) = -halfEven n`. -/
theorem divHalfEven_neg (n : Int) {d : Int} (hd : 0 < d) : divHalfEven (-n) d = -divHalfEven n d := by
  apply (divHalfEven_eq_iff hd).2
  obtain ⟨h1, h2, h3⟩ := divHalfEven_spec n hd
  rw [Int.neg_mul]
  refine ⟨by omega, by omega, fun h => ?_⟩
  have := h3 (by omega)
  omega

/-- Rounding commutes with negation up to mirroring the mode: `rdiv m (-n) d = -rdiv m.neg n d`.
`floor` and `ceil` swap, `halfCeil` and `halfFloor` swap, and the symmetric modes
(`towardZero`, `awayFromZero`, `halfUp`, `halfDown`, `halfEven`) are odd functions. -/
theorem rdiv_neg (m : RoundingMode) (n : Int) {d : Int} (hd : 0 < d) :
    rdiv m (-n) d = -rdiv m.neg n d := by
  have z1 : (0 : Int) / d = 0 := Int.zero_ediv d
  have z2 : divCeil 0 d = 0 := (divCeil_eq_iff hd).2 (by rw [Int.zero_mul]; omega)
  have z3 : divHalfCeil 0 d = 0 := (divHalfCeil_eq_iff hd).2 (by rw [Int.zero_mul]; omega)
  have z4 : divHalfFloor 0 d = 0 := (divHalfFloor_eq_iff hd).2 (by rw [Int.zero_mul]; omega)
  cases m with
  | floor => exact neg_ediv_eq_neg_divCeil n d
  | ceil => exact divCeil_neg n d
  | halfCeil => exact divHalfCeil_neg n d
  | halfFloor => exact divHalfFloor_neg n d
  | halfEven => exact divHalfEven_neg n hd
  | towardZero =>
    simp only [rdiv, RoundingMode.neg]
    by_cases h : n = 0
    · subst h; simp [z1]
    · by_cases hn : 0 ≤ n
      · simp only [show ¬ 0 ≤ -n by omega, hn, ↓reduceIte, divCeil_neg]
      · simp only [show 0 ≤ -n by omega, hn, ↓reduceIte, neg_ediv_eq_neg_divCeil]
  | awayFromZero =>
    simp only [rdiv, RoundingMode.neg]
    by_cases h : n = 0
    · subst h; simp [z2]
    · by_cases hn : 0 ≤ n
      · simp only [show ¬ 0 ≤ -n by omega, hn, ↓reduceIte, neg_ediv_eq_neg_divCeil]
      · simp only [show 0 ≤ -n by omega, hn, ↓reduceIte, divCeil_neg]
  | halfUp =>
    simp only [rdiv, RoundingMode.neg]
    by_cases h : n = 0
    · subst h; simp [z3]
    · by_cases hn : 0 ≤ n
      · simp only [show ¬ 0 ≤ -n by omega, hn, ↓reduceIte, divHalfFloor_neg]
      · simp only [show 0 ≤ -n by omega, hn, ↓reduceIte, divHalfCeil_neg]
  | halfDown =>
    simp only [rdiv, RoundingMode.neg]
    by_cases h : n = 0
    · subst h; simp [z4]
    · by_cases hn : 0 ≤ n
      · simp only [show ¬ 0 ≤ -n by omega, hn, ↓reduceIte, divHalfCeil_neg]
      · simp only [show 0 ≤ -n by omega, hn, ↓reduceIte, divHalfFloor_neg]

/-! ## Monotonicity -/

/-- `ceil` is monotone in the numerator. -/
theorem divCeil_mono {n n' : Int} {d : Int} (hd : 0 < d) (h : n ≤ n') : divCeil n d ≤ divCeil n' d := by
  unfold divCeil
  have := Int.ediv_le_ediv hd (show -n' ≤ -n by omega)
  omega

/-- `halfCeil` is monotone in the numerator. -/
theorem divHalfCeil_mono {n n' : Int} {d : Int} (hd : 0 < d) (h : n ≤ n') :
    divHalfCeil n d ≤ divHalfCeil n' d :=
  Int.ediv_le_ediv (by omega) (by omega)

/-- `halfFloor` is monotone in the numerator. -/
theorem divHalfFloor_mono {n n' : Int} {d : Int} (hd : 0 < d) (h : n ≤ n') :
    divHalfFloor n d ≤ divHalfFloor n' d := by
  unfold divHalfFloor
  have := Int.ediv_le_ediv (show 0 < 2 * d by omega) (show d - 2 * n' ≤ d - 2 * n by omega)
  omega

/-- `halfEven` is monotone in the numerator. -/
theorem divHalfEven_mono {n n' : Int} {d : Int} (hd : 0 < d) (h : n ≤ n') :
    divHalfEven n d ≤ divHalfEven n' d := by
  rcases Int.lt_or_eq_of_le h with h | h
  · have := divHalfEven_spec n hd
    have := divHalfEven_spec n' hd
    exact le_of_mul_lt_mul_add hd (by omega)
  · subst h; exact Int.le_refl _

/-- Every mode is monotone in the numerator. -/
theorem rdiv_mono (m : RoundingMode) {n n' : Int} {d : Int} (hd : 0 < d) (h : n ≤ n') :
    rdiv m n d ≤ rdiv m n' d := by
  have f := Int.ediv_le_ediv hd h
  have c := divCeil_mono hd h
  have hc := divHalfCeil_mono hd h
  have hf := divHalfFloor_mono hd h
  have fc := ediv_le_divCeil n' hd
  have hfc := divHalfFloor_le_divHalfCeil n' hd
  have hfc' := divHalfFloor_le_divHalfCeil n hd
  have fc' := ediv_le_divCeil n hd
  have n1 := rdiv_nonpos .ceil hd (n := n)
  have n2 := rdiv_nonneg .floor hd (n := n')
  have n3 := rdiv_nonpos .halfCeil hd (n := n)
  have n4 := rdiv_nonneg .halfFloor hd (n := n')
  simp only [rdiv_ceil, rdiv_floor, rdiv_halfCeil, rdiv_halfFloor] at n1 n2 n3 n4
  cases m with
  | floor => exact f
  | ceil => exact c
  | halfCeil => exact hc
  | halfFloor => exact hf
  | halfEven => exact divHalfEven_mono hd h
  | towardZero =>
    simp only [rdiv]
    split <;> split <;> omega
  | awayFromZero =>
    simp only [rdiv]
    split <;> split <;> omega
  | halfUp =>
    simp only [rdiv]
    split <;> split <;> omega
  | halfDown =>
    simp only [rdiv]
    split <;> split <;> omega

/-! ## Scale invariance and the order of fractions -/

/-- Floor division depends only on the value of the fraction. -/
theorem ediv_mul_mul (n d : Int) {k : Int} (hk : 0 < k) : n * k / (d * k) = n / d := by
  rw [Int.mul_comm n k, Int.mul_comm d k]
  exact Int.mul_ediv_mul_of_pos n d hk

/-- `ceil` depends only on the value of the fraction. -/
theorem divCeil_mul_mul (n d : Int) {k : Int} (hk : 0 < k) :
    divCeil (n * k) (d * k) = divCeil n d := by
  unfold divCeil
  rw [← Int.neg_mul, ediv_mul_mul _ _ hk]

/-- `halfCeil` depends only on the value of the fraction. -/
theorem divHalfCeil_mul_mul (n d : Int) {k : Int} (hk : 0 < k) :
    divHalfCeil (n * k) (d * k) = divHalfCeil n d := by
  unfold divHalfCeil
  have e1 : 2 * (n * k) + d * k = (2 * n + d) * k := by grind
  have e2 : 2 * (d * k) = 2 * d * k := by grind
  rw [e1, e2, ediv_mul_mul _ _ hk]

/-- `halfFloor` depends only on the value of the fraction. -/
theorem divHalfFloor_mul_mul (n d : Int) {k : Int} (hk : 0 < k) :
    divHalfFloor (n * k) (d * k) = divHalfFloor n d := by
  unfold divHalfFloor
  have e1 : d * k - 2 * (n * k) = (d - 2 * n) * k := by grind
  have e2 : 2 * (d * k) = 2 * d * k := by grind
  rw [e1, e2, ediv_mul_mul _ _ hk]

/-- `halfEven` depends only on the value of the fraction. -/
theorem divHalfEven_mul_mul (n : Int) {d k : Int} (hd : 0 < d) (hk : 0 < k) :
    divHalfEven (n * k) (d * k) = divHalfEven n d := by
  apply (divHalfEven_eq_iff (Int.mul_pos hd hk)).2
  obtain ⟨h1, h2, h3⟩ := divHalfEven_spec n hd
  generalize divHalfEven n d = q at h1 h2 h3 ⊢
  have e : 2 * (q * (d * k) - n * k) = 2 * (q * d - n) * k := by grind
  have e2 : -(d * k) = -d * k := by rw [Int.neg_mul]
  rw [e, e2]
  refine ⟨(Int.mul_le_mul_right hk).2 h1, (Int.mul_le_mul_right hk).2 h2, fun h => h3 ?_⟩
  rcases h with h | h
  · exact Or.inl (Int.eq_of_mul_eq_mul_right (show k ≠ 0 by omega) h)
  · exact Or.inr (Int.eq_of_mul_eq_mul_right (show k ≠ 0 by omega) h)

/-- Every mode depends only on the value of the fraction:
`rdiv m (n * k) (d * k) = rdiv m n d` for `0 < k`. -/
theorem rdiv_mul_mul (m : RoundingMode) (n : Int) {d k : Int} (hd : 0 < d) (hk : 0 < k) :
    rdiv m (n * k) (d * k) = rdiv m n d := by
  have s : (0 ≤ n * k) ↔ 0 ≤ n := by
    constructor
    · intro h
      rcases Int.lt_or_le n 0 with hn | hn
      · have := Int.mul_lt_mul_of_pos_right hn hk; rw [Int.zero_mul] at this; omega
      · exact hn
    · intro h; exact Int.mul_nonneg h (Int.le_of_lt hk)
  have a := ediv_mul_mul n d hk
  have b := divCeil_mul_mul n d hk
  have c := divHalfCeil_mul_mul n d hk
  have e := divHalfFloor_mul_mul n d hk
  cases m <;> simp only [rdiv, s, a, b, c, e, divHalfEven_mul_mul n hd hk]

/-- Every mode respects the order of fractions: `n / d ≤ n' / d'` as rationals (by
cross-multiplication, `n * d' ≤ n' * d`) gives `rdiv m n d ≤ rdiv m n' d'`. -/
theorem rdiv_le_rdiv_of_mul_le (m : RoundingMode) {n d n' d' : Int} (hd : 0 < d) (hd' : 0 < d')
    (h : n * d' ≤ n' * d) : rdiv m n d ≤ rdiv m n' d' := by
  rw [← rdiv_mul_mul m n hd hd', ← rdiv_mul_mul m n' hd' hd, Int.mul_comm d' d]
  exact rdiv_mono m (Int.mul_pos hd hd') h

/-! ## Integer shifts -/

/-- Adding a multiple of the divisor shifts the floor by the multiplier. -/
theorem ediv_add_mul (n k : Int) {d : Int} (hd : 0 < d) : (n + k * d) / d = n / d + k :=
  Int.add_mul_ediv_right n k (show d ≠ 0 by omega)

/-- `floor`, `ceil`, `halfCeil` and `halfFloor` commute with adding a multiple of the divisor
(the sign-dependent modes and `halfEven` do not: `halfEven` changes its tie choice with the
parity of the shift). -/
theorem rdiv_add_mul {m : RoundingMode} (hm : m = .floor ∨ m = .ceil ∨ m = .halfCeil ∨ m = .halfFloor)
    (n k : Int) {d : Int} (hd : 0 < d) : rdiv m (n + k * d) d = rdiv m n d + k := by
  have e : ∀ q : Int, (q + k) * d - (n + k * d) = q * d - n := fun q => by
    rw [Int.add_mul]; omega
  rcases hm with rfl | rfl | rfl | rfl
  · exact ediv_add_mul n k hd
  · simp only [rdiv_ceil]
    apply (divCeil_eq_iff hd).2
    have := divCeil_bounds n hd
    have := e (divCeil n d)
    omega
  · simp only [rdiv_halfCeil]
    apply (divHalfCeil_eq_iff hd).2
    rw [e]; exact divHalfCeil_bounds n hd
  · simp only [rdiv_halfFloor]
    apply (divHalfFloor_eq_iff hd).2
    rw [e]; exact divHalfFloor_bounds n hd

/-! ## Rounding a sum and summing rounded parts -/

/-- Pointwise bounds on a scaled error give bounds on the total: if every `n` of the list has
`lo ≤ k * (f n * d - n) ≤ hi`, the total error `k * (Σ f n * d - Σ n)` lies between
`length * lo` and `length * hi`. -/
theorem sum_error_bounds (f : Int → Int) {k d lo hi : Int} (ns : List Int)
    (h : ∀ n ∈ ns, lo ≤ k * (f n * d - n) ∧ k * (f n * d - n) ≤ hi) :
    ns.length * lo ≤ k * ((ns.map f).sum * d - ns.sum) ∧
      k * ((ns.map f).sum * d - ns.sum) ≤ ns.length * hi := by
  induction ns with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun n hn => h n (by simp [hn]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e : k * ((f a + (l.map f).sum) * d - (a + l.sum)) =
        k * (f a * d - a) + k * ((l.map f).sum * d - l.sum) := by grind
    have e1 : ((l.length + 1 : Nat) : Int) * lo = (l.length : Int) * lo + lo := by
      push_cast; rw [Int.add_mul, Int.one_mul]
    have e2 : ((l.length + 1 : Nat) : Int) * hi = (l.length : Int) * hi + hi := by
      push_cast; rw [Int.add_mul, Int.one_mul]
    rw [e, e1, e2]
    omega

/-- Rounding each part down loses at least as much as rounding the sum down: the sum of the
floors is at most the floor of the sum. -/
theorem sum_ediv_le_ediv_sum (ns : List Int) {d : Int} (hd : 0 < d) :
    (ns.map (· / d)).sum ≤ ns.sum / d := by
  have := sum_error_bounds (· / d) (k := 1) (d := d) (lo := 1 - d) (hi := 0) ns
    (fun n _ => by have := ediv_bounds n hd; omega)
  apply (Int.le_ediv_iff_mul_le hd).2
  omega

/-- Rounding each of the parts of a nonempty list down loses less than one unit per part
beyond rounding the sum: `floor (Σ n) < Σ floor n + length`. -/
theorem ediv_sum_lt_sum_ediv_add_length (ns : List Int) {d : Int} (hd : 0 < d) (hne : ns ≠ []) :
    ns.sum / d < (ns.map (· / d)).sum + ns.length := by
  have := sum_error_bounds (· / d) (k := 1) (d := d) (lo := 1 - d) (hi := 0) ns
    (fun n _ => by have := ediv_bounds n hd; omega)
  have hl : 0 < ns.length := List.length_pos_iff.mpr hne
  have hb := ediv_bounds ns.sum hd
  generalize (ns.map (· / d)).sum = s at this ⊢
  have e1 : (s + ((ns.length : Int) - 1)) * d = s * d + (ns.length : Int) * d - d := by grind
  have e2 : (ns.length : Int) * (1 - d) = ns.length - ns.length * d := by grind
  rw [e2] at this
  have := le_of_mul_lt_mul_add (q := ns.sum / d) (q' := s + ((ns.length : Int) - 1)) hd
    (by rw [e1]; omega)
  omega

/-- `divCeil n d ≤ q` exactly when `n ≤ q * d`. -/
theorem divCeil_le_iff {n d q : Int} (hd : 0 < d) : divCeil n d ≤ q ↔ n ≤ q * d := by
  have := divCeil_bounds n hd
  constructor
  · intro h; have := mul_le_mul_of_le (Int.le_of_lt hd) h; omega
  · intro h; exact le_of_mul_lt_mul_add hd (by omega)

/-- `q ≤ n / d` exactly when `q * d ≤ n`. -/
theorem le_ediv_iff {n d q : Int} (hd : 0 < d) : q ≤ n / d ↔ q * d ≤ n := Int.le_ediv_iff_mul_le hd

/-- The ceiling of the sum is at most the sum of the ceilings. -/
theorem divCeil_sum_le_sum_divCeil (ns : List Int) {d : Int} (hd : 0 < d) :
    divCeil ns.sum d ≤ (ns.map (divCeil · d)).sum := by
  have := sum_error_bounds (divCeil · d) (k := 1) (d := d) (lo := 0) (hi := d - 1) ns
    (fun n _ => by have := divCeil_bounds n hd; omega)
  apply (divCeil_le_iff hd).2
  omega

/-- Rounding each part of a nonempty list up gains less than one unit per part beyond rounding
the sum up: `Σ ceil n < ceil (Σ n) + length`. -/
theorem sum_divCeil_lt_divCeil_sum_add_length (ns : List Int) {d : Int} (hd : 0 < d)
    (hne : ns ≠ []) : (ns.map (divCeil · d)).sum < divCeil ns.sum d + ns.length := by
  have := sum_error_bounds (divCeil · d) (k := 1) (d := d) (lo := 0) (hi := d - 1) ns
    (fun n _ => by have := divCeil_bounds n hd; omega)
  have hl : 0 < ns.length := List.length_pos_iff.mpr hne
  have hb := divCeil_bounds ns.sum hd
  generalize (ns.map (divCeil · d)).sum = s at this ⊢
  have e1 : (divCeil ns.sum d + ((ns.length : Int) - 1)) * d =
      divCeil ns.sum d * d + (ns.length : Int) * d - d := by grind
  have e2 : (ns.length : Int) * (d - 1) = ns.length * d - ns.length := by grind
  rw [e2] at this
  have := le_of_mul_lt_mul_add (q := s) (q' := divCeil ns.sum d + ((ns.length : Int) - 1)) hd
    (by rw [e1]; omega)
  omega

/-- In every mode, rounding the sum and summing the rounded parts differ by at most the
number of parts. -/
theorem rdiv_sum_sub_sum_rdiv (m : RoundingMode) (ns : List Int) {d : Int} (hd : 0 < d) :
    -(ns.length : Int) ≤ rdiv m ns.sum d - (ns.map (rdiv m · d)).sum ∧
      rdiv m ns.sum d - (ns.map (rdiv m · d)).sum ≤ ns.length := by
  have := sum_error_bounds (rdiv m · d) (k := 1) (d := d) (lo := 1 - d) (hi := d - 1) ns
    (fun n _ => by have := rdiv_bounds m n hd; omega)
  have hb := rdiv_bounds m ns.sum hd
  generalize (ns.map (rdiv m · d)).sum = s at this ⊢
  generalize rdiv m ns.sum d = Q at hb ⊢
  have e1 : (s + (ns.length : Int)) * d = s * d + (ns.length : Int) * d := by grind
  have e2 : (Q + (ns.length : Int)) * d = Q * d + (ns.length : Int) * d := by grind
  have e3 : (ns.length : Int) * (1 - d) = ns.length - ns.length * d := by grind
  have e4 : (ns.length : Int) * (d - 1) = ns.length * d - ns.length := by grind
  rw [e3, e4] at this
  have := le_of_mul_lt_mul_add (q := Q) (q' := s + ns.length) hd (by rw [e1]; omega)
  have := le_of_mul_lt_mul_add (q := s) (q' := Q + ns.length) hd (by rw [e2]; omega)
  omega

/-- In the nearest-integer modes, rounding the sum and summing the rounded parts differ by at
most half the number of parts plus one half: `|2 * (rdiv m (Σ n) d - Σ rdiv m n d)| ≤ length + 1`.
For two parts the difference is at most one unit. -/
theorem rdiv_sum_sub_sum_rdiv_half {m : RoundingMode} (hm : m.isHalf = true) (ns : List Int)
    {d : Int} (hd : 0 < d) :
    -((ns.length : Int) + 1) ≤ 2 * (rdiv m ns.sum d - (ns.map (rdiv m · d)).sum) ∧
      2 * (rdiv m ns.sum d - (ns.map (rdiv m · d)).sum) ≤ ns.length + 1 := by
  have := sum_error_bounds (rdiv m · d) (k := 2) (d := d) (lo := -d) (hi := d) ns
    (fun n _ => by have := rdiv_half_bounds hm n hd; omega)
  have hb := rdiv_half_bounds hm ns.sum hd
  generalize (ns.map (rdiv m · d)).sum = s at this ⊢
  generalize rdiv m ns.sum d = Q at hb ⊢
  have e1 : (2 * (Q - s)) * d = 2 * (Q * d - ns.sum) - 2 * (s * d - ns.sum) := by grind
  have e2 : (2 * (s - Q)) * d = 2 * (s * d - ns.sum) - 2 * (Q * d - ns.sum) := by grind
  have e3 : ((ns.length : Int) + 1) * d = (ns.length : Int) * d + d := by grind
  have e4 : (ns.length : Int) * -d = -((ns.length : Int) * d) := by grind
  rw [e4] at this
  have := le_of_mul_lt_mul_add (q := 2 * (Q - s)) (q' := (ns.length : Int) + 1) hd
    (by rw [e1, e3]; omega)
  have := le_of_mul_lt_mul_add (q := 2 * (s - Q)) (q' := (ns.length : Int) + 1) hd
    (by rw [e2, e3]; omega)
  omega

/-! ## Natural-number fractions and Lean's other divisions -/

/-- On natural numbers `floor` is `Nat` division. -/
theorem rdiv_floor_natCast (n d : Nat) : rdiv .floor (n : Int) (d : Int) = ((n / d : Nat) : Int) :=
  (Int.natCast_ediv n d).symm

/-- On natural numbers `ceil` is `ceilDiv`. -/
theorem rdiv_ceil_natCast (n : Nat) {d : Nat} (hd : 0 < d) :
    rdiv .ceil (n : Int) (d : Int) = ((ceilDiv n d : Nat) : Int) := by
  simp only [rdiv_ceil]
  have := ceilDiv_spec n d hd
  apply (divCeil_eq_iff (by omega)).2
  have e : ((ceilDiv n d : Nat) : Int) * (d : Int) = ((ceilDiv n d * d : Nat) : Int) := by push_cast; rfl
  rw [e]
  omega

/-- `towardZero` is Lean's `Int.tdiv` (Go's and C's integer division) for a positive divisor. -/
theorem rdiv_towardZero_eq_tdiv (n d : Int) : rdiv .towardZero n d = n.tdiv d := by
  by_cases hn : 0 ≤ n
  · rw [rdiv_towardZero_of_nonneg d hn, Int.tdiv_eq_ediv_of_nonneg hn]
  · rw [rdiv_towardZero_of_neg d (by omega)]
    have : n.tdiv d = -((-n).tdiv d) := by rw [Int.neg_tdiv, Int.neg_neg]
    rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    rfl

/-- `floor` is Lean's `Int.fdiv` for a positive divisor. -/
theorem rdiv_floor_eq_fdiv (n : Int) {d : Int} (hd : 0 < d) : rdiv .floor n d = n.fdiv d :=
  (Int.fdiv_eq_ediv_of_nonneg n (Int.le_of_lt hd)).symm

end ProofForgeFin.Money
