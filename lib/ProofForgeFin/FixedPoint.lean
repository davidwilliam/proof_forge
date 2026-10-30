import ProofForgeFin.Rounding
/-!
# Fixed-point arithmetic on natural numbers

A fixed-point number with scale `one` represents the rational `x / one` by the natural number
`x` (Solidity's 18-decimal `WAD` has `one = 10^18`, Compound's `doubleScale` has `one = 10^36`,
a Q64.64 number has `one = 2^64`). Every operation here takes the scale as its first argument,
so one set of lemmas covers every scale; the lemmas need only `0 < one`.

* `mulDiv a n d` and `mulDivUp a n d`: `a * n / d` rounded down and rounded up. Every other
  operation is one of these two.
* `mulDown one a b`, `mulUp one a b`: the product `a * b / one`, rounded down or up
  (`FixedPoint.mulDown`, `FixedPoint.mulUp`).
* `divDown one a b`, `divUp one a b`: the quotient `a * one / b`, rounded down or up
  (`FixedPoint.divDown`, `FixedPoint.divUp`).
* `scaleDown`, `scaleUp`: conversion of a raw amount to scaled units with a scaling factor
  (Balancer's `_upscale`), rounded down or up; `unscaleDown`, `unscaleUp`: the conversion back
  (`_downscaleDown`, `_downscaleUp`).

For each operation the module proves the exact bounds (the result is within one unit of the
exact value, on the stated side), the order between the two rounding directions (rounding up is
at least rounding down and at most one more), monotonicity, and round trips (converting and
converting back in the direction that favours the holder of the funds never gains a unit).
-/

namespace ProofForgeFin

/-! ## Scaled quotient -/

/-- `a * n / d`, rounded down. -/
def mulDiv (a n d : Nat) : Nat := a * n / d

/-- `a * n / d`, rounded up. -/
def mulDivUp (a n d : Nat) : Nat := ceilDiv (a * n) d

/-- `mulDiv` is within one unit below the exact value `a * n / d`. -/
theorem mulDiv_spec (a n d : Nat) (hd : 0 < d) :
    mulDiv a n d * d ≤ a * n ∧ a * n < (mulDiv a n d + 1) * d :=
  floor_spec (a * n) d hd

/-- `mulDivUp` is within one unit above the exact value `a * n / d`. -/
theorem mulDivUp_spec (a n d : Nat) (hd : 0 < d) :
    a * n ≤ mulDivUp a n d * d ∧ mulDivUp a n d * d < a * n + d :=
  ceilDiv_spec (a * n) d hd

/-- Rounding down is at most rounding up. -/
theorem mulDiv_le_mulDivUp (a n d : Nat) : mulDiv a n d ≤ mulDivUp a n d := div_le_ceilDiv _ _

/-- Rounding up is at most one unit above rounding down. -/
theorem mulDivUp_le_mulDiv_add_one (a n d : Nat) : mulDivUp a n d ≤ mulDiv a n d + 1 :=
  ceilDiv_le_div_add_one _ _

/-- `mulDiv` is monotone in both factors. -/
theorem mulDiv_mono {a a' n n' : Nat} (d : Nat) (ha : a ≤ a') (hn : n ≤ n') :
    mulDiv a n d ≤ mulDiv a' n' d :=
  div_mono_left d (Nat.mul_le_mul ha hn)

/-- `mulDivUp` is monotone in both factors. -/
theorem mulDivUp_mono {a a' n n' : Nat} (d : Nat) (ha : a ≤ a') (hn : n ≤ n') :
    mulDivUp a n d ≤ mulDivUp a' n' d :=
  ceilDiv_mono_left d (Nat.mul_le_mul ha hn)

/-- `mulDiv` is antitone in a positive divisor. -/
theorem mulDiv_anti {d d' : Nat} (a n : Nat) (hd : 0 < d) (h : d ≤ d') :
    mulDiv a n d' ≤ mulDiv a n d :=
  div_anti_right _ hd h

/-- `mulDivUp` is antitone in a positive divisor. -/
theorem mulDivUp_anti {d d' : Nat} (a n : Nat) (hd : 0 < d) (h : d ≤ d') :
    mulDivUp a n d' ≤ mulDivUp a n d :=
  ceilDiv_anti_right _ hd h

/-- Multiplying and dividing by the same positive number is the identity, in both directions. -/
theorem mulDiv_self (a : Nat) {d : Nat} (hd : 0 < d) : mulDiv a d d = a := Nat.mul_div_cancel a hd

/-- `mulDivUp a d d = a`. -/
theorem mulDivUp_self (a : Nat) {d : Nat} (hd : 0 < d) : mulDivUp a d d = a :=
  ceilDiv_mul_cancel a hd

/-- The two roundings agree exactly when the division is exact. -/
theorem mulDivUp_eq_mulDiv_iff (a n d : Nat) (hd : 0 < d) :
    mulDivUp a n d = mulDiv a n d ↔ a * n % d = 0 :=
  ceilDiv_eq_div_iff _ _ hd

/-- A share `t ≤ s` of an amount `a`, rounded down, is at most `a`. -/
theorem mulDiv_le_of_le {t a s : Nat} (h : t ≤ s) : mulDiv t a s ≤ a := mul_div_le_of_le h

/-- A share `t ≤ s` of an amount `a`, rounded up, is at most `a`. -/
theorem mulDivUp_le_of_le {t a s : Nat} (hs : 0 < s) (h : t ≤ s) : mulDivUp t a s ≤ a := by
  apply (ceilDiv_le_iff hs).2
  rw [Nat.mul_comm a s]
  exact Nat.mul_le_mul_right a h

/-! ## Fixed-point product and quotient -/

/-- Fixed-point product rounded down: `a * b / one` (`FixedPoint.mulDown`). -/
def mulDown (one a b : Nat) : Nat := mulDiv a b one

/-- Fixed-point product rounded up (`FixedPoint.mulUp`). -/
def mulUp (one a b : Nat) : Nat := mulDivUp a b one

/-- Fixed-point quotient rounded down: `a * one / b` (`FixedPoint.divDown`). -/
def divDown (one a b : Nat) : Nat := mulDiv a one b

/-- Fixed-point quotient rounded up (`FixedPoint.divUp`). -/
def divUp (one a b : Nat) : Nat := mulDivUp a one b

/-- `mulDown` is within one unit below the exact product: `a * b / one` rounded down. -/
theorem mulDown_spec (one a b : Nat) (h : 0 < one) :
    mulDown one a b * one ≤ a * b ∧ a * b < (mulDown one a b + 1) * one :=
  mulDiv_spec a b one h

/-- `mulUp` is within one unit above the exact product. -/
theorem mulUp_spec (one a b : Nat) (h : 0 < one) :
    a * b ≤ mulUp one a b * one ∧ mulUp one a b * one < a * b + one :=
  mulDivUp_spec a b one h

/-- `mulDown one a b` never exceeds the exact product. -/
theorem mulDown_mul_le (one a b : Nat) : mulDown one a b * one ≤ a * b := div_mul_le _ _

/-- The exact product never exceeds `mulUp one a b`. -/
theorem le_mulUp_mul (one a b : Nat) (h : 0 < one) : a * b ≤ mulUp one a b * one :=
  (mulUp_spec one a b h).1

/-- `mulDown ≤ mulUp`. -/
theorem mulDown_le_mulUp (one a b : Nat) : mulDown one a b ≤ mulUp one a b :=
  mulDiv_le_mulDivUp _ _ _

/-- `mulUp ≤ mulDown + 1`. -/
theorem mulUp_le_mulDown_add_one (one a b : Nat) : mulUp one a b ≤ mulDown one a b + 1 :=
  mulDivUp_le_mulDiv_add_one _ _ _

/-- `mulDown` is commutative. -/
theorem mulDown_comm (one a b : Nat) : mulDown one a b = mulDown one b a := by
  unfold mulDown mulDiv; rw [Nat.mul_comm]

/-- `mulUp` is commutative. -/
theorem mulUp_comm (one a b : Nat) : mulUp one a b = mulUp one b a := by
  unfold mulUp mulDivUp; rw [Nat.mul_comm]

/-- `mulDown` is monotone in both arguments. -/
theorem mulDown_mono {a a' b b' : Nat} (one : Nat) (ha : a ≤ a') (hb : b ≤ b') :
    mulDown one a b ≤ mulDown one a' b' := mulDiv_mono one ha hb

/-- `mulUp` is monotone in both arguments. -/
theorem mulUp_mono {a a' b b' : Nat} (one : Nat) (ha : a ≤ a') (hb : b ≤ b') :
    mulUp one a b ≤ mulUp one a' b' := mulDivUp_mono one ha hb

/-- Multiplying by one (the scale) is the identity, rounded either way. -/
theorem mulDown_one (one a : Nat) (h : 0 < one) : mulDown one a one = a := mulDiv_self a h

/-- `mulUp one a one = a`. -/
theorem mulUp_one (one a : Nat) (h : 0 < one) : mulUp one a one = a := mulDivUp_self a h

/-- A product with zero is zero. -/
@[simp] theorem mulDown_zero (one a : Nat) : mulDown one a 0 = 0 := by simp [mulDown, mulDiv]

/-- A product with zero is zero, rounded up. -/
@[simp] theorem mulUp_zero (one a : Nat) : mulUp one a 0 = 0 := by simp [mulUp, mulDivUp]

/-- Balancer's `FixedPoint.mulUp`, `if a * b = 0 then 0 else (a * b - 1) / one + 1`, is `mulUp`. -/
theorem mulUp_eq_ite (one a b : Nat) (h : 0 < one) :
    mulUp one a b = if a * b = 0 then 0 else (a * b - 1) / one + 1 :=
  ceilDiv_eq_ite _ _ h

/-- The form `(a * b + (one - 1)) / one` is `mulUp`. -/
theorem mulUp_eq_add_pred (one a b : Nat) (h : 0 < one) :
    mulUp one a b = (a * b + (one - 1)) / one :=
  ceilDiv_eq_add_pred _ _ h

/-- `divDown` is within one unit below the exact quotient `a * one / b`. -/
theorem divDown_spec (one a b : Nat) (hb : 0 < b) :
    divDown one a b * b ≤ a * one ∧ a * one < (divDown one a b + 1) * b :=
  mulDiv_spec a one b hb

/-- `divUp` is within one unit above the exact quotient. -/
theorem divUp_spec (one a b : Nat) (hb : 0 < b) :
    a * one ≤ divUp one a b * b ∧ divUp one a b * b < a * one + b :=
  mulDivUp_spec a one b hb

/-- `divDown ≤ divUp`. -/
theorem divDown_le_divUp (one a b : Nat) : divDown one a b ≤ divUp one a b :=
  mulDiv_le_mulDivUp _ _ _

/-- `divUp ≤ divDown + 1`. -/
theorem divUp_le_divDown_add_one (one a b : Nat) : divUp one a b ≤ divDown one a b + 1 :=
  mulDivUp_le_mulDiv_add_one _ _ _

/-- `divDown` is monotone in the dividend. -/
theorem divDown_mono_left {a a' : Nat} (one b : Nat) (h : a ≤ a') :
    divDown one a b ≤ divDown one a' b := mulDiv_mono b h (Nat.le_refl _)

/-- `divUp` is monotone in the dividend. -/
theorem divUp_mono_left {a a' : Nat} (one b : Nat) (h : a ≤ a') :
    divUp one a b ≤ divUp one a' b := mulDivUp_mono b h (Nat.le_refl _)

/-- `divDown` is antitone in a positive divisor. -/
theorem divDown_anti_right {b b' : Nat} (one a : Nat) (hb : 0 < b) (h : b ≤ b') :
    divDown one a b' ≤ divDown one a b := mulDiv_anti a one hb h

/-- `divUp` is antitone in a positive divisor. -/
theorem divUp_anti_right {b b' : Nat} (one a : Nat) (hb : 0 < b) (h : b ≤ b') :
    divUp one a b' ≤ divUp one a b := mulDivUp_anti a one hb h

/-- Dividing by one (the scale) is the identity, rounded either way. -/
theorem divDown_one (one a : Nat) (h : 0 < one) : divDown one a one = a := mulDiv_self a h

/-- `divUp one a one = a`. -/
theorem divUp_one (one a : Nat) (h : 0 < one) : divUp one a one = a := mulDivUp_self a h

/-- Balancer's `FixedPoint.divUp` for a nonzero divisor,
`if a = 0 then 0 else (a * one - 1) / b + 1`, is `divUp`. -/
theorem divUp_eq_ite (one a b : Nat) (h : 0 < one) (hb : 0 < b) :
    divUp one a b = if a = 0 then 0 else (a * one - 1) / b + 1 := by
  unfold divUp mulDivUp
  rw [ceilDiv_eq_ite _ _ hb]
  by_cases ha : a = 0
  · simp [ha]
  · have : a * one ≠ 0 := Nat.mul_ne_zero ha (Nat.pos_iff_ne_zero.mp h)
    simp [ha, this]

/-! ## Round trips -/

/-- Multiplying down and then dividing down by the same factor never returns more than
the start. -/
theorem divDown_mulDown_le (one a b : Nat) : divDown one (mulDown one a b) b ≤ a := by
  unfold divDown mulDiv
  apply div_le_of_le_mul'
  exact mulDown_mul_le one a b

/-- Dividing down and then multiplying down by the same factor never returns more than the
start. -/
theorem mulDown_divDown_le (one a b : Nat) : mulDown one (divDown one a b) b ≤ a := by
  unfold mulDown mulDiv
  apply div_le_of_le_mul'
  exact div_mul_le _ _

/-- Multiplying up and then dividing up by the same positive factor never returns less than the
start. -/
theorem le_divUp_mulUp (one a b : Nat) (h : 0 < one) (hb : 0 < b) :
    a ≤ divUp one (mulUp one a b) b := by
  have h1 := le_mulUp_mul one a b h
  have h2 := (divUp_spec one (mulUp one a b) b hb).1
  rw [Nat.mul_comm a b] at h1
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans (by rw [Nat.mul_comm]; exact h1) h2) hb

/-- Dividing up and then multiplying up by the same factor never returns less than the start. -/
theorem le_mulUp_divUp (one a b : Nat) (h : 0 < one) (hb : 0 < b) :
    a ≤ mulUp one (divUp one a b) b := by
  have h1 := (divUp_spec one a b hb).1
  have h2 := le_mulUp_mul one (divUp one a b) b h
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans h1 h2) h

/-! ## Scaled conversions -/

/-- A raw amount `a` in scaled units with scaling factor `r` (a fixed-point number at scale
`one`), rounded down: Balancer's `_upscale`, `mulDown(a, r)`. -/
abbrev scaleDown (one a r : Nat) : Nat := mulDown one a r

/-- A raw amount in scaled units, rounded up: `mulUp(a, r)`. -/
abbrev scaleUp (one a r : Nat) : Nat := mulUp one a r

/-- A scaled amount back in raw units, rounded down: Balancer's `_downscaleDown`,
`divDown(a, r)`. -/
abbrev unscaleDown (one a r : Nat) : Nat := divDown one a r

/-- A scaled amount back in raw units, rounded up: Balancer's `_downscaleUp`, `divUp(a, r)`. -/
abbrev unscaleUp (one a r : Nat) : Nat := divUp one a r

/-- Converting an amount with `d` decimals to one with `e` decimals, rounded down. -/
def convertDecimalsDown (a d e : Nat) : Nat := mulDiv a (10 ^ e) (10 ^ d)

/-- Converting an amount with `d` decimals to one with `e` decimals, rounded up. -/
def convertDecimalsUp (a d e : Nat) : Nat := mulDivUp a (10 ^ e) (10 ^ d)

/-- The decimal conversions are within one unit of the exact value, on their sides. -/
theorem convertDecimals_spec (a d e : Nat) :
    convertDecimalsDown a d e * 10 ^ d ≤ a * 10 ^ e ∧
    a * 10 ^ e ≤ convertDecimalsUp a d e * 10 ^ d ∧
    convertDecimalsUp a d e ≤ convertDecimalsDown a d e + 1 := by
  have hp : 0 < 10 ^ d := Nat.pow_pos (by decide : 0 < 10)
  exact ⟨(mulDiv_spec _ _ _ hp).1, (mulDivUp_spec _ _ _ hp).1, mulDivUp_le_mulDiv_add_one _ _ _⟩

/-- Converting to more decimals is exact: `a * 10^(e - d)`. -/
theorem convertDecimalsDown_of_le (a : Nat) {d e : Nat} (h : d ≤ e) :
    convertDecimalsDown a d e = a * 10 ^ (e - d) := by
  unfold convertDecimalsDown mulDiv
  have hp : 0 < 10 ^ d := Nat.pow_pos (by decide : 0 < 10)
  have : 10 ^ e = 10 ^ (e - d) * 10 ^ d := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, ← Nat.mul_assoc, Nat.mul_div_cancel _ hp]

/-- Two fixed-point products rounded down never exceed the exact product of three factors at
scale `one * one`. -/
theorem mulDown_mulDown_le (one a b c : Nat) :
    mulDown one (mulDown one a b) c * (one * one) ≤ a * b * c := by
  have h1 := mulDown_mul_le one (mulDown one a b) c
  have h2 := mulDown_mul_le one a b
  calc mulDown one (mulDown one a b) c * (one * one)
      = (mulDown one (mulDown one a b) c * one) * one := by rw [Nat.mul_assoc]
    _ ≤ (mulDown one a b * c) * one := Nat.mul_le_mul_right one h1
    _ = (mulDown one a b * one) * c := by rw [Nat.mul_right_comm]
    _ ≤ a * b * c := Nat.mul_le_mul_right c h2

/-- Two fixed-point products rounded up never fall below the exact product of three factors at
scale `one * one`. -/
theorem le_mulUp_mulUp (one a b c : Nat) (h : 0 < one) :
    a * b * c ≤ mulUp one (mulUp one a b) c * (one * one) := by
  have h1 := le_mulUp_mul one (mulUp one a b) c h
  have h2 := le_mulUp_mul one a b h
  calc a * b * c ≤ (mulUp one a b * one) * c := Nat.mul_le_mul_right c h2
    _ = (mulUp one a b * c) * one := by rw [Nat.mul_right_comm]
    _ ≤ (mulUp one (mulUp one a b) c * one) * one := Nat.mul_le_mul_right one h1
    _ = mulUp one (mulUp one a b) c * (one * one) := by rw [Nat.mul_assoc]

end ProofForgeFin
