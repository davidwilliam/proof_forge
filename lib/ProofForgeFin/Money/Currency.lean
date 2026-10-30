import ProofForgeFin.Money.Round
/-!
# Currencies, minor units and exponents

Money libraries store an amount as a signed integer number of minor units of a currency whose
exponent is the number of decimal places of the minor unit: 2 for USD and EUR, 0 for JPY, 3
for KWD and BHD (ISO 4217). Ledgers often keep more places internally (4 or 6) and round when
they post or display.

* `Currency`, `Money`, `Money.add?` (addition defined only within one currency),
  `Money.ValueLe` (comparison of values across exponents by cross-multiplication).
* `rescale m e e' a`: `a` minor units at exponent `e` as minor units at exponent `e'`, rounded
  with mode `m` when `e' < e` and exact when `e ≤ e'`.

The main fact is `rescale_eq_rdiv`: rescaling is `rdiv m (a * 10 ^ e') (10 ^ e)`, the exact
value rounded once, for every pair of exponents. Every lemma of `ProofForgeFin.Money.Round`
applies through it: the result is within one unit of exact (`rescale_bounds`), monotone,
odd for the symmetric modes. Rescaling to more places and back is the identity
(`rescale_rescale_of_le`); rescaling to fewer places and back loses less than one unit of the
coarser exponent (`rescale_floor_rescale`).
-/

namespace ProofForgeFin.Money

/-- A currency: its ISO 4217 code and the exponent of its minor unit. -/
structure Currency where
  /-- The ISO 4217 code, such as `"USD"`. -/
  code : String
  /-- The number of decimal places of the minor unit. -/
  exponent : Nat
  deriving DecidableEq, Repr

/-- US dollar: two decimal places. -/
def Currency.USD : Currency := ⟨"USD", 2⟩
/-- Euro: two decimal places. -/
def Currency.EUR : Currency := ⟨"EUR", 2⟩
/-- Japanese yen: no decimal places. -/
def Currency.JPY : Currency := ⟨"JPY", 0⟩
/-- Kuwaiti dinar: three decimal places. -/
def Currency.KWD : Currency := ⟨"KWD", 3⟩

/-- An amount: a currency and a signed number of its minor units. -/
structure Money where
  /-- The currency. -/
  currency : Currency
  /-- The amount in minor units (negative for a debit or a refund). -/
  minor : Int
  deriving DecidableEq, Repr

namespace Money

/-- Addition within one currency; amounts in different currencies are not added. -/
def add? (x y : Money) : Option Money :=
  if x.currency = y.currency then some ⟨x.currency, x.minor + y.minor⟩ else none

/-- Addition succeeds exactly for amounts in the same currency. -/
theorem isSome_add?_iff (x y : Money) : (x.add? y).isSome ↔ x.currency = y.currency := by
  unfold add?; split <;> simp_all

/-- The sum of two amounts in one currency. -/
theorem add?_of_eq {x y : Money} (h : x.currency = y.currency) :
    x.add? y = some ⟨x.currency, x.minor + y.minor⟩ := by
  simp [add?, h]

/-- Addition is commutative. -/
theorem add?_comm (x y : Money) : x.add? y = y.add? x := by
  unfold add?
  by_cases h : x.currency = y.currency
  · simp only [h, ↓reduceIte, Int.add_comm]
  · simp only [h, ↓reduceIte, show ¬ y.currency = x.currency from fun e => h e.symm]

/-- Addition is associative where it is defined. -/
theorem add?_assoc (x y z : Money) :
    (x.add? y).bind (·.add? z) = (y.add? z).bind (x.add? ·) := by
  unfold add?
  by_cases h1 : x.currency = y.currency <;> by_cases h2 : y.currency = z.currency <;>
    simp [h1, h2, Int.add_assoc] <;> simp_all

/-- The value of `x` is at most the value of `y`: `x.minor / 10 ^ ex ≤ y.minor / 10 ^ ey`,
by cross-multiplication (currencies are not compared). -/
def ValueLe (x y : Money) : Prop :=
  x.minor * 10 ^ y.currency.exponent ≤ y.minor * 10 ^ x.currency.exponent

/-- Value comparison is reflexive. -/
theorem valueLe_refl (x : Money) : ValueLe x x := Int.le_refl _

/-- Value comparison is transitive. -/
theorem valueLe_trans {x y z : Money} (h1 : ValueLe x y) (h2 : ValueLe y z) : ValueLe x z := by
  unfold ValueLe at *
  have p : (0 : Int) < 10 ^ y.currency.exponent := Int.pow_pos (by decide)
  have a := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt (Int.pow_pos (by decide) :
    (0 : Int) < 10 ^ z.currency.exponent))
  have b := Int.mul_le_mul_of_nonneg_right h2 (Int.le_of_lt (Int.pow_pos (by decide) :
    (0 : Int) < 10 ^ x.currency.exponent))
  apply (Int.mul_le_mul_right p).1
  have e1 : x.minor * 10 ^ z.currency.exponent * 10 ^ y.currency.exponent =
      x.minor * 10 ^ y.currency.exponent * 10 ^ z.currency.exponent := by grind
  have e2 : y.minor * 10 ^ x.currency.exponent * 10 ^ z.currency.exponent =
      y.minor * 10 ^ z.currency.exponent * 10 ^ x.currency.exponent := by grind
  have e3 : z.minor * 10 ^ x.currency.exponent * 10 ^ y.currency.exponent =
      z.minor * 10 ^ y.currency.exponent * 10 ^ x.currency.exponent := by grind
  omega

end Money

/-- `a` minor units at exponent `e` as minor units at exponent `e'`: exact when `e ≤ e'`,
rounded with mode `m` when `e' < e`. -/
def rescale (m : RoundingMode) (e e' : Nat) (a : Int) : Int :=
  if e ≤ e' then a * 10 ^ (e' - e) else rdiv m a (10 ^ (e - e'))

/-- A positive power of ten. -/
theorem ten_pow_pos (e : Nat) : (0 : Int) < 10 ^ e := Int.pow_pos (by decide)

/-- Rescaling is the exact value `a * 10 ^ e' / 10 ^ e` rounded once with mode `m`. -/
theorem rescale_eq_rdiv (m : RoundingMode) (e e' : Nat) (a : Int) :
    rescale m e e' a = rdiv m (a * 10 ^ e') (10 ^ e) := by
  unfold rescale
  split
  · rename_i h
    have : a * 10 ^ e' = a * 10 ^ (e' - e) * 10 ^ e := by
      rw [Int.mul_assoc, ← Int.pow_add, Nat.sub_add_cancel h]
    rw [this, rdiv_mul_self m _ (ten_pow_pos e)]
  · rename_i h
    have : (10 : Int) ^ e = 10 ^ (e - e') * 10 ^ e' := by
      rw [← Int.pow_add, Nat.sub_add_cancel (by omega)]
    rw [this, rdiv_mul_mul m a (ten_pow_pos _) (ten_pow_pos _)]

/-- Rescaling to at least as many places is exact. -/
theorem rescale_of_le (m : RoundingMode) {e e' : Nat} (h : e ≤ e') (a : Int) :
    rescale m e e' a = a * 10 ^ (e' - e) := by simp [rescale, h]

/-- Rescaling to fewer places rounds `a / 10 ^ (e - e')`. -/
theorem rescale_of_lt (m : RoundingMode) {e e' : Nat} (h : e' < e) (a : Int) :
    rescale m e e' a = rdiv m a (10 ^ (e - e')) := by simp [rescale, show ¬ e ≤ e' by omega]

/-- Rescaling is within one unit of the target exponent of the exact value:
`-10^e < rescale m e e' a * 10^e - a * 10^e' < 10^e`. -/
theorem rescale_bounds (m : RoundingMode) (e e' : Nat) (a : Int) :
    -(10 : Int) ^ e < rescale m e e' a * 10 ^ e - a * 10 ^ e' ∧
      rescale m e e' a * 10 ^ e - a * 10 ^ e' < 10 ^ e := by
  rw [rescale_eq_rdiv]; exact rdiv_bounds m _ (ten_pow_pos e)

/-- Rescaling is monotone in the amount. -/
theorem rescale_mono (m : RoundingMode) (e e' : Nat) {a b : Int} (h : a ≤ b) :
    rescale m e e' a ≤ rescale m e e' b := by
  rw [rescale_eq_rdiv, rescale_eq_rdiv]
  exact rdiv_mono m (ten_pow_pos e) (Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt (ten_pow_pos e')))

/-- Rescaling commutes with negation up to mirroring the mode. -/
theorem rescale_neg (m : RoundingMode) (e e' : Nat) (a : Int) :
    rescale m e e' (-a) = -rescale m.neg e e' a := by
  rw [rescale_eq_rdiv, rescale_eq_rdiv, Int.neg_mul]
  exact rdiv_neg m _ (ten_pow_pos e)

/-- Rescaling to more places and back is the identity, whatever the modes. -/
theorem rescale_rescale_of_le (m m' : RoundingMode) {e e' : Nat} (h : e ≤ e') (a : Int) :
    rescale m' e' e (rescale m e e' a) = a := by
  rw [rescale_of_le m h]
  rcases Nat.lt_or_eq_of_le h with h | h
  · rw [rescale_of_lt m' h]; exact rdiv_mul_self m' a (ten_pow_pos _)
  · subst h; simp [rescale]

/-- Rescaling to fewer places rounded down and back never gains and loses less than one unit
of the coarser exponent: `a - 10^(e - e') < back ≤ a`. -/
theorem rescale_floor_rescale {e e' : Nat} (h : e' ≤ e) (a : Int) :
    a - 10 ^ (e - e') < rescale .floor e' e (rescale .floor e e' a) ∧
      rescale .floor e' e (rescale .floor e e' a) ≤ a := by
  rw [rescale_of_le .floor h, rescale_eq_rdiv, rdiv_floor]
  have hp : (10 : Int) ^ e = 10 ^ (e - e') * 10 ^ e' := by
    rw [← Int.pow_add, Nat.sub_add_cancel h]
  rw [hp, ediv_mul_mul a _ (ten_pow_pos e')]
  have := ediv_bounds a (ten_pow_pos (e - e'))
  omega

/-- Rescaling to fewer places in any mode and back stays within one unit of the coarser
exponent: `|back - a| < 10^(e - e')`. -/
theorem rescale_rescale_bounds (m m' : RoundingMode) {e e' : Nat} (h : e' ≤ e) (a : Int) :
    -(10 : Int) ^ (e - e') < rescale m' e' e (rescale m e e' a) - a ∧
      rescale m' e' e (rescale m e e' a) - a < 10 ^ (e - e') := by
  rw [rescale_of_le m' h, rescale_eq_rdiv]
  have hp : (10 : Int) ^ e = 10 ^ (e - e') * 10 ^ e' := by
    rw [← Int.pow_add, Nat.sub_add_cancel h]
  rw [hp, rdiv_mul_mul m a (ten_pow_pos _) (ten_pow_pos e')]
  have := rdiv_bounds m a (ten_pow_pos (e - e'))
  omega

/-- An amount converted to another exponent of the same currency, rounded with mode `m`. -/
def Money.rescaleTo (m : RoundingMode) (e' : Nat) (x : Money) : Money :=
  ⟨⟨x.currency.code, e'⟩, rescale m x.currency.exponent e' x.minor⟩

/-- Converting an amount to another exponent keeps its value within one unit of the target
exponent. -/
theorem Money.rescaleTo_bounds (m : RoundingMode) (e' : Nat) (x : Money) :
    -(10 : Int) ^ x.currency.exponent <
        (x.rescaleTo m e').minor * 10 ^ x.currency.exponent - x.minor * 10 ^ e' ∧
      (x.rescaleTo m e').minor * 10 ^ x.currency.exponent - x.minor * 10 ^ e' <
        10 ^ x.currency.exponent :=
  rescale_bounds m _ _ _

/-- 1.005 dollars kept with four places (10050) posted with two places, by banker's rounding,
is 1.00 dollars; rounded half up it is 1.01 dollars. -/
theorem rescale_example : rescale .halfEven 4 2 10050 = 100 ∧ rescale .halfUp 4 2 10050 = 101 := by
  decide

end ProofForgeFin.Money
