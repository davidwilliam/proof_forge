import ProofForgeFin.FixedPoint
import ProofForgeFin.Money.Round
/-!
# Currency conversion

An exchange at rate `rn / rd` (one unit of the source currency buys `rn / rd` units of the
target currency, in minor units) of a natural-number amount `a`:

* `fxDown rn rd a = a * rn / rd`: the amount paid out, rounded in the house's favour;
* `fxUp rn rd a = ceilDiv (a * rn) rd`: the amount charged, rounded in the house's favour.

Facts:

* Exact bounds (`fxDown_spec`, `fxUp_spec`) and monotonicity in the amount and the rate.
* The cost of a target amount (`fxCost`): the least source amount whose conversion pays out at
  least `b` is `fxUp rd rn b`, as a Galois connection (`le_fxDown_iff`).
* Round trips: converting and converting back at the inverse rate, both rounded down, never
  gains (`fxDown_fxDown_inv_le`) and loses less than `1 + rd / rn` units
  (`lt_fxDown_fxDown_inv`).
* No arbitrage: with buy and sell rates whose product is at most one, a round trip never
  gains (`fxDown_round_trip_le`), and neither does any cycle of conversions whose rates
  multiply to at most one (`fxChain_le`).
* Minor units of currencies with different exponents (`fxMinor`).
* Signed amounts: `fxInt m rn rd a = rdiv m (a * rn) rd` in any rounding mode; rounding toward
  zero pays out at most the exact magnitude for credits and debits alike
  (`natAbs_fxInt_towardZero_le`).
-/

namespace ProofForgeFin.Money

/-- `a` converted at rate `rn / rd`, rounded down: `a * rn / rd`. -/
def fxDown (rn rd a : Nat) : Nat := mulDiv a rn rd

/-- `a` converted at rate `rn / rd`, rounded up. -/
def fxUp (rn rd a : Nat) : Nat := mulDivUp a rn rd

/-- The conversion rounded down is within one unit below the exact value. -/
theorem fxDown_spec (rn : Nat) {rd : Nat} (a : Nat) (hd : 0 < rd) :
    fxDown rn rd a * rd ≤ a * rn ∧ a * rn < (fxDown rn rd a + 1) * rd :=
  mulDiv_spec a rn rd hd

/-- The conversion rounded up is within one unit above the exact value. -/
theorem fxUp_spec (rn : Nat) {rd : Nat} (a : Nat) (hd : 0 < rd) :
    a * rn ≤ fxUp rn rd a * rd ∧ fxUp rn rd a * rd < a * rn + rd :=
  mulDivUp_spec a rn rd hd

/-- Rounding down is at most rounding up, which is at most one unit more. -/
theorem fxDown_le_fxUp (rn rd a : Nat) : fxDown rn rd a ≤ fxUp rn rd a ∧ fxUp rn rd a ≤ fxDown rn rd a + 1 :=
  ⟨mulDiv_le_mulDivUp _ _ _, mulDivUp_le_mulDiv_add_one _ _ _⟩

/-- The conversion is monotone in the amount and the rate. -/
theorem fxDown_mono {rn rn' a a' : Nat} (rd : Nat) (hr : rn ≤ rn') (ha : a ≤ a') :
    fxDown rn rd a ≤ fxDown rn' rd a' := mulDiv_mono rd ha hr

/-- The conversion rounded up is monotone in the amount and the rate. -/
theorem fxUp_mono {rn rn' a a' : Nat} (rd : Nat) (hr : rn ≤ rn') (ha : a ≤ a') :
    fxUp rn rd a ≤ fxUp rn' rd a' := mulDivUp_mono rd ha hr

/-- The conversion is antitone in the rate's denominator. -/
theorem fxDown_anti {rd rd' : Nat} (rn a : Nat) (hd : 0 < rd) (h : rd ≤ rd') :
    fxDown rn rd' a ≤ fxDown rn rd a := mulDiv_anti a rn hd h

/-- The source amount needed to receive `b` at rate `rn / rd`: `ceilDiv (b * rd) rn`. -/
abbrev fxCost (rn rd b : Nat) : Nat := fxUp rd rn b

/-- The conversion of `a` pays out at least `b` exactly when `a` is at least the cost of `b`. -/
theorem le_fxDown_iff {rn rd : Nat} (a b : Nat) (hn : 0 < rn) (hd : 0 < rd) :
    b ≤ fxDown rn rd a ↔ fxCost rn rd b ≤ a := by
  unfold fxDown fxCost fxUp mulDiv mulDivUp
  rw [le_div_iff hd, ceilDiv_le_iff hn, Nat.mul_comm a rn, Nat.mul_comm]

/-- Paying the cost of `b` pays out at least `b`. -/
theorem le_fxDown_fxCost {rn rd : Nat} (b : Nat) (hn : 0 < rn) (hd : 0 < rd) :
    b ≤ fxDown rn rd (fxCost rn rd b) :=
  (le_fxDown_iff _ b hn hd).2 (Nat.le_refl _)

/-- Converting and converting back at the inverse rate, both rounded down, never gains. -/
theorem fxDown_fxDown_inv_le (rn rd a : Nat) : fxDown rd rn (fxDown rn rd a) ≤ a := by
  unfold fxDown mulDiv
  rcases Nat.eq_zero_or_pos rn with hn | hn
  · subst hn; simp
  · apply Nat.div_le_of_le_mul
    rw [Nat.mul_comm rn a]
    exact div_mul_le _ _

/-- Converting and converting back at the inverse rate, both rounded down, loses less than
`1 + rd / rn` units: `a * rn < back * rn + rn + rd`. -/
theorem lt_fxDown_fxDown_inv {rn rd : Nat} (a : Nat) (hn : 0 < rn) (hd : 0 < rd) :
    a * rn < fxDown rd rn (fxDown rn rd a) * rn + rn + rd := by
  have h1 := fxDown_spec rn a hd
  have h2 := fxDown_spec rd (fxDown rn rd a) hn
  rw [Nat.add_mul, Nat.one_mul] at h1 h2
  omega

/-- No arbitrage on a round trip: buying at rate `bn / bd` and selling back at `sn / sd`, both
rounded in the house's favour, never returns more than the start when the product of the
rates is at most one (`bn * sn ≤ bd * sd`). -/
theorem fxDown_round_trip_le {bn bd sn sd : Nat} (a : Nat) (hbd : 0 < bd) (hsd : 0 < sd)
    (h : bn * sn ≤ bd * sd) : fxDown sn sd (fxDown bn bd a) ≤ a := by
  have h1 := (fxDown_spec bn a hbd).1
  have h2 := (fxDown_spec sn (fxDown bn bd a) hsd).1
  generalize fxDown bn bd a = y at h1 h2
  generalize fxDown sn sd y = z at h2 ⊢
  have m1 : z * sd * bd ≤ y * sn * bd := Nat.mul_le_mul_right bd h2
  have m2 : y * bd * sn ≤ a * bn * sn := Nat.mul_le_mul_right sn h1
  have m3 : a * (bn * sn) ≤ a * (bd * sd) := Nat.mul_le_mul_left a h
  have : z * (bd * sd) ≤ a * (bd * sd) := by
    have e1 : z * (bd * sd) = z * sd * bd := by grind
    have e2 : y * sn * bd = y * bd * sn := by grind
    have e3 : a * bn * sn = a * (bn * sn) := by grind
    omega
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos hbd hsd)

/-- A sequence of conversions at the rates `(numerator, denominator)` of the list, each
rounded down. -/
def fxChain : List (Nat × Nat) → Nat → Nat
  | [], a => a
  | (rn, rd) :: rs, a => fxChain rs (fxDown rn rd a)

/-- A chain of conversions rounded down never exceeds the exact chain:
`result * Π denominators ≤ a * Π numerators`. -/
theorem fxChain_mul_le (rs : List (Nat × Nat)) (a : Nat) :
    fxChain rs a * (rs.map (·.2)).prod ≤ a * (rs.map (·.1)).prod := by
  induction rs generalizing a with
  | nil => simp [fxChain]
  | cons p rs ih =>
    obtain ⟨rn, rd⟩ := p
    simp only [fxChain, List.map_cons, List.prod_cons]
    have h1 := ih (fxDown rn rd a)
    have h2 : fxDown rn rd a * rd ≤ a * rn := div_mul_le _ _
    generalize fxChain rs (fxDown rn rd a) = z at h1 ⊢
    generalize (rs.map (·.2)).prod = D at h1 ⊢
    generalize (rs.map (·.1)).prod = N at h1 ⊢
    generalize fxDown rn rd a = y at h1 h2
    have m1 : z * D * rd ≤ y * N * rd := Nat.mul_le_mul_right rd h1
    have m2 : y * rd * N ≤ a * rn * N := Nat.mul_le_mul_right N h2
    have e1 : z * (rd * D) = z * D * rd := by grind
    have e2 : y * N * rd = y * rd * N := by grind
    have e3 : a * rn * N = a * (rn * N) := by grind
    omega

/-- No arbitrage over a cycle: if the rates of a chain of conversions multiply to at most one,
the chain rounded down never returns more than it started with. -/
theorem fxChain_le (rs : List (Nat × Nat)) (a : Nat) (hd : 0 < (rs.map (·.2)).prod)
    (h : (rs.map (·.1)).prod ≤ (rs.map (·.2)).prod) : fxChain rs a ≤ a := by
  have h1 := fxChain_mul_le rs a
  have h2 := Nat.mul_le_mul_left a h
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans h1 h2) hd

/-- Minor units of a currency with exponent `eFrom` converted to minor units of a currency
with exponent `eTo`, at the major-unit rate `rn / rd`, rounded down. -/
def fxMinor (rn rd eFrom eTo a : Nat) : Nat := fxDown (rn * 10 ^ eTo) (rd * 10 ^ eFrom) a

/-- The minor-unit conversion is within one target minor unit below the exact value. -/
theorem fxMinor_spec (rn : Nat) {rd : Nat} (eFrom eTo a : Nat) (hd : 0 < rd) :
    fxMinor rn rd eFrom eTo a * (rd * 10 ^ eFrom) ≤ a * (rn * 10 ^ eTo) ∧
      a * (rn * 10 ^ eTo) < (fxMinor rn rd eFrom eTo a + 1) * (rd * 10 ^ eFrom) :=
  fxDown_spec _ a (Nat.mul_pos hd (Nat.pow_pos (by decide)))

/-- A signed amount (a credit or a debit) converted at rate `rn / rd` with rounding mode `m`. -/
def fxInt (m : RoundingMode) (rn rd : Nat) (a : Int) : Int := rdiv m (a * rn) rd

/-- The signed conversion is within one unit of the exact value in every mode. -/
theorem fxInt_bounds (m : RoundingMode) (rn : Nat) {rd : Nat} (a : Int) (hd : 0 < rd) :
    -(rd : Int) < fxInt m rn rd a * rd - a * rn ∧ fxInt m rn rd a * rd - a * rn < rd :=
  rdiv_bounds m _ (by omega)

/-- Rounding toward zero pays out at most the exact magnitude, for credits and debits alike:
`|fxInt .towardZero rn rd a| * rd ≤ |a| * rn`. -/
theorem natAbs_fxInt_towardZero_le (rn : Nat) {rd : Nat} (a : Int) (hd : 0 < rd) :
    ((fxInt .towardZero rn rd a).natAbs : Int) * rd ≤ (a.natAbs : Int) * rn := by
  have := natAbs_towardZero_mul_le (a * rn) (d := rd) (by omega)
  unfold fxInt
  have e : ((a * (rn : Int)).natAbs : Int) = (a.natAbs : Int) * rn := by
    rw [Int.natAbs_mul]; push_cast; rfl
  rw [e] at this
  exact this

/-- On a natural-number amount the signed conversion rounded down is `fxDown`. -/
theorem fxInt_floor_natCast (rn rd a : Nat) : fxInt .floor rn rd a = (fxDown rn rd a : Int) := by
  unfold fxInt fxDown mulDiv
  have := rdiv_floor_natCast (a * rn) rd
  push_cast at this
  exact this

/-- 1000 cents at 0.9 (rate 9/10) buy 900 cents; at the inverse rate 10/9 these buy back 1000. -/
theorem fxDown_example : fxDown 9 10 1000 = 900 ∧ fxDown 10 9 900 = 1000 ∧ fxDown 10 9 (fxDown 9 10 1001) = 1000 := by
  decide

end ProofForgeFin.Money
