/-!
# Proportional allocation specification (protected)

Owner-reviewed definitions for a money allocation routine: split an amount, in minor units
(cents), among parties in proportion to whole-number ratios. This is the operation behind
"split this bill", "allocate this payment 75/25" and similar calls in money libraries.

Candidates may not edit this file. Every requirement is a predicate over an implementation
`allocate : Impl`; the locked challenge (`Allocation/Challenge.lean`) applies each one to the
definition hole `Allocation.allocate`. Each requirement is stated twice: once for a single
input and output (the `...On` predicates, which are decidable, so a concrete counterexample
can be checked by `decide`), and once for the implementation.
-/

namespace Allocation

/-- An allocation routine. `allocate amount ratios` returns `some shares`, one share per
ratio in the same order, or `none` when the routine fails (an error, an exception or a
panic). `amount` may be negative (a refund or an income). -/
abbrev Impl := Int → List Nat → Option (List Int)

set_option linter.unusedVariables false in
/-- Inputs that every allocation routine must accept: at least one party, and ratios that do
not all equal zero. Any amount is accepted. -/
def Valid (amount : Int) (ratios : List Nat) : Prop :=
  ratios ≠ [] ∧ 0 < ratios.sum

instance (amount : Int) (ratios : List Nat) : Decidable (Valid amount ratios) := by
  unfold Valid; infer_instance

/-- How far share `x` is above the exact proportional share `amount * r / S` of a party with
ratio `r`, where `S` is the sum of the ratios, measured in units of `1 / S`:
`x * S - amount * r`. Zero means the share is exact; a value in `(-S, S)` means the share is
less than one minor unit away from exact. -/
def excess (amount : Int) (S : Nat) (x : Int) (r : Nat) : Int :=
  x * (S : Int) - amount * (r : Int)

/-! ## Requirements on one input and its output -/

/-- One share per ratio. -/
def OneShareEachOn (ratios : List Nat) (shares : List Int) : Prop :=
  shares.length = ratios.length

/-- The shares add up to exactly the amount: no minor unit is lost or created. -/
def ConservesOn (amount : Int) (shares : List Int) : Prop :=
  shares.sum = amount

/-- Every share is less than one minor unit away from its exact proportional share
`amount * r / S`. -/
def WithinOneUnitOn (amount : Int) (ratios : List Nat) (shares : List Int) : Prop :=
  ∀ i (hx : i < shares.length) (hr : i < ratios.length),
    -(ratios.sum : Int) < excess amount ratios.sum shares[i] ratios[i] ∧
    excess amount ratios.sum shares[i] ratios[i] < (ratios.sum : Int)

/-- A party whose ratio is zero receives nothing. -/
def ZeroRatioOn (ratios : List Nat) (shares : List Int) : Prop :=
  ∀ i (hx : i < shares.length) (hr : i < ratios.length), ratios[i] = 0 → shares[i] = 0

/-- Shares have the sign of the amount: a nonnegative amount gives no negative share, and a
nonpositive amount gives no positive share. -/
def SignOn (amount : Int) (shares : List Int) : Prop :=
  ∀ x ∈ shares, (0 ≤ amount → 0 ≤ x) ∧ (amount ≤ 0 → x ≤ 0)

/-- Leftover minor units go to the largest remainders (Hamilton apportionment): if share `i`
was rounded up and share `j` was rounded down, then moving one unit from `i` to `j` would
not bring the shares closer to exact. In terms of `excess`: `excess i - excess j ≤ S`. -/
def LargestRemainderOn (amount : Int) (ratios : List Nat) (shares : List Int) : Prop :=
  ∀ i (hi : i < shares.length) (hri : i < ratios.length)
    j (hj : j < shares.length) (hrj : j < ratios.length),
    0 < excess amount ratios.sum shares[i] ratios[i] →
    excess amount ratios.sum shares[j] ratios[j] < 0 →
    excess amount ratios.sum shares[i] ratios[i] - excess amount ratios.sum shares[j] ratios[j]
      ≤ (ratios.sum : Int)

instance (r : List Nat) (s : List Int) : Decidable (OneShareEachOn r s) := by
  unfold OneShareEachOn; infer_instance
instance (a : Int) (s : List Int) : Decidable (ConservesOn a s) := by
  unfold ConservesOn; infer_instance
instance (a : Int) (r : List Nat) (s : List Int) : Decidable (WithinOneUnitOn a r s) := by
  unfold WithinOneUnitOn; infer_instance
instance (r : List Nat) (s : List Int) : Decidable (ZeroRatioOn r s) := by
  unfold ZeroRatioOn; infer_instance
instance (a : Int) (s : List Int) : Decidable (SignOn a s) := by
  unfold SignOn; infer_instance
instance (a : Int) (r : List Nat) (s : List Int) : Decidable (LargestRemainderOn a r s) := by
  unfold LargestRemainderOn; infer_instance

/-! ## Requirements on the implementation -/

/-- REQ-VALID-SUCCEEDS: every valid input is allocated; the routine does not fail. -/
def ValidSucceeds (allocate : Impl) : Prop :=
  ∀ amount ratios, Valid amount ratios → (allocate amount ratios).isSome

/-- REQ-INVALID-FAILS: an input with no party, or with ratios that are all zero, is refused. -/
def InvalidFails (allocate : Impl) : Prop :=
  ∀ amount ratios, ¬ Valid amount ratios → allocate amount ratios = none

/-- REQ-ONE-SHARE-EACH: a result has exactly one share per ratio. -/
def OneShareEach (allocate : Impl) : Prop :=
  ∀ amount ratios shares, allocate amount ratios = some shares → OneShareEachOn ratios shares

/-- REQ-CONSERVATION: the shares add up to exactly the amount. -/
def Conserves (allocate : Impl) : Prop :=
  ∀ amount ratios shares, allocate amount ratios = some shares → ConservesOn amount shares

/-- REQ-WITHIN-ONE-UNIT: every share is less than one minor unit away from its exact
proportional share. -/
def WithinOneUnit (allocate : Impl) : Prop :=
  ∀ amount ratios shares, allocate amount ratios = some shares →
    WithinOneUnitOn amount ratios shares

/-- REQ-ZERO-RATIO: a party whose ratio is zero receives nothing. -/
def ZeroRatio (allocate : Impl) : Prop :=
  ∀ amount ratios shares, allocate amount ratios = some shares → ZeroRatioOn ratios shares

/-- REQ-SIGN: shares have the sign of the amount. -/
def Sign (allocate : Impl) : Prop :=
  ∀ amount ratios shares, allocate amount ratios = some shares → SignOn amount shares

/-- REQ-LARGEST-REMAINDER: leftover minor units go to the parties with the largest
remainders. -/
def LargestRemainder (allocate : Impl) : Prop :=
  ∀ amount ratios shares, allocate amount ratios = some shares →
    LargestRemainderOn amount ratios shares

end Allocation
