/-!
# Equal split specification (protected)

Owner-reviewed definitions for a money split routine: divide an amount, in minor units
(cents), into `n` shares that are as equal as possible. This is the operation behind
"split this bill three ways" in money libraries.

Candidates may not edit this file. Every requirement is a predicate over an implementation
`split : Impl`; the locked challenge (`EqualSplit/Challenge.lean`) applies each one to the
definition hole `EqualSplit.split`. Each requirement is stated twice: once for a single input
and output (the `...On` predicates, which are decidable, so a concrete counterexample can be
checked by `decide`), and once for the implementation.
-/

namespace EqualSplit

/-- A split routine. `split amount n` returns `some shares` with `n` shares, or `none` when the
routine fails (an error, an exception or a panic). `amount` may be negative (a refund). -/
abbrev Impl := Int → Nat → Option (List Int)

/-! ## Requirements on one input and its output -/

/-- One share per party. -/
def OneShareEachOn (n : Nat) (shares : List Int) : Prop :=
  shares.length = n

/-- The shares add up to exactly the amount: no minor unit is lost or created. -/
def ConservesOn (amount : Int) (shares : List Int) : Prop :=
  shares.sum = amount

/-- Every share is less than one minor unit away from the exact share `amount / n`:
`-n < x * n - amount < n`. -/
def WithinOneUnitOn (amount : Int) (n : Nat) (shares : List Int) : Prop :=
  ∀ x ∈ shares, -(n : Int) < x * (n : Int) - amount ∧ x * (n : Int) - amount < (n : Int)

/-- Shares have the sign of the amount: a nonnegative amount gives no negative share, and a
nonpositive amount gives no positive share. -/
def SignOn (amount : Int) (shares : List Int) : Prop :=
  ∀ x ∈ shares, (0 ≤ amount → 0 ≤ x) ∧ (amount ≤ 0 → x ≤ 0)

instance (n : Nat) (s : List Int) : Decidable (OneShareEachOn n s) := by
  unfold OneShareEachOn; infer_instance
instance (a : Int) (s : List Int) : Decidable (ConservesOn a s) := by
  unfold ConservesOn; infer_instance
instance (a : Int) (n : Nat) (s : List Int) : Decidable (WithinOneUnitOn a n s) := by
  unfold WithinOneUnitOn; infer_instance
instance (a : Int) (s : List Int) : Decidable (SignOn a s) := by
  unfold SignOn; infer_instance

/-! ## Requirements on the implementation -/

/-- REQ-VALID-SUCCEEDS: splitting among one or more parties succeeds; the routine does not
fail. -/
def ValidSucceeds (split : Impl) : Prop :=
  ∀ amount n, 0 < n → (split amount n).isSome

/-- REQ-INVALID-FAILS: splitting among zero parties is refused. -/
def InvalidFails (split : Impl) : Prop :=
  ∀ amount, split amount 0 = none

/-- REQ-ONE-SHARE-EACH: a result has exactly `n` shares. -/
def OneShareEach (split : Impl) : Prop :=
  ∀ amount n shares, split amount n = some shares → OneShareEachOn n shares

/-- REQ-CONSERVATION: the shares add up to exactly the amount. -/
def Conserves (split : Impl) : Prop :=
  ∀ amount n shares, split amount n = some shares → ConservesOn amount shares

/-- REQ-WITHIN-ONE-UNIT: every share is less than one minor unit away from `amount / n`. -/
def WithinOneUnit (split : Impl) : Prop :=
  ∀ amount n shares, split amount n = some shares → WithinOneUnitOn amount n shares

/-- REQ-SIGN: shares have the sign of the amount. -/
def Sign (split : Impl) : Prop :=
  ∀ amount n shares, split amount n = some shares → SignOn amount shares

end EqualSplit
