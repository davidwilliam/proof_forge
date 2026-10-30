import ProofForgeFin
/-!
# Demonstration: the eight requirements of `rw-moneyphp-allocate` with the library

The definitions below are copied without change from
`realworld/tasks/rw-moneyphp-allocate/spec/Allocation/Spec.lean` (the same file as
`rw-spliit-balances/spec/Allocation/Spec.lean`). The task files are not imported or modified.

The reference solution (`reference/SolutionA.lean`, 387 lines) defines a greedy
largest-remainder loop and proves the eight requirements with its own sums, argmax lemmas, a
loop invariant and per-requirement arithmetic. Here the implementation is the library's
`largestRemainder`, and each requirement is one library theorem: the task's predicates are
the library's `ConservesOn`, `WithinOneUnitOn`, `ZeroRatioOn`, `SignOn` and
`LargestRemainderOn` up to unfolding.
-/

namespace ProofForgeFinDemo.Money.Allocation

/-! ## Copied from `spec/Allocation/Spec.lean` -/

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

/-! ## The implementation and the eight requirements -/

/-- The allocation: the library's largest-remainder method on valid inputs. -/
def allocate : Impl := fun amount ratios =>
  if Valid amount ratios then some (ProofForgeFin.Money.largestRemainder amount ratios) else none

/-- A successful call is a valid input allocated by `largestRemainder`. -/
theorem allocate_some {amount : Int} {ratios : List Nat} {out : List Int}
    (h : allocate amount ratios = some out) :
    0 < ratios.sum ∧ out = ProofForgeFin.Money.largestRemainder amount ratios := by
  unfold allocate at h
  split at h
  · rename_i hv; exact ⟨hv.2, (Option.some.inj h).symm⟩
  · contradiction

/-- REQ-VALID-SUCCEEDS. -/
theorem req_valid_succeeds : ValidSucceeds allocate := by
  intro amount ratios hv; simp [allocate, hv]

/-- REQ-INVALID-FAILS. -/
theorem req_invalid_fails : InvalidFails allocate := by
  intro amount ratios hv; simp [allocate, hv]

/-- REQ-ONE-SHARE-EACH: `length_largestRemainder`. -/
theorem req_one_share_each : OneShareEach allocate := by
  intro amount ratios out h
  obtain ⟨_, rfl⟩ := allocate_some h
  exact ProofForgeFin.Money.length_largestRemainder amount ratios

/-- REQ-CONSERVATION: `largestRemainder_conserves`. -/
theorem req_conservation : Conserves allocate := by
  intro amount ratios out h
  obtain ⟨hS, rfl⟩ := allocate_some h
  exact ProofForgeFin.Money.largestRemainder_conserves amount hS

/-- REQ-WITHIN-ONE-UNIT: `largestRemainder_within`. -/
theorem req_within_one_unit : WithinOneUnit allocate := by
  intro amount ratios out h
  obtain ⟨hS, rfl⟩ := allocate_some h
  exact ProofForgeFin.Money.largestRemainder_within amount hS

/-- REQ-ZERO-RATIO: `largestRemainder_zeroRatio`. -/
theorem req_zero_ratio : ZeroRatio allocate := by
  intro amount ratios out h
  obtain ⟨hS, rfl⟩ := allocate_some h
  exact ProofForgeFin.Money.largestRemainder_zeroRatio amount hS

/-- REQ-SIGN: `largestRemainder_sign`. -/
theorem req_sign : Sign allocate := by
  intro amount ratios out h
  obtain ⟨hS, rfl⟩ := allocate_some h
  exact ProofForgeFin.Money.largestRemainder_sign amount hS

/-- REQ-LARGEST-REMAINDER: `largestRemainder_largestRemainder`. -/
theorem req_largest_remainder : LargestRemainder allocate := by
  intro amount ratios out h
  obtain ⟨hS, rfl⟩ := allocate_some h
  exact ProofForgeFin.Money.largestRemainder_largestRemainder amount hS

/-- The input of moneyphp issue 436 is allocated `[0, 4, 1]`. -/
theorem allocate_issue_436 : allocate 5 [0, 7, 3] = some [0, 4, 1] := by decide

end ProofForgeFinDemo.Money.Allocation
