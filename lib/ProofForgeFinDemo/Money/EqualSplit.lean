import ProofForgeFin
/-!
# Demonstration: the six requirements of `rw-gomoney-split` for go-money's fixed `Split`

The definitions below are copied without change from
`realworld/tasks/rw-gomoney-split/spec/EqualSplit/Spec.lean`. The task files are not imported
or modified.

The implementation is a port of `Money.Split` in Rhymond/go-money 1.0.6 and later (the fix of
pull request 107): every share is the truncated quotient `amount.tdiv n`, and the
`|amount.tmod n|` leftover units are handed one each to the first shares, as `-1` for a
negative amount and `+1` otherwise. The reference solution (`reference/SolutionA.lean`,
114 lines) instead implements the Euclidean split and proves the requirements with its own sum
and sign arithmetic. Here the library identifies the go-money code with `splitSym`
(`splitSym_eq_tdiv`) and each requirement is one library theorem about `splitSym`.
-/

namespace ProofForgeFinDemo.Money.EqualSplit

/-! ## Copied from `spec/EqualSplit/Spec.lean` -/

/-- A split routine. `split amount n` returns `some shares` with `n` shares, or `none` when the
routine fails (an error, an exception or a panic). `amount` may be negative (a refund). -/
abbrev Impl := Int → Nat → Option (List Int)

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

/-! ## go-money's `Money.Split` from 1.0.6 on, and the six requirements -/

/-- Port of `Money.Split` (go-money 1.0.6 and later): the truncated quotient for every party,
and the absolute truncated remainder handed out one unit at a time to the first parties, with
the sign of the amount. `n = 0` returns an error. -/
def split : Impl := fun amount n =>
  if n = 0 then none
  else
    let q := amount.tdiv n
    let l := (amount.tmod n).natAbs
    let v : Int := if amount < 0 then -1 else 1
    some ((List.range n).map fun p => q + if p < l then v else 0)

/-- A successful call is the library's symmetric split. -/
theorem split_some {amount : Int} {n : Nat} {out : List Int} (h : split amount n = some out) :
    0 < n ∧ out = ProofForgeFin.Money.splitSym amount n := by
  unfold split at h
  split at h
  · contradiction
  · rename_i hn
    refine ⟨by omega, ?_⟩
    rw [ProofForgeFin.Money.splitSym_eq_tdiv]
    exact (Option.some.inj h).symm

/-- REQ-VALID-SUCCEEDS. -/
theorem req_valid_succeeds : ValidSucceeds split := by
  intro amount n hn; simp [split, show n ≠ 0 by omega]

/-- REQ-INVALID-FAILS. -/
theorem req_invalid_fails : InvalidFails split := by
  intro amount; simp [split]

/-- REQ-ONE-SHARE-EACH: `length_splitSym`. -/
theorem req_one_share_each : OneShareEach split := by
  intro amount n out h
  obtain ⟨_, rfl⟩ := split_some h
  exact ProofForgeFin.Money.length_splitSym amount n

/-- REQ-CONSERVATION: `sum_splitSym`. -/
theorem req_conservation : Conserves split := by
  intro amount n out h
  obtain ⟨hn, rfl⟩ := split_some h
  exact ProofForgeFin.Money.sum_splitSym amount hn

/-- REQ-WITHIN-ONE-UNIT: `splitSym_within`. -/
theorem req_within_one_unit : WithinOneUnit split := by
  intro amount n out h
  obtain ⟨hn, rfl⟩ := split_some h
  exact fun x hx => ProofForgeFin.Money.splitSym_within hn hx

/-- REQ-SIGN: `splitSym_sign`. -/
theorem req_sign : Sign split := by
  intro amount n out h
  obtain ⟨hn, rfl⟩ := split_some h
  exact fun x hx => ProofForgeFin.Money.splitSym_sign hn hx

/-- The input of the task's issue (split -101 cents four ways), where go-money 1.0.3 panicked. -/
theorem split_issue : split (-101) 4 = some [-26, -25, -25, -25] := by decide

end ProofForgeFinDemo.Money.EqualSplit
