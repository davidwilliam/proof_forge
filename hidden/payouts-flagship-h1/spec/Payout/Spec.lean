/-!
# Payout specification (protected)

Owner-reviewed definitions for the payout component. Candidates may not edit this file.
Every requirement is a predicate over an implementation `step : Impl`; the locked
challenge (`Payout/Challenge.lean`) applies each one to the definition hole `Payout.step`.
-/

namespace Payout

abbrev AccountId := Nat
abbrev TxId := Nat

/-- Ledger state: a fixed account universe, balances in cents, an authorization relation
(`auth requester source`), and the IDs of transactions already applied. -/
structure State where
  accounts : List AccountId
  balance  : AccountId → Int
  auth     : AccountId → AccountId → Bool
  applied  : List TxId

/-- Pay `amount` cents from `source` to `recipients`, split as evenly as possible. -/
structure Request where
  txId       : TxId
  requester  : AccountId
  source     : AccountId
  recipients : List AccountId
  amount     : Nat

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Request → Outcome × State

/-- Sum of an integer-valued function over a list. -/
def sumOver {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun a acc => f a + acc) 0

/-- Total money across the account universe. -/
def total (s : State) : Int := sumOver s.accounts s.balance

/-- The conditions under which a payout must succeed. -/
def ValidPayout (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.recipients ≠ [] ∧
  r.recipients.Nodup ∧
  r.source ∉ r.recipients ∧
  r.source ∈ s.accounts ∧
  (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧
  (r.amount : Int) ≤ s.balance r.source ∧
  r.txId ∉ s.applied

/-- Share of the recipient at position `i` of `n`: `amount / n`, plus one extra cent for
the first `amount % n` recipients in list order. -/
def fairShare (amount n i : Nat) : Nat :=
  amount / n + if i < amount % n then 1 else 0

/-- Position of `a` in a list, if present. -/
def indexOf? : List AccountId → AccountId → Option Nat
  | [], _ => none
  | x :: xs, a => if x = a then some 0 else (indexOf? xs a).map (· + 1)

/-- The amount account `a` receives from request `r`. -/
def shareOf (r : Request) (a : AccountId) : Nat :=
  match indexOf? r.recipients a with
  | some i => fairShare r.amount r.recipients.length i
  | none => 0

/-- The balance account `a` must have after a successful payout. -/
def expectedBalance (s : State) (r : Request) (a : AccountId) : Int :=
  s.balance a - (if a = r.source then (r.amount : Int) else 0) + (shareOf r a : Int)

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid payout succeeds. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, ValidPayout s r → (step s r).1 = .ok

/-- REQ-INVALID-NOOP: every invalid payout is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ ValidPayout s r → step s r = (.rejected, s)

/-- REQ-FAIR-SHARES: on success, recipient `i` receives exactly `fairShare amount n i`. -/
def FairShares (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    ∀ (i : Nat) (h : i < r.recipients.length),
      (step s r).2.balance r.recipients[i] - s.balance r.recipients[i]
        = (fairShare r.amount r.recipients.length i : Int)

/-- REQ-EFFECTS: on success, the whole next state (other than applied IDs, see
REQ-IDEMPOTENCY) is determined: balances are exactly `expectedBalance`, and the account
universe and authorization relation are unchanged. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.accounts = s.accounts ∧
    (step s r).2.auth = s.auth ∧
    ∀ a, (step s r).2.balance a = expectedBalance s r a

/-- REQ-CONSERVATION: on success, total money is unchanged. -/
def Conserves (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → total (step s r).2 = total s

/-- REQ-NONNEGATIVE: nonnegative balances stay nonnegative. -/
def NonNegative (step : Impl) : Prop :=
  ∀ s r, (∀ a ∈ s.accounts, 0 ≤ s.balance a) →
    ∀ a ∈ (step s r).2.accounts, 0 ≤ (step s r).2.balance a

/-- REQ-AUTHORIZATION: success implies the requester is authorized for the source. -/
def AuthorizedOnly (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → s.auth r.requester r.source = true

/-- REQ-IDEMPOTENCY: on success, the applied IDs are exactly the old ones plus this one,
and resubmitting the same request is rejected without changing the state. -/
def Idempotent (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied) ∧
    step (step s r).2 r = (.rejected, (step s r).2)

end Payout
