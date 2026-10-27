/-!
# Fee payout specification (protected)

Owner-reviewed definitions for the fee payout component. Candidates may not edit this file.
Every requirement is a predicate over an implementation `step : Impl`; the locked
challenge (`FeePayout/Challenge.lean`) applies each one to the definition hole `FeePayout.step`.
-/

namespace FeePayout

abbrev AccountId := Nat
abbrev TxId := Nat

/-- Ledger state: a fixed account universe, balances in cents, an authorization relation
(`auth requester source`), the IDs of transactions already applied, and the platform fee
configuration: the account that collects fees and the fee rate in basis points. -/
structure State where
  accounts   : List AccountId
  balance    : AccountId → Int
  auth       : AccountId → AccountId → Bool
  applied    : List TxId
  feeAccount : AccountId
  feeBps     : Nat

/-- Pay `amount` cents from `source`: the platform fee goes to the fee account and the
rest is split equally among `recipients`. -/
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
  s.feeBps ≤ 10000 ∧
  0 < r.amount ∧
  r.recipients ≠ [] ∧
  r.recipients.Nodup ∧
  r.source ∉ r.recipients ∧
  s.feeAccount ∉ r.recipients ∧
  s.feeAccount ≠ r.source ∧
  r.source ∈ s.accounts ∧
  s.feeAccount ∈ s.accounts ∧
  (∀ x ∈ r.recipients, x ∈ s.accounts) ∧
  s.auth r.requester r.source = true ∧
  (r.amount : Int) ≤ s.balance r.source ∧
  r.txId ∉ s.applied

/-- Platform fee on `amount` at `bps` basis points, rounded down. -/
def feeOf (bps amount : Nat) : Nat := amount * bps / 10000

/-- The part of `amount` left for the recipients after the fee. -/
def netOf (bps amount : Nat) : Nat := amount - feeOf bps amount

/-- Each of `n` recipients receives the net amount divided by `n`, rounded down. -/
def recipientShare (bps amount n : Nat) : Nat := netOf bps amount / n

/-- The fee account receives the fee plus the cents left over from the equal split. -/
def feeCredit (bps amount n : Nat) : Nat := feeOf bps amount + netOf bps amount % n

/-- The balance account `a` must have after a successful payout. -/
def expectedBalance (s : State) (r : Request) (a : AccountId) : Int :=
  s.balance a - (if a = r.source then (r.amount : Int) else 0)
    + (if a ∈ r.recipients then (recipientShare s.feeBps r.amount r.recipients.length : Int) else 0)
    + (if a = s.feeAccount then (feeCredit s.feeBps r.amount r.recipients.length : Int) else 0)

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid payout succeeds. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, ValidPayout s r → (step s r).1 = .ok

/-- REQ-INVALID-NOOP: every invalid payout is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ ValidPayout s r → step s r = (.rejected, s)

/-- REQ-AUTHORIZATION: success implies the requester is authorized for the source. -/
def AuthorizedOnly (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → s.auth r.requester r.source = true

/-- REQ-EFFECTS: on success, the whole next state (other than applied IDs, see
REQ-IDEMPOTENCY) is determined: balances are exactly `expectedBalance`, and the account
universe, authorization relation and fee configuration are unchanged. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.accounts = s.accounts ∧
    (step s r).2.auth = s.auth ∧
    (step s r).2.feeAccount = s.feeAccount ∧
    (step s r).2.feeBps = s.feeBps ∧
    ∀ a, (step s r).2.balance a = expectedBalance s r a

/-- REQ-IDEMPOTENCY: on success, the applied IDs are exactly the old ones plus this one,
and resubmitting the same request is rejected without changing the state. -/
def Idempotent (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied) ∧
    step (step s r).2 r = (.rejected, (step s r).2)

/-- REQ-NONNEGATIVE: nonnegative balances stay nonnegative. -/
def NonNegative (step : Impl) : Prop :=
  ∀ s r, (∀ a ∈ s.accounts, 0 ≤ s.balance a) →
    ∀ a ∈ (step s r).2.accounts, 0 ≤ (step s r).2.balance a

/-- REQ-EQUAL-SHARES: on success, every recipient receives exactly
`recipientShare feeBps amount n`. -/
def EqualShares (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    ∀ x ∈ r.recipients,
      (step s r).2.balance x - s.balance x
        = (recipientShare s.feeBps r.amount r.recipients.length : Int)

/-- REQ-FEE-COLLECTED: on success, the fee account receives exactly
`feeCredit feeBps amount n`. -/
def FeeCollected (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.balance s.feeAccount - s.balance s.feeAccount
      = (feeCredit s.feeBps r.amount r.recipients.length : Int)

/-- REQ-CONSERVATION: on success, total money is unchanged. -/
def Conserves (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → total (step s r).2 = total s

end FeePayout
