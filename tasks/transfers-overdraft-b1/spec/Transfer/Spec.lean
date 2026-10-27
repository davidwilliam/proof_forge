/-!
# Transfer specification (protected)

Owner-reviewed definitions for a two-party transfer between accounts with per-account
overdraft limits. Candidates may not edit this file. Every requirement is a predicate over
an implementation `step : Impl`; the locked challenge (`Transfer/Challenge.lean`) applies
each one to the definition hole `Transfer.step`.
-/

namespace Transfer

abbrev AccountId := Nat
abbrev TxId := Nat

/-- Ledger state: a fixed account universe, balances in cents, per-account overdraft
limits (a balance may go down to `-limit a`), an authorization relation
(`auth requester source`), and the IDs of transactions already applied. -/
structure State where
  accounts : List AccountId
  balance  : AccountId → Int
  limit    : AccountId → Nat
  auth     : AccountId → AccountId → Bool
  applied  : List TxId

/-- Move `amount` cents from `source` to `target`, on behalf of `requester`. -/
structure Request where
  txId      : TxId
  requester : AccountId
  source    : AccountId
  target    : AccountId
  amount    : Nat

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

/-- Every account of the universe is at or above its overdraft floor. -/
def WithinLimits (s : State) : Prop :=
  ∀ a ∈ s.accounts, -(s.limit a : Int) ≤ s.balance a

/-- The conditions under which a transfer must succeed. -/
def ValidTransfer (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  0 < r.amount ∧
  r.source ≠ r.target ∧
  r.source ∈ s.accounts ∧
  r.target ∈ s.accounts ∧
  s.auth r.requester r.source = true ∧
  -(s.limit r.source : Int) ≤ s.balance r.source - r.amount ∧
  r.txId ∉ s.applied

/-- The balance account `a` must have after a successful transfer. -/
def expectedBalance (s : State) (r : Request) (a : AccountId) : Int :=
  s.balance a - (if a = r.source then (r.amount : Int) else 0)
    + (if a = r.target then (r.amount : Int) else 0)

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid transfer succeeds. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, ValidTransfer s r → (step s r).1 = .ok

/-- REQ-INVALID-NOOP: every invalid transfer is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s r, ¬ ValidTransfer s r → step s r = (.rejected, s)

/-- REQ-AUTHORIZATION: success implies the requester is authorized for the source. -/
def AuthorizedOnly (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → s.auth r.requester r.source = true

/-- REQ-DEBIT-CREDIT: on success, the source is debited and the target credited by
exactly the amount. -/
def DebitCredit (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.balance r.source = s.balance r.source - r.amount ∧
    (step s r).2.balance r.target = s.balance r.target + r.amount

/-- REQ-EFFECTS: on success, the whole next state (other than applied IDs, see
REQ-IDEMPOTENCY) is determined: balances are exactly `expectedBalance`, and the account
universe, limits and authorization relation are unchanged. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.accounts = s.accounts ∧
    (step s r).2.limit = s.limit ∧
    (step s r).2.auth = s.auth ∧
    ∀ a, (step s r).2.balance a = expectedBalance s r a

/-- REQ-IDEMPOTENCY: on success, the applied IDs are exactly the old ones plus this one,
and resubmitting the same request is rejected without changing the state. -/
def Idempotent (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (∀ x, x ∈ (step s r).2.applied ↔ x = r.txId ∨ x ∈ s.applied) ∧
    step (step s r).2 r = (.rejected, (step s r).2)

/-- REQ-LIMIT: a state within its overdraft limits stays within them. -/
def LimitRespected (step : Impl) : Prop :=
  ∀ s r, WithinLimits s → WithinLimits (step s r).2

/-- REQ-CONSERVATION: on success, total money is unchanged. -/
def Conserves (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → total (step s r).2 = total s

end Transfer
