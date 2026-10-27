/-!
# Double-entry journal specification (protected)

Definitions for posting journal entries. Candidates may not edit this file.
A journal entry is a list of lines, each a signed amount for one account (positive for a
debit, negative for a credit). A valid entry balances to zero and touches only known
accounts; posting it adds every line to its account's balance.
Every requirement is a predicate over an implementation `step : Impl`; the locked
challenge (`Journal/Challenge.lean`) applies each one to the definition hole `Journal.step`.
-/

namespace Journal

abbrev AccountId := Nat
abbrev EntryId := Nat

/-- One journal line: an account and a signed amount in cents. -/
abbrev Line := AccountId × Int

/-- A journal entry. An account may appear on several lines. -/
structure Entry where
  id    : EntryId
  lines : List Line

/-- Ledger state: a fixed account universe, balances in cents, and the IDs of entries
already posted. -/
structure State where
  accounts : List AccountId
  balance  : AccountId → Int
  posted   : List EntryId

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Entry → Outcome × State

/-- Sum of an integer-valued function over a list. -/
def sumOver {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun a acc => f a + acc) 0

/-- Trial balance: the sum of all balances over the account universe. -/
def total (s : State) : Int := sumOver s.accounts s.balance

/-- Sum of the amounts on a list of lines. -/
def lineSum (ls : List Line) : Int := sumOver ls (·.2)

/-- Net amount the lines post to account `a`. -/
def netOf (ls : List Line) (a : AccountId) : Int :=
  sumOver ls (fun l => if l.1 = a then l.2 else 0)

/-- The conditions under which posting an entry must succeed. -/
def ValidEntry (s : State) (e : Entry) : Prop :=
  s.accounts.Nodup ∧
  e.lines ≠ [] ∧
  (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧
  (∀ l ∈ e.lines, l.2 ≠ 0) ∧
  lineSum e.lines = 0 ∧
  e.id ∉ s.posted ∧
  (e.lines.map (·.1)).Nodup

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid entry is posted successfully. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s e, ValidEntry s e → (step s e).1 = .ok

/-- REQ-INVALID-NOOP: every invalid entry is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s e, ¬ ValidEntry s e → step s e = (.rejected, s)

/-- REQ-KNOWN-ACCOUNTS: a posted entry touches only accounts of the universe. -/
def KnownAccounts (step : Impl) : Prop :=
  ∀ s e, (step s e).1 = .ok → ∀ l ∈ e.lines, l.1 ∈ s.accounts

/-- REQ-BALANCED: the lines of a posted entry sum to zero. -/
def Balanced (step : Impl) : Prop :=
  ∀ s e, (step s e).1 = .ok → lineSum e.lines = 0

/-- REQ-EFFECTS: on success the account universe is unchanged and each account's balance
changes by exactly the net amount of its lines (other than posted IDs, see
REQ-IDEMPOTENCY). -/
def Effects (step : Impl) : Prop :=
  ∀ s e, (step s e).1 = .ok →
    (step s e).2.accounts = s.accounts ∧
    ∀ a, (step s e).2.balance a = s.balance a + netOf e.lines a

/-- REQ-IDEMPOTENCY: on success the posted IDs are exactly the old ones plus this one, and
posting the same entry again is rejected without changing the state. -/
def Idempotent (step : Impl) : Prop :=
  ∀ s e, (step s e).1 = .ok →
    (∀ x, x ∈ (step s e).2.posted ↔ x = e.id ∨ x ∈ s.posted) ∧
    step (step s e).2 e = (.rejected, (step s e).2)

/-- REQ-TRIAL-BALANCE: on success the sum of all balances is unchanged. -/
def TrialBalance (step : Impl) : Prop :=
  ∀ s e, (step s e).1 = .ok → total (step s e).2 = total s

end Journal
