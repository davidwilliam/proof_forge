/-!
# Idempotent entry log specification (protected)

Definitions for an append-only ledger log. Candidates may not edit this file.
Each submitted entry carries a client-chosen ID. A new valid entry is appended to the log
and its amount is added to the cached balance of its account. Resubmitting an ID that is
already in the log returns the receipt of the original entry and changes nothing.
Every requirement is a predicate over an implementation `step : Impl`; the locked
challenge (`EntryLog/Challenge.lean`) applies each one to the definition hole `EntryLog.step`.
-/

namespace EntryLog

abbrev AccountId := Nat
abbrev EntryId := Nat

/-- A ledger entry: a signed amount in cents for one account. -/
structure Entry where
  id      : EntryId
  account : AccountId
  amount  : Int
  deriving DecidableEq, Repr

/-- Ledger state: a fixed account universe, the entry log (oldest first), and the cached
balance of every account. -/
structure State where
  accounts : List AccountId
  log      : List Entry
  balance  : AccountId → Int

/-- `ok n` means the entry is recorded at position `n` of the log (its receipt). -/
inductive Outcome where
  | ok (receipt : Nat)
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Entry → Outcome × State

/-- Sum of an integer-valued function over a list. -/
def sumOver {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun a acc => f a + acc) 0

/-- The IDs of a log, in log order. -/
def ids (log : List Entry) : List EntryId := log.map (·.id)

/-- Position of the first log entry with ID `i`, if any. -/
def receiptOf : List Entry → EntryId → Option Nat
  | [], _ => none
  | e :: es, i => if e.id = i then some 0 else (receiptOf es i).map (· + 1)

/-- Sum of the amounts the log records for account `a`. -/
def logSum (log : List Entry) (a : AccountId) : Int :=
  sumOver log (fun e => if e.account = a then e.amount else 0)

/-- Every cached balance equals the sum of that account's entries in the log. -/
def Consistent (s : State) : Prop :=
  ∀ a, s.balance a = logSum s.log a

/-- The conditions under which an entry with a new ID must be accepted. -/
def ValidEntry (s : State) (e : Entry) : Prop :=
  e.account ∈ s.accounts ∧
  e.amount ≠ 0 ∧
  0 < s.balance e.account + e.amount

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: a valid entry with a new ID succeeds with the next log position as
its receipt. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s e, e.id ∉ ids s.log → ValidEntry s e → (step s e).1 = .ok s.log.length

/-- REQ-INVALID-NOOP: an invalid entry with a new ID is rejected and leaves the state
unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s e, e.id ∉ ids s.log → ¬ ValidEntry s e → step s e = (.rejected, s)

/-- REQ-DUPLICATE: an entry whose ID is already in the log returns the receipt of the
original entry and leaves the state unchanged, whatever its other fields are. -/
def DuplicateReturnsOriginal (step : Impl) : Prop :=
  ∀ s e n, receiptOf s.log e.id = some n → step s e = (.ok n, s)

/-- REQ-EFFECTS: for a valid entry with a new ID, the account universe is unchanged, the
entry is appended at the end of the log, and only its account's balance changes, by exactly
its amount. -/
def Effects (step : Impl) : Prop :=
  ∀ s e, e.id ∉ ids s.log → ValidEntry s e →
    (step s e).2.accounts = s.accounts ∧
    (step s e).2.log = s.log ++ [e] ∧
    ∀ a, (step s e).2.balance a = s.balance a + (if a = e.account then e.amount else 0)

/-- REQ-APPEND-ONLY: every step keeps the existing log as a prefix of the new log. -/
def AppendOnly (step : Impl) : Prop :=
  ∀ s e, ∃ t, (step s e).2.log = s.log ++ t

/-- REQ-UNIQUE-IDS: if the IDs in the log are distinct, they stay distinct. -/
def UniqueIds (step : Impl) : Prop :=
  ∀ s e, (ids s.log).Nodup → (ids (step s e).2.log).Nodup

/-- REQ-NONNEGATIVE: if every account balance is nonnegative, it stays nonnegative. -/
def NonNegative (step : Impl) : Prop :=
  ∀ s e, (∀ a ∈ s.accounts, 0 ≤ s.balance a) →
    ∀ a ∈ (step s e).2.accounts, 0 ≤ (step s e).2.balance a

/-- REQ-CONSISTENT: if every balance equals the sum of its account's log entries, this
still holds after the step. -/
def StaysConsistent (step : Impl) : Prop :=
  ∀ s e, Consistent s → Consistent (step s e).2

end EntryLog
