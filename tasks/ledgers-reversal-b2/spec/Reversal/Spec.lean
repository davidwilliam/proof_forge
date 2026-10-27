/-!
# Journal with reversals: specification (protected)

Definitions for a ledger that posts balanced journal entries and reverses posted entries by
ID. Candidates may not edit this file.
A posted entry stays in the journal. Reversing it marks its ID as reversed, at most once,
and subtracts every one of its lines from the balances, so a reversal exactly undoes the
posting. Every requirement is a predicate over an implementation `step : Impl`; the locked
challenge (`Reversal/Challenge.lean`) applies each one to the definition hole `Reversal.step`.
-/

namespace Reversal

abbrev AccountId := Nat
abbrev EntryId := Nat

/-- One journal line: an account and a signed amount in cents. -/
abbrev Line := AccountId × Int

/-- A journal entry. An account may appear on several lines. -/
structure Entry where
  id    : EntryId
  lines : List Line

/-- Ledger state: a fixed account universe, opening balances, current balances, the journal
of posted entries (oldest first), and the IDs of reversed entries. -/
structure State where
  accounts : List AccountId
  opening  : AccountId → Int
  balance  : AccountId → Int
  journal  : List Entry
  reversed : List EntryId

/-- A command posts a new entry or reverses a posted entry by ID. -/
inductive Command where
  | post (e : Entry)
  | reverse (i : EntryId)

inductive Outcome where
  | ok
  | rejected
  deriving DecidableEq, Repr

/-- An implementation returns an outcome and the next state. -/
abbrev Impl := State → Command → Outcome × State

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

/-- The IDs of the journal entries, in journal order. -/
def ids (j : List Entry) : List EntryId := j.map (·.id)

/-- The first journal entry with ID `i`, if any. -/
def findEntry : List Entry → EntryId → Option Entry
  | [], _ => none
  | e :: es, i => if e.id = i then some e else findEntry es i

/-- Net amount that the entries not yet reversed post to account `a`. -/
def activeNet (s : State) (a : AccountId) : Int :=
  sumOver s.journal (fun e => if e.id ∈ s.reversed then 0 else netOf e.lines a)

/-- Structural invariant: distinct accounts, distinct journal IDs, only journal IDs are
marked reversed, and every journal entry is balanced and touches only known accounts. -/
def WellFormed (s : State) : Prop :=
  s.accounts.Nodup ∧
  (ids s.journal).Nodup ∧
  (∀ i ∈ s.reversed, i ∈ ids s.journal) ∧
  (∀ e ∈ s.journal, (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧ lineSum e.lines = 0)

/-- Every balance equals its opening balance plus the net of the entries not reversed. -/
def Consistent (s : State) : Prop :=
  ∀ a, s.balance a = s.opening a + activeNet s a

/-- The conditions under which posting an entry must succeed. -/
def ValidPost (s : State) (e : Entry) : Prop :=
  e.lines ≠ [] ∧
  (∀ l ∈ e.lines, l.1 ∈ s.accounts) ∧
  (∀ l ∈ e.lines, l.2 ≠ 0) ∧
  lineSum e.lines = 0 ∧
  e.id ∉ ids s.journal ∧
  e.id ∉ s.reversed

/-- The conditions under which reversing entry `i` must succeed. -/
def ValidReverse (s : State) (i : EntryId) : Prop :=
  i ∈ ids s.journal ∧ i ∉ s.reversed

/-- The conditions under which a command must succeed. -/
def Valid (s : State) : Command → Prop
  | .post e => ValidPost s e
  | .reverse i => ValidReverse s i

/-! ## Requirements -/

/-- REQ-POST-SUCCEEDS: every valid posting succeeds. -/
def PostSucceeds (step : Impl) : Prop :=
  ∀ s e, ValidPost s e → (step s (.post e)).1 = .ok

/-- REQ-REVERSE-SUCCEEDS: every valid reversal succeeds. -/
def ReverseSucceeds (step : Impl) : Prop :=
  ∀ s i, ValidReverse s i → (step s (.reverse i)).1 = .ok

/-- REQ-INVALID-NOOP: every invalid command is rejected and leaves the state unchanged. -/
def InvalidNoop (step : Impl) : Prop :=
  ∀ s c, ¬ Valid s c → step s c = (.rejected, s)

/-- REQ-POST-EFFECTS: a successful posting appends the entry to the journal, adds the net
of its lines to each balance, and changes nothing else. -/
def PostEffects (step : Impl) : Prop :=
  ∀ s e, (step s (.post e)).1 = .ok →
    (step s (.post e)).2.accounts = s.accounts ∧
    (step s (.post e)).2.opening = s.opening ∧
    (step s (.post e)).2.journal = s.journal ++ [e] ∧
    (step s (.post e)).2.reversed = s.reversed ∧
    ∀ a, (step s (.post e)).2.balance a = s.balance a + netOf e.lines a

/-- REQ-REVERSE-EFFECTS: a successful reversal of the entry `e` with ID `i` keeps the
journal, marks exactly `i` as newly reversed, subtracts the net of `e`'s lines from each
balance, and changes nothing else. -/
def ReverseEffects (step : Impl) : Prop :=
  ∀ s i e, (step s (.reverse i)).1 = .ok → findEntry s.journal i = some e →
    (step s (.reverse i)).2.accounts = s.accounts ∧
    (step s (.reverse i)).2.opening = s.opening ∧
    (step s (.reverse i)).2.journal = s.journal ∧
    (∀ x, x ∈ (step s (.reverse i)).2.reversed ↔ x = i ∨ x ∈ s.reversed) ∧
    ∀ a, (step s (.reverse i)).2.balance a = s.balance a - netOf e.lines a

/-- REQ-REVERSE-ONCE: after a successful reversal, reversing the same ID again is rejected
and leaves the state unchanged. -/
def ReverseOnce (step : Impl) : Prop :=
  ∀ s i, (step s (.reverse i)).1 = .ok →
    step (step s (.reverse i)).2 (.reverse i) = (.rejected, (step s (.reverse i)).2)

/-- REQ-ROUNDTRIP: right after a successful posting, reversing the posted entry succeeds and
restores every balance to its value before the posting. -/
def RoundTrip (step : Impl) : Prop :=
  ∀ s e, (step s (.post e)).1 = .ok →
    (step (step s (.post e)).2 (.reverse e.id)).1 = .ok ∧
    (step (step s (.post e)).2 (.reverse e.id)).2.balance = s.balance

/-- REQ-TRIAL-BALANCE: in a well-formed state, every successful command keeps the sum of
all balances unchanged. -/
def TrialBalance (step : Impl) : Prop :=
  ∀ s c, WellFormed s → (step s c).1 = .ok → total (step s c).2 = total s

/-- REQ-WELL-FORMED: every command keeps a well-formed state well-formed. -/
def StaysWellFormed (step : Impl) : Prop :=
  ∀ s c, WellFormed s → WellFormed (step s c).2

/-- REQ-CONSISTENT: in a well-formed state, every command keeps each balance equal to its
opening balance plus the net of the entries not reversed. -/
def StaysConsistent (step : Impl) : Prop :=
  ∀ s c, WellFormed s → Consistent s → Consistent (step s c).2

end Reversal
