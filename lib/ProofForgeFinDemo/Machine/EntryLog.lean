import ProofForgeFin
/-!
# Demonstration: the cached balances of `ledgers-log-b4` with `ProofForgeFin.Machine.Refine`

The specification definitions below are copied without change from
`tasks/ledgers-log-b4/spec/EntryLog/Spec.lean`, the lemmas `receiptOf_eq_none` and
`receiptOf_isSome` from `spec/EntryLog/Lemmas.lean`, and the implementation (`appendEntry`,
`step`) from `reference/SolutionA.lean`. The task files are not imported or modified.

The implementation keeps a cached balance per account next to an append-only log; REQ-CONSISTENT
says the cache always equals the sum of the account's log entries, which the specification
recomputes from the log (`logSum`). This is the cached-field pattern of
`Machine.cache_log_invariant'`: the view of the log is a left fold, and every step either leaves
the log and the cache unchanged or appends one entry to the log and folds the same entry into the
cache. The reference proof does the fold computation inside its case analysis; here the case
analysis only says which of the two shapes each step has. The library then also gives the
statement over whole runs (`consistent_run`), which the task does not ask for.
-/

namespace ProofForgeFinDemo.Machine.EntryLogB4

open ProofForgeFin ProofForgeFin.Machine

/-! ## Copied from `spec/EntryLog/Spec.lean` -/

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
  0 ≤ s.balance e.account + e.amount

/-- REQ-CONSISTENT: if every balance equals the sum of its account's log entries, this
still holds after the step. -/
def StaysConsistent (step : Impl) : Prop :=
  ∀ s e, Consistent s → Consistent (step s e).2

/-! ## Copied from `spec/EntryLog/Lemmas.lean` -/

theorem receiptOf_eq_none {log : List Entry} {i : EntryId} (h : i ∉ ids log) :
    receiptOf log i = none := by
  induction log with
  | nil => rfl
  | cons e es ih =>
    simp only [ids, List.map_cons, List.mem_cons, not_or] at h
    simp [receiptOf, Ne.symm h.1, ih h.2]

theorem receiptOf_isSome {log : List Entry} {i : EntryId} (h : i ∈ ids log) :
    ∃ n, receiptOf log i = some n := by
  induction log with
  | nil => simp [ids] at h
  | cons e es ih =>
    by_cases he : e.id = i
    · exact ⟨0, by simp [receiptOf, he]⟩
    · have h' : i ∈ ids es := by
        simp only [ids, List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm he
        · exact h
      obtain ⟨n, hn⟩ := ih h'
      exact ⟨n + 1, by simp [receiptOf, he, hn]⟩

/-! ## Copied from `reference/SolutionA.lean`: the implementation -/

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- The state after appending a new entry. -/
def appendEntry (s : State) (e : Entry) : State :=
  { s with log := s.log ++ [e],
           balance := fun a => s.balance a + (if a = e.account then e.amount else 0) }

def step : Impl := fun s e =>
  match receiptOf s.log e.id with
  | some n => (.ok n, s)
  | none => if ValidEntry s e then (.ok s.log.length, appendEntry s e) else (.rejected, s)

/-! ## Re-proved with the library -/

/-- The cached-balance update for one entry: the fold step of the view. -/
def credit (bal : AccountId → Int) (e : Entry) : AccountId → Int :=
  fun a => bal a + (if a = e.account then e.amount else 0)

/-- The specification's view of a log is a left fold of `credit`. -/
theorem logSum_snoc (log : List Entry) (e : Entry) :
    (fun a => logSum (log ++ [e]) a) = credit (fun a => logSum log a) e := by
  funext a
  show Ledger.sumOver (log ++ [e]) _ = Ledger.sumOver log _ + _
  rw [Ledger.sumOver_append]
  by_cases h : a = e.account
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Every step either changes neither the log nor the cache, or appends one entry to the log and
credits it to the cache. -/
theorem step_shape (s : State) (e : Entry) :
    ((step s e).2.log = s.log ∧ (step s e).2.balance = s.balance) ∨
      ∃ x, (step s e).2.log = s.log ++ [x] ∧ (step s e).2.balance = credit s.balance x := by
  unfold step
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · split
    · exact Or.inr ⟨e, rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

/-- The state part of `step`. -/
def stepState (s : State) (e : Entry) : State := (step s e).2

/-- The cache equals the view of the log in every state the implementation reaches from a
consistent state. -/
theorem preserves_consistent :
    Seq.Preserves stepState (fun s : State => s.balance = fun a => logSum s.log a) :=
  cache_log_invariant' (cache := State.balance) (log := State.log)
    (view := fun l a => logSum l a) logSum_snoc step_shape

theorem consistent_iff (s : State) : Consistent s ↔ s.balance = fun a => logSum s.log a :=
  ⟨fun h => funext h, fun h a => congrFun h a⟩

theorem req_consistent : StaysConsistent step := fun s e hc =>
  (consistent_iff _).mpr (preserves_consistent s e ((consistent_iff s).mp hc))

/-- Beyond the task: the cache is consistent after every sequence of submissions, including
duplicates, invalid entries and resubmissions with other fields. -/
theorem consistent_run {s : State} (hc : Consistent s) (es : List Entry) :
    Consistent (Seq.run (fun t e => (step t e).2) s es) :=
  Seq.run_invariant (I := Consistent) (fun t e ht => req_consistent t e ht) hc es

end ProofForgeFinDemo.Machine.EntryLogB4
