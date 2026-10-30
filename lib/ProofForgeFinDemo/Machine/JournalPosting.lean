import ProofForgeFin
/-!
# Demonstration: the requirements of `ledgers-journal-b3` with `ProofForgeFin.Machine.Journal`

The specification definitions below are copied without change from
`tasks/ledgers-journal-b3/spec/Journal/Spec.lean`, and the implementation (`adjust`,
`postLines`, `step`) from `tasks/ledgers-journal-b3/reference/SolutionA.lean`. The task files are
not imported or modified.

The reference solution proves the seven requirements with its own `postLines_eq`, `sumOver_zero`
and `sum_netOf` (an induction over the lines with the indicator-sum lemma of the task's
`Journal/Lemmas.lean`). Here the task's `sumOver`, `netOf`, `lineSum` and `postLines` are the
library's (`rfl` or a one-line induction), REQ-EFFECTS is `Journal.postLines_apply` and
REQ-TRIAL-BALANCE is `Journal.trial_balance_post`.
-/

namespace ProofForgeFinDemo.Machine.JournalB3

open ProofForgeFin ProofForgeFin.Machine

/-! ## Copied from `spec/Journal/Spec.lean` -/

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
  e.id ∉ s.posted

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

/-! ## Copied from `reference/SolutionA.lean`: the implementation -/

instance instDecidableValidEntry (s : State) (e : Entry) : Decidable (ValidEntry s e) := by
  unfold ValidEntry; infer_instance

/-- Add `amt` to account `a`. -/
def adjust (bal : AccountId → Int) (a : AccountId) (amt : Int) : AccountId → Int :=
  fun b => if b = a then bal b + amt else bal b

/-- Post every line, first to last. -/
def postLines : List Line → (AccountId → Int) → (AccountId → Int)
  | [], bal => bal
  | l :: ls, bal => postLines ls (adjust bal l.1 l.2)

def step : Impl := fun s e =>
  if ValidEntry s e then
    (.ok, { s with balance := postLines e.lines s.balance, posted := e.id :: s.posted })
  else (.rejected, s)

/-! ## Re-proved with the library -/

/-- The task's posting loop is the library's. -/
theorem postLines_eq (ls : List Line) (bal : AccountId → Int) :
    postLines ls bal = Machine.Journal.post bal ls := by
  rw [← Machine.Journal.postLines_eq_post]
  induction ls generalizing bal with
  | nil => rfl
  | cons l ls ih => exact ih _

theorem step_of_valid {s : State} {e : Entry} (h : ValidEntry s e) :
    step s e = (.ok, { s with balance := postLines e.lines s.balance, posted := e.id :: s.posted }) := by
  simp [step, h]

theorem step_of_invalid {s : State} {e : Entry} (h : ¬ ValidEntry s e) : step s e = (.rejected, s) := by
  simp [step, h]

theorem ok_valid {s : State} {e : Entry} (h : (step s e).1 = .ok) : ValidEntry s e := by
  by_cases hv : ValidEntry s e
  · exact hv
  · rw [step_of_invalid hv] at h; cases h

theorem req_valid_succeeds : ValidSucceeds step := fun s e h => by rw [step_of_valid h]

theorem req_invalid_noop : InvalidNoop step := fun _ _ h => step_of_invalid h

theorem req_known_accounts : KnownAccounts step := fun _ _ h => (ok_valid h).2.2.1

theorem req_balanced : Balanced step := fun _ _ h => (ok_valid h).2.2.2.2.1

theorem req_effects : Effects step := by
  intro s e h
  rw [step_of_valid (ok_valid h)]
  exact ⟨rfl, fun a => by rw [postLines_eq]; rfl⟩

theorem req_idempotency : Idempotent step := by
  intro s e h
  rw [step_of_valid (ok_valid h)]
  exact ⟨fun x => by simp, step_of_invalid (fun h' => h'.2.2.2.2.2 (by simp))⟩

theorem req_trial_balance : TrialBalance step := by
  intro s e h
  have hv := ok_valid h
  rw [step_of_valid hv]
  show Ledger.sumOver s.accounts (postLines e.lines s.balance) = Ledger.sumOver s.accounts s.balance
  rw [postLines_eq]
  exact Machine.Journal.trial_balance_post hv.1 _ hv.2.2.1 hv.2.2.2.2.1

end ProofForgeFinDemo.Machine.JournalB3
