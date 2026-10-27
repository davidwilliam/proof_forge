/-!
# Batch transfer specification (protected)

Owner-reviewed definitions for an atomic batch of transfers applied in order, all or
nothing. Candidates may not edit this file. Every requirement is a predicate over an
implementation `step : Impl`; the locked challenge (`Batch/Challenge.lean`) applies each
one to the definition hole `Batch.step`.
-/

namespace Batch

abbrev AccountId := Nat
abbrev BatchId := Nat

/-- Ledger state: a fixed account universe, balances in cents, per-account overdraft
limits (a balance may go down to `-limit a`), and the IDs of batches already applied. -/
structure State where
  accounts : List AccountId
  balance  : AccountId → Int
  limit    : AccountId → Nat
  applied  : List BatchId

/-- One transfer of a batch: move `amount` cents from `source` to `target`. -/
structure Leg where
  source : AccountId
  target : AccountId
  amount : Nat

/-- A batch of legs, applied in list order. -/
structure Request where
  batchId : BatchId
  legs    : List Leg

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

/-- Balances after moving one leg's amount, with no validity check. -/
def shift (bal : AccountId → Int) (l : Leg) : AccountId → Int :=
  fun a => bal a - (if a = l.source then (l.amount : Int) else 0)
    + (if a = l.target then (l.amount : Int) else 0)

/-- Balances after moving every leg in order, with no validity check. -/
def applyLegs : (AccountId → Int) → List Leg → (AccountId → Int)
  | bal, [] => bal
  | bal, l :: ls => applyLegs (shift bal l) ls

/-- A leg is admissible against the running balances `bal` at the point it is applied. -/
def LegOk (s : State) (bal : AccountId → Int) (l : Leg) : Prop :=
  0 < l.amount ∧
  l.source ≠ l.target ∧
  l.source ∈ s.accounts ∧
  l.target ∈ s.accounts ∧
  -(s.limit l.source : Int) ≤ bal l.source - l.amount

/-- Every leg is admissible at the point it is applied, starting from `bal`. -/
def LegsOk (s : State) : (AccountId → Int) → List Leg → Prop
  | _, [] => True
  | bal, l :: ls => LegOk s bal l ∧ LegsOk s (shift bal l) ls

/-- The conditions under which a batch must succeed. -/
def ValidBatch (s : State) (r : Request) : Prop :=
  s.accounts.Nodup ∧
  r.legs ≠ [] ∧
  r.batchId ∉ s.applied ∧
  LegsOk s s.balance r.legs

/-! ## Requirements -/

/-- REQ-VALID-SUCCEEDS: every valid batch succeeds. -/
def ValidSucceeds (step : Impl) : Prop :=
  ∀ s r, ValidBatch s r → (step s r).1 = .ok

/-- REQ-ATOMICITY: a batch with any leg that is inadmissible at the point it is applied
(or that is otherwise invalid) is rejected and leaves the whole state unchanged. -/
def Atomicity (step : Impl) : Prop :=
  ∀ s r, ¬ ValidBatch s r → step s r = (.rejected, s)

/-- REQ-SINGLE-LEG: a successful one-leg batch debits the source and credits the target
by exactly the amount. -/
def SingleLeg (step : Impl) : Prop :=
  ∀ s r l, r.legs = [l] → (step s r).1 = .ok →
    (step s r).2.balance l.source = s.balance l.source - l.amount ∧
    (step s r).2.balance l.target = s.balance l.target + l.amount

/-- REQ-EFFECTS: on success, the whole next state (other than applied IDs, see
REQ-IDEMPOTENCY) is determined: balances are those obtained by applying the legs in
order, and the account universe and limits are unchanged. -/
def Effects (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (step s r).2.accounts = s.accounts ∧
    (step s r).2.limit = s.limit ∧
    ∀ a, (step s r).2.balance a = applyLegs s.balance r.legs a

/-- REQ-IDEMPOTENCY: on success, the applied IDs are exactly the old ones plus this
batch's, and resubmitting the same batch is rejected without changing the state. -/
def Idempotent (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok →
    (∀ x, x ∈ (step s r).2.applied ↔ x = r.batchId ∨ x ∈ s.applied) ∧
    step (step s r).2 r = (.rejected, (step s r).2)

/-- REQ-CONSERVATION: on success, total money is unchanged. -/
def Conserves (step : Impl) : Prop :=
  ∀ s r, (step s r).1 = .ok → total (step s r).2 = total s

/-- REQ-LIMIT-EVERY-STEP: from a state within its limits, the next state is within its
limits, and on success every intermediate state of the batch (after each prefix of the
legs) is within the limits too. -/
def LimitEveryStep (step : Impl) : Prop :=
  ∀ s r, WithinLimits s →
    WithinLimits (step s r).2 ∧
    ((step s r).1 = .ok → ∀ k, ∀ a ∈ s.accounts,
      -(s.limit a : Int) ≤ applyLegs s.balance (r.legs.take k) a)

end Batch
