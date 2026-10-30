import ProofForgeFin
/-!
# Demonstration: conservation of `transfers-batch-b3` with the library

The definitions below are copied without change from `tasks/transfers-batch-b3/spec/Batch/Spec.lean`.
The reference solution (`reference/SolutionA.lean`) proves `sum_shift` and `sum_applyLegs`, the
facts behind REQ-CONSERVATION, with the indicator-sum lemmas of the task's `Batch/Lemmas.lean`
and an induction over the legs. Here `shift` is `Ledger.transfer`, `applyLegs` is
`Ledger.applyMoves`, and the statement of `sum_applyLegs` follows from
`Ledger.sumOver_applyMoves` once each admissible leg is known to name accounts of the ledger.
-/

namespace ProofForgeFinDemo.BatchTransfer

open ProofForgeFin

/-! ## Copied from `spec/Batch/Spec.lean` -/

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

/-- Sum of an integer-valued function over a list. -/
def sumOver {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun a acc => f a + acc) 0

/-- Total money across the account universe. -/
def total (s : State) : Int := sumOver s.accounts s.balance

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

/-! ## Re-proved with the library -/

/-- A leg as a library transfer order. -/
def Leg.toMove (l : Leg) : Ledger.Move AccountId := ⟨l.source, l.target, l.amount⟩

/-- The task's `sumOver` is the library's. -/
theorem sumOver_eq {α : Type} (l : List α) (f : α → Int) : sumOver l f = Ledger.sumOver l f := rfl

/-- The task's `shift` is a library transfer. -/
theorem shift_eq (bal : AccountId → Int) (l : Leg) :
    shift bal l = Ledger.transfer bal l.source l.target l.amount := rfl

/-- The task's `applyLegs` is the library's `applyMoves`. -/
theorem applyLegs_eq (bal : AccountId → Int) (ls : List Leg) :
    applyLegs bal ls = Ledger.applyMoves bal (ls.map Leg.toMove) := by
  induction ls generalizing bal with
  | nil => rfl
  | cons l ls ih => exact ih (shift bal l)

/-- Every leg of an admissible sequence names two accounts of the ledger. -/
theorem legsOk_mem (s : State) : ∀ (ls : List Leg) (bal : AccountId → Int), LegsOk s bal ls →
    ∀ l ∈ ls, l.source ∈ s.accounts ∧ l.target ∈ s.accounts
  | [], _, _, _, hl => by simp at hl
  | l :: ls, bal, h, l', hl' => by
    rcases List.mem_cons.mp hl' with e | e
    · subst e; exact ⟨h.1.2.2.1, h.1.2.2.2.1⟩
    · exact legsOk_mem s ls (shift bal l) h.2 l' e

/-- `sum_shift` of the reference solution. -/
theorem sum_shift (s : State) (bal : AccountId → Int) (l : Leg) (hnd : s.accounts.Nodup)
    (hl : LegOk s bal l) : sumOver s.accounts (shift bal l) = sumOver s.accounts bal :=
  Ledger.sumOver_transfer hnd bal l.amount hl.2.2.1 hl.2.2.2.1

/-- `sum_applyLegs` of the reference solution: an admissible batch conserves the total. -/
theorem sum_applyLegs (s : State) (hnd : s.accounts.Nodup) :
    ∀ (ls : List Leg) (bal : AccountId → Int), LegsOk s bal ls →
      sumOver s.accounts (applyLegs bal ls) = sumOver s.accounts bal := by
  intro ls bal h
  rw [applyLegs_eq, sumOver_eq, sumOver_eq]
  apply Ledger.sumOver_applyMoves hnd
  intro m hm
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  exact legsOk_mem s ls bal h l hl

end ProofForgeFinDemo.BatchTransfer
