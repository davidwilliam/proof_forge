import ProofForgeFin
import ProofForgeFinDemo.Compound
/-!
# Tactic tests: `struct_simp` and `step_cases`

The first section reduces the terms step functions produce: projections of structure
instances, pairs and options, updates, `List.modify`, constructor equations and decided
conditions. The second copies goals from the error messages of the failed attempts on
`rw-compound-comp` (`results/compound-1/*/events.jsonl`) with the hypotheses they had, and gives
the proof without the automation next to each. The third splits calls of the Comptroller model
of `ProofForgeFinDemo.Compound` on their conditions and on the result of the implementation.

`compInitialIndex`, `accrueSide`, `accrualStart`, `Legacy`, `initSide` and `upgrade` are copied
without change from `realworld/tasks/rw-compound-comp/spec/CompRewards/Spec.lean`; `Side`,
`Acct`, `St`, `doubleScale` and `exec` come from `ProofForgeFinDemo.Compound`, which copies them
from the same file.
-/

namespace ProofForgeFinDemo.Tactic.StructSimp

open ProofForgeFin ProofForgeFinDemo.Compound

/-! ## Copied from `spec/CompRewards/Spec.lean` -/

/-- `compInitialIndex` (Comptroller.sol): the value a market's reward index is set to when its
rewards are initialized. -/
def compInitialIndex : Nat := 10 ^ 36

/-- A side brought up to block `now` over `total` units (`updateCompSupplyIndex`,
`updateCompBorrowIndex`): when blocks have passed, the speed is positive and units exist, the
index grows by the COMP emitted per unit, `blocks * speed * 1e36 / total` rounded down; the
side is then up to date at `now`. -/
def accrueSide (sd : Side) (now total : Nat) : Side :=
  if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then
    { sd with index := sd.index + (now - sd.block) * sd.speed * doubleScale / total, block := now }
  else
    { sd with block := now }

/-- The index from which an account accrues in a market whose index is `index`: the account's
recorded index; for an account with no recorded index, `compInitialIndex` once the market's
index has reached it (rewards there began at `compInitialIndex`), and 0 in a market whose index
is still below it (that index grew from 0). An account is never credited for rewards emitted
before rewards began in the market. -/
def accrualStart (recorded index : Nat) : Nat :=
  if recorded = 0 then (if compInitialIndex ≤ index then compInitialIndex else 0) else recorded

/-- The Comptroller's reward state for the market before Proposal 62 (Comptroller G6): one
speed `compSpeeds[market]` that applied to the supply side and to the borrow side alike,
`compSupplyState` and `compBorrowState`, the accounts, and the Comptroller's COMP.

`supplyStart` and `borrowStart` are not stored on chain. Each records the value its index
started from: `compInitialIndex` for an index initialized by `setCompSpeedInternal` when the
market's rewards began, 0 for an index that grew from 0 (G6 does not initialize an index whose
block is already set), and 0 for an index that is still 0 (the market never had rewards). -/
structure Legacy where
  blockNumber : Nat
  compSpeed : Nat
  supplyIndex : Nat
  supplyBlock : Nat
  borrowIndex : Nat
  borrowBlock : Nat
  supplyStart : Nat
  borrowStart : Nat
  reserve : Nat
  accts : List Acct
  deriving DecidableEq, Repr

/-- `_upgradeSplitCompRewards` for one side: an index that is still 0 is set to
`compInitialIndex`, up to date at the current block. -/
def initSide (now : Nat) (sd : Side) : Side :=
  if sd.index = 0 then { sd with index := compInitialIndex, block := now } else sd

/-- `_upgradeSplitCompRewards` (Proposal 62), run once by `_become`: both speeds are set to
the old `compSpeeds[market]`, and every reward index that is still 0 is initialized.
Accounts are not touched. -/
def upgrade (L : Legacy) : St :=
  { blockNumber := L.blockNumber,
    supplyState := initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩,
    borrowState := initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩,
    reserve := L.reserve,
    accts := L.accts }

/-! ## Records, updates and conditions -/

example (a b : Nat) : ((some (a, b)).getD (0, 0)).fst = a := by struct_simp

example (p : Shares.Pool) (x t : Nat) : (p.add x t).assets = p.assets + x ∧ (p.sub x t).supply = p.supply - t := by
  struct_simp

example (f : Nat → Nat) (k v : Nat) : Ledger.upd f k v k = v := by struct_simp

example (f : Nat → Nat) (k j v : Nat) (h : k ≠ j) : Ledger.upd f k v j = f j := by struct_simp [h]

example (bal : Nat → Int) (s d j : Nat) (x : Int) (hs : j ≠ s) (hd : j ≠ d) :
    Ledger.transfer bal s d x j = bal j := by
  struct_simp [hs, hd]

example (l : List Nat) (i : Nat) (f : Nat → Nat) (h : i < l.length) :
    (l.modify i f).getD i 0 = f (l.getD i 0) := by
  struct_simp [h]

example (step : Nat → Nat → Option Nat) (s a : Nat) (h : step s a = none) : Seq.skip step s a = s := by
  struct_simp [h]

example (a b c d : Nat) : (⟨a, b⟩ : Shares.Pool) = ⟨c, d⟩ ↔ a = c ∧ b = d := by struct_simp

example (s : Side) (c : Prop) [Decidable c] (i : Nat) :
    (if c then { s with index := i } else s).speed = s.speed := by
  struct_simp

/-! ## Goals copied from failed attempts on `rw-compound-comp` -/

/-- `results/compound-1/implement-1/events.jsonl`, line 653 (the lemma `ab_accrue_ge3`): after
`split` the model was left with a projection of a structure instance in each branch. -/
example (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  step_cases [accrueSide]

example (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- `results/compound-1/repair-A2-1/events.jsonl`, line 61: a structure rebuilt from its
fields. -/
example (sup : Side) (b : Nat) (h : sup.block = b) :
    { index := sup.index, block := b, speed := sup.speed } = sup := by
  struct_simp [← h]

example (sup : Side) (b : Nat) (h : sup.block = b) :
    { index := sup.index, block := b, speed := sup.speed } = sup := by
  subst h
  rfl

/-- `results/compound-1/implement-2/events.jsonl`, line 40: a decided condition and a
condition on a named constant. -/
example (index : Nat) :
    (if 0 = 0 then if compInitialIndex ≤ index then compInitialIndex else 0 else 0) ≤ index := by
  step_cases

example (index : Nat) :
    (if 0 = 0 then if compInitialIndex ≤ index then compInitialIndex else 0 else 0) ≤ index := by
  by_cases h : compInitialIndex ≤ index
  · simp only [h, ite_true]
  · simp only [h, ite_true, ite_false]
    exact Nat.zero_le _

/-- `results/compound-1/repair-A2-1/events.jsonl`, line 1196. -/
example (newI oldI : Nat) (_hOld : compInitialIndex ≤ oldI) (_hNew : compInitialIndex ≤ newI) :
    (if True then compInitialIndex else 0) ≤ if True then compInitialIndex else 0 := by
  struct_simp

/-- `results/compound-1/implement-1/events.jsonl`, line 490: a projection of a condition
between two structure instances (the upgrade of a legacy side). -/
example (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  struct_simp [upgrade, initSide]

example (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  split <;> rfl

/-- `results/compound-1/repair-A2-1/events.jsonl`, line 289: reading a modified list at another
position (`List.getElem_modify_self` does not exist). -/
example (xs : List Acct) (i j : Nat) (f : Acct → Acct) (h : i ≠ j) (hj : j < xs.length) :
    (xs.modify i f)[j]'(by simpa using hj) = xs[j] := by
  struct_simp [h]

example (xs : List Acct) (i j : Nat) (f : Acct → Acct) (h : i ≠ j) (hj : j < xs.length) :
    (xs.modify i f)[j]'(by simpa using hj) = xs[j] := by
  rw [List.getElem_modify]
  simp [h]

/-- The start of an account's accrual (`nb_as_selfX` of `results/compound-1/implement-1`). -/
example (idx : Nat) : accrualStart idx idx = idx := by
  step_cases [accrualStart, compInitialIndex]

example (idx : Nat) : accrualStart idx idx = idx := by
  unfold accrualStart
  by_cases h : idx = 0
  · subst h
    simp [compInitialIndex]
  · simp [h]

/-! ## Clean failures -/

/-- Nothing to reduce: `struct_simp` and `step_cases` fail with a message and leave the goal. -/
example (f : Nat → Nat) (x : Nat) (h : ∀ y, f y = 1) : f x = 1 := by
  fail_if_success struct_simp
  fail_if_success step_cases
  exact h x

/-! ## Splitting calls of the Comptroller model -/

/-- A mint leaves the block number as the hook left it, for every implementation whose hook
keeps it: `step_cases` splits on the account check and on the result of the hook, and the
hypothesis about the hook closes the successful branch. -/
example (impl : Impl) (s : St) (who x : Nat)
    (hhook : ∀ s', impl s (.supplyHook who) = some s' → s'.blockNumber = s.blockNumber) :
    (exec impl s (.mint who x)).blockNumber = s.blockNumber := by
  step_cases [exec, St.withAcct, hhook]

/-- Every operation other than a drip keeps the reserve when no call of the implementation
changes it. `step_cases op` leaves one goal per successful call of the implementation, with the
hypothesis `hc : impl s c = some val` that `grind` combines with the assumption on calls; the
drip, the advance of blocks and every refused call are closed by `step_cases` itself. -/
example (impl : Impl) (s : St) (op : Op)
    (hhook : ∀ t c t', impl t c = some t' → t'.reserve = t.reserve) :
    (exec impl s op).reserve = s.reserve ∨ ∃ x, op = .drip x := by
  step_cases op [exec, St.withAcct]
  all_goals grind

end ProofForgeFinDemo.Tactic.StructSimp
