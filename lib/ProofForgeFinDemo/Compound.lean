import ProofForgeFin
/-!
# Demonstration: the sequence lemmas of `rw-compound-comp` with the library

The definitions in the first section are copied without change from
`realworld/tasks/rw-compound-comp/spec/CompRewards/Spec.lean`: the state, the operations,
`exec`, `run`, and the COMP emitted by a sequence of operations (`emitted`, which threads the
speeds set by earlier operations through `nextSpeeds`). The task files are not imported or
modified.

The reference solution (`reference/SolutionA.lean`) proves the reward bounds in two parts: per
operation, that the invariant `Inv` is preserved (`exec_inv`) and that a potential grows by at
most `doubleScale` times the COMP the operation emits (`exec_pot`); and over sequences, the
inductions `run_inv` and `run_pot` and the final division step (`div_bound`). The second part is
generic. Here it is re-proved for every implementation, every invariant and every potential from
the library: `emitted` is `Seq.accum`, `speedsAfter` is `Seq.run`, the inductions are
`Seq.run_le_scaled_accum`, and the final step is `Seq.run_bound_via_potential`.
-/

namespace ProofForgeFinDemo.Compound

open ProofForgeFin

/-! ## Copied from `spec/CompRewards/Spec.lean` -/

/-- `doubleScale` (ExponentialNoError.sol): the scale of reward index mantissas. -/
def doubleScale : Nat := 10 ^ 36

/-- Accounts are numbered by their position in the account list. -/
abbrev Account := Nat

/-- One side (supply or borrow) of the market: reward index, the block it was last brought up
to date, and the speed in COMP per block. -/
structure Side where
  index : Nat
  block : Nat
  speed : Nat
  deriving DecidableEq, Repr

/-- One account's position and reward record. -/
structure Acct where
  supply : Nat
  borrow : Nat
  supplierIndex : Nat
  borrowerIndex : Nat
  accrued : Nat
  wallet : Nat
  deriving DecidableEq, Repr

/-- An account with nothing: the record of any account number beyond the list. -/
def noAcct : Acct := ⟨0, 0, 0, 0, 0, 0⟩

/-- Comptroller state for the market: current block, both sides, the Comptroller's COMP, and
the accounts. -/
structure St where
  blockNumber : Nat
  supplyState : Side
  borrowState : Side
  reserve : Nat
  accts : List Acct
  deriving DecidableEq, Repr

/-- The record of account `who`. -/
def St.acct (s : St) (who : Account) : Acct := s.accts.getD who noAcct

/-- `s` with the record of account `who` changed by `f` (no change beyond the list). -/
def St.withAcct (s : St) (who : Account) (f : Acct → Acct) : St :=
  { s with accts := s.accts.modify who f }

/-- COMP held or accrued by every account: accrued and not yet paid, plus paid out. -/
def St.credited (s : St) : Nat := (s.accts.map fun a => a.accrued + a.wallet).sum

/-- Calls handled by the implementation.
* `supplyHook who`: the supply-side policy hooks for `who` (`mintAllowed`, `redeemAllowed`, and
  `transferAllowed` and `seizeAllowed`, which run it for both accounts).
* `borrowHook who`: the borrow-side policy hooks for `who` (`borrowAllowed`,
  `repayBorrowAllowed`).
* `claim who`: `claimComp(who, [market])`.
* `setSpeeds supplySpeed borrowSpeed`: `_setCompSpeeds([market], [supplySpeed], [borrowSpeed])`. -/
inductive Call where
  | supplyHook (who : Account)
  | borrowHook (who : Account)
  | claim (who : Account)
  | setSpeeds (supplySpeed borrowSpeed : Nat)
  deriving DecidableEq, Repr

/-- An implementation returns the next state, or `none` when the call reverts. -/
abbrev Impl := St → Call → Option St

/-- What can happen to the market. Balance changes call the implementation's hook first, as a
cToken calls the Comptroller before it moves balances, and then change the balance; an
operation that names an account beyond the list, an amount above the balance, or (for a
transfer) the same account twice is refused.
* `mint who x`, `redeem who x`: supply hook for `who`, then its cToken balance grows or shrinks.
* `transfer src dst x`: supply hooks for `src` and `dst`, then `x` cTokens move (a cToken
  transfer, or the seizure of collateral in a liquidation).
* `borrow who x`, `repay who x`: borrow hook for `who`, then its borrow grows or shrinks (a
  liquidator repaying for `who` is `repay who x`).
* `claim who`, `setSpeeds a b`: the calls of the same name.
* `advance k`: `k` blocks pass.
* `drip x`: `x` COMP is sent to the Comptroller (the Reservoir's drip, or any transfer). -/
inductive Op where
  | mint (who amount : Nat)
  | redeem (who amount : Nat)
  | transfer (src dst amount : Nat)
  | borrow (who amount : Nat)
  | repay (who amount : Nat)
  | claim (who : Nat)
  | setSpeeds (supplySpeed borrowSpeed : Nat)
  | advance (blocks : Nat)
  | drip (amount : Nat)
  deriving DecidableEq, Repr

/-- One operation. A refused operation leaves the state unchanged. -/
def exec (impl : Impl) (s : St) : Op → St
  | .mint who x =>
    if who < s.accts.length then
      match impl s (.supplyHook who) with
      | some s' => s'.withAcct who fun a => { a with supply := a.supply + x }
      | none => s
    else s
  | .redeem who x =>
    if who < s.accts.length then
      match impl s (.supplyHook who) with
      | some s' =>
        if x ≤ (s'.acct who).supply then s'.withAcct who fun a => { a with supply := a.supply - x }
        else s
      | none => s
    else s
  | .transfer src dst x =>
    if src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst then
      match impl s (.supplyHook src) with
      | some s₁ =>
        match impl s₁ (.supplyHook dst) with
        | some s₂ =>
          if x ≤ (s₂.acct src).supply then
            (s₂.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst
              fun a => { a with supply := a.supply + x }
          else s
        | none => s
      | none => s
    else s
  | .borrow who x =>
    if who < s.accts.length then
      match impl s (.borrowHook who) with
      | some s' => s'.withAcct who fun a => { a with borrow := a.borrow + x }
      | none => s
    else s
  | .repay who x =>
    if who < s.accts.length then
      match impl s (.borrowHook who) with
      | some s' =>
        if x ≤ (s'.acct who).borrow then s'.withAcct who fun a => { a with borrow := a.borrow - x }
        else s
      | none => s
    else s
  | .claim who => (impl s (.claim who)).getD s
  | .setSpeeds a b => (impl s (.setSpeeds a b)).getD s
  | .advance k => { s with blockNumber := s.blockNumber + k }
  | .drip x => { s with reserve := s.reserve + x }

/-- The state after a sequence of operations. -/
def run (impl : Impl) (s : St) : List Op → St
  | [] => s
  | op :: ops => run impl (exec impl s op) ops

/-- Supply and borrow speeds after `op`, starting from `sp`: as last set by `setSpeeds`. -/
def nextSpeeds (sp : Nat × Nat) : Op → Nat × Nat
  | .setSpeeds a b => (a, b)
  | _ => sp

/-- COMP emitted by `op` at speeds `sp`: blocks passed times the sum of both speeds. -/
def emittedBy (sp : Nat × Nat) : Op → Nat
  | .advance k => k * (sp.1 + sp.2)
  | _ => 0

/-- COMP the market emits over `ops`, starting with speeds `sp`. It is computed from the
operations alone, never from the implementation's state. -/
def emitted : Nat × Nat → List Op → Nat
  | _, [] => 0
  | sp, op :: ops => emittedBy sp op + emitted (nextSpeeds sp op) ops

/-- Speeds after `ops`, starting with speeds `sp`. -/
def speedsAfter : Nat × Nat → List Op → Nat × Nat
  | sp, [] => sp
  | sp, op :: ops => speedsAfter (nextSpeeds sp op) ops


/-! ## Re-proved with the library -/

/-- The task's `run` is the library's. -/
theorem run_eq (impl : Impl) (s : St) (ops : List Op) : run impl s ops = Seq.run (exec impl) s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- The speeds after a sequence are a library run of `nextSpeeds`. -/
theorem speedsAfter_eq (sp : Nat × Nat) (ops : List Op) :
    speedsAfter sp ops = Seq.run nextSpeeds sp ops := by
  induction ops generalizing sp with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- The COMP emitted by a sequence is a library ghost accumulator with the speeds as ghost
state. -/
theorem emitted_eq (sp : Nat × Nat) (ops : List Op) :
    emitted sp ops = Seq.accum nextSpeeds emittedBy sp ops := by
  induction ops generalizing sp with
  | nil => rfl
  | cons op ops ih => simp only [emitted, Seq.accum_cons, ih]

/-- `run_inv` of the reference solution, for every implementation and every invariant that each
operation preserves while the speeds follow `nextSpeeds`. -/
theorem run_inv (impl : Impl) (Inv : Nat × Nat → St → Prop)
    (exec_inv : ∀ sp s op, Inv sp s → Inv (nextSpeeds sp op) (exec impl s op)) (ops : List Op) :
    ∀ (sp : Nat × Nat) (s : St), Inv sp s → Inv (speedsAfter sp ops) (run impl s ops) := by
  intro sp s h
  rw [speedsAfter_eq, run_eq]
  exact (Seq.run_le_accum (next := nextSpeeds) (f := emittedBy) Inv (fun _ => 0) exec_inv
    (fun _ _ _ _ => Nat.zero_le _) h ops).2

/-- `run_pot` of the reference solution, for every implementation, invariant and potential: a
potential that each operation raises by at most `doubleScale` times the COMP it emits is raised
by a sequence by at most `doubleScale` times the COMP the sequence emits. -/
theorem run_pot (impl : Impl) (Inv : Nat × Nat → St → Prop) (P : St → Nat)
    (exec_inv : ∀ sp s op, Inv sp s → Inv (nextSpeeds sp op) (exec impl s op))
    (exec_pot : ∀ sp s op, Inv sp s → P (exec impl s op) ≤ P s + doubleScale * emittedBy sp op)
    (ops : List Op) :
    ∀ (sp : Nat × Nat) (s : St), Inv sp s → P (run impl s ops) ≤ P s + doubleScale * emitted sp ops := by
  intro sp s h
  rw [emitted_eq, run_eq]
  exact (Seq.run_le_scaled_accum Inv P doubleScale exec_inv exec_pot h ops).1

/-- The shape of REQ-REWARDS-BOUNDED as the reference solution concludes it: if the COMP
credited, at scale `doubleScale`, is covered by the potential (`credited_le_phi`), and at the
start the potential is at most `B * doubleScale + R`, then after any sequence the COMP credited
is at most `B` plus the COMP emitted plus `R / doubleScale`. -/
theorem credited_bound (impl : Impl) (Inv : Nat × Nat → St → Prop) (P : St → Nat)
    (exec_inv : ∀ sp s op, Inv sp s → Inv (nextSpeeds sp op) (exec impl s op))
    (exec_pot : ∀ sp s op, Inv sp s → P (exec impl s op) ≤ P s + doubleScale * emittedBy sp op)
    (credited_le : ∀ sp s, Inv sp s → s.credited * doubleScale ≤ P s)
    {sp : Nat × Nat} {s : St} {B R : Nat} (h0 : Inv sp s) (hstart : P s ≤ B * doubleScale + R)
    (ops : List Op) :
    (run impl s ops).credited ≤ B + emitted sp ops + R / doubleScale := by
  rw [emitted_eq, run_eq]
  exact Seq.run_bound_via_potential Inv P St.credited (by unfold doubleScale; decide) exec_inv
    exec_pot credited_le h0 hstart ops

end ProofForgeFinDemo.Compound
