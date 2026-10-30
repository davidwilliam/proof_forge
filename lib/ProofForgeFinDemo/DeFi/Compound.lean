import ProofForgeFin.DeFi
/-!
# Demonstration: the reward bounds of `rw-compound-comp` with the library

The first section copies `realworld/tasks/rw-compound-comp/spec/CompRewards/Spec.lean` without
change (its namespace body, with every doc string). The task files are not imported or modified.

The second section proves the three sequence requirements, REQ-REWARDS-BOUNDED,
REQ-ACCOUNT-BOUNDED and REQ-NO-BACKDATED-REWARDS, for every implementation that meets the five
per-call requirements REQ-CALLS-SUCCEED, REQ-SUPPLY-HOOK, REQ-BORROW-HOOK, REQ-CLAIM and
REQ-SET-SPEEDS (`bounds_of_calls`). The reference solution proves the three bounds for its own
implementation only; here they hold for any implementation whose calls have the specified effects,
which includes the reference.

The proof is the potential argument of `ProofForgeFin.DeFi.Rewards`: an account's term is its COMP
credited at scale `1e36` plus its pending COMP on each side from its effective start
(`Rewards.effStart`, the start of an index for an account with no recorded index). The library
supplies the settlement inequality (`Rewards.settle_le_self`), the condition the Proposal 62 code
broke (`Rewards.effStart_le_firstStart`), the index increment bound (`total_mul_indexDelta_le`),
the sums over accounts (`sum_le_of_index_le₂`, `Ledger.sum_map_modify_le`), the per-account
accrual inequality (`ite_accrue_le`), and the sequence bound (`Seq.run_bound_via_potential`).
-/

namespace ProofForgeFinDemo.DeFi.Compound

/-! ## Copied from `spec/CompRewards/Spec.lean` -/


/-- `doubleScale` (ExponentialNoError.sol): the scale of reward index mantissas. -/
def doubleScale : Nat := 10 ^ 36

/-- `compInitialIndex` (Comptroller.sol): the value a market's reward index is set to when its
rewards are initialized. -/
def compInitialIndex : Nat := 10 ^ 36

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

/-- `CToken.totalSupply`: the sum of all supply balances. -/
def totalSupply (s : St) : Nat := (s.accts.map Acct.supply).sum

/-- Total borrow units: the sum of all borrow balances. -/
def totalBorrows (s : St) : Nat := (s.accts.map Acct.borrow).sum

/-- COMP held or accrued by every account: accrued and not yet paid, plus paid out. -/
def St.credited (s : St) : Nat := (s.accts.map fun a => a.accrued + a.wallet).sum

/-- COMP held or accrued by account `who`. -/
def St.creditedTo (s : St) (who : Account) : Nat := (s.acct who).accrued + (s.acct who).wallet

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

/-! ## Expected effects of a call -/

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

/-- COMP credited for `units` held from index `start` to index `index`:
`mul_(units, Double(index - start))`, rounded down. -/
def creditFor (units start index : Nat) : Nat := units * (index - start) / doubleScale

/-- `s'` is `s` after the supply index was brought up to date and `who` was credited for its
supply (`updateCompSupplyIndex`, `distributeSupplierComp`). The call reverts when the side's
block lies ahead of the current block or when the account's start lies above the index (both
are `sub_` underflows), so the relation then has no `s'`. -/
def SupplyDistributed (s : St) (who : Account) (s' : St) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧
  s' = { s with
    supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }

/-- `s'` is `s` after the borrow index was brought up to date and `who` was credited for its
borrow (`updateCompBorrowIndex`, `distributeBorrowerComp`). -/
def BorrowDistributed (s : St) (who : Account) (s' : St) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ∧
  s' = { s with
    borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }

/-- `grantCompInternal(who, compAccrued[who])`: when the account has accrued a positive amount
and the Comptroller holds at least that much COMP, the whole amount is paid to the account;
otherwise nothing is paid. -/
def grant (s : St) (who : Account) : St :=
  if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
  else s

/-- `s'` is `s` after `claimComp(who, [market])`: the borrow side for `who`, then the supply
side for `who`, then the payment of everything `who` has accrued. -/
def Claimed (s : St) (who : Account) (s' : St) : Prop :=
  ∃ m₁ m₂, BorrowDistributed s who m₁ ∧ SupplyDistributed m₁ who m₂ ∧ s' = grant m₂ who

/-- `s'` is `s` after `_setCompSpeeds` (`setCompSpeedInternal`): a side whose speed changes is
first brought up to date at its old speed, so that COMP already emitted is accrued at the old
speed and the new speed applies from this block on; a side whose speed is unchanged is left as
it is. -/
def SpeedsSet (s : St) (sup bor : Nat) (s' : St) : Prop :=
  (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
  s' = { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }

/-- A state in which no call needs to revert: no side's block lies ahead of the current block
and no account's recorded index lies above the market's. -/
def Consistent (s : St) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧ s.borrowState.block ≤ s.blockNumber ∧
  ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index

/-! ## Operations and runs -/

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

/-! ## COMP emitted -/

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

/-! ## The state before the upgrade and the upgrade -/

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

/-- The facts G6 maintains: each index started from 0 or `compInitialIndex` and never
decreased; no side's block lies ahead of the current block; and an account's recorded index is
a copy of the market index at an earlier interaction, so it never exceeds the market index. -/
def Legacy.WellFormed (L : Legacy) : Prop :=
  (L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex) ∧ L.supplyStart ≤ L.supplyIndex ∧
  (L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex) ∧ L.borrowStart ≤ L.borrowIndex ∧
  L.supplyBlock ≤ L.blockNumber ∧ L.borrowBlock ≤ L.blockNumber ∧
  ∀ a ∈ L.accts, a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex

instance (L : Legacy) : Decidable L.WellFormed := by unfold Legacy.WellFormed; infer_instance

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

/-! ## COMP owed at the upgrade -/

/-- The index from which an account was owed rewards before the upgrade: its recorded index,
or for an account with no recorded index (it has not interacted since the index started),
the value the index started from. -/
def legacyStart (start recorded : Nat) : Nat := if recorded = 0 then start else recorded

/-- Rewards owed to account `a` for both sides at the legacy state, scaled by 1e36: units
held times the index gained since the account's start. -/
def Legacy.pendingScaled (L : Legacy) (a : Acct) : Nat :=
  a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) +
  a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex)

/-- COMP emitted on the supply side since its index was last brought up to date. -/
def Legacy.unindexedSupply (L : Legacy) : Nat := (L.blockNumber - L.supplyBlock) * L.compSpeed

/-- COMP emitted on the borrow side since its index was last brought up to date. -/
def Legacy.unindexedBorrow (L : Legacy) : Nat := (L.blockNumber - L.borrowBlock) * L.compSpeed

/-- COMP owed at the upgrade to all accounts together: their pending rewards, rounded down,
plus COMP emitted and not yet in either index. -/
def Legacy.owed (L : Legacy) : Nat :=
  (L.accts.map L.pendingScaled).sum / doubleScale + L.unindexedSupply + L.unindexedBorrow

/-- COMP owed at the upgrade to account `who`: its pending rewards, rounded down, plus the
COMP emitted and not yet indexed on each side where it holds a position. -/
def Legacy.owedTo (L : Legacy) (who : Account) : Nat :=
  L.pendingScaled (L.accts.getD who noAcct) / doubleScale +
  (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
  (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)

/-- Account `who` holds no position in `s`: no cTokens and no borrow. -/
def NoPosition (s : St) (who : Account) : Prop :=
  (s.acct who).supply = 0 ∧ (s.acct who).borrow = 0

/-! ## Requirements on the implementation -/

/-- REQ-CALLS-SUCCEED: in a consistent state, every call succeeds: the policy hooks for any
account, claims and speed changes never revert. -/
def CallsSucceed (comptroller : Impl) : Prop :=
  ∀ s c, Consistent s → (comptroller s c).isSome

/-- REQ-SUPPLY-HOOK: a supply hook brings the supply index up to date and credits `who` for
exactly the supply rewards since its start (`accrualStart`), rounded down; nothing else
changes. -/
def SupplyHookEffects (comptroller : Impl) : Prop :=
  ∀ s who s', comptroller s (.supplyHook who) = some s' → SupplyDistributed s who s'

/-- REQ-BORROW-HOOK: a borrow hook brings the borrow index up to date and credits `who` for
exactly the borrow rewards since its start, rounded down; nothing else changes. -/
def BorrowHookEffects (comptroller : Impl) : Prop :=
  ∀ s who s', comptroller s (.borrowHook who) = some s' → BorrowDistributed s who s'

/-- REQ-CLAIM: a claim credits `who` on both sides as the hooks do and then pays it everything
it has accrued when the Comptroller holds enough COMP. -/
def ClaimEffects (comptroller : Impl) : Prop :=
  ∀ s who s', comptroller s (.claim who) = some s' → Claimed s who s'

/-- REQ-SET-SPEEDS: a speed change accrues what was emitted at the old speed and then applies
the new speeds. -/
def SetSpeedsEffects (comptroller : Impl) : Prop :=
  ∀ s a b s', comptroller s (.setSpeeds a b) = some s' → SpeedsSet s a b s'

/-- REQ-REWARDS-BOUNDED: from the upgrade of any well-formed pre-upgrade state, after any
sequence of operations, the COMP paid out to accounts plus the COMP accrued to them never
exceeds what they held or had accrued before the upgrade, plus what they were owed at the
upgrade, plus the COMP emitted since. -/
def RewardsBounded (comptroller : Impl) : Prop :=
  ∀ (L : Legacy) (ops : List Op), L.WellFormed →
    (run comptroller (upgrade L) ops).credited ≤
      (upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops

/-- REQ-ACCOUNT-BOUNDED: the same for every single account: from the upgrade of any
well-formed pre-upgrade state, no account ever holds or has accrued more COMP than it held or
had accrued before the upgrade, plus what it was owed at the upgrade, plus the COMP emitted
since. -/
def AccountBounded (comptroller : Impl) : Prop :=
  ∀ (L : Legacy) (ops : List Op) (who : Account), L.WellFormed →
    (run comptroller (upgrade L) ops).creditedTo who ≤
      (upgrade L).creditedTo who + L.owedTo who + emitted (L.compSpeed, L.compSpeed) ops

/-- REQ-NO-BACKDATED-REWARDS: an account is never credited for blocks before it held a
position. In any state reached from the upgrade of a well-formed pre-upgrade state, if an
account holds no position, then whatever happens next it gains at most the COMP emitted from
then on. -/
def NoBackdatedRewards (comptroller : Impl) : Prop :=
  ∀ (L : Legacy) (history ops : List Op) (who : Account), L.WellFormed →
    NoPosition (run comptroller (upgrade L) history) who →
    (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who ≤
      (run comptroller (upgrade L) history).creditedTo who +
        emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops

/-! ## Re-proved with the library

Everything below is new. The bounds are proved for every implementation that meets the four
per-call effect requirements, so they hold for the reference implementation (which proves those
four) and for any other implementation that does. -/

open ProofForgeFin ProofForgeFin.DeFi.Rewards

/-- The index scale is positive. -/
theorem doubleScale_pos : 0 < doubleScale := by unfold doubleScale; decide

/-! ### The task's arithmetic is the library's -/

/-- `creditFor` is the library's `credit` at scale `doubleScale`. -/
theorem creditFor_eq (u s i : Nat) : creditFor u s i = credit doubleScale u s i := rfl

/-- `legacyStart` is the library's `effStart`. -/
theorem legacyStart_eq (g r : Nat) : legacyStart g r = effStart g r := rfl

/-- `accrualStart` is the library's `firstStart` with `init = compInitialIndex`. -/
theorem accrualStart_eq (r i : Nat) : accrualStart r i = firstStart compInitialIndex r i := rfl

/-- The task's `run` is the library's. -/
theorem run_eq (impl : Impl) (s : St) (ops : List Op) :
    run impl s ops = Seq.run (exec impl) s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- The speeds after a sequence are a library run of `nextSpeeds`. -/
theorem speedsAfter_eq (sp : Nat × Nat) (ops : List Op) :
    speedsAfter sp ops = Seq.run nextSpeeds sp ops := by
  induction ops generalizing sp with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- The COMP emitted is a library ghost accumulator with the speeds as ghost state. -/
theorem emitted_eq (sp : Nat × Nat) (ops : List Op) :
    emitted sp ops = Seq.accum nextSpeeds emittedBy sp ops := by
  induction ops generalizing sp with
  | nil => rfl
  | cons op ops ih => simp only [emitted, Seq.accum_cons, ih]

/-! ### One side brought up to date -/

/-- The side is up to date at the current block. -/
theorem accrueSide_block (sd : Side) (now T : Nat) : (accrueSide sd now T).block = now := by
  unfold accrueSide; split <;> rfl

/-- The speed is unchanged. -/
theorem accrueSide_speed (sd : Side) (now T : Nat) : (accrueSide sd now T).speed = sd.speed := by
  unfold accrueSide; split <;> rfl

/-- The index grows by an increment that the COMP emitted since the side's block covers. -/
theorem accrueSide_index (sd : Side) (now T : Nat) :
    sd.index ≤ (accrueSide sd now T).index ∧
      T * ((accrueSide sd now T).index - sd.index) ≤ doubleScale * ((now - sd.block) * sd.speed) := by
  unfold accrueSide
  split
  · dsimp only
    refine ⟨Nat.le_add_right _ _, ?_⟩
    rw [Nat.add_sub_cancel_left, Nat.mul_comm doubleScale]
    exact total_mul_indexDelta_le doubleScale _ T
  · simp

/-- A side already up to date is unchanged. -/
theorem accrueSide_current {sd : Side} {now : Nat} (T : Nat) (h : sd.block = now) :
    accrueSide sd now T = sd := by
  subst h; unfold accrueSide; simp

/-! ### The potentials

`gs` and `gb` are the values the supply and borrow indices started from. An account's term is the
COMP credited to it, at scale `doubleScale`, plus the COMP pending on each side from its effective
start (`effStart`); the global potential `Phi` adds the scaled COMP emitted and not yet in either
index, and the potential `Psi` of one account adds it for each side on which the account holds a
position. -/

/-- The potential term of an account at indices `iS` and `iB`. -/
def term (gs gb iS iB : Nat) (a : Acct) : Nat :=
  (a.accrued + a.wallet) * doubleScale + pending a.supply (effStart gs a.supplierIndex) iS +
    pending a.borrow (effStart gb a.borrowerIndex) iB

/-- COMP emitted on the supply side since its index was last brought up to date. -/
def unS (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- COMP emitted on the borrow side since its index was last brought up to date. -/
def unB (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- The global potential. -/
def Phi (gs gb : Nat) (s : St) : Nat :=
  (s.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum +
    doubleScale * unS s + doubleScale * unB s

/-- The potential of account `w`. -/
def Psi (gs gb : Nat) (w : Account) (s : St) : Nat :=
  term gs gb s.supplyState.index s.borrowState.index (s.acct w) +
    doubleScale * (if 0 < (s.acct w).supply then unS s else 0) +
    doubleScale * (if 0 < (s.acct w).borrow then unB s else 0)

/-! ### Terms of one account -/

/-- Raising the indices raises a term by at most the units times the increments. -/
theorem term_index_le (gs gb : Nat) {iS iS' iB iB' : Nat} (hS : iS ≤ iS') (hB : iB ≤ iB')
    (a : Acct) :
    term gs gb iS' iB' a ≤ term gs gb iS iB a + a.supply * (iS' - iS) + a.borrow * (iB' - iB) := by
  have h1 := pending_le_add a.supply (effStart gs a.supplierIndex) hS
  have h2 := pending_le_add a.borrow (effStart gb a.borrowerIndex) hB
  unfold term; omega

/-- Settling the supply side of an account from a start at or after its effective start does not
raise its term, whatever its supply afterwards. -/
theorem term_settleS {gs gb iS iB q : Nat} {a b : Acct} (hq : effStart gs a.supplierIndex ≤ q)
    (hk : b.supplierIndex = iS) (hb : b.borrow = a.borrow) (hbi : b.borrowerIndex = a.borrowerIndex)
    (hc : b.accrued + b.wallet = a.accrued + a.wallet + credit doubleScale a.supply q iS) :
    term gs gb iS iB b ≤ term gs gb iS iB a := by
  have := settle_le_self hc hq
  unfold term; rw [hk, pending_effStart_self, hb, hbi]; omega

/-- Settling the borrow side, likewise. -/
theorem term_settleB {gs gb iS iB q : Nat} {a b : Acct} (hq : effStart gb a.borrowerIndex ≤ q)
    (hk : b.borrowerIndex = iB) (hb : b.supply = a.supply) (hbi : b.supplierIndex = a.supplierIndex)
    (hc : b.accrued + b.wallet = a.accrued + a.wallet + credit doubleScale a.borrow q iB) :
    term gs gb iS iB b ≤ term gs gb iS iB a := by
  have := settle_le_self hc hq
  unfold term; rw [hk, pending_effStart_self, hb, hbi]; omega

/-- A supply balance change of an account settled at the supply index keeps its term. -/
theorem term_balS {gs gb iS iB : Nat} {a : Acct} (x : Nat) (hk : a.supplierIndex = iS) :
    term gs gb iS iB { a with supply := x } = term gs gb iS iB a := by
  unfold term; dsimp only; rw [hk, pending_effStart_self, pending_effStart_self]

/-- A borrow balance change of an account settled at the borrow index keeps its term. -/
theorem term_balB {gs gb iS iB : Nat} {a : Acct} (x : Nat) (hk : a.borrowerIndex = iB) :
    term gs gb iS iB { a with borrow := x } = term gs gb iS iB a := by
  unfold term; dsimp only; rw [hk, pending_effStart_self, pending_effStart_self]

/-- A paid claim keeps the term. -/
theorem term_grant (gs gb iS iB : Nat) (a : Acct) :
    term gs gb iS iB { a with accrued := 0, wallet := a.wallet + a.accrued } = term gs gb iS iB a := by
  unfold term; dsimp only; rw [Nat.zero_add, Nat.add_comm a.wallet]

/-! ### The next states the effect requirements fix -/

/-- The supply side brought up to date. -/
def sideS (s : St) : Side := accrueSide s.supplyState s.blockNumber (totalSupply s)

/-- The borrow side brought up to date. -/
def sideB (s : St) : Side := accrueSide s.borrowState s.blockNumber (totalBorrows s)

/-- An account credited for its supply up to index `i`. -/
def distS (i : Nat) (a : Acct) : Acct :=
  { a with supplierIndex := i,
           accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex i) i }

/-- An account credited for its borrow up to index `i`. -/
def distB (i : Nat) (a : Acct) : Acct :=
  { a with borrowerIndex := i,
           accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex i) i }

/-- The state `SupplyDistributed` fixes. -/
def supplyNext (s : St) (who : Account) : St :=
  { s with supplyState := sideS s, accts := s.accts.modify who (distS (sideS s).index) }

/-- The state `BorrowDistributed` fixes. -/
def borrowNext (s : St) (who : Account) : St :=
  { s with borrowState := sideB s, accts := s.accts.modify who (distB (sideB s).index) }

/-- The supply side after a supply hook. -/
@[simp] theorem supplyNext_supplyState (s : St) (who : Account) :
    (supplyNext s who).supplyState = sideS s := rfl

/-- The borrow side after a borrow hook. -/
@[simp] theorem borrowNext_borrowState (s : St) (who : Account) :
    (borrowNext s who).borrowState = sideB s := rfl

/-- The state `SpeedsSet` fixes. -/
def speedsNext (s : St) (sup bor : Nat) : St :=
  { s with
    supplyState := if s.supplyState.speed = sup then s.supplyState else { sideS s with speed := sup },
    borrowState := if s.borrowState.speed = bor then s.borrowState else { sideB s with speed := bor } }

section Effects

variable {impl : Impl}

/-- REQ-SUPPLY-HOOK fixes the state after a successful supply hook. -/
theorem supply_eq (h : SupplyHookEffects impl) {s s' : St} {who : Account}
    (e : impl s (.supplyHook who) = some s') : s' = supplyNext s who := (h s who s' e).2.2

/-- REQ-BORROW-HOOK fixes the state after a successful borrow hook. -/
theorem borrow_eq (h : BorrowHookEffects impl) {s s' : St} {who : Account}
    (e : impl s (.borrowHook who) = some s') : s' = borrowNext s who := (h s who s' e).2.2

/-- REQ-CLAIM fixes the state after a successful claim. -/
theorem claim_eq (h : ClaimEffects impl) {s s' : St} {who : Account}
    (e : impl s (.claim who) = some s') : s' = grant (supplyNext (borrowNext s who) who) who := by
  obtain ⟨_, _, ⟨-, -, rfl⟩, ⟨-, -, rfl⟩, rfl⟩ := h s who s' e; rfl

/-- REQ-SET-SPEEDS fixes the state after a successful speed change. -/
theorem speeds_eq (h : SetSpeedsEffects impl) {s s' : St} {a b : Nat}
    (e : impl s (.setSpeeds a b) = some s') : s' = speedsNext s a b := (h s a b s' e).2.2

end Effects

/-! ### Facts about the next states -/

/-- Reading an account after a change of one account. -/
theorem acct_withAcct (s : St) (w v : Account) (f : Acct → Acct) :
    (s.withAcct w f).acct v = if w = v ∧ v < s.accts.length then f (s.acct v) else s.acct v :=
  Ledger.getD_modify _ _ _ _ _

/-- Reading an account after a supply hook. -/
theorem acct_supplyNext (s : St) (who w : Account) :
    (supplyNext s who).acct w =
      if who = w ∧ w < s.accts.length then distS (sideS s).index (s.acct w) else s.acct w :=
  Ledger.getD_modify _ _ _ _ _

/-- Reading an account after a borrow hook. -/
theorem acct_borrowNext (s : St) (who w : Account) :
    (borrowNext s who).acct w =
      if who = w ∧ w < s.accts.length then distB (sideB s).index (s.acct w) else s.acct w :=
  Ledger.getD_modify _ _ _ _ _

/-- An account holds at most the total supply. -/
theorem supply_le_total (s : St) (w : Account) : (s.acct w).supply ≤ totalSupply s :=
  Ledger.getD_le_sum_map _ _ _ _ rfl

/-- An account holds at most the total borrows. -/
theorem borrow_le_total (s : St) (w : Account) : (s.acct w).borrow ≤ totalBorrows s :=
  Ledger.getD_le_sum_map _ _ _ _ rfl

/-- After a supply hook, nothing is unindexed on the supply side. -/
theorem unS_supplyNext (s : St) (who : Account) : unS (supplyNext s who) = 0 := by
  simp [unS, supplyNext, sideS, accrueSide_block]

/-- After a borrow hook, nothing is unindexed on the borrow side. -/
theorem unB_borrowNext (s : St) (who : Account) : unB (borrowNext s who) = 0 := by
  simp [unB, borrowNext, sideB, accrueSide_block]

/-- After a supply hook, every account settled at the supply index before stays settled, and the
hooked account is settled. -/
theorem supplyNext_settled (s : St) (who w : Account)
    (h : (who = w ∧ w < s.accts.length) ∨
      ((s.acct w).supplierIndex = s.supplyState.index ∧ s.supplyState.block = s.blockNumber)) :
    ((supplyNext s who).acct w).supplierIndex = (supplyNext s who).supplyState.index := by
  rw [acct_supplyNext]
  split
  · rfl
  · rename_i hn
    rcases h with h | ⟨h1, h2⟩
    · exact absurd h hn
    · show _ = (sideS s).index
      rw [sideS, accrueSide_current _ h2, h1]

/-- After a borrow hook, likewise on the borrow side. -/
theorem borrowNext_settled (s : St) (who w : Account)
    (h : (who = w ∧ w < s.accts.length) ∨
      ((s.acct w).borrowerIndex = s.borrowState.index ∧ s.borrowState.block = s.blockNumber)) :
    ((borrowNext s who).acct w).borrowerIndex = (borrowNext s who).borrowState.index := by
  rw [acct_borrowNext]
  split
  · rfl
  · rename_i hn
    rcases h with h | ⟨h1, h2⟩
    · exact absurd h hn
    · show _ = (sideB s).index
      rw [sideB, accrueSide_current _ h2, h1]

/-! ### The potentials along a step

`phi_le` and `psi_le` are the only places where the potentials are unfolded: every step below
is one of them with its hypotheses checked. -/

/-- The global potential does not grow from `s` to `s'` when both indices grow by increments the
unindexed COMP of `s` covers, net of what `s'` leaves unindexed, and the accounts of `s'` have, at
the new indices, terms no larger in total than those of `s`. -/
theorem phi_le {gs gb : Nat} {s s' : St}
    (hS : s.supplyState.index ≤ s'.supplyState.index) (hB : s.borrowState.index ≤ s'.borrowState.index)
    (eS : totalSupply s * (s'.supplyState.index - s.supplyState.index) + doubleScale * unS s' ≤
      doubleScale * unS s)
    (eB : totalBorrows s * (s'.borrowState.index - s.borrowState.index) + doubleScale * unB s' ≤
      doubleScale * unB s)
    (ha : (s'.accts.map (term gs gb s'.supplyState.index s'.borrowState.index)).sum ≤
      (s.accts.map (term gs gb s'.supplyState.index s'.borrowState.index)).sum) :
    Phi gs gb s' ≤ Phi gs gb s := by
  have := sum_le_of_index_le₂ s.accts (term gs gb s.supplyState.index s.borrowState.index)
    (term gs gb s'.supplyState.index s'.borrowState.index) Acct.supply Acct.borrow
    (fun a _ => term_index_le gs gb hS hB a) (Nat.le_refl _)
  unfold Phi; unfold totalSupply at eS; unfold totalBorrows at eB; omega

/-- The potential of account `w` does not grow from `s` to `s'` under the same conditions on the
indices, when its record at the new indices has a term no larger than before and, on each side,
its units are unchanged or nothing is left unindexed. -/
theorem psi_le {gs gb : Nat} {w : Account} {s s' : St}
    (hS : s.supplyState.index ≤ s'.supplyState.index) (hB : s.borrowState.index ≤ s'.borrowState.index)
    (eS : totalSupply s * (s'.supplyState.index - s.supplyState.index) + doubleScale * unS s' ≤
      doubleScale * unS s)
    (eB : totalBorrows s * (s'.borrowState.index - s.borrowState.index) + doubleScale * unB s' ≤
      doubleScale * unB s)
    (ht : term gs gb s'.supplyState.index s'.borrowState.index (s'.acct w) ≤
      term gs gb s'.supplyState.index s'.borrowState.index (s.acct w))
    (uS : (s'.acct w).supply = (s.acct w).supply ∨ unS s' = 0)
    (uB : (s'.acct w).borrow = (s.acct w).borrow ∨ unB s' = 0) :
    Psi gs gb w s' ≤ Psi gs gb w s := by
  have h1 := term_index_le gs gb hS hB (s.acct w)
  have h2 := ite_accrue_le (units := (s.acct w).supply) (supply_le_total s w) eS uS
  have h3 := ite_accrue_le (units := (s.acct w).borrow) (borrow_le_total s w) eB uB
  unfold Psi; omega

/-- The side conditions of `phi_le` and `psi_le` for a side left as it is. -/
theorem side_same {T i i' u u' : Nat} (hi : i' = i) (hu : u' = u) :
    i ≤ i' ∧ T * (i' - i) + doubleScale * u' ≤ doubleScale * u := by
  subst hi hu; simp

/-- The side conditions for a side brought up to date (and then given any speed). -/
theorem side_accrued (sd : Side) (now T : Nat) {sd' : Side} (hi : sd'.index = (accrueSide sd now T).index)
    (hb : sd'.block = now) (sp : Nat) :
    sd.index ≤ sd'.index ∧
      T * (sd'.index - sd.index) + doubleScale * ((now - sd'.block) * sp) ≤
        doubleScale * ((now - sd.block) * sd.speed) := by
  have := accrueSide_index sd now T
  rw [hi, hb]; simp only [Nat.sub_self, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]; exact this

/-- `phi_le` for a step that changes the accounts only. -/
theorem phi_accts {gs gb : Nat} {s s' : St} (hS : s'.supplyState = s.supplyState)
    (hB : s'.borrowState = s.borrowState) (hn : s'.blockNumber = s.blockNumber)
    (ha : (s'.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum ≤
      (s.accts.map (term gs gb s.supplyState.index s.borrowState.index)).sum) :
    Phi gs gb s' ≤ Phi gs gb s := by
  unfold Phi unS unB; rw [hS, hB, hn]; omega

/-- `psi_le` for a step that changes the accounts only. -/
theorem psi_accts {gs gb : Nat} {w : Account} {s s' : St} (hS : s'.supplyState = s.supplyState)
    (hB : s'.borrowState = s.borrowState) (hn : s'.blockNumber = s.blockNumber)
    (ht : term gs gb s.supplyState.index s.borrowState.index (s'.acct w) ≤
      term gs gb s.supplyState.index s.borrowState.index (s.acct w))
    (uS : (s'.acct w).supply = (s.acct w).supply ∨ unS s = 0)
    (uB : (s'.acct w).borrow = (s.acct w).borrow ∨ unB s = 0) : Psi gs gb w s' ≤ Psi gs gb w s := by
  have e1 : unS s' = unS s := by unfold unS; rw [hS, hn]
  have e2 : unB s' = unB s := by unfold unB; rw [hB, hn]
  obtain ⟨h1, h2⟩ := side_same (T := totalSupply s) (congrArg Side.index hS) e1
  obtain ⟨h3, h4⟩ := side_same (T := totalBorrows s) (congrArg Side.index hB) e2
  exact psi_le h1 h3 h2 h4 (by rw [hS, hB]; exact ht) (by rw [e1]; exact uS) (by rw [e2]; exact uB)

/-- The side conditions of a speed change, for both sides. -/
theorem speeds_sides (s : St) (a b : Nat) :
    (s.supplyState.index ≤ (speedsNext s a b).supplyState.index ∧
      totalSupply s * ((speedsNext s a b).supplyState.index - s.supplyState.index) +
        doubleScale * unS (speedsNext s a b) ≤ doubleScale * unS s) ∧
    (s.borrowState.index ≤ (speedsNext s a b).borrowState.index ∧
      totalBorrows s * ((speedsNext s a b).borrowState.index - s.borrowState.index) +
        doubleScale * unB (speedsNext s a b) ≤ doubleScale * unB s) := by
  unfold speedsNext unS unB; dsimp only
  constructor <;> split
  · exact side_same rfl rfl
  · exact side_accrued _ _ _ rfl (accrueSide_block _ _ _) a
  · exact side_same rfl rfl
  · exact side_accrued _ _ _ rfl (accrueSide_block _ _ _) b

/-- The invariant: each index started from 0 or `compInitialIndex` and has not fallen below its
start, no side's block lies ahead, the speeds are the ghost speeds `sp`, and no recorded index lies
above the market's (so the state is `Consistent` and REQ-CALLS-SUCCEED applies). -/
structure Inv (gs gb : Nat) (sp : Nat × Nat) (s : St) : Prop where
  /-- The supply index started from `gs`. -/
  startS : (gs = 0 ∨ gs = compInitialIndex) ∧ gs ≤ s.supplyState.index
  /-- The borrow index started from `gb`. -/
  startB : (gb = 0 ∨ gb = compInitialIndex) ∧ gb ≤ s.borrowState.index
  /-- The supply side is not ahead. -/
  blockS : s.supplyState.block ≤ s.blockNumber
  /-- The borrow side is not ahead. -/
  blockB : s.borrowState.block ≤ s.blockNumber
  /-- The supply speed is the ghost one. -/
  speedS : s.supplyState.speed = sp.1
  /-- The borrow speed is the ghost one. -/
  speedB : s.borrowState.speed = sp.2
  /-- No recorded index lies above the market's. -/
  accts : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index

/-- A potential `P` that no step of a call raises and that blocks passing raise by at most the
COMP emitted. `Phi` and every `Psi` are such potentials. -/
structure Moves (gs gb : Nat) (P : St → Nat) : Prop where
  /-- A supply hook. -/
  supply : ∀ sp s who, Inv gs gb sp s → P (supplyNext s who) ≤ P s
  /-- A borrow hook. -/
  borrow : ∀ sp s who, Inv gs gb sp s → P (borrowNext s who) ≤ P s
  /-- A payment. -/
  grant : ∀ s who, P (grant s who) ≤ P s
  /-- A supply balance change of a settled account at an up-to-date side. -/
  balS : ∀ s w (g : Nat → Nat), (s.acct w).supplierIndex = s.supplyState.index →
    s.supplyState.block = s.blockNumber → P (s.withAcct w fun a => { a with supply := g a.supply }) ≤ P s
  /-- A borrow balance change of a settled account at an up-to-date side. -/
  balB : ∀ s w (g : Nat → Nat), (s.acct w).borrowerIndex = s.borrowState.index →
    s.borrowState.block = s.blockNumber → P (s.withAcct w fun a => { a with borrow := g a.borrow }) ≤ P s
  /-- A speed change. -/
  speeds : ∀ s a b, P (speedsNext s a b) ≤ P s
  /-- Blocks passing. -/
  advance : ∀ sp s k, Inv gs gb sp s →
    P { s with blockNumber := s.blockNumber + k } ≤ P s + doubleScale * (k * (sp.1 + sp.2))
  /-- COMP sent to the Comptroller. -/
  drip : ∀ s x, P { s with reserve := s.reserve + x } ≤ P s

/-- `Phi` is such a potential. -/
theorem phi_moves (gs gb : Nat) : Moves gs gb (Phi gs gb) where
  supply sp s who hI := by
    obtain ⟨h1, h2⟩ := side_accrued s.supplyState s.blockNumber (totalSupply s)
      (sd' := sideS s) rfl (accrueSide_block _ _ _) (sideS s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalBorrows s) (i := s.borrowState.index) (u := unB s) rfl rfl
    exact phi_le h1 h3 h2 h4 (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ =>
      term_settleS (effStart_le_firstStart _ hI.startS.1 (Nat.le_trans hI.startS.2 h1)) rfl rfl rfl
        (by simp only [distS, creditFor_eq, accrualStart_eq, supplyNext_supplyState]; omega))
  borrow sp s who hI := by
    obtain ⟨h1, h2⟩ := side_accrued s.borrowState s.blockNumber (totalBorrows s)
      (sd' := sideB s) rfl (accrueSide_block _ _ _) (sideB s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalSupply s) (i := s.supplyState.index) (u := unS s) rfl rfl
    exact phi_le h3 h1 h4 h2 (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ =>
      term_settleB (effStart_le_firstStart _ hI.startB.1 (Nat.le_trans hI.startB.2 h1)) rfl rfl rfl
        (by simp only [distB, creditFor_eq, accrualStart_eq, borrowNext_borrowState]; omega))
  grant s who := by
    unfold grant; split
    · exact phi_accts rfl rfl rfl
        (Nat.le_of_eq (Ledger.sum_map_modify_eq _ _ _ _ noAcct fun _ => term_grant _ _ _ _ _))
    · exact Nat.le_refl _
  balS s w g hk _ := phi_accts rfl rfl rfl
    (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ => Nat.le_of_eq (term_balS _ hk))
  balB s w g hk _ := phi_accts rfl rfl rfl
    (Ledger.sum_map_modify_le _ _ _ _ noAcct fun _ => Nat.le_of_eq (term_balB _ hk))
  speeds s a b :=
    have h := speeds_sides s a b
    phi_le h.1.1 h.2.1 h.1.2 h.2.2 (Nat.le_refl _)
  advance sp s k hI := by
    have e1 := elapsed_add_mul k s.supplyState.speed hI.blockS
    have e2 := elapsed_add_mul k s.borrowState.speed hI.blockB
    unfold Phi unS unB; dsimp only
    rw [e1, e2, ← hI.speedS, ← hI.speedB]
    simp only [Nat.mul_add]; omega
  drip _ _ := Nat.le_refl _

/-- Every `Psi` is such a potential. -/
theorem psi_moves (gs gb : Nat) (w : Account) : Moves gs gb (Psi gs gb w) where
  supply sp s who hI := by
    obtain ⟨h1, h2⟩ := side_accrued s.supplyState s.blockNumber (totalSupply s)
      (sd' := sideS s) rfl (accrueSide_block _ _ _) (sideS s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalBorrows s) (i := s.borrowState.index) (u := unB s) rfl rfl
    refine psi_le h1 h3 h2 h4 ?_ (Or.inr (unS_supplyNext s who)) (Or.inl ?_)
    · rw [acct_supplyNext]; split
      · exact term_settleS (effStart_le_firstStart _ hI.startS.1 (Nat.le_trans hI.startS.2 h1))
          rfl rfl rfl (by simp only [distS, creditFor_eq, accrualStart_eq, supplyNext_supplyState]; omega)
      · exact Nat.le_refl _
    · rw [acct_supplyNext]; split <;> rfl
  borrow sp s who hI := by
    obtain ⟨h1, h2⟩ := side_accrued s.borrowState s.blockNumber (totalBorrows s)
      (sd' := sideB s) rfl (accrueSide_block _ _ _) (sideB s).speed
    obtain ⟨h3, h4⟩ := side_same (T := totalSupply s) (i := s.supplyState.index) (u := unS s) rfl rfl
    refine psi_le h3 h1 h4 h2 ?_ (Or.inl ?_) (Or.inr (unB_borrowNext s who))
    · rw [acct_borrowNext]; split
      · exact term_settleB (effStart_le_firstStart _ hI.startB.1 (Nat.le_trans hI.startB.2 h1))
          rfl rfl rfl (by simp only [distB, creditFor_eq, accrualStart_eq, borrowNext_borrowState]; omega)
      · exact Nat.le_refl _
    · rw [acct_borrowNext]; split <;> rfl
  grant s who := by
    unfold grant; split
    · have e := Ledger.getD_modify s.accts who w
        (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) noAcct
      refine psi_accts (w := w) rfl rfl rfl ?_ (Or.inl ?_) (Or.inl ?_)
      · show term _ _ _ _ ((s.accts.modify who _).getD w noAcct) ≤ _
        rw [e]; split
        · exact Nat.le_of_eq (term_grant _ _ _ _ _)
        · exact Nat.le_refl _
      · show ((s.accts.modify who _).getD w noAcct).supply = _
        rw [e]; split <;> rfl
      · show ((s.accts.modify who _).getD w noAcct).borrow = _
        rw [e]; split <;> rfl
    · exact Nat.le_refl _
  balS s v g hk hc := by
    refine psi_accts rfl rfl rfl ?_ (Or.inr (by unfold unS; rw [hc]; simp)) (Or.inl ?_)
    · rw [acct_withAcct]; split
      · rename_i h; obtain ⟨rfl, -⟩ := h; exact Nat.le_of_eq (term_balS _ hk)
      · exact Nat.le_refl _
    · rw [acct_withAcct]; split <;> rfl
  balB s v g hk hc := by
    refine psi_accts rfl rfl rfl ?_ (Or.inl ?_) (Or.inr (by unfold unB; rw [hc]; simp))
    · rw [acct_withAcct]; split
      · rename_i h; obtain ⟨rfl, -⟩ := h; exact Nat.le_of_eq (term_balB _ hk)
      · exact Nat.le_refl _
    · rw [acct_withAcct]; split <;> rfl
  speeds s a b :=
    have h := speeds_sides s a b
    psi_le h.1.1 h.2.1 h.1.2 h.2.2 (Nat.le_refl _) (Or.inl rfl) (Or.inl rfl)
  advance sp s k hI := by
    have e1 := elapsed_add_mul k s.supplyState.speed hI.blockS
    have e2 := elapsed_add_mul k s.borrowState.speed hI.blockB
    unfold Psi unS unB St.acct; dsimp only
    rw [e1, e2, ← hI.speedS, ← hI.speedB]
    split <;> split <;> simp only [Nat.mul_add, Nat.mul_zero, Nat.add_zero] <;> omega
  drip _ _ := Nat.le_refl _

/-! ### One operation -/

/-- The invariant is kept by a state with the same sides and block whose accounts record no index
above the market's. -/
theorem Inv.of_eq {gs gb : Nat} {sp : Nat × Nat} {s s' : St} (h : Inv gs gb sp s)
    (hS : s'.supplyState = s.supplyState) (hB : s'.borrowState = s.borrowState)
    (hn : s'.blockNumber = s.blockNumber)
    (ha : ∀ a ∈ s'.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index) :
    Inv gs gb sp s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨hS ▸ h1, hB ▸ h2, hS ▸ hn ▸ h3, hB ▸ hn ▸ h4, hS ▸ h5, hB ▸ h6, hS ▸ hB ▸ ha⟩

/-- A state with the invariant is consistent. -/
theorem Inv.consistent {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) : Consistent s :=
  ⟨h.blockS, h.blockB, h.accts⟩

/-- A supply hook keeps the invariant. -/
theorem inv_supplyNext {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (who : Account) :
    Inv gs gb sp (supplyNext s who) :=
  have hi := (accrueSide_index s.supplyState s.blockNumber (totalSupply s)).1
  ⟨⟨h.startS.1, Nat.le_trans h.startS.2 hi⟩, h.startB,
    Nat.le_of_eq (accrueSide_block _ _ _), h.blockB, (accrueSide_speed _ _ _).trans h.speedS, h.speedB,
    forall_mem_modify (fun a ha => ⟨Nat.le_trans (h.accts a ha).1 hi, (h.accts a ha).2⟩)
      (fun a ha => ⟨Nat.le_refl _, (h.accts a ha).2⟩)⟩

/-- A borrow hook keeps the invariant. -/
theorem inv_borrowNext {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (who : Account) :
    Inv gs gb sp (borrowNext s who) :=
  have hi := (accrueSide_index s.borrowState s.blockNumber (totalBorrows s)).1
  ⟨h.startS, ⟨h.startB.1, Nat.le_trans h.startB.2 hi⟩, h.blockS,
    Nat.le_of_eq (accrueSide_block _ _ _), h.speedS, (accrueSide_speed _ _ _).trans h.speedB,
    forall_mem_modify (fun a ha => ⟨(h.accts a ha).1, Nat.le_trans (h.accts a ha).2 hi⟩)
      (fun a ha => ⟨(h.accts a ha).1, Nat.le_refl _⟩)⟩

/-- A balance change keeps the invariant. -/
theorem inv_withAcct {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (w : Account)
    {f : Acct → Acct}
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex ∧ (f a).borrowerIndex = a.borrowerIndex) :
    Inv gs gb sp (s.withAcct w f) :=
  h.of_eq rfl rfl rfl (forall_mem_modify h.accts fun a ha => (hf a).1 ▸ (hf a).2 ▸ h.accts a ha)

/-- A payment keeps the invariant. -/
theorem inv_grant {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (who : Account) :
    Inv gs gb sp (grant s who) := by
  unfold ProofForgeFinDemo.DeFi.Compound.grant; split
  · exact h.of_eq rfl rfl rfl (forall_mem_modify h.accts fun a ha => h.accts a ha)
  · exact h

/-- A speed change keeps the invariant with the new ghost speeds. -/
theorem inv_speedsNext {gs gb : Nat} {sp : Nat × Nat} {s : St} (h : Inv gs gb sp s) (a b : Nat) :
    Inv gs gb (a, b) (speedsNext s a b) := by
  obtain ⟨h1, h2, h3, h4, -, -, h7⟩ := h
  have iS : s.supplyState.index ≤ (speedsNext s a b).supplyState.index := by
    unfold ProofForgeFinDemo.DeFi.Compound.speedsNext; dsimp only; split
    · exact Nat.le_refl _
    · exact (accrueSide_index _ _ _).1
  have iB : s.borrowState.index ≤ (speedsNext s a b).borrowState.index := by
    unfold ProofForgeFinDemo.DeFi.Compound.speedsNext; dsimp only; split
    · exact Nat.le_refl _
    · exact (accrueSide_index _ _ _).1
  refine ⟨⟨h1.1, Nat.le_trans h1.2 iS⟩, ⟨h2.1, Nat.le_trans h2.2 iB⟩, ?_, ?_, ?_, ?_,
    fun x hx => ⟨Nat.le_trans (h7 x hx).1 iS, Nat.le_trans (h7 x hx).2 iB⟩⟩ <;>
    unfold ProofForgeFinDemo.DeFi.Compound.speedsNext <;> dsimp only <;> split
  all_goals first
    | exact h3 | exact h4 | exact Nat.le_of_eq (accrueSide_block _ _ _) | assumption | rfl

/-- The facts a balance change after a supply hook needs: the account is settled and the side is
up to date. -/
theorem supplyNext_ready (s : St) (who : Account) (h : who < s.accts.length) :
    ((supplyNext s who).acct who).supplierIndex = (supplyNext s who).supplyState.index ∧
      (supplyNext s who).supplyState.block = (supplyNext s who).blockNumber :=
  ⟨supplyNext_settled s who who (Or.inl ⟨rfl, h⟩), accrueSide_block _ _ _⟩

/-- The same after a borrow hook. -/
theorem borrowNext_ready (s : St) (who : Account) (h : who < s.accts.length) :
    ((borrowNext s who).acct who).borrowerIndex = (borrowNext s who).borrowState.index ∧
      (borrowNext s who).borrowState.block = (borrowNext s who).blockNumber :=
  ⟨borrowNext_settled s who who (Or.inl ⟨rfl, h⟩), accrueSide_block _ _ _⟩

section Exec

variable {impl : Impl} (hOK : CallsSucceed impl) (hS : SupplyHookEffects impl)
  (hB : BorrowHookEffects impl) (hC : ClaimEffects impl) (hP : SetSpeedsEffects impl)
include hOK hS hB hC hP

/-- One operation keeps the invariant, with the ghost speeds following `nextSpeeds` (a speed
change cannot be refused, by REQ-CALLS-SUCCEED, so the stored speeds follow the ghost speeds), and
raises a potential with `Moves` by at most `doubleScale` times the COMP it emits. -/
theorem exec_step {gs gb : Nat} {P : St → Nat} (hm : Moves gs gb P) (sp : Nat × Nat) (s : St)
    (op : Op) (h : Inv gs gb sp s) :
    Inv gs gb (nextSpeeds sp op) (exec impl s op) ∧
      P (exec impl s op) ≤ P s + doubleScale * emittedBy sp op := by
  have keep : Inv gs gb sp s ∧ P s ≤ P s := ⟨h, Nat.le_refl _⟩
  cases op with
  | mint who x | redeem who x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      split
      · rename_i e; rw [supply_eq hS e]
        have hr := supplyNext_ready s who hlt
        have hi := inv_supplyNext h who
        try split
        all_goals first
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balS _ who (· + x) hr.1 hr.2) (hm.supply sp s who h)⟩
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balS _ who (· - x) hr.1 hr.2) (hm.supply sp s who h)⟩
          | exact keep
      · exact keep
    · exact keep
  | borrow who x | repay who x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hlt
      split
      · rename_i e; rw [borrow_eq hB e]
        have hr := borrowNext_ready s who hlt
        have hi := inv_borrowNext h who
        try split
        all_goals first
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balB _ who (· + x) hr.1 hr.2) (hm.borrow sp s who h)⟩
          | exact ⟨inv_withAcct hi who fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balB _ who (· - x) hr.1 hr.2) (hm.borrow sp s who h)⟩
          | exact keep
      · exact keep
    · exact keep
  | transfer src dst x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    split
    · rename_i hc
      obtain ⟨hs, hd, hne⟩ := hc
      split
      · rename_i e₁; rw [supply_eq hS e₁]
        split
        · rename_i e₂; rw [supply_eq hS e₂]
          split
          · have r1 := supplyNext_ready s src hs
            have r2 := supplyNext_ready (supplyNext s src) dst
              (by rw [show (supplyNext s src).accts.length = s.accts.length from
                List.length_modify _ _ _]; exact hd)
            have r3 := supplyNext_settled (supplyNext s src) dst src (Or.inr r1)
            refine ⟨inv_withAcct (inv_withAcct (inv_supplyNext (inv_supplyNext h src) dst) src
                fun _ => by exact ⟨rfl, rfl⟩) dst fun _ => by exact ⟨rfl, rfl⟩,
              Nat.le_trans (hm.balS _ dst (· + x) ?_ r2.2) (Nat.le_trans (hm.balS _ src (· - x) r3 r2.2)
                (Nat.le_trans (hm.supply sp _ dst (inv_supplyNext h src)) (hm.supply sp s src h)))⟩
            rw [acct_withAcct, ite_eq_right (fun h => hne h.1)]
            exact r2.1
          · exact keep
        · exact keep
      · exact keep
    · exact keep
  | claim who =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    cases e : impl s (.claim who) with
    | none => exact keep
    | some s' =>
      rw [Option.getD_some, claim_eq hC e]
      exact ⟨inv_grant (inv_supplyNext (inv_borrowNext h who) who) who, Nat.le_trans (hm.grant _ who)
        (Nat.le_trans (hm.supply sp _ who (inv_borrowNext h who)) (hm.borrow sp s who h))⟩
  | setSpeeds a b =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    cases e : impl s (.setSpeeds a b) with
    | none => have := hOK s (.setSpeeds a b) h.consistent; rw [e] at this; cases this
    | some s' =>
      rw [Option.getD_some, speeds_eq hP e]; exact ⟨inv_speedsNext h a b, hm.speeds s a b⟩
  | advance k =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨⟨h1, h2, Nat.le_trans h3 (Nat.le_add_right _ _), Nat.le_trans h4 (Nat.le_add_right _ _),
      h5, h6, h7⟩, hm.advance sp s k ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  | drip x =>
    simp only [exec, nextSpeeds, emittedBy, Nat.mul_zero, Nat.add_zero]
    exact ⟨h.of_eq rfl rfl rfl h.accts, hm.drip s x⟩

end Exec

/-! ### The upgrade -/

/-- The value the supply index starts from after the upgrade: `compInitialIndex` for an index the
upgrade initialized, otherwise the value it started from before. -/
def gsOf (L : Legacy) : Nat := if L.supplyIndex = 0 then compInitialIndex else L.supplyStart

/-- The value the borrow index starts from after the upgrade. -/
def gbOf (L : Legacy) : Nat := if L.borrowIndex = 0 then compInitialIndex else L.borrowStart

/-- The index of an initialized side. -/
theorem initSide_index (now : Nat) (sd : Side) :
    (initSide now sd).index = if sd.index = 0 then compInitialIndex else sd.index := by
  unfold initSide; split <;> rfl

/-- The block of an initialized side. -/
theorem initSide_block (now : Nat) (sd : Side) :
    (initSide now sd).block = if sd.index = 0 then now else sd.block := by
  unfold initSide; split <;> rfl

/-- The speed of an initialized side. -/
theorem initSide_speed (now : Nat) (sd : Side) : (initSide now sd).speed = sd.speed := by
  unfold initSide; split <;> rfl

/-- The upgrade of a well-formed state satisfies the invariant. -/
theorem inv_upgrade (L : Legacy) (hw : L.WellFormed) :
    Inv (gsOf L) (gbOf L) (L.compSpeed, L.compSpeed) (upgrade L) := by
  obtain ⟨hs1, hs2, hb1, hb2, hbs, hbb, ha⟩ := hw
  refine ⟨?_, ?_, ?_, ?_, initSide_speed _ _, initSide_speed _ _, ?_⟩ <;>
    simp only [upgrade, initSide_index, initSide_block, gsOf, gbOf]
  · split
    · exact ⟨Or.inr rfl, Nat.le_refl _⟩
    · exact ⟨hs1, hs2⟩
  · split
    · exact ⟨Or.inr rfl, Nat.le_refl _⟩
    · exact ⟨hb1, hb2⟩
  · split
    · exact Nat.le_refl _
    · exact hbs
  · split
    · exact Nat.le_refl _
    · exact hbb
  · intro a hm
    obtain ⟨h1, h2⟩ := ha a hm
    constructor <;> split <;> omega

/-- The pending COMP of one side at the upgrade is at most what it was before. -/
theorem pend_upgrade (idx start r u : Nat) (h : r ≤ idx) :
    pending u (effStart (if idx = 0 then compInitialIndex else start) r)
        (if idx = 0 then compInitialIndex else idx) ≤ u * (idx - legacyStart start r) := by
  split
  · have : r = 0 := by omega
    subst this; simp
  · exact Nat.le_refl _

/-- An account's term at the upgrade is its COMP credited, scaled, plus what it was owed. -/
theorem term_upgrade (L : Legacy) (a : Acct)
    (ha : a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex) :
    term (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index a ≤
      (a.accrued + a.wallet) * doubleScale + L.pendingScaled a := by
  have h1 := pend_upgrade L.supplyIndex L.supplyStart a.supplierIndex a.supply ha.1
  have h2 := pend_upgrade L.borrowIndex L.borrowStart a.borrowerIndex a.borrow ha.2
  simp only [term, Legacy.pendingScaled, upgrade, initSide_index, gsOf, gbOf]
  omega

/-- Nothing unindexed at the upgrade beyond what was unindexed before, supply side. -/
theorem unS_upgrade (L : Legacy) : unS (upgrade L) ≤ L.unindexedSupply := by
  simp only [unS, Legacy.unindexedSupply, upgrade, initSide_block, initSide_speed]
  split
  · simp
  · exact Nat.le_refl _

/-- Nothing unindexed at the upgrade beyond what was unindexed before, borrow side. -/
theorem unB_upgrade (L : Legacy) : unB (upgrade L) ≤ L.unindexedBorrow := by
  simp only [unB, Legacy.unindexedBorrow, upgrade, initSide_block, initSide_speed]
  split
  · simp
  · exact Nat.le_refl _

/-- The global potential at the upgrade. -/
theorem phi_upgrade (L : Legacy) (hw : L.WellFormed) :
    Phi (gsOf L) (gbOf L) (upgrade L) ≤
      ((upgrade L).credited + L.unindexedSupply + L.unindexedBorrow) * doubleScale +
        (L.accts.map L.pendingScaled).sum := by
  have h1 := Ledger.sum_map_le_add L.accts (fun a => (a.accrued + a.wallet) * doubleScale)
    (term (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index)
    L.pendingScaled (fun a ha => term_upgrade L a (hw.2.2.2.2.2.2 a ha))
  rw [Ledger.sum_map_mul_right] at h1
  have h2 := Nat.mul_le_mul_left doubleScale (unS_upgrade L)
  have h3 := Nat.mul_le_mul_left doubleScale (unB_upgrade L)
  have e : (upgrade L).accts = L.accts := rfl
  unfold Phi St.credited
  rw [e, Nat.add_mul, Nat.add_mul, Nat.mul_comm L.unindexedSupply, Nat.mul_comm L.unindexedBorrow]
  omega

/-- The potential of one account at the upgrade. -/
theorem psi_upgrade (L : Legacy) (hw : L.WellFormed) (who : Account) :
    Psi (gsOf L) (gbOf L) who (upgrade L) ≤
      ((upgrade L).creditedTo who +
          ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
            (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0))) * doubleScale +
        L.pendingScaled (L.accts.getD who noAcct) := by
  have hacct : (upgrade L).acct who = L.accts.getD who noAcct := rfl
  have hp : term (gsOf L) (gbOf L) (upgrade L).supplyState.index (upgrade L).borrowState.index
      (L.accts.getD who noAcct) ≤
        ((L.accts.getD who noAcct).accrued + (L.accts.getD who noAcct).wallet) * doubleScale +
          L.pendingScaled (L.accts.getD who noAcct) := by
    rcases Ledger.getD_mem_or L.accts who noAcct with hm | hm
    · exact term_upgrade L _ (hw.2.2.2.2.2.2 _ hm)
    · rw [hm]; simp [term, noAcct]
  have h2 := Nat.mul_le_mul_left doubleScale (unS_upgrade L)
  have h3 := Nat.mul_le_mul_left doubleScale (unB_upgrade L)
  rw [Nat.add_mul] at hp
  unfold Psi St.creditedTo
  rw [hacct]
  by_cases hs : 0 < (L.accts.getD who noAcct).supply <;>
    by_cases hb : 0 < (L.accts.getD who noAcct).borrow <;>
    simp only [hs, hb, ↓reduceIte, Nat.add_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero,
      Nat.mul_comm L.unindexedSupply, Nat.mul_comm L.unindexedBorrow] <;> omega

/-- COMP credited, scaled, is covered by the global potential. -/
theorem credited_le_phi (gs gb : Nat) (s : St) : s.credited * doubleScale ≤ Phi gs gb s := by
  have := sum_mul_le_of_le s.accts (fun a => a.accrued + a.wallet)
    (term gs gb s.supplyState.index s.borrowState.index) doubleScale (fun a _ => by unfold term; omega)
  unfold Phi St.credited; omega

/-- COMP credited to one account, scaled, is covered by its potential. -/
theorem creditedTo_le_psi (gs gb : Nat) (w : Account) (s : St) :
    s.creditedTo w * doubleScale ≤ Psi gs gb w s := by
  unfold Psi term St.creditedTo; omega

/-- The potential of an account without a position is its COMP credited, scaled. -/
theorem psi_noPosition (gs gb : Nat) (s : St) (who : Account) (h : NoPosition s who) :
    Psi gs gb who s = s.creditedTo who * doubleScale := by
  unfold Psi term St.creditedTo
  rw [h.1, h.2]
  simp

/-! ### The three bounds -/

section Bounds

variable {impl : Impl} (hOK : CallsSucceed impl) (hS : SupplyHookEffects impl)
  (hB : BorrowHookEffects impl) (hC : ClaimEffects impl) (hP : SetSpeedsEffects impl)
include hOK hS hB hC hP

/-- REQ-REWARDS-BOUNDED for every implementation that meets the five per-call requirements. -/
theorem rewards_bounded : RewardsBounded impl := by
  intro L ops hw
  have h := Seq.run_bound_via_potential (Inv (gsOf L) (gbOf L)) (Phi (gsOf L) (gbOf L))
    St.credited doubleScale_pos (fun sp s op hI => (exec_step hOK hS hB hC hP (phi_moves _ _) sp s op hI).1)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (phi_moves _ _) sp s op hI).2)
    (fun _ s _ => credited_le_phi _ _ s) (inv_upgrade L hw) (phi_upgrade L hw) ops
  rw [run_eq, emitted_eq]
  unfold Legacy.owed
  omega

/-- REQ-ACCOUNT-BOUNDED for every implementation that meets the five per-call requirements. -/
theorem account_bounded : AccountBounded impl := by
  intro L ops who hw
  have h := Seq.run_bound_via_potential (Inv (gsOf L) (gbOf L)) (Psi (gsOf L) (gbOf L) who)
    (fun t => t.creditedTo who) doubleScale_pos
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).1)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).2)
    (fun _ s _ => creditedTo_le_psi _ _ who s) (inv_upgrade L hw) (psi_upgrade L hw who) ops
  rw [run_eq, emitted_eq]
  unfold Legacy.owedTo
  omega

/-- REQ-NO-BACKDATED-REWARDS for every implementation that meets the five per-call
requirements. -/
theorem no_backdated : NoBackdatedRewards impl := by
  intro L history ops who hw hpos
  simp only [run_eq] at hpos ⊢
  rw [speedsAfter_eq, emitted_eq]
  have hI := (Seq.run_le_accum (Inv (gsOf L) (gbOf L)) (fun _ => 0) (f := emittedBy)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (phi_moves _ _) sp s op hI).1)
    (fun _ _ _ _ => Nat.zero_le _)
    (inv_upgrade L hw) history).2
  have h := Seq.run_bound_via_potential (Inv (gsOf L) (gbOf L)) (Psi (gsOf L) (gbOf L) who)
    (fun t => t.creditedTo who) doubleScale_pos
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).1)
    (fun sp s op hI => (exec_step hOK hS hB hC hP (psi_moves _ _ who) sp s op hI).2)
    (fun _ s _ => creditedTo_le_psi _ _ who s) hI
    (B := (Seq.run (exec impl) (upgrade L) history).creditedTo who) (R := 0)
    (by rw [psi_noPosition _ _ _ _ hpos]; simp) ops
  simpa using h

/-- The three sequence requirements of `rw-compound-comp` follow from the five per-call
requirements (REQ-CALLS-SUCCEED, REQ-SUPPLY-HOOK, REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS), for
every implementation. -/
theorem bounds_of_calls :
    RewardsBounded impl ∧ AccountBounded impl ∧ NoBackdatedRewards impl :=
  ⟨rewards_bounded hOK hS hB hC hP, account_bounded hOK hS hB hC hP, no_backdated hOK hS hB hC hP⟩

end Bounds

end ProofForgeFinDemo.DeFi.Compound
