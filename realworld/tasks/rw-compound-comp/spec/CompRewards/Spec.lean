/-!
# COMP reward distribution specification (protected)

Owner-reviewed definitions for the reward flywheel of Compound's Comptroller: the supply and
borrow reward indices of a market, the index recorded for each account, the COMP accrued to
each account, claims, and the one-time upgrade that Compound Proposal 62 ran on mainnet
(`_upgradeSplitCompRewards`, block 13322798, 2021-09-29). Candidates may not edit this file.
Every requirement is a predicate over an implementation `comptroller : Impl`; the locked
challenge (`CompRewards/Challenge.lean`) applies each one to the definition hole
`CompRewards.comptroller`.

Model, as a reader of `contracts/Comptroller.sol` would map it:

* One market. Its supply side and borrow side each have a reward index (`compSupplyState`,
  `compBorrowState`: `index` and `block`) and a speed in COMP per block (`compSupplySpeeds`,
  `compBorrowSpeeds`). Indices are mantissas at scale 1e36 (`doubleScale`).
* An account holds `supply` cTokens (`CToken.balanceOf`) and `borrow` borrow units (Compound's
  `borrowBalanceStored / borrowIndex`). The market's totals are the sums over all accounts.
* `supplierIndex` and `borrowerIndex` are `compSupplierIndex` and `compBorrowerIndex`; 0 means
  the Comptroller has no index recorded for the account. `accrued` is `compAccrued`, `wallet`
  is the COMP the account holds, and `reserve` is the COMP held by the Comptroller.
* Amounts are natural numbers in the smallest unit (1e-18 COMP); arithmetic is unbounded, so
  the 224-bit and 32-bit overflow checks never fail. A call that reverts is `none`.

The implementation handles the Comptroller's calls: the policy hooks a cToken calls before it
changes a balance (`mintAllowed`, `redeemAllowed`, `transferAllowed`, `seizeAllowed` on the
supply side; `borrowAllowed`, `repayBorrowAllowed` on the borrow side), `claimComp` and
`_setCompSpeeds`. Balance changes, the passing of blocks and COMP sent to the Comptroller are
modelled here, outside the implementation.
-/

namespace CompRewards

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

end CompRewards
