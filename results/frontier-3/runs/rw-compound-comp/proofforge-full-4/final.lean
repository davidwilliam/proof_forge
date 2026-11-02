import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
/-!
Port of the COMP distribution of Compound's Comptroller as deployed by Proposal 62
(implementation 0x374ABb8cE19A73f2c4EFAd642bda76c797f19233, active on mainnet from block
13322798 to block 13382884). Source: compound-finance/compound-protocol, commit
f73b29373eb65cedf24896d7be46eed38435fc91, `contracts/Comptroller.sol`, byte-identical to the
verified source of the deployed implementation, and `contracts/ExponentialNoError.sol`.

* `updateCompSupplyIndex` (lines 1163 to 1177) and `updateCompBorrowIndex` (lines 1184 to 1198).
* `distributeSupplierComp` (lines 1205 to 1236) and `distributeBorrowerComp` (lines 1244 to 1275).
* `claimComp(holders, cTokens, true, true)` (lines 1320 to 1341) for one holder and one market,
  and `grantCompInternal` (lines 1350 to 1358).
* `setCompSpeedInternal` (lines 1130 to 1156).

The cToken's borrow index is taken as 1e18, so `div_(borrowBalanceStored, borrowIndex)` is the
account's borrow units. A `sub_` underflow or a `require` failure is `none`.
-/
namespace CompRewards

/-- `fraction(a, b)` (ExponentialNoError.sol): `Double(div_(mul_(a, doubleScale), b))`. -/
def fraction (a b : Nat) : Nat := a * doubleScale / b

/-- `mul_(uint a, Double b)` (ExponentialNoError.sol): `a * b.mantissa / doubleScale`. -/
def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

/-- `sub_(a, b)` (ExponentialNoError.sol): reverts on underflow. -/
def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

/-- `updateCompSupplyIndex(cToken)`. -/
def updateCompSupplyIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.supplyState.block with
  | none => none
  | some deltaBlocks =>
    if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
      let supplyTokens := totalSupply s
      let compAccrued := deltaBlocks * s.supplyState.speed
      let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
      some { s with supplyState :=
        { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s

/-- `updateCompBorrowIndex(cToken, marketBorrowIndex)`. -/
def updateCompBorrowIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.borrowState.block with
  | none => none
  | some deltaBlocks =>
    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
      let borrowAmount := totalBorrows s
      let compAccrued := deltaBlocks * s.borrowState.speed
      let ratio := if borrowAmount > 0 then fraction compAccrued borrowAmount else 0
      some { s with borrowState :=
        { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with borrowState := { s.borrowState with block := s.blockNumber } }
    else some s

/-- `distributeSupplierComp(cToken, supplier)`. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  let supplyIndex := s.supplyState.index
  let supplierIndex :=
    if (s.acct supplier).supplierIndex = 0 ∧ compInitialIndex ≤ supplyIndex then compInitialIndex
    else (s.acct supplier).supplierIndex
  match subChecked supplyIndex supplierIndex with
  | none => none
  | some deltaIndex =>
    let supplierDelta := mulDouble (s.acct supplier).supply deltaIndex
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex, accrued := a.accrued + supplierDelta })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex :=
    if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ borrowIndex then compInitialIndex
    else (s.acct borrower).borrowerIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some deltaIndex =>
    let borrowerDelta := mulDouble (s.acct borrower).borrow deltaIndex
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := borrowIndex, accrued := a.accrued + borrowerDelta })

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + amount } }
  else s

/-- `claimComp([holder], [market], true, true)`. -/
def claimComp (s : St) (holder : Account) : Option St := do
  let s ← updateCompBorrowIndex s
  let s ← distributeBorrowerComp s holder
  let s ← updateCompSupplyIndex s
  let s ← distributeSupplierComp s holder
  return grantCompInternal s holder

/-- The supply branch of `setCompSpeedInternal`: when the supply speed changes, accrue at the
old speed, then store the new one. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    (updateCompSupplyIndex s).map fun s =>
      { s with supplyState := { s.supplyState with speed := supplySpeed } }
  else some s

/-- The borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    (updateCompBorrowIndex s).map fun s =>
      { s with borrowState := { s.borrowState with speed := borrowSpeed } }
  else some s

/-- `setCompSpeedInternal(cToken, supplySpeed, borrowSpeed)`: the supply branch, then the borrow
branch. -/
def setCompSpeedInternal (s : St) (supplySpeed borrowSpeed : Nat) : Option St :=
  (setSupplySpeed s supplySpeed).bind fun s => setBorrowSpeed s borrowSpeed

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => do
    let s ← updateCompSupplyIndex s
    distributeSupplierComp s who
  | .borrowHook who => do
    let s ← updateCompBorrowIndex s
    distributeBorrowerComp s who
  | .claim who => claimComp s who
  | .setSpeeds a b => setCompSpeedInternal s a b

theorem modify_congr_at {α : Type} (l : List α) (w : Nat) (f g : α → α) (d : α)
    (h : f (l.getD w d) = g (l.getD w d)) : l.modify w f = l.modify w g := by
  induction l generalizing w with
  | nil => simp
  | cons a l ih =>
    cases w with
    | zero => simp_all
    | succ w => simp_all [ih]

theorem start_supply_eq (rec index : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ index then compInitialIndex else rec) =
      accrualStart rec index := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr]

theorem start_borrow_eq (rec index : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ index then compInitialIndex else rec) =
      accrualStart rec index := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr]

theorem subChecked_some (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem upd_supply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hs : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := subChecked_some _ _ h
  unfold updateCompSupplyIndex accrueSide totalSupply fraction
  simp only [hs]
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [hd]
    by_cases ht : (s.accts.map Acct.supply).sum > 0
    · have hd3 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < (s.accts.map Acct.supply).sum := by omega
      simp only [hd3, ht]
      rfl
    · have hd3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < (s.accts.map Acct.supply).sum) := by omega
      simp only [hd3, ht]
      rfl
  · have hd3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < (s.accts.map Acct.supply).sum) := by omega
    simp only [hd, hd3]
    by_cases hdb : s.blockNumber - s.supplyState.block > 0
    · simp only [hdb]
      rfl
    · simp only [hdb]
      have hb : s.supplyState.block = s.blockNumber := by omega
      cases s with | mk bn sup bor res ac =>
        simp_all
        cases sup with | mk ix bl sp =>
          simp_all

theorem upd_supply_none (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  have hs : subChecked s.blockNumber s.supplyState.block = none :=
    subChecked_none _ _ h
  unfold updateCompSupplyIndex
  simp [hs]

theorem upd_borrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hs : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := subChecked_some _ _ h
  unfold updateCompBorrowIndex accrueSide totalBorrows fraction
  simp only [hs]
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [hd]
    by_cases ht : (s.accts.map Acct.borrow).sum > 0
    · have hd3 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < (s.accts.map Acct.borrow).sum := by omega
      simp only [hd3, ht]
      rfl
    · have hd3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < (s.accts.map Acct.borrow).sum) := by omega
      simp only [hd3, ht]
      rfl
  · have hd3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < (s.accts.map Acct.borrow).sum) := by omega
    simp only [hd, hd3]
    by_cases hdb : s.blockNumber - s.borrowState.block > 0
    · simp only [hdb]
      rfl
    · simp only [hdb]
      have hb : s.borrowState.block = s.blockNumber := by omega
      cases s with | mk bn sup bor res ac =>
        simp_all
        cases bor with | mk ix bl sp =>
          simp_all

theorem upd_borrow_none (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  have hs : subChecked s.blockNumber s.borrowState.block = none :=
    subChecked_none _ _ h
  unfold updateCompBorrowIndex
  simp [hs]

theorem req_calls_succeed       : CallsSucceed comptroller := sorry
theorem req_supply_hook         : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook         : BorrowHookEffects comptroller := sorry
theorem req_claim               : ClaimEffects comptroller := sorry
theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
