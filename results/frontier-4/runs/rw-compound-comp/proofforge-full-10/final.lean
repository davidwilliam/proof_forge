import CompRewards.Spec
import ProofForgeFin.Ledger
open ProofForgeFin.Ledger
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

theorem updSupply_some (s s1 : St) (hU : updateCompSupplyIndex s = some s1) : s.supplyState.block ≤ s.blockNumber ∧ s1 = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by
  simp only [updateCompSupplyIndex, subChecked, totalSupply, fraction, doubleScale] at hU
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ite_true] at hU
    refine ⟨hb, ?_⟩
    have hT : totalSupply s = (s.accts.map Acct.supply).sum := rfl
    simp only [accrueSide, hT]
    by_cases hd12 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · simp [hd12] at hU ⊢
      by_cases ht : 0 < (s.accts.map Acct.supply).sum
      · simp [ht, doubleScale] at hU ⊢
        rw [hU]
      · simp [ht] at hU ⊢
        exact hU.symm
    · simp [hd12] at hU ⊢
      by_cases hdb : 0 < s.blockNumber - s.supplyState.block
      · have hsp : ¬0 < s.supplyState.speed := by omega
        simp [hdb, hsp] at hU ⊢
        rw [← hU]
      · simp [hdb] at hU ⊢
        have hbeq : s.supplyState.block = s.blockNumber := by omega
        have hEq : ({ s with supplyState := ({ s.supplyState with block := s.blockNumber } : Side) } : St) = s := by
          cases s with
          | mk bn sup bor res accts =>
            cases sup with
            | mk idx blk spd =>
              simp_all
        rw [hEq] at ⊢
        exact hU.symm
  · simp only [hb, ite_false] at hU
    simp at hU

theorem updBorrow_some (s s1 : St) (hU : updateCompBorrowIndex s = some s1) : s.borrowState.block ≤ s.blockNumber ∧ s1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by
  simp only [updateCompBorrowIndex, subChecked, totalBorrows, fraction, doubleScale] at hU
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ite_true] at hU
    refine ⟨hb, ?_⟩
    have hT : totalBorrows s = (s.accts.map Acct.borrow).sum := rfl
    simp only [accrueSide, hT]
    by_cases hd12 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · simp [hd12] at hU ⊢
      by_cases ht : 0 < (s.accts.map Acct.borrow).sum
      · simp [ht, doubleScale] at hU ⊢
        rw [hU]
      · simp [ht] at hU ⊢
        exact hU.symm
    · simp [hd12] at hU ⊢
      by_cases hdb : 0 < s.blockNumber - s.borrowState.block
      · have hsp : ¬0 < s.borrowState.speed := by omega
        simp [hdb, hsp] at hU ⊢
        rw [← hU]
      · simp [hdb] at hU ⊢
        have hbeq : s.borrowState.block = s.blockNumber := by omega
        have hEq : ({ s with borrowState := ({ s.borrowState with block := s.blockNumber } : Side) } : St) = s := by
          cases s with
          | mk bn sup bor res accts =>
            cases bor with
            | mk idx blk spd =>
              simp_all
        rw [hEq] at ⊢
        exact hU.symm
  · simp only [hb, ite_false] at hU
    simp at hU

theorem distSupply_some (s : St) (who : Account) (s' : St) (hD : distributeSupplierComp s who = some s') : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧ s' = ({ s with accts := s.accts.modify who fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } : St) := by
  have hStart : ∀ (a : Acct), (if a.supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else a.supplierIndex) = accrualStart a.supplierIndex s.supplyState.index := by
    intro a
    unfold accrualStart
    by_cases hr : a.supplierIndex = 0
    · simp only [hr, ite_true, true_and]
    · simp only [hr, ite_false, false_and]
  simp only [distributeSupplierComp, subChecked] at hD
  by_cases hP : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index
  · simp [hP] at hD
    have hFix := hStart (s.acct who)
    have hLe : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
      rw [← hFix]
      exact hP
    refine ⟨hLe, ?_⟩
    have hEq : s.withAcct who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) }) = ({ s with accts := s.accts.modify who fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } : St) := by
      unfold St.withAcct
      congr 1
      apply modify_congr _ _ noAcct
      intro hmem
      have h1 : (s.acct who).supply = (s.accts.getD who noAcct).supply := rfl
      have h2 : (s.acct who).supplierIndex = (s.accts.getD who noAcct).supplierIndex := rfl
      rw [h1, h2, hStart]
      simp only [mulDouble, creditFor]
    exact hD.symm.trans hEq
  · simp [hP] at hD

theorem distBorrow_some (s : St) (who : Account) (s' : St) (hD : distributeBorrowerComp s who = some s') : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧ s' = ({ s with accts := s.accts.modify who fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } : St) := by
  have hStart : ∀ (a : Acct), (if a.borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else a.borrowerIndex) = accrualStart a.borrowerIndex s.borrowState.index := by
    intro a
    unfold accrualStart
    by_cases hr : a.borrowerIndex = 0
    · simp only [hr, ite_true, true_and]
    · simp only [hr, ite_false, false_and]
  simp only [distributeBorrowerComp, subChecked] at hD
  by_cases hP : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index
  · simp [hP] at hD
    have hFix := hStart (s.acct who)
    have hLe : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
      rw [← hFix]
      exact hP
    refine ⟨hLe, ?_⟩
    have hEq : s.withAcct who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)) }) = ({ s with accts := s.accts.modify who fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } : St) := by
      unfold St.withAcct
      congr 1
      apply modify_congr _ _ noAcct
      intro hmem
      have h1 : (s.acct who).borrow = (s.accts.getD who noAcct).borrow := rfl
      have h2 : (s.acct who).borrowerIndex = (s.accts.getD who noAcct).borrowerIndex := rfl
      rw [h1, h2, hStart]
      simp only [mulDouble, creditFor]
    exact hD.symm.trans hEq
  · simp [hP] at hD

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    rw [hU] at h
    simp at h
  | some s1 =>
    rw [hU] at h
    simp at h
    obtain ⟨hb, hU1⟩ := updSupply_some s s1 hU
    obtain ⟨hle, hD⟩ := distSupply_some s1 who s' h
    subst hU1
    simp only [St.acct] at hle hD ⊢
    unfold SupplyDistributed
    exact ⟨hb, hle, hD⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    rw [hU] at h
    simp at h
  | some s1 =>
    rw [hU] at h
    simp at h
    obtain ⟨hb, hU1⟩ := updBorrow_some s s1 hU
    obtain ⟨hle, hD⟩ := distBorrow_some s1 who s' h
    subst hU1
    simp only [St.acct] at hle hD ⊢
    unfold BorrowDistributed
    exact ⟨hb, hle, hD⟩

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp [h]
    apply modify_congr _ _ noAcct
    intro hmem
    cases hA : s.accts.getD who noAcct with
    | mk sup bor sIdx bIdx acc wal =>
      simp_all [St.acct]
  · simp [h]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  cases hU1 : updateCompBorrowIndex s with
  | none =>
    rw [hU1] at h
    simp at h
  | some s1 =>
    rw [hU1] at h
    simp at h
    cases hD1 : distributeBorrowerComp s1 who with
    | none =>
      rw [hD1] at h
      simp at h
    | some s2 =>
      rw [hD1] at h
      simp at h
      cases hU2 : updateCompSupplyIndex s2 with
      | none =>
        rw [hU2] at h
        simp at h
      | some s3 =>
        rw [hU2] at h
        simp at h
        cases hD2 : distributeSupplierComp s3 who with
        | none =>
          rw [hD2] at h
          simp at h
        | some s4 =>
          rw [hD2] at h
          simp at h
          obtain ⟨hb1, hU1e⟩ := updBorrow_some s s1 hU1
          obtain ⟨hle1, hD1e⟩ := distBorrow_some s1 who s2 hD1
          subst hU1e
          simp only [St.acct] at hle1 hD1e
          have hB : BorrowDistributed s who s2 := by
            unfold BorrowDistributed
            exact ⟨hb1, hle1, hD1e⟩
          obtain ⟨hb2, hU2e⟩ := updSupply_some s2 s3 hU2
          obtain ⟨hle2, hD2e⟩ := distSupply_some s3 who s4 hD2
          subst hU2e
          simp only [St.acct] at hle2 hD2e
          have hS : SupplyDistributed s2 who s4 := by
            unfold SupplyDistributed
            exact ⟨hb2, hle2, hD2e⟩
          have hG := grant_eq s4 who
          rw [hG] at h
          exact ⟨s2, s4, hB, hS, h.symm⟩

theorem accrue_le (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem updSupply_isSome (s : St) (hb : s.supplyState.block ≤ s.blockNumber) : (updateCompSupplyIndex s).isSome = true := by
  unfold updateCompSupplyIndex subChecked
  simp [hb]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem updBorrow_isSome (s : St) (hb : s.borrowState.block ≤ s.blockNumber) : (updateCompBorrowIndex s).isSome = true := by
  unfold updateCompBorrowIndex subChecked
  simp [hb]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem start_le (rec idx : Nat) (hRec : rec ≤ idx) : accrualStart rec idx ≤ idx := by
  unfold accrualStart
  by_cases hr : rec = 0
  · simp [hr]
    by_cases hI : compInitialIndex ≤ idx
    · simp [hI]
    · simp [hI]
  · simp [hr]
    exact hRec

theorem distSupply_isSome (s : St) (who : Account) (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) : (distributeSupplierComp s who).isSome = true := by
  have hStart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    unfold accrualStart
    by_cases hr : (s.acct who).supplierIndex = 0
    · simp [hr]
    · simp [hr]
  unfold distributeSupplierComp subChecked
  by_cases hP : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index
  · simp [hP]
  · have hC : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
      rw [hStart]
      exact hle
    cases hP hC

theorem distBorrow_isSome (s : St) (who : Account) (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) : (distributeBorrowerComp s who).isSome = true := by
  have hStart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
    unfold accrualStart
    by_cases hr : (s.acct who).borrowerIndex = 0
    · simp [hr]
    · simp [hr]
  unfold distributeBorrowerComp subChecked
  by_cases hP : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index
  · simp [hP]
  · have hC : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
      rw [hStart]
      exact hle
    cases hP hC

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hC
  cases c with
  | supplyHook who =>
    simp only [comptroller]
    have hb : s.supplyState.block ≤ s.blockNumber := hC.1
    cases hU : updateCompSupplyIndex s with
    | none =>
      have hF : (updateCompSupplyIndex s).isSome = true := updSupply_isSome s hb
      rw [hU] at hF
      simp at hF
    | some s1 =>
      simp
      obtain ⟨_, hU1e⟩ := updSupply_some s s1 hU
      subst hU1e
      have hAll := hC.2.2
      have hRec : (s.acct who).supplierIndex ≤ s.supplyState.index := by
        rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
        · exact (hAll _ hm).1
        · simp only [St.acct, hm]
          exact Nat.zero_le _
      have hMono : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrue_le _ _ _
      have hRecNew : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := Nat.le_trans hRec hMono
      have hle : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := start_le _ _ hRecNew
      exact distSupply_isSome _ _ hle
  | borrowHook who =>
    simp only [comptroller]
    have hb : s.borrowState.block ≤ s.blockNumber := hC.2.1
    cases hU : updateCompBorrowIndex s with
    | none =>
      have hF : (updateCompBorrowIndex s).isSome = true := updBorrow_isSome s hb
      rw [hU] at hF
      simp at hF
    | some s1 =>
      simp
      obtain ⟨_, hU1e⟩ := updBorrow_some s s1 hU
      subst hU1e
      have hAll := hC.2.2
      have hRec : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
        rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
        · exact (hAll _ hm).2
        · simp only [St.acct, hm]
          exact Nat.zero_le _
      have hMono : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrue_le _ _ _
      have hRecNew : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := Nat.le_trans hRec hMono
      have hle : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := start_le _ _ hRecNew
      exact distBorrow_isSome _ _ hle
  | claim who =>
    simp only [comptroller, claimComp]
    have hbS : s.supplyState.block ≤ s.blockNumber := hC.1
    have hbB : s.borrowState.block ≤ s.blockNumber := hC.2.1
    cases hU1 : updateCompBorrowIndex s with
    | none =>
      have hF := updBorrow_isSome s hbB
      rw [hU1] at hF
      simp at hF
    | some s1 =>
      simp
      obtain ⟨_, hU1e⟩ := updBorrow_some s s1 hU1
      subst hU1e
      have hAll := hC.2.2
      have hRecB : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
        rcases getD_mem_or s.accts who noAcct with hm | hm
        · exact (hAll _ hm).2
        · simp only [St.acct, hm]
          exact Nat.zero_le _
      have hMonoB : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrue_le _ _ _
      have hRecBNew : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := Nat.le_trans hRecB hMonoB
      have hleB : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := start_le _ _ hRecBNew
      have hD1 : (distributeBorrowerComp ({ blockNumber := s.blockNumber, supplyState := s.supplyState, borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), reserve := s.reserve, accts := s.accts } : St) who).isSome = true := distBorrow_isSome _ _ hleB
      cases hD1' : distributeBorrowerComp ({ blockNumber := s.blockNumber, supplyState := s.supplyState, borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), reserve := s.reserve, accts := s.accts } : St) who with
      | none =>
        rw [hD1'] at hD1
        simp at hD1
      | some s2 =>
        simp
        sorry
  | setSpeeds a b =>
    sorry
theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller, setCompSpeedInternal, setSupplySpeed, setBorrowSpeed] at h
  by_cases hs : s.supplyState.speed ≠ a
  · simp [hs] at h
    cases hU1 : updateCompSupplyIndex s with
    | none =>
      rw [hU1] at h
      simp at h
    | some s1 =>
      rw [hU1] at h
      simp at h
      obtain ⟨hb1, hU1e⟩ := updSupply_some s s1 hU1
      subst hU1e
      simp at h
      by_cases hb : s.borrowState.speed = b
      · simp [hb] at h
        unfold SpeedsSet
        refine ⟨fun _ => hb1, by simp [hb], ?_⟩
        simp [hs, hb]
        exact h.symm
      · simp [hb] at h
        obtain ⟨s2, hU2, hEq2⟩ := h
        obtain ⟨hb2, hU2e⟩ := updBorrow_some _ s2 hU2
        subst hU2e
        simp at hb2
        simp at hEq2
        unfold SpeedsSet
        refine ⟨fun _ => hb1, fun _ => hb2, ?_⟩
        simp [hs, hb]
        exact hEq2.symm
  · simp [hs] at h
    have hsa : s.supplyState.speed = a := by omega
    by_cases hb : s.borrowState.speed = b
    · simp [hb] at h
      unfold SpeedsSet
      refine ⟨by simp [hs], by simp [hb], ?_⟩
      simp [hsa, hb]
      exact h.symm
    · simp [hb] at h
      obtain ⟨s2, hU2, hEq2⟩ := h
      obtain ⟨hb2, hU2e⟩ := updBorrow_some s s2 hU2
      subst hU2e
      simp at hEq2
      unfold SpeedsSet
      refine ⟨by simp [hs], fun _ => hb2, ?_⟩
      simp [hsa, hb]
      exact hEq2.symm
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
