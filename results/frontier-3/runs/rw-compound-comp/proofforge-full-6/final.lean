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

theorem updSupplyAux (s : St) (s1 : St) (h : updateCompSupplyIndex s = some s1) : s.supplyState.block ≤ s.blockNumber ∧ s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    refine ⟨hb, ?_⟩
    simp only [accrueSide, fraction] at h ⊢
    by_cases hp : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
    · simp only [hp, ↓reduceIte] at ⊢
      have hp1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 := ⟨hp.1, hp.2.1⟩
      have ht : totalSupply s > 0 := hp.2.2
      simp only [hp1, ht, ↓reduceIte] at h
      have e := Option.some_inj.mp h
      subst e
      rfl
    · simp only [hp, ↓reduceIte] at ⊢
      by_cases hq : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
      · simp only [hq, ↓reduceIte] at h
        by_cases ht : totalSupply s > 0
        · simp only [ht, ↓reduceIte] at h
          have : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s := ⟨hq.1, hq.2, ht⟩
          omega
        · simp only [ht, ↓reduceIte] at h
          have e := Option.some_inj.mp h
          subst e
          rfl
      · simp only [hq, ↓reduceIte] at h
        by_cases hr : s.blockNumber - s.supplyState.block > 0
        · simp only [hr, ↓reduceIte] at h
          have e := Option.some_inj.mp h
          subst e
          rfl
        · simp only [hr, ↓reduceIte] at h
          have e := Option.some_inj.mp h
          subst e
          have hb2 : s.blockNumber = s.supplyState.block := by omega
          cases s
          simp_all
  · simp only [hb, ↓reduceIte] at h
    simp at h

theorem updBorrowAux (s : St) (s1 : St) (h : updateCompBorrowIndex s = some s1) : s.borrowState.block ≤ s.blockNumber ∧ s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    refine ⟨hb, ?_⟩
    simp only [accrueSide, fraction] at h ⊢
    by_cases hp : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
    · simp only [hp, ↓reduceIte] at ⊢
      have hp1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hp.1, hp.2.1⟩
      have ht : totalBorrows s > 0 := hp.2.2
      simp only [hp1, ht, ↓reduceIte] at h
      have e := Option.some_inj.mp h
      subst e
      rfl
    · simp only [hp, ↓reduceIte] at ⊢
      by_cases hq : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
      · simp only [hq, ↓reduceIte] at h
        by_cases ht : totalBorrows s > 0
        · simp only [ht, ↓reduceIte] at h
          have : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s := ⟨hq.1, hq.2, ht⟩
          omega
        · simp only [ht, ↓reduceIte] at h
          have e := Option.some_inj.mp h
          subst e
          rfl
      · simp only [hq, ↓reduceIte] at h
        by_cases hr : s.blockNumber - s.borrowState.block > 0
        · simp only [hr, ↓reduceIte] at h
          have e := Option.some_inj.mp h
          subst e
          rfl
        · simp only [hr, ↓reduceIte] at h
          have e := Option.some_inj.mp h
          subst e
          have hb2 : s.blockNumber = s.borrowState.block := by omega
          cases s
          simp_all
  · simp only [hb, ↓reduceIte] at h
    simp at h

theorem accStartEq (r idx : Nat) : (if r = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else r) = accrualStart r idx := by unfold accrualStart; by_cases h0 : r = 0; simp [h0]; simp [h0]

theorem modCongr (l : List Acct) (i : Nat) (f g : Acct → Acct) (h : f (l.getD i noAcct) = g (l.getD i noAcct)) : l.modify i f = l.modify i g := by induction l generalizing i with | nil => simp [List.modify]; cases i; rfl; rfl | cons a t ih => cases i with | zero => simp [List.getD] at h; simp [List.modify, h] | succ n => simp [List.getD] at h; simp [List.modify]; exact ih n h

theorem acctWith (s s1 : St) (e1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) (who : Nat) : s1.acct who = s.acct who := by simp [e1, St.acct]

theorem supplyRecLe (s : St) (who : Nat) (hRec : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hRec _ hm).1
  · rw [hm]
    simp [noAcct]

theorem borrowRecLe (s : St) (who : Nat) (hRec : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hRec _ hm).2
  · rw [hm]
    simp [noAcct]

theorem leAccrueSupply (s : St) : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp only [h, ↓reduceIte]
    exact Nat.le_add_right _ _
  · simp only [h, ↓reduceIte]
    exact Nat.le_refl _

theorem leAccrueBorrow (s : St) : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp only [h, ↓reduceIte]
    exact Nat.le_add_right _ _
  · simp only [h, ↓reduceIte]
    exact Nat.le_refl _

theorem accStartLeNew (rec newIdx : Nat) (hRec : rec ≤ newIdx) : accrualStart rec newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases h0 : rec = 0
  · simp only [h0, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ newIdx
    · simp only [hi, ↓reduceIte]
    · simp only [hi, ↓reduceIte]
      exact Nat.zero_le _
  · simp only [h0, ↓reduceIte]
    exact hRec

theorem updSupplyEqUnused : True := trivial

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hbS, hbB, hRec⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    cases hU : updateCompSupplyIndex s with
    | none =>
      exfalso
      unfold updateCompSupplyIndex subChecked at hU
      simp [hbS] at hU
      by_cases hC1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
      · simp [hC1] at hU
      · simp [hC1] at hU
        by_cases hC2 : s.blockNumber - s.supplyState.block > 0
        · simp [hC2] at hU
        · simp [hC2] at hU
    | some s1 =>
      have hUpd := updSupplyAux s s1 hU
      obtain ⟨_, e1⟩ := hUpd
      have hOldLe : (s.acct who).supplierIndex ≤ s.supplyState.index := supplyRecLe s who hRec
      have hOldNew : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := leAccrueSupply s
      have hRecNew : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := Nat.le_trans hOldLe hOldNew
      have hLe : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accStartLeNew _ _ hRecNew
      have hac : s1.acct who = s.acct who := by simp [e1, St.acct]
      have hIdx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by simp [e1]
      have hStartEq : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hac, hIdx]; exact accStartEq _ _
      cases hD : distributeSupplierComp s1 who with
      | none =>
        exfalso
        simp only [distributeSupplierComp, subChecked] at hD
        rw [hStartEq, hIdx] at hD
        simp [hLe] at hD
      | some _ =>
        simp [hU, hD]
  | borrowHook who =>
    unfold comptroller
    cases hU : updateCompBorrowIndex s with
    | none =>
      exfalso
      unfold updateCompBorrowIndex subChecked at hU
      simp [hbB] at hU
      by_cases hC1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
      · simp [hC1] at hU
      · simp [hC1] at hU
        by_cases hC2 : s.blockNumber - s.borrowState.block > 0
        · simp [hC2] at hU
        · simp [hC2] at hU
    | some s1 =>
      have hUpd := updBorrowAux s s1 hU
      obtain ⟨_, e1⟩ := hUpd
      have hOldLe : (s.acct who).borrowerIndex ≤ s.borrowState.index := borrowRecLe s who hRec
      have hOldNew : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := leAccrueBorrow s
      have hRecNew : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := Nat.le_trans hOldLe hOldNew
      have hLe : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accStartLeNew _ _ hRecNew
      have hac : s1.acct who = s.acct who := by simp [e1, St.acct]
      have hIdx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [e1]
      have hStartEq : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hac, hIdx]; exact accStartEq _ _
      cases hD : distributeBorrowerComp s1 who with
      | none =>
        exfalso
        simp only [distributeBorrowerComp, subChecked] at hD
        rw [hStartEq, hIdx] at hD
        simp [hLe] at hD
      | some _ =>
        simp [hU, hD]
  | claim who =>
    unfold comptroller claimComp
    cases hU1 : updateCompBorrowIndex s with
    | none =>
      exfalso
      unfold updateCompBorrowIndex subChecked at hU1
      simp [hbB] at hU1
      by_cases hC1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
      · simp [hC1] at hU1
      · simp [hC1] at hU1
        by_cases hC2 : s.blockNumber - s.borrowState.block > 0
        · simp [hC2] at hU1
        · simp [hC2] at hU1
    | some sB =>
      have hUpdB := updBorrowAux s sB hU1
      obtain ⟨_, e1B⟩ := hUpdB
      have hOldLeB : (s.acct who).borrowerIndex ≤ s.borrowState.index := borrowRecLe s who hRec
      have hOldNewB : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := leAccrueBorrow s
      have hRecNewB : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := Nat.le_trans hOldLeB hOldNewB
      have hLeB : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accStartLeNew _ _ hRecNewB
      have hacB : sB.acct who = s.acct who := by simp [e1B, St.acct]
      have hIdxB : sB.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [e1B]
      have hStartEqB : (if (sB.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ sB.borrowState.index then compInitialIndex else (sB.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hacB, hIdxB]; exact accStartEq _ _
      cases hD1 : distributeBorrowerComp sB who with
      | none =>
        exfalso
        simp only [distributeBorrowerComp, subChecked] at hD1
        rw [hStartEqB, hIdxB] at hD1
        simp [hLeB] at hD1
      | some m1 =>
        have hUpdB2 := updBorrowAux s sB hU1
        obtain ⟨_, e1B'⟩ := hUpdB2
        have hSupM1 : m1.supplyState = s.supplyState := by
          have h1 : sB.supplyState = s.supplyState := by simp [e1B]
          have h2 : m1.supplyState = sB.supplyState := by
            simp only [distributeBorrowerComp, subChecked] at hD1
            rw [hStartEqB, hIdxB] at hD1
            simp only [hLeB, ↓reduceIte] at hD1
            have e2 := Option.some_inj.mp hD1
            simp [←e2, St.withAcct]
          rw [h2, h1]
        have hBlkM1 : m1.blockNumber = s.blockNumber := by
          have h1 : sB.blockNumber = s.blockNumber := by simp [e1B]
          have h2 : m1.blockNumber = sB.blockNumber := by
            simp only [distributeBorrowerComp, subChecked] at hD1
            rw [hStartEqB, hIdxB] at hD1
            simp only [hLeB, ↓reduceIte] at hD1
            have e2 := Option.some_inj.mp hD1
            simp [←e2, St.withAcct]
          rw [h2, h1]
        have hbSM1 : m1.supplyState.block ≤ m1.blockNumber := by rw [hSupM1, hBlkM1]; exact hbS
        cases hU2 : updateCompSupplyIndex m1 with
        | none =>
          exfalso
          unfold updateCompSupplyIndex subChecked at hU2
          simp [hbSM1] at hU2
          by_cases hC1 : m1.blockNumber - m1.supplyState.block > 0 ∧ m1.supplyState.speed > 0
          · simp [hC1] at hU2
          · simp [hC1] at hU2
            by_cases hC2 : m1.blockNumber - m1.supplyState.block > 0
            · simp [hC2] at hU2
            · simp [hC2] at hU2
        | some sS =>
          have hUpdS := updSupplyAux m1 sS hU2
          obtain ⟨_, e1S⟩ := hUpdS
          have hRecSupM1 : (m1.acct who).supplierIndex ≤ m1.supplyState.index := by
            have hacSup1 : (m1.acct who).supplierIndex = (sB.acct who).supplierIndex := by
              simp only [distributeBorrowerComp, subChecked] at hD1
              rw [hStartEqB, hIdxB] at hD1
              simp only [hLeB, ↓reduceIte] at hD1
              have e2 := Option.some_inj.mp hD1
              have hPres : ∀ a : Acct, ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + mulDouble (sB.acct who).borrow ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) }).supplierIndex = a.supplierIndex := fun a => rfl
              have hEqSup : ((sB.withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + mulDouble (sB.acct who).borrow ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) }).acct who).supplierIndex = (sB.acct who).supplierIndex := by
                simp only [St.withAcct, St.acct, ProofForgeFin.Ledger.getD_modify, hPres]
                split
                · rfl
                · rfl
              have e2' : (sB.withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + mulDouble (sB.acct who).borrow ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) }) = m1 := e2
              rw [←e2']
              exact hEqSup
            have hacSB : (sB.acct who).supplierIndex = (s.acct who).supplierIndex := by simp [e1B, St.acct]
            have hacSup : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := Eq.trans hacSup1 hacSB
            have hIdxSup : m1.supplyState.index = s.supplyState.index := by simp [hSupM1]
            rw [hacSup, hIdxSup]
            exact supplyRecLe s who hRec
          have hOldNewS : m1.supplyState.index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := leAccrueSupply m1
          have hRecNewS : (m1.acct who).supplierIndex ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := Nat.le_trans hRecSupM1 hOldNewS
          have hLeS : accrualStart (m1.acct who).supplierIndex (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := accStartLeNew _ _ hRecNewS
          have hacS : sS.acct who = m1.acct who := by simp [e1S, St.acct]
          have hIdxS : sS.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by simp [e1S]
          have hStartEqS : (if (sS.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ sS.supplyState.index then compInitialIndex else (sS.acct who).supplierIndex) = accrualStart (m1.acct who).supplierIndex (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by rw [hacS, hIdxS]; exact accStartEq _ _
          cases hD2 : distributeSupplierComp sS who with
          | none =>
            exfalso
            simp only [distributeSupplierComp, subChecked] at hD2
            rw [hStartEqS, hIdxS] at hD2
            simp [hLeS] at hD2
          | some _ =>
            simp [hU1, hD1, hU2, hD2]
  | setSpeeds a b =>
    sorry
theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    simp [hU] at h
  | some s1 =>
    simp [hU] at h
    have hUpd := updSupplyAux s s1 hU
    obtain ⟨hb, e1⟩ := hUpd
    have hac : s1.acct who = s.acct who := by simp [e1, St.acct]
    have hIdx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by simp [e1]
    have hStart : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hac, hIdx]
      exact accStartEq _ _
    simp only [distributeSupplierComp, subChecked] at h
    rw [hStart] at h
    rw [hIdx] at h
    have hSup : (s1.acct who).supply = (s.acct who).supply := by rw [hac]
    rw [hSup] at h
    by_cases hLe : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    · simp only [hLe, ↓reduceIte] at h
      have e2 := Option.some_inj.mp h
      refine ⟨hb, hLe, ?_⟩
      have hEq : (fun a : Acct => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + mulDouble (s.acct who).supply ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) }) (s.accts.getD who noAcct) = (fun a : Acct => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) (s.accts.getD who noAcct) := by
        have hrfl : s.accts.getD who noAcct = s.acct who := rfl
        rw [hrfl]
        simp only [mulDouble, creditFor]
      have hMod : s.accts.modify who (fun a : Acct => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + mulDouble (s.acct who).supply ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) }) = s.accts.modify who (fun a : Acct => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) := modCongr _ _ _ _ hEq
      have hAccts : s1.accts = s.accts := by simp [e1]
      rw [←e2]
      simp only [St.withAcct, hAccts, hMod, e1]
    · simp only [hLe, ↓reduceIte] at h
      simp at h
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    simp [hU] at h
  | some s1 =>
    simp [hU] at h
    have hUpd := updBorrowAux s s1 hU
    obtain ⟨hb, e1⟩ := hUpd
    have hac : s1.acct who = s.acct who := by simp [e1, St.acct]
    have hIdx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [e1]
    have hStart : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hac, hIdx]
      exact accStartEq _ _
    simp only [distributeBorrowerComp, subChecked] at h
    rw [hStart] at h
    rw [hIdx] at h
    have hBor : (s1.acct who).borrow = (s.acct who).borrow := by rw [hac]
    rw [hBor] at h
    by_cases hLe : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    · simp only [hLe, ↓reduceIte] at h
      have e2 := Option.some_inj.mp h
      refine ⟨hb, hLe, ?_⟩
      have hEq : (fun a : Acct => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + mulDouble (s.acct who).borrow ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) }) (s.accts.getD who noAcct) = (fun a : Acct => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) (s.accts.getD who noAcct) := by
        have hrfl : s.accts.getD who noAcct = s.acct who := rfl
        rw [hrfl]
        simp only [mulDouble, creditFor]
      have hMod : s.accts.modify who (fun a : Acct => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + mulDouble (s.acct who).borrow ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) }) = s.accts.modify who (fun a : Acct => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) := modCongr _ _ _ _ hEq
      have hAccts : s1.accts = s.accts := by simp [e1]
      rw [←e2]
      simp only [St.withAcct, hAccts, hMod, e1]
    · simp only [hLe, ↓reduceIte] at h
      simp at h
theorem grantEq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [hc, ↓reduceIte]
    have hEq : (fun a : Acct => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) (s.accts.getD who noAcct) = (fun a : Acct => { a with accrued := 0, wallet := a.wallet + a.accrued }) (s.accts.getD who noAcct) := by
      have hrfl : s.accts.getD who noAcct = s.acct who := rfl
      rw [hrfl]
    have hMod : s.accts.modify who (fun a : Acct => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) = s.accts.modify who (fun a : Acct => { a with accrued := 0, wallet := a.wallet + a.accrued }) := modCongr s.accts who (fun a : Acct => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) (fun a : Acct => { a with accrued := 0, wallet := a.wallet + a.accrued }) hEq
    rw [hMod]
  · simp only [hc, ↓reduceIte]
theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  cases hU1 : updateCompBorrowIndex s with
  | none =>
    simp [hU1] at h
  | some sB =>
    simp [hU1] at h
    cases hD1 : distributeBorrowerComp sB who with
    | none =>
      simp [hD1] at h
    | some m1 =>
      simp [hD1] at h
      cases hU2 : updateCompSupplyIndex m1 with
      | none =>
        simp [hU2] at h
      | some sS =>
        simp [hU2] at h
        cases hD2 : distributeSupplierComp sS who with
        | none =>
          simp [hD2] at h
        | some m2 =>
          simp [hD2, grantEq] at h
          have hB : comptroller s (.borrowHook who) = some m1 := by simp [comptroller, hU1, hD1]
          have hS : comptroller m1 (.supplyHook who) = some m2 := by simp [comptroller, hU2, hD2]
          have hBm := req_borrow_hook s who m1 hB
          have hSm := req_supply_hook m1 who m2 hS
          refine ⟨m1, m2, hBm, hSm, ?_⟩
          simp [h] at ⊢
theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  cases hSup : decide (s.supplyState.speed = a) with
  | true =>
    have heq : s.supplyState.speed = a := of_decide_eq_true hSup
    simp [heq, setSupplySpeed] at h
    cases hBor : decide (s.borrowState.speed = b) with
    | true =>
      have heqB : s.borrowState.speed = b := of_decide_eq_true hBor
      simp [heqB, setBorrowSpeed] at h
      subst h
      unfold SpeedsSet
      simp [heq, heqB]
    | false =>
      have hneB : s.borrowState.speed ≠ b := of_decide_eq_false hBor
      simp [hneB, setBorrowSpeed] at h
      obtain ⟨s1, hU, rfl⟩ := h
      have hUpd := updBorrowAux s s1 hU
      obtain ⟨hb, e1⟩ := hUpd
      refine ⟨fun heq' => absurd heq heq', fun _ => hb, ?_⟩
      simp [heq, hneB, e1]
  | false =>
    have hne : s.supplyState.speed ≠ a := of_decide_eq_false hSup
    simp [hne, setSupplySpeed] at h
    cases hU : updateCompSupplyIndex s with
    | none =>
      simp [hU] at h
    | some s1 =>
      simp [hU] at h
      have hUpd := updSupplyAux s s1 hU
      obtain ⟨hbS, e1S⟩ := hUpd
      have hMid : ({ s1 with supplyState := { s1.supplyState with speed := a } }).borrowState.speed = s.borrowState.speed := by simp [e1S]
      cases hBor : decide (s.borrowState.speed = b) with
      | true =>
        have heqB : s.borrowState.speed = b := of_decide_eq_true hBor
        simp [setBorrowSpeed, e1S, heqB] at h
        obtain ⟨_, hU2, rfl⟩ := h
        refine ⟨fun _ => hbS, fun heq' => absurd heqB heq', ?_⟩
        simp [hne, heqB, e1S]
      | false =>
        have hneB : s.borrowState.speed ≠ b := of_decide_eq_false hBor
        simp [setBorrowSpeed, e1S, hneB] at h
        obtain ⟨s2, hU2, rfl⟩ := h
        have hUpd2 := updBorrowAux _ s2 hU2
        obtain ⟨hbB, e1B⟩ := hUpd2
        have hbB' : s.borrowState.block ≤ s.blockNumber := by
          simp [e1S] at hbB
          exact hbB
        refine ⟨fun _ => hbS, fun _ => hbB', ?_⟩
        have hTot : totalBorrows ({ s1 with supplyState := { s1.supplyState with speed := a } }) = totalBorrows s := by simp [e1S, totalBorrows]
        simp [hne, hneB, e1S, e1B, hTot, totalBorrows]
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
