import CompRewards.Spec
import ProofForgeFin
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

theorem updSup_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide subChecked fraction
  simp only [h, ↓reduceIte]
  by_cases hU : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [hU, ↓reduceIte] at ⊢
    simp at ⊢
    by_cases hT : 0 < totalSupply s
    · simp [hT]
    · simp [hT, Nat.add_zero]
  · simp only [hU, ↓reduceIte] at ⊢
    simp at ⊢
    have h3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := by
      intro hh
      apply hU
      exact ⟨hh.1, hh.2.1⟩
    simp only [h3, ↓reduceIte] at ⊢
    simp at ⊢
    intro hd
    have hb : s.blockNumber = s.supplyState.block := by omega
    cases s with | mk bn sup bor res ac =>
      simp only at hb hd ⊢
      subst hb
      rfl

theorem updBor_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide subChecked fraction
  simp only [h, ↓reduceIte]
  by_cases hU : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [hU, ↓reduceIte] at ⊢
    simp at ⊢
    by_cases hT : 0 < totalBorrows s
    · simp [hT]
    · simp [hT, Nat.add_zero]
  · simp only [hU, ↓reduceIte] at ⊢
    simp at ⊢
    have h3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := by
      intro hh
      apply hU
      exact ⟨hh.1, hh.2.1⟩
    simp only [h3, ↓reduceIte] at ⊢
    simp at ⊢
    intro hd
    have hb : s.blockNumber = s.borrowState.block := by omega
    cases s with | mk bn sup bor res ac =>
      simp only at hb hd ⊢
      subst hb
      rfl

theorem distSup_start_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0 <;> simp [h0]

theorem distBor_start_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0 <;> simp [h0]

theorem accrueSupply_le (s : St) :
    s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < totalSupply s <;>
    simp [h]

theorem accrueBorrow_le (s : St) :
    s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < totalBorrows s <;>
    simp [h]

theorem accrualStart_le_of_le (rec idx idx' : Nat) (hrec : rec ≤ idx) (hle : idx ≤ idx') :
    accrualStart rec idx' ≤ idx' := by
  unfold accrualStart
  by_cases h0 : rec = 0
  · simp only [h0, ↓reduceIte]
    by_cases h1 : compInitialIndex ≤ idx'
    · simp [h1]
    · simp [h1]
  · simp only [h0, ↓reduceIte]
    exact Nat.le_trans hrec hle

theorem mulDouble_eq_creditFor (units start index : Nat) :
    mulDouble units (index - start) = creditFor units start index := by
  rfl

theorem modify_congr (l : List Acct) (who : Nat) (f1 f2 : Acct → Acct)
    (h : f1 (l.getD who noAcct) = f2 (l.getD who noAcct)) :
    l.modify who f1 = l.modify who f2 := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero] at h
      simp only [List.modify_zero_cons, h]
    | succ n =>
      have h' : f1 (tl.getD n noAcct) = f2 (tl.getD n noAcct) := h
      simp only [List.modify_succ_cons, ih n h']

theorem rec_sup_le (s : St) (who : Account) (hcon : Consistent s) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  have hP : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (hcon.2.2 a ha).1
  have hd : noAcct.supplierIndex ≤ s.supplyState.index := Nat.zero_le _
  exact ProofForgeFin.Accumulator.Market.forall_getD (P := fun a => a.supplierIndex ≤ s.supplyState.index) (l := s.accts) who hP hd

theorem rec_bor_le (s : St) (who : Account) (hcon : Consistent s) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  have hP : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := fun a ha => (hcon.2.2 a ha).2
  have hd : noAcct.borrowerIndex ≤ s.borrowState.index := Nat.zero_le _
  exact ProofForgeFin.Accumulator.Market.forall_getD (P := fun a => a.borrowerIndex ≤ s.borrowState.index) (l := s.accts) who hP hd

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hcon
  cases c with
  | supplyHook who =>
    have hB : s.supplyState.block ≤ s.blockNumber := hcon.1
    let s1 : St := ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)
    have hUpd : updateCompSupplyIndex s = some s1 := updSup_eq s hB
    have hle_idx : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrueSupply_le s
    have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index := rec_sup_le s who hcon
    have hstart : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrualStart_le_of_le _ _ _ hrec hle_idx
    have hstart_le_s1 : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by rw [distSup_start_eq s1 who]; exact hstart
    have hDist : distributeSupplierComp s1 who = some (s1.withAcct who fun a => ({ a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct)) := by unfold distributeSupplierComp subChecked; simp [hstart_le_s1]
    have hComp : comptroller s (.supplyHook who) = some (s1.withAcct who fun a => ({ a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct)) := by simp [comptroller, hUpd, hDist]
    exact Option.isSome_iff_exists.mpr ⟨_, hComp⟩
  | borrowHook who =>
    have hB : s.borrowState.block ≤ s.blockNumber := hcon.2.1
    let s1 : St := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)
    have hUpd : updateCompBorrowIndex s = some s1 := updBor_eq s hB
    have hle_idx : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrueBorrow_le s
    have hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index := rec_bor_le s who hcon
    have hstart : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrualStart_le_of_le _ _ _ hrec hle_idx
    have hstart_le_s1 : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by rw [distBor_start_eq s1 who]; exact hstart
    have hDist : distributeBorrowerComp s1 who = some (s1.withAcct who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) := by unfold distributeBorrowerComp subChecked; simp [hstart_le_s1]
    have hComp : comptroller s (.borrowHook who) = some (s1.withAcct who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) := by simp [comptroller, hUpd, hDist]
    exact Option.isSome_iff_exists.mpr ⟨_, hComp⟩
  | claim who =>
    have hBbor : s.borrowState.block ≤ s.blockNumber := hcon.2.1
    have hBsup : s.supplyState.block ≤ s.blockNumber := hcon.1
    let s1 : St := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)
    have hUpdBor : updateCompBorrowIndex s = some s1 := updBor_eq s hBbor
    have hle_bor : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrueBorrow_le s
    have hrec_bor : (s.acct who).borrowerIndex ≤ s.borrowState.index := rec_bor_le s who hcon
    have hstart_bor : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrualStart_le_of_le _ _ _ hrec_bor hle_bor
    have hstart_le_s1 : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by rw [distBor_start_eq s1 who]; exact hstart_bor
    have hDistBor : distributeBorrowerComp s1 who = some (s1.withAcct who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) := by unfold distributeBorrowerComp subChecked; simp [hstart_le_s1]
    have hrec_sup : (s.acct who).supplierIndex ≤ s.supplyState.index := rec_sup_le s who hcon
    have hle_sup : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrueSupply_le s
    let m1 : St := (s1.withAcct who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct))
    have hDistBor_eq : distributeBorrowerComp s1 who = some m1 := hDistBor
    have hBsup_m1 : m1.supplyState.block ≤ m1.blockNumber := hcon.1
    let s2 : St := ({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St)
    have hUpdSup : updateCompSupplyIndex m1 = some s2 := updSup_eq m1 hBsup_m1
    have hpres1 : (m1.acct who).supplierIndex = (s1.acct who).supplierIndex := by have hm1 : m1 = s1.withAcct who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct) := rfl; simp only [hm1, St.withAcct, St.acct, ProofForgeFin.Ledger.getD_modify]; split; rfl; rfl
    have hpres2 : (s1.acct who).supplierIndex = (s.acct who).supplierIndex := by rfl
    have hrec_sup_m1 : (m1.acct who).supplierIndex ≤ m1.supplyState.index := by rw [hpres1, hpres2]; exact rec_sup_le s who hcon
    have hle_sup_m1 : m1.supplyState.index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := accrueSupply_le m1
    have hstart_sup : accrualStart (m1.acct who).supplierIndex (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := accrualStart_le_of_le _ _ _ hrec_sup_m1 hle_sup_m1
    have hstart_le_s2 : (if (s2.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s2.supplyState.index then compInitialIndex else (s2.acct who).supplierIndex) ≤ s2.supplyState.index := by rw [distSup_start_eq s2 who]; exact hstart_sup
    have hDistSup : distributeSupplierComp s2 who = some (s2.withAcct who fun a => ({ a with supplierIndex := s2.supplyState.index, accrued := a.accrued + mulDouble (s2.acct who).supply (s2.supplyState.index - (if (s2.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s2.supplyState.index then compInitialIndex else (s2.acct who).supplierIndex)) } : Acct)) := by unfold distributeSupplierComp subChecked; simp [hstart_le_s2]
    have hCompClaim : comptroller s (.claim who) = some (grantCompInternal (s2.withAcct who fun a => ({ a with supplierIndex := s2.supplyState.index, accrued := a.accrued + mulDouble (s2.acct who).supply (s2.supplyState.index - (if (s2.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s2.supplyState.index then compInitialIndex else (s2.acct who).supplierIndex)) } : Acct)) who) := by simp [comptroller, claimComp, hUpdBor, hDistBor_eq, hUpdSup, hDistSup]
    exact Option.isSome_iff_exists.mpr ⟨_, hCompClaim⟩
  | setSpeeds a b =>
    have hBsup : s.supplyState.block ≤ s.blockNumber := hcon.1
    have hBbor : s.borrowState.block ≤ s.blockNumber := hcon.2.1
    let t1 : St := ({ s with supplyState := if s.supplyState.speed = a then s.supplyState else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St)
    have hSup : setSupplySpeed s a = some t1 := by
      unfold setSupplySpeed
      by_cases hSa : s.supplyState.speed ≠ a
      · simp [hSa, updSup_eq s hBsup, t1]
      · have heq : s.supplyState.speed = a := by omega
        simp [heq, t1]
    have hBbor_t1 : t1.borrowState.block ≤ t1.blockNumber := hBbor
    have hBor : setBorrowSpeed t1 b = some ({ t1 with borrowState := if t1.borrowState.speed = b then t1.borrowState else ({ accrueSide t1.borrowState t1.blockNumber (totalBorrows t1) with speed := b } : Side) } : St) := by
      unfold setBorrowSpeed
      by_cases hSb : t1.borrowState.speed ≠ b
      · simp [hSb, updBor_eq t1 hBbor_t1]
      · have heq : t1.borrowState.speed = b := by omega
        simp [heq]
    have hComp : comptroller s (.setSpeeds a b) = some (({ t1 with borrowState := if t1.borrowState.speed = b then t1.borrowState else ({ accrueSide t1.borrowState t1.blockNumber (totalBorrows t1) with speed := b } : Side) } : St)) := by simp [comptroller, setCompSpeedInternal, hSup, hBor]
    exact Option.isSome_iff_exists.mpr ⟨_, hComp⟩
theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases e1 : updateCompSupplyIndex s with
  | none => simp [e1] at h
  | some s1 =>
    simp [e1] at h
    have hB : s.supplyState.block ≤ s.blockNumber := by
      by_cases hB : s.supplyState.block ≤ s.blockNumber
      · exact hB
      · have hn : updateCompSupplyIndex s = none := by unfold updateCompSupplyIndex subChecked; simp only [hB, ↓reduceIte]
        rw [hn] at e1
        simp at e1
    have e1eq : s1 = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by have he := updSup_eq s hB; rw [e1] at he; simp at he; exact he
    have hstart_le : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by
      by_cases hle : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index
      · exact hle
      · unfold distributeSupplierComp subChecked at h
        simp only [hle, ↓reduceIte] at h
        simp at h
    unfold distributeSupplierComp subChecked at h
    simp only [hstart_le, ↓reduceIte] at h
    have h_eq : (s1.withAcct who fun a => ({ a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct)) = s' := by cases h; rfl
    refine ⟨hB, ?_, ?_⟩
    · have h2 := hstart_le
      rw [distSup_start_eq s1 who] at h2
      rw [e1eq] at h2
      exact h2
    · have haccts : s1.accts = s.accts := by rw [e1eq]
      have hacct : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
      have hidx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [e1eq]
      have hstart : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) = accrualStart (s1.acct who).supplierIndex s1.supplyState.index := distSup_start_eq s1 who
      have hval : (fun a => ({ a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct)) (s.acct who) = (fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct)) (s.acct who) := by rw [hstart, hacct, hidx]; rfl
      have hmod : s1.accts.modify who (fun a => ({ a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct)) = s.accts.modify who (fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct)) := by rw [haccts]; apply modify_congr; exact hval
      have h_with : s1.withAcct who (fun a => ({ a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct)) = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who (fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct)) } : St) := by unfold St.withAcct; rw [hmod, e1eq]
      exact h_eq.symm.trans h_with
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases e1 : updateCompBorrowIndex s with
  | none => simp [e1] at h
  | some s1 =>
    simp [e1] at h
    have hB : s.borrowState.block ≤ s.blockNumber := by
      by_cases hB : s.borrowState.block ≤ s.blockNumber
      · exact hB
      · have hn : updateCompBorrowIndex s = none := by unfold updateCompBorrowIndex subChecked; simp only [hB, ↓reduceIte]
        rw [hn] at e1
        simp at e1
    have e1eq : s1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by have he := updBor_eq s hB; rw [e1] at he; simp at he; exact he
    have hstart_le : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by
      by_cases hle : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index
      · exact hle
      · unfold distributeBorrowerComp subChecked at h
        simp only [hle, ↓reduceIte] at h
        simp at h
    unfold distributeBorrowerComp subChecked at h
    simp only [hstart_le, ↓reduceIte] at h
    have h_eq : (s1.withAcct who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) = s' := by cases h; rfl
    refine ⟨hB, ?_, ?_⟩
    · have h2 := hstart_le
      rw [distBor_start_eq s1 who] at h2
      rw [e1eq] at h2
      exact h2
    · have haccts : s1.accts = s.accts := by rw [e1eq]
      have hacct : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
      have hidx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [e1eq]
      have hstart : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) = accrualStart (s1.acct who).borrowerIndex s1.borrowState.index := distBor_start_eq s1 who
      have hval : (fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) (s.acct who) = (fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } : Acct)) (s.acct who) := by rw [hstart, hacct, hidx]; rfl
      have hmod : s1.accts.modify who (fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) = s.accts.modify who (fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } : Acct)) := by rw [haccts]; apply modify_congr; exact hval
      have h_with : s1.withAcct who (fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who (fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } : Acct)) } : St) := by unfold St.withAcct; rw [hmod, e1eq]
      exact h_eq.symm.trans h_with
theorem grant_eq : ∀ (s : St) (who : Account), grantCompInternal s who = grant s who := by
  intro s who
  unfold grantCompInternal grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · have h1 : (s.acct who).accrued > 0 := h.1
    simp only [h, h1, ↓reduceIte] at ⊢
    simp at ⊢
    apply modify_congr
    rfl
  · have h1 : ¬((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) := h
    simp only [h, h1, ↓reduceIte] at ⊢
theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  cases e1 : updateCompBorrowIndex s with
  | none => simp [e1] at h
  | some t1 =>
    simp [e1] at h
    cases e2 : distributeBorrowerComp t1 who with
    | none => simp [e2] at h
    | some m1 =>
      simp [e2] at h
      cases e3 : updateCompSupplyIndex m1 with
      | none => simp [e3] at h
      | some t2 =>
        simp [e3] at h
        cases e4 : distributeSupplierComp t2 who with
        | none => simp [e4] at h
        | some m2 =>
          simp [e4] at h
          have hgrant : grantCompInternal m2 who = s' := by cases h; rfl
          have hb : comptroller s (.borrowHook who) = some m1 := by simp [comptroller, e1, e2]
          have hs : comptroller m1 (.supplyHook who) = some m2 := by simp [comptroller, e3, e4]
          have hBor := req_borrow_hook s who m1 hb
          have hSup := req_supply_hook m1 who m2 hs
          exact ⟨m1, m2, hBor, hSup, by rw [←hgrant, grant_eq]⟩
theorem setSupply_eq (s : St) (a : Nat) (s1 : St) (h : setSupplySpeed s a = some s1) : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧ s1 = ({ s with supplyState := if s.supplyState.speed = a then s.supplyState else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St) := by
  unfold setSupplySpeed at h
  by_cases hSa : s.supplyState.speed ≠ a
  · simp [hSa] at h
    have hB : s.supplyState.block ≤ s.blockNumber := by
      by_cases hB : s.supplyState.block ≤ s.blockNumber
      · exact hB
      · have hn : updateCompSupplyIndex s = none := by unfold updateCompSupplyIndex subChecked; simp only [hB, ↓reduceIte]
        simp [hn, hSa] at h
    have he := updSup_eq s hB
    simp [he] at h
    cases h
    refine ⟨fun _ => hB, ?_⟩
    simp [hSa]
  · have heq : s.supplyState.speed = a := by omega
    simp [heq] at h
    cases h
    refine ⟨fun hcon => False.elim (hSa hcon), ?_⟩
    simp [heq]
theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller, setCompSpeedInternal] at h
  cases e1 : setSupplySpeed s a with
  | none => simp [e1] at h
  | some t1 =>
    simp [e1] at h
    cases e2 : setBorrowSpeed t1 b with
    | none => simp [e2] at h
    | some t2 =>
      simp [e2] at h
      subst h
      have hSup := setSupply_eq s a t1 e1
      have hBor : (t1.borrowState.speed ≠ b → t1.borrowState.block ≤ t1.blockNumber) ∧ t2 = ({ t1 with borrowState := if t1.borrowState.speed = b then t1.borrowState else ({ accrueSide t1.borrowState t1.blockNumber (totalBorrows t1) with speed := b } : Side) } : St) := by
        unfold setBorrowSpeed at e2
        by_cases hSb : t1.borrowState.speed ≠ b
        · simp [hSb] at e2
          have hB : t1.borrowState.block ≤ t1.blockNumber := by
            by_cases hB : t1.borrowState.block ≤ t1.blockNumber
            · exact hB
            · have hn : updateCompBorrowIndex t1 = none := by unfold updateCompBorrowIndex subChecked; simp only [hB, ↓reduceIte]
              simp [hn] at e2
          have he := updBor_eq t1 hB
          simp [he] at e2
          cases e2
          refine ⟨fun _ => hB, ?_⟩
          simp [hSb]
        · have heq : t1.borrowState.speed = b := by omega
          simp [heq] at e2
          cases e2
          refine ⟨fun hcon => False.elim (hSb hcon), ?_⟩
          simp [heq]
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exact (hSup.1 hne)
      · intro hne
        have h1 : t1.borrowState.speed = s.borrowState.speed := by rw [hSup.2]
        have h2 : t1.borrowState.block = s.borrowState.block := by rw [hSup.2]
        have h3 : t1.blockNumber = s.blockNumber := by rw [hSup.2]
        have h4 : totalBorrows t1 = totalBorrows s := by rw [hSup.2]; rfl
        rw [h1, h2, h3] at hBor
        exact (hBor.1 hne)
      · have h1 : t1.borrowState.speed = s.borrowState.speed := by rw [hSup.2]
        have h2 : t1.borrowState.block = s.borrowState.block := by rw [hSup.2]
        have h3 : t1.blockNumber = s.blockNumber := by rw [hSup.2]
        have h4 : totalBorrows t1 = totalBorrows s := by unfold totalBorrows; rw [hSup.2]
        have h5 : t1.accts = s.accts := by rw [hSup.2]
        rw [h1, h2, h3, h4, h5] at hBor
        rw [hBor.2, hSup.2]
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
