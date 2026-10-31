import CompRewards.Spec
import ProofForgeFin.DeFi.Distributor
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

def fooTest123 : Nat := 1

def testSt123 : St := { blockNumber := 100, supplyState := { index := 0, block := 0, speed := 0 }, borrowState := { index := 0, block := 0, speed := 0 }, reserve := 100000000000000000000000, accts := [{ supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def testClaim123 : Option St := comptroller testSt123 (.claim 0)

def upTest123 : St := upgrade { blockNumber := 10, compSpeed := 0, supplyIndex := 0, supplyBlock := 10, borrowIndex := 0, borrowBlock := 10, supplyStart := 0, borrowStart := 0, reserve := 1000000000000000000000000000000, accts := [{ supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def afterAdv123 : St := { upTest123 with blockNumber := upTest123.blockNumber + 139 }

def claimRes123 : Option St := comptroller afterAdv123 (.claim 0)
#check upTest123
#check claimRes123

def checkClaimVal123 : Nat := match claimRes123 with | some s => (s.acct 0).accrued + (s.acct 0).wallet | none => 999999

theorem checkClaimVal123_is_zero : checkClaimVal123 = 0 := by rfl

def dummyOk123 : Nat := 0

def probeA123 : Bool := true
#check @List.getD
#check @List.modify
#check Consistent
#check St.acct
#check subChecked

def probeB123 : Nat := 1

theorem myHelper123 : 1 + 1 = 2 := rfl

theorem myTestHelperAux : True := trivial

theorem updSupplyEqAux2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (subChecked s.blockNumber s.supplyState.block) = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [h]

theorem borrow_update_eq_aux2 (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem borrow_delta_unfold (s : St) :
    (subChecked s.blockNumber s.borrowState.block) =
    if s.borrowState.block ≤ s.blockNumber then some (s.blockNumber - s.borrowState.block) else none := by
  unfold subChecked; rfl

theorem aux_updateSupply_eq (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem aux_probe_simp (s : St) : totalSupply s = (s.accts.map Acct.supply).sum := by
  simp only [totalSupply]

theorem simpTest (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧ True := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp [hb] at h
    exact ⟨hb, trivial⟩
  · simp [hb] at h

theorem pot_test_aux : doubleScale = 10 ^ 36 := rfl
#check ProofForgeFin.DeFi.Rewards.credit
#check ProofForgeFin.DeFi.Rewards.firstStart
#check ProofForgeFin.DeFi.Rewards.pending
#check @ProofForgeFin.DeFi.Distributor.State
#check ProofForgeFin.DeFi.Rewards.credit_anti_start

def pendingSupply (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)

def pendingBorrow (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)

def unindexedSupply (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def unindexedBorrow (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def potTo (s : St) (who : Account) : Nat :=
  (s.creditedTo who) * doubleScale + pendingSupply s who + pendingBorrow s who +
  (if 0 < (s.acct who).supply then unindexedSupply s * doubleScale else 0) +
  (if 0 < (s.acct who).borrow then unindexedBorrow s * doubleScale else 0)

theorem potTo_ge_credited (s : St) (who : Account) :
  (s.creditedTo who) * doubleScale ≤ potTo s who := by
  unfold potTo pendingSupply pendingBorrow
  omega

def checkListLemmasAux999 : Nat := 0
#check @List.getD
#check @List.modify
#check @List.length_modify
#check @List.getElem_mem
#check @Option.isSome

theorem updSupply_some_aux2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  unfold updateCompSupplyIndex subChecked
  simp only [h, ↓reduceIte]
  by_cases hd : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hd, and_self, ↓reduceIte]
    rfl
  · simp only [hd, ↓reduceIte]
    by_cases hd2 : 0 < s.blockNumber - s.supplyState.block
    · simp [hd2]
    · simp [hd2]

theorem updBorrow_some_aux2 (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  unfold updateCompBorrowIndex subChecked
  simp only [h, ↓reduceIte]
  by_cases hd : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hd, and_self, ↓reduceIte]
    rfl
  · simp only [hd, ↓reduceIte]
    by_cases hd2 : 0 < s.blockNumber - s.borrowState.block
    · simp [hd2]
    · simp [hd2]

theorem accrualStart_le_index2 (recorded index : Nat) (h : recorded = 0 ∨ recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp only [hr]
    by_cases hi : compInitialIndex ≤ index
    · simp only [if_pos hi]
      exact hi
    · simp only [if_neg hi]
      exact Nat.zero_le index
  · simp only [hr]
    cases h with
    | inl h0 => exact absurd h0 hr
    | inr hle => exact hle

theorem getD_default_of_le : ∀ (l : List Acct) (n : Nat), l.length ≤ n → l.getD n noAcct = noAcct := by
  intro l
  induction l with
  | nil => intro n h; simp [List.getD]
  | cons hd tl ih =>
    intro n h
    cases n with
    | zero => simp at h
    | succ n => simp [List.getD]; exact ih n (by simp at h ⊢; omega)







theorem plan0_distributeSupplier_exists (s : St) (who : Account)
    (h : (s.acct who).supplierIndex = 0 ∨
      (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' ∧
      s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  have hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
    by_cases hc : ((s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index)
    · simp only [hc, ↓reduceIte]
      exact hc.2
    · simp only [hc]
      rcases h with h0 | hle2
      · rw [h0]; exact Nat.zero_le _
      · exact hle2
  have hsub : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = some (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) := by
    unfold subChecked
    simp only [hle, ↓reduceIte]
  unfold distributeSupplierComp
  simp only at hsub ⊢
  rw [hsub]
  exact ⟨_, rfl, rfl, rfl, rfl⟩


theorem plan0_distributeBorrower_exists (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' ∧
      (s'.acct who).supplierIndex = (s.acct who).supplierIndex ∧
      s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  sorry

theorem plan0_consistent_acct_bounds_aux_mem : ∀ (l : List Acct) (n : Nat), n < l.length → l.getD n noAcct ∈ l := by
  intro l
  induction l with
  | nil => intro n h; simp at h
  | cons hd tl ih =>
    intro n h
    cases n with
    | zero => simp [List.getD]
    | succ n => simp [List.getD]; exact Or.inr (ih n (by simp at h ⊢; omega))

theorem plan0_consistent_acct_bounds (s : St) (who : Account) (h : Consistent s) :
    ((s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index) ∧
      ((s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index) := by
  unfold Consistent at h
  obtain ⟨_, _, hall⟩ := h
  by_cases hwho : who < s.accts.length
  · have hmem : s.acct who ∈ s.accts := by
      unfold St.acct
      exact plan0_consistent_acct_bounds_aux_mem s.accts who hwho
    have hb := hall (s.acct who) hmem
    exact ⟨Or.inr hb.1, Or.inr hb.2⟩
  · have hle : s.accts.length ≤ who := Nat.le_of_not_gt hwho
    have hget : s.accts.getD who noAcct = noAcct := getD_default_of_le s.accts who hle
    have hacct : s.acct who = noAcct := by unfold St.acct; exact hget
    rw [hacct]
    exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem plan0_updateSupply_exists (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' ∧
      s.supplyState.index ≤ s'.supplyState.index ∧
      s'.accts = s.accts ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompSupplyIndex
  rw [hsub]
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc, ↓reduceIte]
    exact ⟨_, rfl, Nat.le_add_right _ _, rfl, rfl, rfl⟩
  · simp only [hc, ↓reduceIte]
    by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩

theorem plan0_updateBorrow_exists (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' ∧
      s.borrowState.index ≤ s'.borrowState.index ∧
      s'.accts = s.accts ∧ s'.supplyState = s.supplyState ∧
      s'.blockNumber = s.blockNumber := by
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompBorrowIndex
  rw [hsub]
  by_cases hc : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hc, ↓reduceIte]
    exact ⟨_, rfl, Nat.le_add_right _ _, rfl, rfl, rfl⟩
  · simp only [hc, ↓reduceIte]
    by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩

theorem tmpProbeThm : True := trivial

theorem tmpExploreModify : List.modify [1,2] 0 (· + 1) = [2,2] := by rfl

theorem tmpProbeThm3 : True := trivial

theorem tmpProbeThm4 : True := trivial

theorem tmpP5 : True := trivial



theorem plan1_borrower_adjusted_le (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by sorry







theorem plan1_subChecked_of_le (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by unfold subChecked; simp [h]

theorem plan1_borrower_adjusted_le2 (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
  by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · rw [if_pos hc]
    exact hc.2
  · rw [if_neg hc]
    rcases h with h0 | hle
    · rw [h0]
      exact Nat.zero_le _
    · exact hle

theorem plan1_borrower_adjusted_le_aux_tmp : True := trivial

theorem plan1_modify_getD_supplierIndex (l : List Acct) (n : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD n noAcct).supplierIndex = (l.getD n noAcct).supplierIndex := by
  have h := ProofForgeFin.Ledger.getD_modify l n n f noAcct
  by_cases hn : n < l.length
  · have h2 : (l.modify n f).getD n noAcct = f (l.getD n noAcct) := by
      rw [h]
      simp [hn]
    rw [h2, hf]
  · have h2 : (l.modify n f).getD n noAcct = l.getD n noAcct := by
      rw [h]
      simp [hn]
    rw [h2]

theorem plan1_withAcct_supplierIndex (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.withAcct St.acct
  simp only
  exact plan1_modify_getD_supplierIndex s.accts who f hf

theorem plan1_distributeBorrower_supplierIndex (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by
  have hunfold : distributeBorrowerComp s who =
    match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
    | none => (none : Option St)
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex }) := rfl
  rw [hunfold] at h
  cases heq : subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
  | none => simp [heq] at h
  | some d =>
    simp [heq] at h
    rw [← h]
    apply plan1_withAcct_supplierIndex
    intro a
    rfl

theorem plan0_distributeBorrower_exists_PROBE (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' ∧
      (s'.acct who).supplierIndex = (s.acct who).supplierIndex ∧
      s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  have hle : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index :=
    plan1_borrower_adjusted_le2 s who h
  have hsub : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = some (s.borrowState.index - (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)) :=
    plan1_subChecked_of_le _ _ hle
  unfold distributeBorrowerComp
  simp only [hsub]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
  apply plan1_withAcct_supplierIndex
  intro a
  rfl

theorem borrowerPreserveClean (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts who who f noAcct
  have h1 : ((s.withAcct who f).acct who) = ((s.accts.modify who f).getD who noAcct) := rfl
  have h2 : (s.acct who) = (s.accts.getD who noAcct) := rfl
  rw [h1, h2]
  rw [hmod]
  by_cases hn : who < s.accts.length
  · simp [hn, hf]
  · simp [hn]

theorem testPreserveGeneric (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.withAcct St.acct
  simp only
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts who who f noAcct
  rw [hmod]
  by_cases hn : who < s.accts.length
  · simp [hn, hf]
  · simp [hn]

theorem probe_ledger_lemmas : True := trivial
#check ProofForgeFin.Ledger.getD_modify
#check ProofForgeFin.DeFi.Distributor.State

theorem supplyBound_transfer_aux (s s1 : St) (who : Account)
    (haccts : s1.accts = s.accts) (hle : s.supplyState.index ≤ s1.supplyState.index)
    (h : (s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (s1.acct who).supplierIndex = 0 ∨ (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
  have heq : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
  rw [heq]
  rcases h with h0 | hle2
  · exact Or.inl h0
  · exact Or.inr (Nat.le_trans hle2 hle)

theorem borrowBound_transfer_aux (s s1 : St) (who : Account)
    (haccts : s1.accts = s.accts) (hle : s.borrowState.index ≤ s1.borrowState.index)
    (h : (s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (s1.acct who).borrowerIndex = 0 ∨ (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
  have heq : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
  rw [heq]
  rcases h with h0 | hle2
  · exact Or.inl h0
  · exact Or.inr (Nat.le_trans hle2 hle)

theorem updSupply_isSome_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := updSupply_some_aux2 s h

theorem updBorrow_isSome_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := updBorrow_some_aux2 s h

theorem distSup_isSome_of_bound (s : St) (who : Account)
    (h : (s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome = true := by
  obtain ⟨s', hs', _, _, _⟩ := plan0_distributeSupplier_exists s who h
  rw [hs']
  rfl

theorem distBor_isSome_of_bound (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome = true := by
  obtain ⟨s', hs', _, _, _, _⟩ := plan0_distributeBorrower_exists_PROBE s who h
  rw [hs']
  rfl

theorem updSupply_char_aux (s : St) (mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem updSupply_inv (s : St) (mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid h
  unfold updateCompSupplyIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem supplyHook_decomp_ok (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ mid, updateCompSupplyIndex s = some mid ∧ distributeSupplierComp mid who = some s' := by
  unfold comptroller at h
  cases hup : updateCompSupplyIndex s with
  | none =>
    simp [hup] at h
  | some mid =>
    simp [hup] at h
    exact ⟨mid, rfl, h⟩

theorem plan2_accrualStart_adjusted (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp only [hr, true_and]
    by_cases hi : compInitialIndex ≤ index <;> simp [hi]
  · simp [hr]




theorem plan2_distributeSupplier_char (mid : St) (who : Account) (s' : St)
    (h : distributeSupplierComp mid who = some s') :
    accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤
        mid.supplyState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            supplierIndex := mid.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex mid.supplyState.index)
              mid.supplyState.index } } := by
  sorry



theorem plan2_updateSupply_accrueSide (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid h
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompSupplyIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide at ⊢
  by_cases hdb : 0 < s.blockNumber - s.supplyState.block
  · by_cases hsp : 0 < s.supplyState.speed
    · by_cases htot : 0 < totalSupply s
      · simp only [hdb, hsp, htot, and_self, ↓reduceIte] at ⊢
        have hrw : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        unfold fraction at h
        cases h
        rfl
      · have hrw : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        have hfalse : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
          simp [htot]
        simp only [hfalse, ↓reduceIte] at ⊢
        cases h
        rfl
    · have hrw : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by
        simp [hsp]
      simp only [hrw, ↓reduceIte] at h
      have hfalse : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        simp [hsp]
      simp only [hfalse, ↓reduceIte] at ⊢
      simp only [hdb, ↓reduceIte] at h ⊢
      cases h
      rfl
  · have hrw : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by
      simp [hdb]
    simp only [hrw, ↓reduceIte] at h
    have hfalse : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
      simp [hdb]
    simp only [hfalse, ↓reduceIte] at ⊢
    simp only [hdb, ↓reduceIte] at h ⊢
    cases h
    have heq : s.blockNumber = s.supplyState.block := by omega
    cases s with
    | mk bn sup bor res accts =>
      simp only at heq ⊢
      cases sup with
      | mk idx blk spd =>
        simp only at heq ⊢
        subst heq
        rfl

theorem snippet_probe_modify_eq : True := trivial
#check @List.modify
#check @List.getD

theorem snippet_modify_congr_test (l : List Acct) (n : Nat) (f1 f2 : Acct → Acct)
    (h : f1 (l.getD n noAcct) = f2 (l.getD n noAcct)) :
    l.modify n f1 = l.modify n f2 := by
  induction l generalizing n with
  | nil =>
    cases n with
    | zero => simp
    | succ n => simp
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp [List.getD] at h
      simp [h]
    | succ n =>
      simp [List.getD] at h
      simp [ih n h]

theorem plan2_distributeSupplier_char_aux_tmp2 : True := trivial
#check @snippet_modify_congr_test
#check distributeSupplierComp
#check subChecked
#check mulDouble
#check creditFor
#check accrualStart







theorem plan3_modify_supplier_credit (l : List Acct) (n idx : Nat) :
    l.modify n (fun a => { a with
        supplierIndex := idx,
        accrued := a.accrued + mulDouble (l.getD n noAcct).supply
          (idx - accrualStart (l.getD n noAcct).supplierIndex idx) }) =
    l.modify n (fun a => { a with
        supplierIndex := idx,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex idx) idx }) := by sorry



theorem plan3_subChecked_some_inv_fix : ∀ (a b d : Nat), subChecked a b = some d → b ≤ a ∧ d = a - b := by
  intro a b d h
  unfold subChecked at h
  by_cases hb : b ≤ a
  · simp only [hb, ↓reduceIte] at h
    cases h
    exact ⟨hb, rfl⟩
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem plan3_subChecked_some_inv (a b d : Nat) (h : subChecked a b = some d) :
    b ≤ a ∧ d = a - b := by
  unfold subChecked at h
  by_cases hb : b ≤ a
  · simp only [hb, ↓reduceIte] at h
    cases h
    exact ⟨hb, rfl⟩
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem plan3_supplier_adjusted_eq_accrualStart_check (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hr : recorded = 0 <;> simp [hr]

theorem plan3_supplier_adjusted_eq_accrualStart (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hr : recorded = 0 <;> simp [hr]

theorem plan3_mulDouble_eq_creditFor (units start index : Nat) :
    mulDouble units (index - start) = creditFor units start index := by
  unfold mulDouble creditFor
  rfl

theorem beta_probe1 (l : List Acct) (n idx : Nat) :
    (fun a : Acct => ({ a with supplierIndex := idx } : Acct)) (l.getD n noAcct) =
    ({ (l.getD n noAcct) with supplierIndex := idx } : Acct) := by rfl

theorem probe_modify_nil (idx : Nat) (n : Nat) :
    List.modify ([] : List Acct) n (fun a => ({ a with supplierIndex := idx } : Acct)) = [] := by
  cases n <;> rfl

theorem plan3_withAcct_eq_modify (s : St) (who : Account) (f : Acct → Acct) :
    s.withAcct who f = { s with accts := s.accts.modify who f } := by rfl

theorem plan2_distributeSupplier_char_test_tmp : True := trivial

theorem probe_congr_goal2 (mid : St) (who : Account) (d : Nat)
    (hmul : mulDouble (mid.acct who).supply d =
          creditFor (mid.acct who).supply (accrualStart (mid.acct who).supplierIndex mid.supplyState.index) mid.supplyState.index) :
    (fun a : Acct => ({ a with supplierIndex := mid.supplyState.index, accrued := a.accrued + mulDouble (mid.acct who).supply d } : Acct)) (mid.accts.getD who noAcct) =
    (fun a : Acct => ({ a with supplierIndex := mid.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex mid.supplyState.index) mid.supplyState.index } : Acct)) (mid.accts.getD who noAcct) := by
  have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
  simp only [← hacct, hmul]

theorem plan2_dist_char_PROOFTEST4 (mid : St) (who : Account) (s' : St)
    (h : distributeSupplierComp mid who = some s') :
    accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤
        mid.supplyState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            supplierIndex := mid.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex mid.supplyState.index)
              mid.supplyState.index } } := by
  have hadj : (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) =
      accrualStart (mid.acct who).supplierIndex mid.supplyState.index := by
    rw [plan3_supplier_adjusted_eq_accrualStart]
  unfold distributeSupplierComp at h
  simp only at h
  cases hc : subChecked mid.supplyState.index
      (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).supply d =
          creditFor (mid.acct who).supply (accrualStart (mid.acct who).supplierIndex mid.supplyState.index) mid.supplyState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with supplierIndex := mid.supplyState.index, accrued := a.accrued + mulDouble (mid.acct who).supply d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            supplierIndex := mid.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex mid.supplyState.index)
              mid.supplyState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith







theorem plan4_supply_eq_transfer (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          supplierIndex := mid.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex mid.supplyState.index)
            mid.supplyState.index } }) :
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  subst hmid
  exact heq


theorem plan4_acct_eq_check_tmp : ∀ (s mid : St) (who : Account),
    updateCompSupplyIndex s = some mid → mid.acct who = s.acct who := by
  intro s mid who h
  have haccts : mid.accts = s.accts := updSupply_inv s mid h
  unfold St.acct
  rw [haccts]

theorem plan4_updateSupply_acct_eq (s mid : St) (who : Account)
    (h : updateCompSupplyIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updSupply_inv s mid h
  unfold St.acct
  rw [haccts]

theorem plan4_updateSupply_supplyState_eq (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by
  have hmid := plan2_updateSupply_accrueSide s mid h
  rw [hmid]

theorem plan4_supply_bound_transfer (s mid : St) (who : Account)
    (hacct : mid.acct who = s.acct who)
    (hstate : mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s))
    (hle : accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤
        mid.supplyState.index) :
    accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  rw [hacct, hstate] at hle
  exact hle

theorem tmp_snippet_ok : True := trivial

theorem tmpA1 : True := trivial

theorem plan4_aux_test1 (s mid : St) (hmid : mid = { s with supplyState := s.supplyState }) : mid.accts = s.accts := by rw [hmid]

theorem tmpRwTest (a b : Nat) (h : a = b) : a = b := by rw [h]

theorem tmpShort : 1 = 1 := rfl

theorem tmpLineTest : True := trivial

theorem tmpC1 : True := trivial

theorem tmpC2 : True := trivial

theorem plan2_supplyDistributed_of_steps2 (s : St) (who : Account) (mid s' : St)
    (hup : updateCompSupplyIndex s = some mid)
    (hdist : distributeSupplierComp mid who = some s') :
    SupplyDistributed s who s' := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid hup
  have hmid : mid = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    plan2_updateSupply_accrueSide s mid hup
  have hchar := plan2_dist_char_PROOFTEST4 mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have hacct : mid.acct who = s.acct who := plan4_updateSupply_acct_eq s mid who hup
  have hstate : mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) :=
    plan4_updateSupply_supplyState_eq s mid hup
  have hle : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    plan4_supply_bound_transfer s mid who hacct hstate hle_mid
  have heq : s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } :=
    plan4_supply_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan4_supply_eq_transfer3 (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          supplierIndex := mid.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex mid.supplyState.index)
            mid.supplyState.index } }) :
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  subst hmid
  exact heq

theorem plan2_supplyDistributed_of_steps (s : St) (who : Account) (mid s' : St)
    (hup : updateCompSupplyIndex s = some mid)
    (hdist : distributeSupplierComp mid who = some s') :
    SupplyDistributed s who s' :=
  plan2_supplyDistributed_of_steps2 s who mid s' hup hdist

theorem bh_parse_test (mid : St) (who : Account) :
    True := by
  have h : ∀ (s' : St), BorrowDistributed mid who s' → True := fun _ _ => trivial
  trivial

theorem bh_struct_test (mid : St) (who : Account) :
    mid.accts.modify who (fun a => ({ a with borrowerIndex := mid.borrowState.index } : Acct)) =
    mid.accts.modify who (fun a => ({ a with borrowerIndex := mid.borrowState.index } : Acct)) := by
  rfl



theorem plan5_distributeBorrower_char (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    unfold accrualStart
    by_cases hr : (mid.acct who).borrowerIndex = 0 <;> simp [hr]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith


theorem plan5_updateBorrow_accrueSide (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide at ⊢
  by_cases hdb : 0 < s.blockNumber - s.borrowState.block
  · by_cases hsp : 0 < s.borrowState.speed
    · by_cases htot : 0 < totalBorrows s
      · simp only [hdb, hsp, htot, and_self, ↓reduceIte] at ⊢
        have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        unfold fraction at h
        cases h
        rfl
      · have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          simp [htot]
        simp only [hfalse, ↓reduceIte] at ⊢
        cases h
        rfl
    · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
        simp [hsp]
      simp only [hrw, ↓reduceIte] at h
      have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [hsp]
      simp only [hfalse, ↓reduceIte] at ⊢
      simp only [hdb, ↓reduceIte] at h ⊢
      cases h
      rfl
  · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
      simp [hdb]
    simp only [hrw, ↓reduceIte] at h
    have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
      simp [hdb]
    simp only [hfalse, ↓reduceIte] at ⊢
    simp only [hdb, ↓reduceIte] at h ⊢
    cases h
    have heq : s.blockNumber = s.borrowState.block := by omega
    cases s with
    | mk bn sup bor res accts =>
      simp only at heq ⊢
      cases bor with
      | mk idx blk spd =>
        simp only at heq ⊢
        subst heq
        rfl


theorem plan5_borrow_eq_transfer (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          borrowerIndex := mid.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex mid.borrowState.index)
            mid.borrowState.index } }) :
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  subst hmid
  exact heq


theorem plan5_borrowDistributed_of_steps (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by sorry



theorem plan5_borrower_adjusted_eq_accrualStart (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hr : recorded = 0 <;> simp [hr]

theorem plan5_distributeBorrower_char_PROBE (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    rw [plan5_borrower_adjusted_eq_accrualStart]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan5_distributeBorrower_char_fix (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    rw [plan5_borrower_adjusted_eq_accrualStart]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan5_char_selfcontained (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    unfold accrualStart
    by_cases hr : (mid.acct who).borrowerIndex = 0 <;> simp [hr]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan5_updateBorrow_accrueSide_tmpProbe : True := trivial

theorem plan5_updateBorrow_accrueSide_test (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide at ⊢
  by_cases hdb : 0 < s.blockNumber - s.borrowState.block
  · by_cases hsp : 0 < s.borrowState.speed
    · by_cases htot : 0 < totalBorrows s
      · simp only [hdb, hsp, htot, and_self, ↓reduceIte] at ⊢
        have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        unfold fraction at h
        cases h
        rfl
      · have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          simp [htot]
        simp only [hfalse, ↓reduceIte] at ⊢
        cases h
        rfl
    · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
        simp [hsp]
      simp only [hrw, ↓reduceIte] at h
      have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [hsp]
      simp only [hfalse, ↓reduceIte] at ⊢
      simp only [hdb, ↓reduceIte] at h ⊢
      cases h
      rfl
  · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
      simp [hdb]
    simp only [hrw, ↓reduceIte] at h
    have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
      simp [hdb]
    simp only [hfalse, ↓reduceIte] at ⊢
    simp only [hdb, ↓reduceIte] at h ⊢
    cases h
    have heq : s.blockNumber = s.borrowState.block := by omega
    cases s with
    | mk bn sup bor res accts =>
      simp only at heq ⊢
      cases bor with
      | mk idx blk spd =>
        simp only at heq ⊢
        subst heq
        rfl

theorem plan5_updateBorrow_accrueSide_proof2 : True := trivial

theorem plan5_borrow_eq_transfer_fix_tmp (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          borrowerIndex := mid.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex mid.borrowState.index)
            mid.borrowState.index } }) :
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  subst hmid
  exact heq

theorem updBorrow_inv_test (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan5_updateBorrow_acct_eq_aux (s mid : St) (who : Account)
    (h : updateCompBorrowIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid h
  unfold St.acct
  rw [haccts]

theorem plan5_updateBorrow_state_eq_aux (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
  have hmid := plan5_updateBorrow_accrueSide s mid h
  rw [hmid]

theorem plan5_borrow_bound_transfer_aux (s mid : St) (who : Account)
    (hacct : mid.acct who = s.acct who)
    (hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s))
    (hle : accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index) :
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  rw [hacct, hstate] at hle
  exact hle

theorem plan5_borrowDistributed_aux_final (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid hup
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer_fix_tmp s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan5_borrowDistributed_of_steps_aux_check (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid hup
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer_fix_tmp s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem check_aux_present : True := by
  have h := plan5_borrowDistributed_of_steps_aux_check
  trivial

theorem plan5_borrowDistributed_of_steps_direct (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' :=
  plan5_borrowDistributed_of_steps_aux_check s who mid s' hup hdist

theorem plan5_inline_accts_check (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan6_borrow_update_accts (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl


theorem plan6_borrow_mid_acct (s mid : St) (who : Account)
    (h : updateCompBorrowIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid h
  unfold St.acct
  rw [haccts]








theorem plan6_borrow_update_accts_check_tmp (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan6_borrow_update_accts_fixed (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan6_borrow_update_accts2 (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts :=
  plan6_borrow_update_accts_check_tmp s mid h

theorem plan6_borrow_mid_acct_proof : True := trivial
#check @updBorrow_inv_test
#check @plan6_borrow_update_accts_fixed

theorem plan6_borrow_mid_acct_inline (s mid : St) (who : Account)
    (h : updateCompBorrowIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid h
  unfold St.acct
  rw [haccts]

theorem plan6_borrow_mid_state (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
  have hmid := plan5_updateBorrow_accrueSide s mid h
  rw [hmid]

theorem plan6_borrow_start_le (s mid s' : St) (who : Account)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨hle_mid, _⟩ := hchar
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid hup
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hmid := plan5_updateBorrow_accrueSide s mid hup
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  rw [hacct, hstate] at hle_mid
  exact hle_mid

theorem plan6_borrow_eq_proof_tmp : True := trivial

theorem plan6_borrow_eq_via_subst3 (s mid s' : St) (who : Account)
    (hmid2 : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (heq2 : s' = { mid with accts := mid.accts.modify who fun a => { a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + 1 } }) :
    s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + 1 } } := by
  subst hmid2
  exact heq2

theorem plan6_borrow_eq (s mid s' : St) (who : Account) (hup : updateCompBorrowIndex s = some mid) (hdist : distributeBorrowerComp mid who = some s') : s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨_, heq_mid⟩ := hchar
  have heq2 : s' = { mid with accts := mid.accts.modify who fun a => { a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex mid.borrowState.index) mid.borrowState.index } } := heq_mid
  subst hmid
  exact heq2

theorem plan5_borrowDistributed_of_steps_check_tmp (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' :=
  plan5_borrowDistributed_aux_final s who mid s' hup hdist

theorem plan5_borrowDistributed_of_steps_proof_tmp2 (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' :=
  plan5_borrowDistributed_aux_final s who mid s' hup hdist

theorem plan5_borrowDistributed_of_steps_dup_test (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_distributeBorrower_char mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := by
    unfold updateCompBorrowIndex subChecked at hup
    simp only [hb, ↓reduceIte] at hup
    split at hup
    next hc =>
      split at hup
      next ht => cases hup; rfl
      next ht => cases hup; rfl
    next hc =>
      split at hup
      next hd => cases hup; rfl
      next hd => cases hup; rfl
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan5_borrowDistributed_of_steps_NEWNAME (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_distributeBorrower_char mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := by
    unfold updateCompBorrowIndex subChecked at hup
    simp only [hb, ↓reduceIte] at hup
    split at hup
    next hc =>
      split at hup
      next ht => cases hup; rfl
      next ht => cases hup; rfl
    next hc =>
      split at hup
      next hd => cases hup; rfl
      next hd => cases hup; rfl
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan5_borrowDistributed_of_steps_finalcheck (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  exact plan5_borrowDistributed_of_steps_dup_test s who mid s' hup hdist

theorem plan5_borrowDistributed_inline_early (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_distributeBorrower_char mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := by
    unfold updateCompBorrowIndex subChecked at hup
    simp only [hb, ↓reduceIte] at hup
    split at hup
    next hc =>
      split at hup
      next ht => cases hup; rfl
      next ht => cases hup; rfl
    next hc =>
      split at hup
      next hd => cases hup; rfl
      next hd => cases hup; rfl
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem borrow_accts_nosplit (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    plan1_subChecked_of_le _ _ hb
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  by_cases hc : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hc, ↓reduceIte] at h
    by_cases ht : 0 < totalBorrows s
    · simp only [ht, ↓reduceIte] at h
      cases h
      rfl
    · simp only [ht, ↓reduceIte] at h
      cases h
      rfl
  · simp only [hc, ↓reduceIte] at h
    by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · simp only [hd, ↓reduceIte] at h
      cases h
      rfl
    · simp only [hd, ↓reduceIte] at h
      cases h
      rfl

theorem plan5_borrowHook_decomp (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ mid, updateCompBorrowIndex s = some mid ∧ distributeBorrowerComp mid who = some s' := by
  unfold comptroller at h
  cases hup : updateCompBorrowIndex s with
  | none =>
    simp [hup] at h
  | some mid =>
    simp [hup] at h
    exact ⟨mid, rfl, h⟩

theorem req_borrow_hook_PROBE : BorrowHookEffects comptroller := by
  intro s who s' h
  obtain ⟨mid, hup, hdist⟩ := plan5_borrowHook_decomp s who s' h
  exact plan5_borrowDistributed_aux_final s who mid s' hup hdist

theorem grant_shape (s : St) (who : Account) :
    grantCompInternal s who =
    (let amount := (s.accts.getD who noAcct).accrued;
     if amount > 0 ∧ amount ≤ s.reserve then
      { s with reserve := s.reserve - amount,
               accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + amount } }
     else s) := by rfl

theorem grantUnfold_test (s : St) (who : Account) :
    grantCompInternal s who =
    (if (s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve then
      { s with reserve := s.reserve - (s.accts.getD who noAcct).accrued,
               accts := s.accts.modify who fun a => ({ a with accrued := 0, wallet := a.wallet + (s.accts.getD who noAcct).accrued } : Acct) }
     else s) := by
  unfold grantCompInternal St.acct
  rfl



theorem plan7_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by sorry





theorem tmp_bind_probe6 (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') : True := by
  have hc2 : Option.bind (updateCompBorrowIndex s) (fun b1 =>
      Option.bind (distributeBorrowerComp b1 who) (fun b2 =>
        Option.bind (updateCompSupplyIndex b2) (fun u2 =>
          Option.bind (distributeSupplierComp u2 who) (fun fin =>
            some (grantCompInternal fin who))))) = some s' := h
  rw [Option.bind_eq_some_iff] at hc2
  obtain ⟨b1, hb1, hrest⟩ := hc2
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨b2, hb2, hrest2⟩ := hrest
  rw [Option.bind_eq_some_iff] at hrest2
  obtain ⟨u2, hu2, hrest3⟩ := hrest2
  rw [Option.bind_eq_some_iff] at hrest3
  obtain ⟨fin, hfin, hlast⟩ := hrest3
  simp only [Option.some.injEq] at hlast
  trivial

theorem plan7_claim_decomp (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    ∃ b1 b2 u2 fin,
      updateCompBorrowIndex s = some b1 ∧
      distributeBorrowerComp b1 who = some b2 ∧
      updateCompSupplyIndex b2 = some u2 ∧
      distributeSupplierComp u2 who = some fin ∧
      s' = grantCompInternal fin who := by
  have hc2 : Option.bind (updateCompBorrowIndex s) (fun b1 =>
      Option.bind (distributeBorrowerComp b1 who) (fun b2 =>
        Option.bind (updateCompSupplyIndex b2) (fun u2 =>
          Option.bind (distributeSupplierComp u2 who) (fun fin =>
            some (grantCompInternal fin who))))) = some s' := h
  rw [Option.bind_eq_some_iff] at hc2
  obtain ⟨b1, hb1, hrest⟩ := hc2
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨b2, hb2, hrest2⟩ := hrest
  rw [Option.bind_eq_some_iff] at hrest2
  obtain ⟨u2, hu2, hrest3⟩ := hrest2
  rw [Option.bind_eq_some_iff] at hrest3
  obtain ⟨fin, hfin, hlast⟩ := hrest3
  simp only [Option.some.injEq] at hlast
  subst hlast
  exact ⟨b1, b2, u2, fin, hb1, hb2, hu2, hfin, rfl⟩

theorem plan7_probe_gt (n m : Nat) : (n > m) = (m < n) := rfl

theorem plan7_probe_cond (s : St) (who : Account) :
    (((s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve) =
     (0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve)) := rfl









theorem plan8_modify_grant_wallet_eq_new (s : St) (who : Account) :
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) =
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply snippet_modify_congr_test
  rfl

theorem plan8_modify_grant_wallet_eq (s : St) (who : Account) :
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) =
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply snippet_modify_congr_test
  rfl

theorem plan8_grant_branch_eq_try (s : St) (who : Account) :
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } } =
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  rw [plan8_modify_grant_wallet_eq]

theorem plan8_grant_branch_eq (s : St) (who : Account) :
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } } =
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  rw [plan8_modify_grant_wallet_eq]

theorem plan8_grantCompInternal_eq_if (s : St) (who : Account) :
    grantCompInternal s who =
      if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
        { s with
          reserve := s.reserve - (s.acct who).accrued,
          accts := s.accts.modify who
            fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } }
      else s := by
  unfold grantCompInternal
  rfl

theorem plan8_grant_eq_if (s : St) (who : Account) :
    grant s who =
      if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
        { s with
          reserve := s.reserve - (s.acct who).accrued,
          accts := s.accts.modify who
            fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
      else s := by
  rfl

theorem plan7_claim_steps_distributed
    (s b1 b2 u2 fin : St) (who : Account)
    (hbUp : updateCompBorrowIndex s = some b1)
    (hbDist : distributeBorrowerComp b1 who = some b2)
    (hsUp : updateCompSupplyIndex b2 = some u2)
    (hsDist : distributeSupplierComp u2 who = some fin) :
    BorrowDistributed s who b2 ∧ SupplyDistributed b2 who fin := by
  exact ⟨plan5_borrowDistributed_aux_final s who b1 b2 hbUp hbDist,
    plan2_supplyDistributed_of_steps b2 who u2 fin hsUp hsDist⟩

theorem plan7_claim_of_raw_steps
    (s b1 b2 u2 fin s' : St) (who : Account)
    (hbUp : updateCompBorrowIndex s = some b1)
    (hbDist : distributeBorrowerComp b1 who = some b2)
    (hsUp : updateCompSupplyIndex b2 = some u2)
    (hsDist : distributeSupplierComp u2 who = some fin)
    (hfin : s' = grantCompInternal fin who) :
    Claimed s who s' := by
  have hB : BorrowDistributed s who b2 :=
    plan5_borrowDistributed_aux_final s who b1 b2 hbUp hbDist
  have hS : SupplyDistributed b2 who fin :=
    plan2_supplyDistributed_of_steps b2 who u2 fin hsUp hsDist
  have hgr : grantCompInternal fin who = grant fin who := by
    rw [plan8_grantCompInternal_eq_if, plan8_grant_eq_if, plan8_grant_branch_eq]
  exact ⟨b2, fin, hB, hS, by rw [hfin, hgr]⟩

theorem updSupply_preserve_borrow (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid.borrowState = s.borrowState := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid h
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := plan1_subChecked_of_le _ _ hb
  unfold updateCompSupplyIndex at h
  rw [hsub] at h
  simp only at h
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc, ↓reduceIte] at h
    by_cases ht : 0 < totalSupply s
    · simp only [ht, ↓reduceIte] at h
      cases h; rfl
    · simp only [ht, ↓reduceIte] at h
      cases h; rfl
  · simp only [hc, ↓reduceIte] at h
    by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · simp only [hd, ↓reduceIte] at h
      cases h; rfl
    · simp only [hd, ↓reduceIte] at h
      cases h; rfl

theorem req_calls_succeed       : CallsSucceed comptroller := sorry

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  obtain ⟨mid, hup, hdist⟩ := supplyHook_decomp_ok s who s' h
  exact plan2_supplyDistributed_of_steps s who mid s' hup hdist

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  obtain ⟨mid, hup, hdist⟩ := plan5_borrowHook_decomp s who s' h
  exact plan5_borrowDistributed_aux_final s who mid s' hup hdist

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  obtain ⟨b1, b2, u2, fin, hbUp, hbDist, hsUp, hsDist, hfin⟩ :=
    plan7_claim_decomp s who s' h
  exact plan7_claim_of_raw_steps s b1 b2 u2 fin s' who hbUp hbDist hsUp hsDist hfin

theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry

theorem req_account_bounded     : AccountBounded comptroller := sorry

theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
