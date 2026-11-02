import CompRewards.Spec
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
    some (s.withAcct supplier fun a => Acct.mk a.supply a.borrow supplyIndex
      a.borrowerIndex (a.accrued + mulDouble a.supply deltaIndex) a.wallet)

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex :=
    if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ borrowIndex then compInitialIndex
    else (s.acct borrower).borrowerIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some deltaIndex =>
    some (s.withAcct borrower fun a => Acct.mk a.supply a.borrow
      a.supplierIndex borrowIndex (a.accrued + mulDouble a.borrow deltaIndex) a.wallet)

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => Acct.mk a.supply a.borrow
               a.supplierIndex a.borrowerIndex 0 (a.wallet + amount) }
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

-- Auxiliary lemmas for the effects proofs.
theorem subChecked_some {a b d : Nat} : subChecked a b = some d ↔ b ≤ a ∧ a - b = d := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

theorem subChecked_isSome {a b : Nat} : (subChecked a b).isSome = decide (b ≤ a) := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

theorem subChecked_succ {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem doubleScale_pos : 0 < doubleScale := by
  unfold doubleScale
  decide

theorem compInitialIndex_eq : compInitialIndex = doubleScale := by
  rfl

-- accrueSide unfolds to the update logic when the side block is not ahead.
theorem updateSupply_eq_accrue (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide
  have hs : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    subChecked_succ h
  rw [hs]
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · have hd1 : s.blockNumber - s.supplyState.block > 0 := hd.1
    have hs2 : s.supplyState.speed > 0 := hd.2
    have hpos : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s ∨
        ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
      by_cases ht : 0 < totalSupply s
      · exact Or.inl ⟨hd1, hs2, ht⟩
      · exact Or.inr (by simp [ht])
    by_cases ht : 0 < totalSupply s
    · have hc : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := ⟨hd1, hs2, ht⟩
      simp only [hc, if_true, hd, if_true]
      congr 1
      · congr 1
        · unfold fraction totalSupply
          have : (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s =
              s.supplyState.index + ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / (s.accts.map Acct.supply).sum) - s.supplyState.index := by
            omega
          simp [totalSupply] at hc ⊢
          congr 1
          have h1 : (if totalSupply s > 0 then fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s) else 0) =
              (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s := by
            simp [ht, fraction]
          rw [h1]
        · rfl
      · rfl
    · have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        simp [ht]
      simp only [hc, if_false, hd, if_true]
      have h0 : (if totalSupply s > 0 then fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s) else 0) = 0 := by
        have : ¬ totalSupply s > 0 := by omega
        simp [this]
      simp only [h0]
      congr 1
      · congr 1
        · omega
        · rfl
      · rfl
  · by_cases hdpos : s.blockNumber - s.supplyState.block > 0
    · have hneg : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by
        simp only [hdpos, true_and] at hd ⊢
        omega
      have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        omega
      simp only [hc, if_false, hneg, if_false, hdpos, if_true]
    · have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have hneg : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by omega
      have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      simp only [hc, if_false, hneg, if_false, hzero, gt_iff_lt, lt_irrefl, if_false]
      congr 1
      have : s.supplyState.block = s.blockNumber := hbeq
      simp [this, accrueSide]

theorem updateBorrow_eq_accrue (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide
  have hs : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    subChecked_succ h
  rw [hs]
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · have hd1 : s.blockNumber - s.borrowState.block > 0 := hd.1
    have hs2 : s.borrowState.speed > 0 := hd.2
    by_cases ht : 0 < totalBorrows s
    · have hc : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := ⟨hd1, hs2, ht⟩
      simp only [hc, if_true, hd, if_true]
      congr 1
      · congr 1
        · have h1 : (if totalBorrows s > 0 then fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s) else 0) =
              (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s := by
            simp [ht, fraction]
          rw [h1]
        · rfl
      · rfl
    · have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [ht]
      simp only [hc, if_false, hd, if_true]
      have h0 : (if totalBorrows s > 0 then fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s) else 0) = 0 := by
        have : ¬ totalBorrows s > 0 := by omega
        simp [this]
      simp only [h0]
      congr 1
      · congr 1
        · omega
        · rfl
      · rfl
  · by_cases hdpos : s.blockNumber - s.borrowState.block > 0
    · have hneg : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
        simp only [hdpos, true_and] at hd ⊢
        omega
      have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        omega
      simp only [hc, if_false, hneg, if_false, hdpos, if_true]
    · have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have hneg : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by omega
      have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      simp only [hc, if_false, hneg, if_false, hzero, gt_iff_lt, lt_irrefl, if_false]
      congr 1
      simp [hbeq]

theorem accrualStart_eq_supplier (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · simp [h0]
  · simp [h0]

theorem accrualStart_eq_borrower (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · simp [h0]
  · simp [h0]

theorem modify_supply_congr (xs : List Acct) (who idx deltaFixed : Nat)
    (hdelta : deltaFixed = idx - accrualStart (xs.getD who noAcct).supplierIndex idx) :
    List.modify xs who (fun a => Acct.mk a.supply a.borrow idx a.borrowerIndex
      (a.accrued + a.supply * deltaFixed / doubleScale) a.wallet) =
    List.modify xs who (fun a => Acct.mk a.supply a.borrow idx a.borrowerIndex
      (a.accrued + a.supply * (idx - accrualStart a.supplierIndex idx) / doubleScale) a.wallet) := by
  induction xs generalizing who with
  | nil => simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero] at hdelta
      simp [hdelta]
    | succ n =>
      simp only [List.getD_cons_succ] at hdelta
      simp
      exact ih _ hdelta

theorem modify_borrow_congr (xs : List Acct) (who idx deltaFixed : Nat)
    (hdelta : deltaFixed = idx - accrualStart (xs.getD who noAcct).borrowerIndex idx) :
    List.modify xs who (fun a => Acct.mk a.supply a.borrow a.supplierIndex idx
      (a.accrued + a.borrow * deltaFixed / doubleScale) a.wallet) =
    List.modify xs who (fun a => Acct.mk a.supply a.borrow a.supplierIndex idx
      (a.accrued + a.borrow * (idx - accrualStart a.borrowerIndex idx) / doubleScale) a.wallet) := by
  induction xs generalizing who with
  | nil => simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero] at hdelta
      simp [hdelta]
    | succ n =>
      simp only [List.getD_cons_succ] at hdelta
      simp
      exact ih _ hdelta

theorem accrualStart_le_of_mem (r idx : Nat) (h : r = 0 ∨ r ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases h0 : r = 0
  · simp [h0]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi]
    · simp [hi]
  · simp [h0]
    have hle : r ≤ idx := by
      cases h with
      | inl he => omega
      | inr he => exact he
    exact hle

theorem supplier_mem_le (l : List Acct) (idx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ idx) (who : Nat) :
    (l.getD who noAcct).supplierIndex = 0 ∨ (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    left
    rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero]
      right
      exact hall hd (by simp)
    | succ n =>
      simp only [List.getD_cons_succ]
      exact ih (fun a ha => hall a (List.mem_cons_of_mem hd ha)) n

theorem borrower_mem_le (l : List Acct) (idx : Nat)
    (hall : ∀ a ∈ l, a.borrowerIndex ≤ idx) (who : Nat) :
    (l.getD who noAcct).borrowerIndex = 0 ∨ (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    left
    rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero]
      right
      exact hall hd (by simp)
    | succ n =>
      simp only [List.getD_cons_succ]
      exact ih (fun a ha => hall a (List.mem_cons_of_mem hd ha)) n

theorem consistent_supplier_start_le (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  apply accrualStart_le_of_mem
  obtain ⟨_, _, hall⟩ := hc
  have h := supplier_mem_le s.accts s.supplyState.index (fun a ha => (hall a ha).1) who
  unfold St.acct
  exact h

theorem consistent_borrower_start_le (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  apply accrualStart_le_of_mem
  obtain ⟨_, _, hall⟩ := hc
  have h := borrower_mem_le s.accts s.borrowState.index (fun a ha => (hall a ha).2) who
  unfold St.acct
  exact h

theorem distributeSupply_eq2 (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp creditFor mulDouble
  dsimp only
  rw [accrualStart_eq_supplier]
  have hs : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    subChecked_succ h
  rw [hs]
  simp only [St.withAcct]
  have hmod := modify_supply_congr s.accts who s.supplyState.index
    (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) rfl
  rw [hmod]

theorem distributeBorrow_eq2 (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp creditFor mulDouble
  dsimp only
  rw [accrualStart_eq_borrower]
  have hs : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    subChecked_succ h
  rw [hs]
  simp only [St.withAcct]
  have hmod := modify_borrow_congr s.accts who s.borrowState.index
    (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) rfl
  rw [hmod]

theorem accrueSupply_mono (s : St) :
    s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  by_cases h : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
    0 < totalSupply s)
  · simp [h]
  · simp [h]

theorem accrueBorrow_mono (s : St) :
    s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  by_cases h : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
    0 < totalBorrows s)
  · simp [h]
  · simp [h]

theorem accrueSupply_block (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber := by
  unfold accrueSide
  by_cases h : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
    0 < totalSupply s)
  · simp [h]
  · simp [h]

theorem accrueBorrow_block (s : St) :
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber := by
  unfold accrueSide
  by_cases h : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
    0 < totalBorrows s)
  · simp [h]
  · simp [h]

theorem updateSupply_none_of_ahead (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  have hs : subChecked s.blockNumber s.supplyState.block = none :=
    subChecked_none h
  rw [hs]

theorem updateBorrow_none_of_ahead (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  have hs : subChecked s.blockNumber s.borrowState.block = none :=
    subChecked_none h
  rw [hs]

theorem distributeSupply_none_of_high (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = none := by
  unfold distributeSupplierComp
  dsimp only
  rw [accrualStart_eq_supplier]
  have hs : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none :=
    subChecked_none h
  rw [hs]

theorem distributeBorrow_none_of_high (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp
  dsimp only
  rw [accrualStart_eq_borrower]
  have hs : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none :=
    subChecked_none h
  rw [hs]

theorem supply_start_le_after_accrue (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  apply accrualStart_le_of_mem
  obtain ⟨_, _, hall⟩ := hc
  have hdisj := supplier_mem_le s.accts s.supplyState.index
    (fun a ha => (hall a ha).1) who
  have hmono := accrueSupply_mono s
  unfold St.acct at hdisj ⊢
  cases hdisj with
  | inl he => exact Or.inl he
  | inr he =>
    apply Or.inr
    omega

theorem borrow_start_le_after_accrue (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  apply accrualStart_le_of_mem
  obtain ⟨_, _, hall⟩ := hc
  have hdisj := borrower_mem_le s.accts s.borrowState.index
    (fun a ha => (hall a ha).2) who
  have hmono := accrueBorrow_mono s
  unfold St.acct at hdisj ⊢
  cases hdisj with
  | inl he => exact Or.inl he
  | inr he =>
    apply Or.inr
    omega

theorem grant_modify_congr (xs : List Acct) (who : Nat) (amt : Nat)
    (hamt : amt = (xs.getD who noAcct).accrued) :
    List.modify xs who (fun a => Acct.mk a.supply a.borrow a.supplierIndex a.borrowerIndex
      0 (a.wallet + amt)) =
    List.modify xs who (fun a => Acct.mk a.supply a.borrow a.supplierIndex a.borrowerIndex
      0 (a.wallet + a.accrued)) := by
  induction xs generalizing who with
  | nil => simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero] at hamt
      simp [hamt]
    | succ n =>
      simp only [List.getD_cons_succ] at hamt
      simp
      exact ih _ hamt

theorem modify_map_supply_borrow (xs : List Acct) (who idx : Nat) (delta : Nat) :
    (List.modify xs who (fun a => Acct.mk a.supply a.borrow a.supplierIndex idx
      (a.accrued + a.borrow * delta / doubleScale) a.wallet)).map Acct.supply =
    xs.map Acct.supply := by
  induction xs generalizing who with
  | nil => simp
  | cons hd tl ih =>
    cases who with
    | zero => simp
    | succ n => simp [ih]

theorem modify_map_borrow_supply (xs : List Acct) (who idx : Nat) (delta : Nat) :
    (List.modify xs who (fun a => Acct.mk a.supply a.borrow idx a.borrowerIndex
      (a.accrued + a.supply * delta / doubleScale) a.wallet)).map Acct.borrow =
    xs.map Acct.borrow := by
  induction xs generalizing who with
  | nil => simp
  | cons hd tl ih =>
    cases who with
    | zero => simp
    | succ n => simp [ih]

theorem modify_get_supplierIndex_borrow (xs : List Acct) (who : Nat) (idx delta : Nat) (who0 : Nat) :
    ((List.modify xs who (fun a => Acct.mk a.supply a.borrow a.supplierIndex idx
      (a.accrued + a.borrow * delta / doubleScale) a.wallet)).getD who0 noAcct).supplierIndex =
    ((xs.getD who0 noAcct).supplierIndex) := by
  induction xs generalizing who who0 with
  | nil => simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      cases who0 with
      | zero => simp
      | succ n0 => simp
    | succ n =>
      cases who0 with
      | zero => simp
      | succ n0 =>
        simp only [List.getD_cons_succ] at ⊢
        simp
        exact ih n n0

theorem modify_get_borrowerIndex_supply (xs : List Acct) (who : Nat) (idx delta : Nat) (who0 : Nat) :
    ((List.modify xs who (fun a => Acct.mk a.supply a.borrow idx a.borrowerIndex
      (a.accrued + a.supply * delta / doubleScale) a.wallet)).getD who0 noAcct).borrowerIndex =
    ((xs.getD who0 noAcct).borrowerIndex) := by
  induction xs generalizing who who0 with
  | nil => simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      cases who0 with
      | zero => simp
      | succ n0 => simp
    | succ n =>
      cases who0 with
      | zero => simp
      | succ n0 =>
        simp only [List.getD_cons_succ] at ⊢
        simp
        exact ih n n0

theorem grant_eq (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  dsimp only
  by_cases h : ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve)
  · simp [h]
    have hmod := grant_modify_congr s.accts who (s.acct who).accrued rfl
    rw [hmod]
  · simp [h]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' hs
  unfold comptroller at hs
  cases heq_up : updateCompSupplyIndex s with
  | none =>
    simp [heq_up] at hs
  | some s1 =>
    simp [heq_up] at hs
    have hle : s.supplyState.block ≤ s.blockNumber := by
      by_cases hle : s.supplyState.block ≤ s.blockNumber
      · exact hle
      · have hnone := updateSupply_none_of_ahead s hle
        rw [hnone] at heq_up
        cases heq_up
    have hup_eq := updateSupply_eq_accrue s hle
    have h_eq_some : some s1 = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      rw [← heq_up, hup_eq]
    have hs1_eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      injection h_eq_some
    have hstart1 : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤
        s1.supplyState.index := by
      by_cases hle2 : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤
        s1.supplyState.index
      · exact hle2
      · have hnone := distributeSupply_none_of_high s1 who hle2
        rw [hnone] at hs
        cases hs
    have hdist_eq := distributeSupply_eq2 s1 who hstart1
    have h_eq_some2 : some s' = some { s1 with accts := s1.accts.modify who fun a =>
        { a with supplierIndex := s1.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s1.supplyState.index)
                   s1.supplyState.index } } := by
      rw [← hs, hdist_eq]
    have hs'_eq : s' = { s1 with accts := s1.accts.modify who fun a =>
        { a with supplierIndex := s1.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s1.supplyState.index)
                   s1.supplyState.index } } := by
      injection h_eq_some2
    have hstart0 : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      have h0 : s1.acct who = s.acct who := by simp [hs1_eq, St.acct]
      have h1 : s1.supplyState.index =
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        simp [hs1_eq]
      rw [← h0, ← h1]
      exact hstart1
    rw [hs1_eq] at hs'_eq
    have hs'_eq2 : s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
      rw [hs'_eq]
    exact ⟨hle, hstart0, hs'_eq2⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' hs
  unfold comptroller at hs
  cases heq_up : updateCompBorrowIndex s with
  | none =>
    simp [heq_up] at hs
  | some s1 =>
    simp [heq_up] at hs
    have hle : s.borrowState.block ≤ s.blockNumber := by
      by_cases hle : s.borrowState.block ≤ s.blockNumber
      · exact hle
      · have hnone := updateBorrow_none_of_ahead s hle
        rw [hnone] at heq_up
        cases heq_up
    have hup_eq := updateBorrow_eq_accrue s hle
    have h_eq_some : some s1 = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      rw [← heq_up, hup_eq]
    have hs1_eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      injection h_eq_some
    have hstart1 : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤
        s1.borrowState.index := by
      by_cases hle2 : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤
        s1.borrowState.index
      · exact hle2
      · have hnone := distributeBorrow_none_of_high s1 who hle2
        rw [hnone] at hs
        cases hs
    have hdist_eq := distributeBorrow_eq2 s1 who hstart1
    have h_eq_some2 : some s' = some { s1 with accts := s1.accts.modify who fun a =>
        { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := by
      rw [← hs, hdist_eq]
    have hs'_eq : s' = { s1 with accts := s1.accts.modify who fun a =>
        { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := by
      injection h_eq_some2
    have hstart0 : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      have h0 : s1.acct who = s.acct who := by simp [hs1_eq, St.acct]
      have h1 : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hs1_eq]
      rw [← h0, ← h1]
      exact hstart1
    rw [hs1_eq] at hs'_eq
    have hs'_eq2 : s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
      rw [hs'_eq]
    exact ⟨hle, hstart0, hs'_eq2⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' hs
  unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed at hs
  dsimp only at hs
  by_cases hsup : s.supplyState.speed = a
  · simp [hsup] at hs
    by_cases hbor : s.borrowState.speed = b
    · simp [hbor] at hs
      have hs_eq : s' = s := hs.symm
      subst hs_eq
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exact absurd hsup hne
      · intro hne
        exact absurd hbor hne
      · simp [hsup, hbor]
    · simp only [hbor] at hs
      cases heq_bor : updateCompBorrowIndex s with
      | none =>
        simp [heq_bor] at hs
      | some s1 =>
        simp [heq_bor] at hs
        have hle : s.borrowState.block ≤ s.blockNumber := by
          by_cases hle : s.borrowState.block ≤ s.blockNumber
          · exact hle
          · have hnone := updateBorrow_none_of_ahead s hle
            rw [hnone] at heq_bor
            cases heq_bor
        have hup_eq := updateBorrow_eq_accrue s hle
        have h_eq_some : some s1 = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
          rw [← heq_bor, hup_eq]
        have hs1_eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
          injection h_eq_some
        have hs'_eq : s' = { s1 with borrowState := { s1.borrowState with speed := b } } := hs.symm
        rw [hs1_eq] at hs'_eq
        have hs'_eq2 : s' = { s with supplyState := s.supplyState, borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
          rw [hs'_eq]
        refine ⟨?_, ?_, ?_⟩
        · intro hne
          exact absurd hsup hne
        · intro _
          exact hle
        · simp [hsup, hbor]
          exact hs'_eq2
  · simp [hsup] at hs
    cases heq_sup : updateCompSupplyIndex s with
    | none =>
      simp [heq_sup] at hs
    | some s1 =>
      simp [heq_sup] at hs
      have hle_sup : s.supplyState.block ≤ s.blockNumber := by
        by_cases hle : s.supplyState.block ≤ s.blockNumber
        · exact hle
        · have hnone := updateSupply_none_of_ahead s hle
          rw [hnone] at heq_sup
          cases heq_sup
      have hup_eq_sup := updateSupply_eq_accrue s hle_sup
      have h_eq_some_sup : some s1 = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
        rw [← heq_sup, hup_eq_sup]
      have hs1_eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
        injection h_eq_some_sup
      have hmid_eq : ({ s1 with supplyState := { s1.supplyState with speed := a } }.borrowState.speed = s.borrowState.speed) := by
        simp [hs1_eq]
      have hmid_block : ({ s1 with supplyState := { s1.supplyState with speed := a } }.borrowState.block = s.borrowState.block) := by
        simp [hs1_eq]
      have hmid_num : ({ s1 with supplyState := { s1.supplyState with speed := a } }.blockNumber = s.blockNumber) := by
        simp [hs1_eq]
      have hmid_accts : ({ s1 with supplyState := { s1.supplyState with speed := a } }.accts = s.accts) := by
        simp [hs1_eq]
      by_cases hbor : s.borrowState.speed = b
      · have hbor_mid : ({ s1 with supplyState := { s1.supplyState with speed := a } }.borrowState.speed = b) := by
          rw [hmid_eq, hbor]
        rw [hbor_mid] at hs
        simp at hs
        have hs_eq : s' = { s1 with supplyState := { s1.supplyState with speed := a } } := hs.symm
        rw [hs1_eq] at hs_eq
        have hs'_eq : s' = { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }, borrowState := s.borrowState } := by
          rw [hs_eq]
        refine ⟨?_, ?_, ?_⟩
        · intro _
          exact hle_sup
        · intro hne
          exact absurd hbor hne
        · simp [hsup, hbor]
          exact hs'_eq
      · have hne_mid : ({ s1 with supplyState := { s1.supplyState with speed := a } }.borrowState.speed ≠ b) := by
          rw [hmid_eq]
          exact hbor
        simp [hne_mid] at hs
        cases heq_bor_mid : updateCompBorrowIndex ({ s1 with supplyState := { s1.supplyState with speed := a } } : St) with
        | none =>
          simp [heq_bor_mid] at hs
        | some s2 =>
          simp [heq_bor_mid] at hs
          have hle_bor_mid : (({ s1 with supplyState := { s1.supplyState with speed := a } } : St).borrowState.block ≤ ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).blockNumber) := by
            by_cases hle : (({ s1 with supplyState := { s1.supplyState with speed := a } } : St).borrowState.block ≤ ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).blockNumber)
            · exact hle
            · have hnone := updateBorrow_none_of_ahead _ hle
              rw [hnone] at heq_bor_mid
              cases heq_bor_mid
          have hle_bor : s.borrowState.block ≤ s.blockNumber := by
            rw [← hmid_block, ← hmid_num]
            exact hle_bor_mid
          have hup_eq_bor := updateBorrow_eq_accrue _ hle_bor_mid
          have h_eq_some_bor : some s2 = some ({ ({ s1 with supplyState := { s1.supplyState with speed := a } } : St) with borrowState := accrueSide ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).borrowState ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).blockNumber (totalBorrows ({ s1 with supplyState := { s1.supplyState with speed := a } } : St)) } : St) := by
            rw [← heq_bor_mid, hup_eq_bor]
          have hs2_eq : s2 = ({ ({ s1 with supplyState := { s1.supplyState with speed := a } } : St) with borrowState := accrueSide ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).borrowState ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).blockNumber (totalBorrows ({ s1 with supplyState := { s1.supplyState with speed := a } } : St)) } : St) := by
            injection h_eq_some_bor
          have hs'_eq_bor : s' = { s2 with borrowState := { s2.borrowState with speed := b } } := hs.symm
          have hborrow_eq : (({ s1 with supplyState := { s1.supplyState with speed := a } } : St).borrowState = s.borrowState) := by
            simp [hs1_eq]
          have htotal_bor : totalBorrows ({ s1 with supplyState := { s1.supplyState with speed := a } } : St) = totalBorrows s := by
            simp [hs1_eq, totalBorrows]
          have hnum_bor : (({ s1 with supplyState := { s1.supplyState with speed := a } } : St).blockNumber = s.blockNumber) := by simp [hs1_eq]
          have hacc_bor_eq : accrueSide ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).borrowState ({ s1 with supplyState := { s1.supplyState with speed := a } } : St).blockNumber (totalBorrows ({ s1 with supplyState := { s1.supplyState with speed := a } } : St)) = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
            simp [hs1_eq, totalBorrows]
          rw [hs2_eq, hacc_bor_eq, hs1_eq] at hs'_eq_bor
          have hs'_eq2 : s' = { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }, borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
            rw [hs'_eq_bor]
          refine ⟨?_, ?_, ?_⟩
          · intro _
            exact hle_sup
          · intro _
            exact hle_bor
          · simp [hsup, hbor]
            exact hs'_eq2

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' hs
  unfold comptroller claimComp at hs
  dsimp only at hs
  cases heq_bup : updateCompBorrowIndex s with
  | none =>
    simp [heq_bup] at hs
  | some s1 =>
    simp [heq_bup] at hs
    cases heq_bdist : distributeBorrowerComp s1 who with
    | none =>
      simp [heq_bdist] at hs
    | some s2 =>
      simp [heq_bdist] at hs
      cases heq_sup : updateCompSupplyIndex s2 with
      | none =>
        simp [heq_sup] at hs
      | some s3 =>
        simp [heq_sup] at hs
        cases heq_sdist : distributeSupplierComp s3 who with
        | none =>
          simp [heq_sdist] at hs
        | some s4 =>
          simp [heq_sdist] at hs
          have hs_grant : s' = grantCompInternal s4 who := hs.symm
          have hle_bor : s.borrowState.block ≤ s.blockNumber := by
            by_cases hle : s.borrowState.block ≤ s.blockNumber
            · exact hle
            · have hnone := updateBorrow_none_of_ahead s hle
              rw [hnone] at heq_bup
              cases heq_bup
          have hup_eq_bor := updateBorrow_eq_accrue s hle_bor
          have h_eq_some_bor : some s1 = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
            rw [← heq_bup, hup_eq_bor]
          have hs1_eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
            injection h_eq_some_bor
          have hstart_bor : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
            by_cases hle2 : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index
            · exact hle2
            · have hnone := distributeBorrow_none_of_high s1 who hle2
              rw [hnone] at heq_bdist
              cases heq_bdist
          have hdist_eq_bor := distributeBorrow_eq2 s1 who hstart_bor
          have h_eq_some_bdist : some s2 = some { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := by
            rw [← heq_bdist, hdist_eq_bor]
          have hs2_eq : s2 = { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := by
            injection h_eq_some_bdist
          have hle_sup : s2.supplyState.block ≤ s2.blockNumber := by
            by_cases hle : s2.supplyState.block ≤ s2.blockNumber
            · exact hle
            · have hnone := updateSupply_none_of_ahead s2 hle
              rw [hnone] at heq_sup
              cases heq_sup
          have hup_eq_sup := updateSupply_eq_accrue s2 hle_sup
          have h_eq_some_sup : some s3 = some { s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } := by
            rw [← heq_sup, hup_eq_sup]
          have hs3_eq : s3 = { s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } := by
            injection h_eq_some_sup
          have hstart_sup : accrualStart (s3.acct who).supplierIndex s3.supplyState.index ≤ s3.supplyState.index := by
            by_cases hle2 : accrualStart (s3.acct who).supplierIndex s3.supplyState.index ≤ s3.supplyState.index
            · exact hle2
            · have hnone := distributeSupply_none_of_high s3 who hle2
              rw [hnone] at heq_sdist
              cases heq_sdist
          have hdist_eq_sup := distributeSupply_eq2 s3 who hstart_sup
          have h_eq_some_sdist : some s4 = some { s3 with accts := s3.accts.modify who fun a => { a with supplierIndex := s3.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s3.supplyState.index) s3.supplyState.index } } := by
            rw [← heq_sdist, hdist_eq_sup]
          have hs4_eq : s4 = { s3 with accts := s3.accts.modify who fun a => { a with supplierIndex := s3.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s3.supplyState.index) s3.supplyState.index } } := by
            injection h_eq_some_sdist
          have hs_grant_eq : s' = grant s4 who := by
            rw [hs_grant, grant_eq]
          have hbor_dist : BorrowDistributed s who s2 := by
            have h0 : s1.acct who = s.acct who := by simp [hs1_eq, St.acct]
            have h1 : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hs1_eq]
            rw [h0, h1] at hstart_bor
            rw [hs1_eq] at hs2_eq
            exact ⟨hle_bor, hstart_bor, hs2_eq⟩
          have hsup_dist : SupplyDistributed s2 who s4 := by
            have h0s : s3.acct who = s2.acct who := by simp [hs3_eq, St.acct]
            have h1s : s3.supplyState.index = (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index := by simp [hs3_eq]
            rw [h0s, h1s] at hstart_sup
            rw [hs3_eq] at hs4_eq
            exact ⟨hle_sup, hstart_sup, hs4_eq⟩
          exact ⟨s2, s4, hbor_dist, hsup_dist, hs_grant_eq⟩

theorem req_calls_succeed       : CallsSucceed comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
