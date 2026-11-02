import CompRewards.Spec
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

/-- `distributeSupplierComp(cToken, supplier)`. FIXED: use `accrualStart` (i.e. `≤`)
    so an index equal to `compInitialIndex` (freshly initialized, no rewards emitted) credits nothing. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  match subChecked s.supplyState.index
      (accrualStart (s.acct supplier).supplierIndex s.supplyState.index) with
  | none => none
  | some _ =>
    some { s with accts := s.accts.modify supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } }

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. FIXED likewise. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  match subChecked s.borrowState.index
      (accrualStart (s.acct borrower).borrowerIndex s.borrowState.index) with
  | none => none
  | some _ =>
    some { s with accts := s.accts.modify borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } }

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
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

-- Helper: subChecked succeeds exactly on `≤`.
theorem subChecked_some {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem updateSupply_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  simp only [updateCompSupplyIndex, subChecked_some h, accrueSide, fraction]
  by_cases hd : s.blockNumber - s.supplyState.block > 0
  · by_cases hs : s.supplyState.speed > 0
    · by_cases ht : totalSupply s > 0
      · simp [hd, hs, ht]
      · simp [hd, hs, ht]
    · simp [hd, hs]
  · have hbeq : s.supplyState.block = s.blockNumber := by omega
    cases s with
    | mk bn sup bor res accts =>
      cases sup with
      | mk si sb ss =>
        simp at h hbeq hd ⊢
        rw [hbeq]
        simp [hd]

theorem updateBorrow_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  simp only [updateCompBorrowIndex, subChecked_some h, accrueSide, fraction]
  by_cases hd : s.blockNumber - s.borrowState.block > 0
  · by_cases hs : s.borrowState.speed > 0
    · by_cases ht : totalBorrows s > 0
      · simp [hd, hs, ht]
      · simp [hd, hs, ht]
    · simp [hd, hs]
  · have hbeq : s.borrowState.block = s.blockNumber := by omega
    cases s with
    | mk bn sup bor res accts =>
      cases bor with
      | mk bi bb bs =>
        simp at h hbeq hd ⊢
        rw [hbeq]
        simp [hd]

-- The chosen start equals `accrualStart` (kept for reference; impl uses it directly).
theorem supplyStart_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
     else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0
  · simp [hr]
  · simp [hr]

theorem borrowStart_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
     else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0
  · simp [hr]
  · simp [hr]

theorem distributeSupply_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  simp only [distributeSupplierComp, subChecked_some h]

theorem distributeBorrow_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  simp only [distributeBorrowerComp, subChecked_some h]

theorem getD_modify_supplier (l : List Acct) (n m : Nat) (f : Acct → Acct) (d : Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD m d).supplierIndex = (l.getD m d).supplierIndex := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_modify]
  cases hOpt : l[m]? with
  | none =>
    simp [hOpt]
  | some a =>
    simp [hOpt]
    by_cases hnm : n = m
    · simp [hnm, hf]
    · simp [hnm]

theorem getD_modify_borrower (l : List Acct) (n m : Nat) (f : Acct → Acct) (d : Acct)
    (hf : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((l.modify n f).getD m d).borrowerIndex = (l.getD m d).borrowerIndex := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_modify]
  cases hOpt : l[m]? with
  | none =>
    simp [hOpt]
  | some a =>
    simp [hOpt]
    by_cases hnm : n = m
    · simp [hnm, hf]
    · simp [hnm]

-- accrueSide never decreases the index and sets block to now.
theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  dsimp

theorem acct_eq_getElem (s : St) (who : Account) (h : who < s.accts.length) :
    s.acct who = s.accts[who] := by
  unfold St.acct
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem acct_eq_noAcct (s : St) (who : Account) (h : ¬ who < s.accts.length) :
    s.acct who = noAcct := by
  unfold St.acct
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]
  rfl

theorem acct_mem (s : St) (who : Account) (h : who < s.accts.length) :
    s.acct who ∈ s.accts := by
  rw [acct_eq_getElem s who h]
  exact List.getElem_mem h

theorem accrualStart_le_new (rec oldIdx newIdx : Nat)
    (hrec : rec = 0 ∨ rec ≤ oldIdx) (hold : oldIdx ≤ newIdx) :
    accrualStart rec newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases hr : rec = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ newIdx
    · simp [hi]
    · simp [hi]
  · simp [hr]
    have hle : rec ≤ oldIdx := hrec.resolve_left hr
    have : rec ≤ newIdx := Nat.le_trans hle hold
    omega

theorem supplyRec_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index := by
  by_cases hlen : who < s.accts.length
  · have hmem := acct_mem s who hlen
    obtain ⟨_, _, hmemAll⟩ := hc
    have hle := (hmemAll _ hmem).1
    have heq : s.acct who = s.accts[who] := acct_eq_getElem s who hlen
    rw [heq] at hle ⊢
    by_cases hr : (s.accts[who]).supplierIndex = 0
    · left; exact hr
    · right; exact hle
  · rw [acct_eq_noAcct s who hlen]
    left; rfl

theorem borrowRec_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  by_cases hlen : who < s.accts.length
  · have hmem := acct_mem s who hlen
    obtain ⟨_, _, hmemAll⟩ := hc
    have hle := (hmemAll _ hmem).2
    have heq : s.acct who = s.accts[who] := acct_eq_getElem s who hlen
    rw [heq] at hle ⊢
    by_cases hr : (s.accts[who]).borrowerIndex = 0
    · left; exact hr
    · right; exact hle
  · rw [acct_eq_noAcct s who hlen]
    left; rfl

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' hComp
  simp only [comptroller] at hComp
  by_cases hBlock : s.supplyState.block ≤ s.blockNumber
  · let s1 : St := { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
    have hs1def : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := rfl
    have hUpd : updateCompSupplyIndex s = some s1 := by rw [hs1def]; exact updateSupply_some s hBlock
    simp [hUpd] at hComp
    have hs1acct : (s1.acct who).supplierIndex = (s.acct who).supplierIndex := by simp [hs1def, St.acct]
    have hs1acct2 : s1.acct who = s.acct who := by simp [hs1def, St.acct]
    have hs1sup : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by simp [hs1def]
    by_cases hStart : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index
    · have hDist := distributeSupply_some s1 who hStart
      rw [hDist] at hComp
      cases hComp
      refine ⟨hBlock, ?_, rfl⟩
      rw [hs1sup, hs1acct2] at hStart
      exact hStart
    · have hNone : distributeSupplierComp s1 who = none := by simp only [distributeSupplierComp, subChecked_none hStart]
      rw [hNone] at hComp
      cases hComp
  · have hUpdNone : updateCompSupplyIndex s = none := by simp only [updateCompSupplyIndex, subChecked_none hBlock]
    simp [hUpdNone] at hComp

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' hComp
  simp only [comptroller] at hComp
  by_cases hBlock : s.borrowState.block ≤ s.blockNumber
  · let s1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hs1def : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := rfl
    have hUpd : updateCompBorrowIndex s = some s1 := by rw [hs1def]; exact updateBorrow_some s hBlock
    simp [hUpd] at hComp
    have hs1acct2 : s1.acct who = s.acct who := by simp [hs1def, St.acct]
    have hs1bor : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hs1def]
    by_cases hStart : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index
    · have hDist := distributeBorrow_some s1 who hStart
      rw [hDist] at hComp
      cases hComp
      refine ⟨hBlock, ?_, rfl⟩
      rw [hs1bor, hs1acct2] at hStart
      exact hStart
    · have hNone : distributeBorrowerComp s1 who = none := by simp only [distributeBorrowerComp, subChecked_none hStart]
      rw [hNone] at hComp
      cases hComp
  · have hUpdNone : updateCompBorrowIndex s = none := by simp only [updateCompBorrowIndex, subChecked_none hBlock]
    simp [hUpdNone] at hComp

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' hComp
  simp only [comptroller] at hComp
  simp only [claimComp] at hComp
  by_cases hBlockB : s.borrowState.block ≤ s.blockNumber
  · let s1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hs1def : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := rfl
    have hUpdB : updateCompBorrowIndex s = some s1 := by rw [hs1def]; exact updateBorrow_some s hBlockB
    simp [hUpdB] at hComp
    by_cases hStartB : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index
    · let m1 : St := { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } }
      have hm1def : m1 = { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := rfl
      have hDistB : distributeBorrowerComp s1 who = some m1 := by rw [hm1def]; exact distributeBorrow_some s1 who hStartB
      simp [hDistB] at hComp
      -- supply update on m1
      by_cases hBlockS : m1.supplyState.block ≤ m1.blockNumber
      · let s2 : St := { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) }
        have hs2def : s2 = { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } := rfl
        have hUpdS : updateCompSupplyIndex m1 = some s2 := by rw [hs2def]; exact updateSupply_some m1 hBlockS
        simp [hUpdS] at hComp
        have hs2acct : s2.acct who = m1.acct who := by simp [hs2def, St.acct]
        have hs2sup : s2.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by simp [hs2def]
        by_cases hStartS : accrualStart (s2.acct who).supplierIndex s2.supplyState.index ≤ s2.supplyState.index
        · let m2 : St := { s2 with accts := s2.accts.modify who fun a => { a with supplierIndex := s2.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s2.supplyState.index) s2.supplyState.index } }
          have hm2def : m2 = { s2 with accts := s2.accts.modify who fun a => { a with supplierIndex := s2.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s2.supplyState.index) s2.supplyState.index } } := rfl
          have hDistS : distributeSupplierComp s2 who = some m2 := by rw [hm2def]; exact distributeSupply_some s2 who hStartS
          simp [hDistS] at hComp
          simp only [grant_eq] at hComp
          cases hComp with
          | refl =>
            refine ⟨m1, m2, ?_, ?_, rfl⟩
            · refine ⟨hBlockB, ?_, ?_⟩
              · have hs1acct : s1.acct who = s.acct who := by simp [hs1def, St.acct]
                have hs1bor : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hs1def]
                rw [hs1acct, hs1bor] at hStartB
                exact hStartB
              · simp [hm1def, hs1def]
            · refine ⟨hBlockS, ?_, ?_⟩
              · rw [hs2acct] at hStartS
                have hs2sup2 : s2.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := hs2sup
                rw [hs2sup2] at hStartS
                exact hStartS
              · simp [hm2def, hs2def]
        · have hNoneS : distributeSupplierComp s2 who = none := by simp only [distributeSupplierComp, subChecked_none hStartS]
          simp [hNoneS] at hComp
      · have hUpdNoneS : updateCompSupplyIndex m1 = none := by simp only [updateCompSupplyIndex, subChecked_none hBlockS]
        simp [hUpdNoneS] at hComp
    · have hNone : distributeBorrowerComp s1 who = none := by simp only [distributeBorrowerComp, subChecked_none hStartB]
      simp [hNone] at hComp
  · have hUpdNone : updateCompBorrowIndex s = none := by simp only [updateCompBorrowIndex, subChecked_none hBlockB]
    simp [hUpdNone] at hComp

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' hComp
  simp only [comptroller, setCompSpeedInternal] at hComp
  by_cases hSupNe : s.supplyState.speed ≠ a
  · have hBlockS : s.supplyState.block ≤ s.blockNumber := by
      by_cases h : s.supplyState.block ≤ s.blockNumber
      · exact h
      · exfalso
        have hUpdNone : updateCompSupplyIndex s = none := by simp [updateCompSupplyIndex, subChecked_none h]
        have hSetNone : setSupplySpeed s a = none := by simp [setSupplySpeed, hSupNe, hUpdNone]
        simp [hSetNone] at hComp
    have hSetSup : setSupplySpeed s a = some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
      simp [setSupplySpeed, hSupNe, updateSupply_some s hBlockS]
    simp [hSetSup] at hComp
    by_cases hBorNe : s.borrowState.speed ≠ b
    · have hBlockB : s.borrowState.block ≤ s.blockNumber := by
        by_cases h : s.borrowState.block ≤ s.blockNumber
        · exact h
        · exfalso
          have hUpdNone : updateCompBorrowIndex { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } = none := by simp [updateCompBorrowIndex, subChecked_none h]
          have hSetNone : setBorrowSpeed { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b = none := by simp [setBorrowSpeed, hBorNe, hUpdNone]
          simp [hSetNone] at hComp
      have hSetBor : setBorrowSpeed { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b = some { { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
        have hBorNeX : ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.speed ≠ b := hBorNe
        have hle : ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.block ≤ ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).blockNumber := hBlockB
        have hTot : totalBorrows { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } = totalBorrows s := rfl
        have hEq := updateBorrow_some _ hle
        simp [setBorrowSpeed, hBorNeX, hEq, hTot]
      simp [hSetBor] at hComp
      cases hComp
      refine ⟨?_, ?_, ?_⟩
      · intro _; exact hBlockS
      · intro _; exact hBlockB
      · simp [hSupNe, hBorNe]
    · have hBorEq : s.borrowState.speed = b := Decidable.not_not.mp hBorNe
      have hSetBor : setBorrowSpeed { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b = some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
        simp [setBorrowSpeed, hBorNe]
      simp [hSetBor] at hComp
      cases hComp
      refine ⟨?_, ?_, ?_⟩
      · intro _; exact hBlockS
      · intro hNe; exact absurd hNe hBorNe
      · simp [hSupNe, hBorEq]
  · have hSetSup : setSupplySpeed s a = some s := by simp [setSupplySpeed, hSupNe]
    simp [hSetSup] at hComp
    by_cases hBorNe : s.borrowState.speed ≠ b
    · have hBlockB : s.borrowState.block ≤ s.blockNumber := by
        by_cases h : s.borrowState.block ≤ s.blockNumber
        · exact h
        · exfalso
          have hUpdNone : updateCompBorrowIndex s = none := by simp [updateCompBorrowIndex, subChecked_none h]
          have hSetNone : setBorrowSpeed s b = none := by simp [setBorrowSpeed, hBorNe, hUpdNone]
          simp [hSetNone] at hComp
      have hSetBor : setBorrowSpeed s b = some { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
        simp [setBorrowSpeed, hBorNe, updateBorrow_some s hBlockB]
      simp [hSetBor] at hComp
      cases hComp
      refine ⟨?_, ?_, ?_⟩
      · intro hNe; exact absurd hNe hSupNe
      · intro _; exact hBlockB
      · have hSupEq : s.supplyState.speed = a := Decidable.not_not.mp hSupNe
        simp [hSupEq, hBorNe]
    · have hBorEq : s.borrowState.speed = b := Decidable.not_not.mp hBorNe
      have hSupEq : s.supplyState.speed = a := Decidable.not_not.mp hSupNe
      have hSetBor : setBorrowSpeed s b = some s := by simp [setBorrowSpeed, hBorNe]
      simp [hSetBor] at hComp
      cases hComp
      refine ⟨?_, ?_, ?_⟩
      · intro hNe; exact absurd hNe hSupNe
      · intro hNe; exact absurd hNe hBorNe
      · simp [hSupEq, hBorEq]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have hBlock : s.supplyState.block ≤ s.blockNumber := hc.1
    have hUpd := updateSupply_some s hBlock
    let s1 : St := { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
    have hs1def : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := rfl
    have hUpd2 : updateCompSupplyIndex s = some s1 := by rw [hs1def]; exact hUpd
    have hRec := supplyRec_le s who hc
    have hGe : s.supplyState.index ≤ s1.supplyState.index := by simp [hs1def]; exact accrueSide_index_ge _ _ _
    have hs1acct : s1.acct who = s.acct who := by simp [hs1def, St.acct]
    have hStart : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index := by
      rw [hs1acct]
      have hOld : s.supplyState.index ≤ s1.supplyState.index := by simpa [hs1def] using hGe
      exact accrualStart_le_new _ _ _ hRec hOld
    have hDist := distributeSupply_some s1 who hStart
    simp [comptroller, hUpd2, hDist]
  | borrowHook who =>
    have hBlock : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hUpd := updateBorrow_some s hBlock
    let s1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hs1def : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := rfl
    have hUpd2 : updateCompBorrowIndex s = some s1 := by rw [hs1def]; exact hUpd
    have hRec := borrowRec_le s who hc
    have hGe : s.borrowState.index ≤ s1.borrowState.index := by simp [hs1def]; exact accrueSide_index_ge _ _ _
    have hs1acct : s1.acct who = s.acct who := by simp [hs1def, St.acct]
    have hStart : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
      rw [hs1acct]
      have hOld : s.borrowState.index ≤ s1.borrowState.index := by simpa [hs1def] using hGe
      exact accrualStart_le_new _ _ _ hRec hOld
    have hDist := distributeBorrow_some s1 who hStart
    simp [comptroller, hUpd2, hDist]
  | claim who =>
    have hBlockB : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hBlockS0 : s.supplyState.block ≤ s.blockNumber := hc.1
    have hUpdB := updateBorrow_some s hBlockB
    let s1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hs1def : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := rfl
    have hUpdB2 : updateCompBorrowIndex s = some s1 := by rw [hs1def]; exact hUpdB
    have hRecB := borrowRec_le s who hc
    have hGeB : s.borrowState.index ≤ s1.borrowState.index := by simp [hs1def]; exact accrueSide_index_ge _ _ _
    have hs1acct : s1.acct who = s.acct who := by simp [hs1def, St.acct]
    have hStartB : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
      rw [hs1acct]
      have hOld : s.borrowState.index ≤ s1.borrowState.index := by simpa [hs1def] using hGeB
      exact accrualStart_le_new _ _ _ hRecB hOld
    have hDistB := distributeBorrow_some s1 who hStartB
    let m1 : St := { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } }
    have hm1def : m1 = { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := rfl
    have hDistB2 : distributeBorrowerComp s1 who = some m1 := by rw [hm1def]; exact hDistB
    have hm1sup : m1.supplyState = s.supplyState := by simp [hm1def, hs1def]
    have hm1bn : m1.blockNumber = s.blockNumber := by simp [hm1def, hs1def]
    have hm1supBlock : m1.supplyState.block ≤ m1.blockNumber := by simpa [hm1sup, hm1bn] using hBlockS0
    have hUpdS := updateSupply_some m1 hm1supBlock
    let s2 : St := { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) }
    have hs2def : s2 = { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } := rfl
    have hUpdS2 : updateCompSupplyIndex m1 = some s2 := by rw [hs2def]; exact hUpdS
    have hs2acct : s2.acct who = m1.acct who := by simp [hs2def, St.acct]
    have hRecS : (m1.acct who).supplierIndex = 0 ∨ (m1.acct who).supplierIndex ≤ m1.supplyState.index := by
      have hsup : ∀ a : Acct, ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } : Acct).supplierIndex = a.supplierIndex := fun a => rfl
      have h1 : (m1.acct who).supplierIndex = (s1.acct who).supplierIndex := by
        have hm1eq : (m1.acct who).supplierIndex = ((s1.accts.modify who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } : Acct)).getD who noAcct).supplierIndex := by simp [hm1def, St.acct]
        have hs1eq : (s1.acct who).supplierIndex = (s1.accts.getD who noAcct).supplierIndex := by simp [St.acct]
        have hmod := getD_modify_supplier _ _ _ _ _ hsup
        rw [hm1eq, hmod, ← hs1eq]
      have hs1a : s1.acct who = s.acct who := by simp [hs1def, St.acct]
      have hEqM : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by rw [h1, hs1a]
      have hEqI : m1.supplyState.index = s.supplyState.index := rfl
      cases supplyRec_le s who hc with
      | inl h0 => rw [hEqM]; exact Or.inl h0
      | inr hle => rw [hEqM, hEqI]; exact Or.inr hle
    have hGeS : m1.supplyState.index ≤ s2.supplyState.index := by simp [hs2def]; exact accrueSide_index_ge _ _ _
    have hStartS : accrualStart (s2.acct who).supplierIndex s2.supplyState.index ≤ s2.supplyState.index := by
      rw [hs2acct]
      have hOld : m1.supplyState.index ≤ s2.supplyState.index := by simpa [hs2def] using hGeS
      exact accrualStart_le_new _ _ _ hRecS hOld
    have hDistS := distributeSupply_some s2 who hStartS
    simp [comptroller, claimComp, hUpdB2, hDistB2, hUpdS2, hDistS, grant_eq]
  | setSpeeds a b =>
    have hBlockS : s.supplyState.block ≤ s.blockNumber := hc.1
    have hBlockB : s.borrowState.block ≤ s.blockNumber := hc.2.1
    by_cases hSupNe : s.supplyState.speed ≠ a
    · have hSetSup : setSupplySpeed s a = some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
        simp [setSupplySpeed, hSupNe, updateSupply_some s hBlockS]
      by_cases hBorNe : s.borrowState.speed ≠ b
      · have hBorNeX : ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.speed ≠ b := hBorNe
        have hle : ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.block ≤ ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).blockNumber := hBlockB
        have hTot : totalBorrows { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } = totalBorrows s := rfl
        have hEq := updateBorrow_some _ hle
        have hSetBor : setBorrowSpeed { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b = some { { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
          simp [setBorrowSpeed, hBorNeX, hEq, hTot]
        simp [comptroller, setCompSpeedInternal, hSetSup, hSetBor]
      · have hSetBor : setBorrowSpeed { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b = some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
          simp [setBorrowSpeed, hBorNe]
        simp [comptroller, setCompSpeedInternal, hSetSup, hSetBor]
    · have hSetSup : setSupplySpeed s a = some s := by simp [setSupplySpeed, hSupNe]
      by_cases hBorNe : s.borrowState.speed ≠ b
      · have hSetBor : setBorrowSpeed s b = some { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
          simp [setBorrowSpeed, hBorNe, updateBorrow_some s hBlockB]
        simp [comptroller, setCompSpeedInternal, hSetSup, hSetBor]
      · have hSetBor : setBorrowSpeed s b = some s := by simp [setBorrowSpeed, hBorNe]
        simp [comptroller, setCompSpeedInternal, hSetSup, hSetBor]
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
