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
    if 0 < deltaBlocks ∧ 0 < s.supplyState.speed then
      let supplyTokens := totalSupply s
      let compAccrued := deltaBlocks * s.supplyState.speed
      let ratio := if 0 < supplyTokens then fraction compAccrued supplyTokens else 0
      some { s with supplyState :=
        { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
    else if 0 < deltaBlocks then
      some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s

/-- `updateCompBorrowIndex(cToken, marketBorrowIndex)`. -/
def updateCompBorrowIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.borrowState.block with
  | none => none
  | some deltaBlocks =>
    if 0 < deltaBlocks ∧ 0 < s.borrowState.speed then
      let borrowAmount := totalBorrows s
      let compAccrued := deltaBlocks * s.borrowState.speed
      let ratio := if 0 < borrowAmount then fraction compAccrued borrowAmount else 0
      some { s with borrowState :=
        { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
    else if 0 < deltaBlocks then
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
  if 0 < amount ∧ amount ≤ s.reserve then
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

-- Basic facts
theorem sub_isSome_iff (a b : Nat) : (subChecked a b).isSome = decide (b ≤ a) := by
  unfold subChecked; by_cases h : b ≤ a <;> simp [h]

theorem sub_checked_some (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem accrualStart_zero_le (idx : Nat) : accrualStart 0 idx ≤ idx := by
  unfold accrualStart
  simp
  by_cases h2 : compInitialIndex ≤ idx <;> simp [h2]

theorem accrualStart_eq_fix (r idx : Nat) :
    (if r = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else r) = accrualStart r idx := by
  unfold accrualStart
  by_cases h : r = 0
  · simp [h]
  · simp [h]

theorem accrue_block_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide; by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrue_index_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide; by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h, Nat.le_add_right]

theorem modify_congr (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (heq : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil =>
    cases who <;> rfl
  | cons x xs ih =>
    cases who with
    | zero =>
      have heqx : f x = g x := by
        have h1 : (x :: xs).getD 0 noAcct = x := by simp
        rw [h1] at heq
        exact heq
      simp [List.modify, heqx]
    | succ n =>
      have heq' : f (xs.getD n noAcct) = g (xs.getD n noAcct) := by
        have h1 : (x :: xs).getD (n + 1) noAcct = xs.getD n noAcct := by simp
        rw [h1] at heq
        exact heq
      have e1 : (x :: xs).modify (n + 1) f = x :: xs.modify n f := by simp [List.modify]
      have e2 : (x :: xs).modify (n + 1) g = x :: xs.modify n g := by simp [List.modify]
      rw [e1, e2, ih n heq']

theorem updateSupply_some_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  simp only [updateCompSupplyIndex, sub_checked_some _ _ h, accrueSide, fraction]
  by_cases h1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
  · simp_all
    by_cases h2 : 0 < totalSupply s
    · have hc : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := ⟨h1.1, h1.2, h2⟩
      simp_all
    · have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := by omega
      simp_all
  · have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < totalSupply s) := by
      intro hcon; exact h1 ⟨hcon.1, hcon.2.1⟩
    simp_all
    by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · simp_all
    · have hbeq : s.supplyState.block = s.blockNumber := by omega
      simp_all
      cases s with | mk bn sup bor res accts =>
        cases sup with | mk idx blk spd =>
          simp at hbeq ⊢
          rw [hbeq]

theorem updateBorrow_some_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  simp only [updateCompBorrowIndex, sub_checked_some _ _ h, accrueSide, fraction]
  by_cases h1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
  · simp_all
    by_cases h2 : 0 < totalBorrows s
    · have hc : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := ⟨h1.1, h1.2, h2⟩
      simp_all
    · have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := by omega
      simp_all
  · have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < totalBorrows s) := by
      intro hcon; exact h1 ⟨hcon.1, hcon.2.1⟩
    simp_all
    by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · simp_all
    · have hbeq : s.borrowState.block = s.blockNumber := by omega
      simp_all
      cases s with | mk bn sup bor res accts =>
        cases bor with | mk idx blk spd =>
          simp at hbeq ⊢
          rw [hbeq]

theorem distribSupply_eq (s : St) (who : Account)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some
      { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have heq : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    accrualStart_eq_fix _ _
  have hsub : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    sub_checked_some _ _ hle
  have hfg : ((fun (a : Acct) => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) }) : Acct → Acct) (s.accts.getD who noAcct) = ((fun (a : Acct) => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) : Acct → Acct) (s.accts.getD who noAcct) := by simp only [St.acct]; rfl
  have hmod := modify_congr s.accts who ((fun (a : Acct) => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) }) : Acct → Acct) ((fun (a : Acct) => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) : Acct → Acct) hfg
  simp only [distributeSupplierComp, heq, hsub, St.withAcct, hmod]

theorem distribBorrow_eq (s : St) (who : Account)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some
      { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have heq : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    accrualStart_eq_fix _ _
  have hsub : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    sub_checked_some _ _ hle
  have hfg : ((fun (a : Acct) => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) }) : Acct → Acct) (s.accts.getD who noAcct) = ((fun (a : Acct) => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) : Acct → Acct) (s.accts.getD who noAcct) := by simp only [St.acct]; rfl
  have hmod := modify_congr s.accts who ((fun (a : Acct) => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) }) : Acct → Acct) ((fun (a : Acct) => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) : Acct → Acct) hfg
  simp only [distributeBorrowerComp, heq, hsub, St.withAcct, hmod]

theorem mem_le_supplyIndex (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  by_cases hm : who < s.accts.length
  · have hmem : s.accts[who]'hm ∈ s.accts := List.getElem_mem hm
    have hle := hc.2.2 _ hmem
    have h1 : s.accts.getD who noAcct = s.accts[who]'hm := by simp [List.getD, hm]
    rw [h1]
    exact hle.1
  · have h1 : s.accts.getD who noAcct = noAcct := by simp [List.getD, hm]
    rw [h1]
    exact Nat.zero_le _

theorem mem_le_borrowIndex (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  by_cases hm : who < s.accts.length
  · have hmem : s.accts[who]'hm ∈ s.accts := List.getElem_mem hm
    have hle := hc.2.2 _ hmem
    have h1 : s.accts.getD who noAcct = s.accts[who]'hm := by simp [List.getD, hm]
    rw [h1]
    exact hle.2
  · have h1 : s.accts.getD who noAcct = noAcct := by simp [List.getD, hm]
    rw [h1]
    exact Nat.zero_le _

theorem accrualStart_new_le (r oldIdx newIdx : Nat) (hle : r ≤ oldIdx) (hge : oldIdx ≤ newIdx) :
    accrualStart r newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases h : r = 0
  · simp [h]
    by_cases h2 : compInitialIndex ≤ newIdx <;> simp [h2]
  · simp [h]; omega

theorem distribSupply_succeed (s : St) (who : Account) (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  have heq := accrualStart_eq_fix (s.acct who).supplierIndex s.supplyState.index
  have hsub := sub_checked_some s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) hle
  simp [distributeSupplierComp, heq, hsub]

theorem distribBorrow_succeed (s : St) (who : Account) (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  have heq := accrualStart_eq_fix (s.acct who).borrowerIndex s.borrowState.index
  have hsub := sub_checked_some s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) hle
  simp [distributeBorrowerComp, heq, hsub]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' hs'
  unfold comptroller at hs'
  cases hupd : updateCompSupplyIndex s with
  | none => simp [hupd] at hs'
  | some s1 =>
    simp [hupd] at hs'
    have hle_block : s.supplyState.block ≤ s.blockNumber := by
      by_cases hle : s.supplyState.block ≤ s.blockNumber
      · exact hle
      · exfalso
        have hnone : updateCompSupplyIndex s = none := by
          unfold updateCompSupplyIndex
          have hsub : subChecked s.blockNumber s.supplyState.block = none := by
            unfold subChecked
            simp [hle]
          simp [hsub]
        rw [hnone] at hupd
        contradiction
    have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      have heq := updateSupply_some_of_le s hle_block
      rw [hupd] at heq
      cases heq
      rfl
    have heq_idx := accrualStart_eq_fix (s1.acct who).supplierIndex s1.supplyState.index
    have hle_idx : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index := by
      by_cases hle : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index
      · exact hle
      · exfalso
        have hnone : distributeSupplierComp s1 who = none := by
          unfold distributeSupplierComp
          have hsub : subChecked s1.supplyState.index (accrualStart (s1.acct who).supplierIndex s1.supplyState.index) = none := by
            unfold subChecked
            simp [hle]
          simp [heq_idx, hsub]
        rw [hnone] at hs'
        contradiction
    have hs2 := distribSupply_eq s1 who hle_idx
    have hs_eq : s' = { s1 with accts := s1.accts.modify who fun a => { a with supplierIndex := s1.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index) s1.supplyState.index } } := Option.some_inj.mp (hs'.symm.trans hs2)
    have hacct : s1.acct who = s.acct who := by simp [hs1, St.acct]
    have hidx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by simp [hs1]
    refine ⟨hle_block, ?_, ?_⟩
    · rw [hacct, hidx] at hle_idx
      exact hle_idx
    · subst hs1
      simpa using hs_eq

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' hs'
  unfold comptroller at hs'
  cases hupd : updateCompBorrowIndex s with
  | none => simp [hupd] at hs'
  | some s1 =>
    simp [hupd] at hs'
    have hle_block : s.borrowState.block ≤ s.blockNumber := by
      by_cases hle : s.borrowState.block ≤ s.blockNumber
      · exact hle
      · exfalso
        have hnone : updateCompBorrowIndex s = none := by
          unfold updateCompBorrowIndex
          have hsub : subChecked s.blockNumber s.borrowState.block = none := by
            unfold subChecked
            simp [hle]
          simp [hsub]
        rw [hnone] at hupd
        contradiction
    have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have heq := updateBorrow_some_of_le s hle_block
      rw [hupd] at heq
      cases heq
      rfl
    have heq_idx := accrualStart_eq_fix (s1.acct who).borrowerIndex s1.borrowState.index
    have hle_idx : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
      by_cases hle : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index
      · exact hle
      · exfalso
        have hnone : distributeBorrowerComp s1 who = none := by
          unfold distributeBorrowerComp
          have hsub : subChecked s1.borrowState.index (accrualStart (s1.acct who).borrowerIndex s1.borrowState.index) = none := by
            unfold subChecked
            simp [hle]
          simp [heq_idx, hsub]
        rw [hnone] at hs'
        contradiction
    have hs2 := distribBorrow_eq s1 who hle_idx
    have hs_eq : s' = { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := Option.some_inj.mp (hs'.symm.trans hs2)
    have hacct : s1.acct who = s.acct who := by simp [hs1, St.acct]
    have hidx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hs1]
    refine ⟨hle_block, ?_, ?_⟩
    · rw [hacct, hidx] at hle_idx
      exact hle_idx
    · subst hs1
      simpa using hs_eq

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' hs'
  unfold comptroller claimComp at hs'
  cases ht1 : updateCompBorrowIndex s with
  | none => simp [ht1] at hs'
  | some t1 =>
    simp [ht1] at hs'
    cases ht2 : distributeBorrowerComp t1 who with
    | none => simp [ht2] at hs'
    | some t2 =>
      simp [ht2] at hs'
      cases ht3 : updateCompSupplyIndex t2 with
      | none => simp [ht3] at hs'
      | some t3 =>
        simp [ht3] at hs'
        cases ht4 : distributeSupplierComp t3 who with
        | none => simp [ht4] at hs'
        | some t4 =>
          simp [ht4] at hs'
          have hle_bblock : s.borrowState.block ≤ s.blockNumber := by
            by_cases hle : s.borrowState.block ≤ s.blockNumber
            · exact hle
            · exfalso
              have hnone : updateCompBorrowIndex s = none := by
                unfold updateCompBorrowIndex
                have hsub : subChecked s.blockNumber s.borrowState.block = none := by unfold subChecked; simp [hle]
                simp [hsub]
              rw [hnone] at ht1
              contradiction
          have hs_t1 : t1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
            have heq := updateBorrow_some_of_le s hle_bblock
            rw [ht1] at heq
            cases heq
            rfl
          have heq_bidx := accrualStart_eq_fix (t1.acct who).borrowerIndex t1.borrowState.index
          have hle_bidx : accrualStart (t1.acct who).borrowerIndex t1.borrowState.index ≤ t1.borrowState.index := by
            by_cases hle : accrualStart (t1.acct who).borrowerIndex t1.borrowState.index ≤ t1.borrowState.index
            · exact hle
            · exfalso
              have hnone : distributeBorrowerComp t1 who = none := by
                unfold distributeBorrowerComp
                have hsub : subChecked t1.borrowState.index (accrualStart (t1.acct who).borrowerIndex t1.borrowState.index) = none := by unfold subChecked; simp [hle]
                simp [heq_bidx, hsub]
              rw [hnone] at ht2
              contradiction
          have hs_t2_eq := distribBorrow_eq t1 who hle_bidx
          have hs_t2 : t2 = { t1 with accts := t1.accts.modify who fun a => { a with borrowerIndex := t1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index } } := Option.some_inj.mp (ht2.symm.trans hs_t2_eq)
          have hle_sblock : t2.supplyState.block ≤ t2.blockNumber := by
            by_cases hle : t2.supplyState.block ≤ t2.blockNumber
            · exact hle
            · exfalso
              have hnone : updateCompSupplyIndex t2 = none := by
                unfold updateCompSupplyIndex
                have hsub : subChecked t2.blockNumber t2.supplyState.block = none := by unfold subChecked; simp [hle]
                simp [hsub]
              rw [hnone] at ht3
              contradiction
          have hs_t3 : t3 = { t2 with supplyState := accrueSide t2.supplyState t2.blockNumber (totalSupply t2) } := by
            have heq := updateSupply_some_of_le t2 hle_sblock
            rw [ht3] at heq
            cases heq
            rfl
          have heq_sidx := accrualStart_eq_fix (t3.acct who).supplierIndex t3.supplyState.index
          have hle_sidx : accrualStart (t3.acct who).supplierIndex t3.supplyState.index ≤ t3.supplyState.index := by
            by_cases hle : accrualStart (t3.acct who).supplierIndex t3.supplyState.index ≤ t3.supplyState.index
            · exact hle
            · exfalso
              have hnone : distributeSupplierComp t3 who = none := by
                unfold distributeSupplierComp
                have hsub : subChecked t3.supplyState.index (accrualStart (t3.acct who).supplierIndex t3.supplyState.index) = none := by unfold subChecked; simp [hle]
                simp [heq_sidx, hsub]
              rw [hnone] at ht4
              contradiction
          have hs_t4_eq := distribSupply_eq t3 who hle_sidx
          have hs_t4 : t4 = { t3 with accts := t3.accts.modify who fun a => { a with supplierIndex := t3.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex t3.supplyState.index) t3.supplyState.index } } := Option.some_inj.mp (ht4.symm.trans hs_t4_eq)
          have hgrant : grantCompInternal t4 who = grant t4 who := by
            by_cases h : 0 < (t4.acct who).accrued ∧ (t4.acct who).accrued ≤ t4.reserve
            · simp [grantCompInternal, grant, h]
              have hfg : ((fun (a : Acct) => { a with accrued := 0, wallet := a.wallet + (t4.acct who).accrued }) : Acct → Acct) (t4.accts.getD who noAcct) = ((fun (a : Acct) => { a with accrued := 0, wallet := a.wallet + a.accrued }) : Acct → Acct) (t4.accts.getD who noAcct) := by simp [St.acct]
              have hmod := modify_congr t4.accts who ((fun (a : Acct) => { a with accrued := 0, wallet := a.wallet + (t4.acct who).accrued }) : Acct → Acct) ((fun (a : Acct) => { a with accrued := 0, wallet := a.wallet + a.accrued }) : Acct → Acct) hfg
              simp [hmod]
            · simp [grantCompInternal, grant, h]
          have hs_eq : grant t4 who = s' := hgrant.symm.trans hs'
          have hacct_b : t1.acct who = s.acct who := by simp [hs_t1, St.acct]
          have hidx_b : t1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hs_t1]
          have haccts_b : t1.accts = s.accts := by simp [hs_t1]
          have hb1 : BorrowDistributed s who t2 := by
            have hacct2 : t1.acct who = s.acct who := hacct_b
            have hidx2 : t1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := hidx_b
            refine ⟨hle_bblock, ?_, ?_⟩
            · rw [hacct_b, hidx_b] at hle_bidx
              exact hle_bidx
            · have h2 : t2 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
                subst hs_t1
                subst hs_t2
                simp
              exact h2
          have hacct_s : t3.acct who = t2.acct who := by simp [hs_t3, St.acct]
          have hidx_s : t3.supplyState.index = (accrueSide t2.supplyState t2.blockNumber (totalSupply t2)).index := by simp [hs_t3]
          have hs1 : SupplyDistributed t2 who t4 := by
            refine ⟨hle_sblock, ?_, ?_⟩
            · rw [hacct_s, hidx_s] at hle_sidx
              exact hle_sidx
            · subst hs_t3
              subst hs_t4
              simp
          exact ⟨t2, t4, hb1, hs1, hs_eq.symm⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' hs'
  unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed at hs'
  by_cases heq1 : s.supplyState.speed = a
  · simp [heq1] at hs'
    by_cases heq2 : s.borrowState.speed = b
    · simp [heq2] at hs'
      have hs_eq : s' = s := hs'.symm
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exfalso
        exact hne heq1
      · intro hne
        exfalso
        exact hne heq2
      · rw [hs_eq]
        simp [heq1, heq2]
    · have hne2 : s.borrowState.speed ≠ b := by simp [heq2]
      simp [hne2] at hs'
      cases hupd2 : updateCompBorrowIndex s with
      | none => simp [hupd2] at hs'
      | some t2 =>
        simp [hupd2] at hs'
        have hle2 : s.borrowState.block ≤ s.blockNumber := by
          by_cases hle : s.borrowState.block ≤ s.blockNumber
          · exact hle
          · exfalso
            have hnone : updateCompBorrowIndex s = none := by
              unfold updateCompBorrowIndex
              have hsub : subChecked s.blockNumber s.borrowState.block = none := by unfold subChecked; simp [hle]
              simp [hsub]
            rw [hnone] at hupd2
            contradiction
        have hs_t2 : t2 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
          Option.some_inj.mp (hupd2.symm.trans (updateBorrow_some_of_le s hle2))
        have hs_eq : s' = { t2 with borrowState := { t2.borrowState with speed := b } } := hs'.symm
        refine ⟨?_, ?_, ?_⟩
        · intro hne
          exfalso
          exact hne heq1
        · intro hne
          have : s.borrowState.block ≤ s.blockNumber := hle2
          exact this
        · subst hs_t2
          rw [hs_eq]
          simp [heq1, heq2]
  · have hne1 : s.supplyState.speed ≠ a := by simp [heq1]
    simp [hne1] at hs'
    cases hupd1 : updateCompSupplyIndex s with
    | none => simp [hupd1] at hs'
    | some t1 =>
      simp [hupd1] at hs'
      have hle1 : s.supplyState.block ≤ s.blockNumber := by
        by_cases hle : s.supplyState.block ≤ s.blockNumber
        · exact hle
        · exfalso
          have hnone : updateCompSupplyIndex s = none := by
            unfold updateCompSupplyIndex
            have hsub : subChecked s.blockNumber s.supplyState.block = none := by unfold subChecked; simp [hle]
            simp [hsub]
          rw [hnone] at hupd1
          contradiction
      have hs_t1 : t1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
        Option.some_inj.mp (hupd1.symm.trans (updateSupply_some_of_le s hle1))
      have heq2 : t1.borrowState.speed = s.borrowState.speed := by simp [hs_t1]
      by_cases heq2b : t1.borrowState.speed = b
      · simp [heq2b] at hs'
        have hs_eq : s' = { t1 with supplyState := { t1.supplyState with speed := a } } := hs'.symm
        have hbor_eq : s.borrowState.speed = b := by rw [← heq2, heq2b]
        refine ⟨?_, ?_, ?_⟩
        · intro hne
          exact hle1
        · intro hne
          exfalso
          exact hne hbor_eq
        · subst hs_t1
          rw [hs_eq]
          simp [heq1, hbor_eq]
      · have hne2 : t1.borrowState.speed ≠ b := by simp [heq2b]
        have hne2s : ({ t1 with supplyState := { t1.supplyState with speed := a } }).borrowState.speed ≠ b := by simp [hne2]
        simp [hne2s] at hs'
        cases hupd2 : updateCompBorrowIndex { t1 with supplyState := { t1.supplyState with speed := a } } with
        | none => simp [hupd2] at hs'
        | some t2 =>
          simp [hupd2] at hs'
          have hle2 : ({ t1 with supplyState := { t1.supplyState with speed := a } }).borrowState.block ≤ ({ t1 with supplyState := { t1.supplyState with speed := a } }).blockNumber := by
            by_cases hle : ({ t1 with supplyState := { t1.supplyState with speed := a } }).borrowState.block ≤ ({ t1 with supplyState := { t1.supplyState with speed := a } }).blockNumber
            · exact hle
            · exfalso
              have hnone : updateCompBorrowIndex { t1 with supplyState := { t1.supplyState with speed := a } } = none := by
                unfold updateCompBorrowIndex
                have hsub : subChecked ({ t1 with supplyState := { t1.supplyState with speed := a } }).blockNumber ({ t1 with supplyState := { t1.supplyState with speed := a } }).borrowState.block = none := by unfold subChecked; simp [hle]
                simp [hsub]
              rw [hnone] at hupd2
              contradiction
          have ht1s_eq : ({ t1 with supplyState := { t1.supplyState with speed := a } }).borrowState = t1.borrowState := by simp
          have ht1s_bn : ({ t1 with supplyState := { t1.supplyState with speed := a } }).blockNumber = t1.blockNumber := by simp
          have hs_t2 : t2 = { ({ t1 with supplyState := { t1.supplyState with speed := a } }) with borrowState := accrueSide t1.borrowState t1.blockNumber (totalBorrows t1) } := by
            have heq := updateBorrow_some_of_le { t1 with supplyState := { t1.supplyState with speed := a } } (by simpa [ht1s_eq, ht1s_bn] using hle2)
            have htot : totalBorrows { t1 with supplyState := { t1.supplyState with speed := a } } = totalBorrows t1 := by simp [totalBorrows]
            have heq2 : accrueSide ({ t1 with supplyState := { t1.supplyState with speed := a } }).borrowState ({ t1 with supplyState := { t1.supplyState with speed := a } }).blockNumber (totalBorrows { t1 with supplyState := { t1.supplyState with speed := a } }) = accrueSide t1.borrowState t1.blockNumber (totalBorrows t1) := by rw [ht1s_eq, ht1s_bn, htot]
            rw [heq2] at heq
            exact Option.some_inj.mp (hupd2.symm.trans heq)
          have hs_eq : s' = { t2 with borrowState := { t2.borrowState with speed := b } } := hs'.symm
          have hle1' : s.supplyState.block ≤ s.blockNumber := hle1
          have hle2' : s.borrowState.block ≤ s.blockNumber := by
            have h1 : t1.borrowState.block = s.borrowState.block := by simp [hs_t1]
            have h2 : t1.blockNumber = s.blockNumber := by simp [hs_t1]
            have hb : t1.borrowState.block ≤ t1.blockNumber := by
              have ht1b : ({ t1 with supplyState := { t1.supplyState with speed := a } }).borrowState.block = t1.borrowState.block := by simp
              have ht1n : ({ t1 with supplyState := { t1.supplyState with speed := a } }).blockNumber = t1.blockNumber := by simp
              simpa [ht1b, ht1n] using hle2
            simpa [h1, h2] using hb
          refine ⟨?_, ?_, ?_⟩
          · intro hne
            exact hle1'
          · intro hne
            exact hle2'
          · subst hs_t1
            subst hs_t2
            rw [hs_eq]
            simp [heq1, heq2b, totalBorrows, totalSupply]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    have hle1 : s.supplyState.block ≤ s.blockNumber := hc.1
    have hupd := updateSupply_some_of_le s hle1
    have hge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_index_ge _ _ _
    have hle_mem := mem_le_supplyIndex s who hc
    have hle_new : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrualStart_new_le _ _ _ hle_mem hge
    have hle_t1 : accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.acct who).supplierIndex) ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index)) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index)) := hle_new
    simp [hupd, distribSupply_succeed _ _ hle_t1]
  | borrowHook who =>
    unfold comptroller
    have hle1 : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hupd := updateBorrow_some_of_le s hle1
    have hge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_index_ge _ _ _
    have hle_mem := mem_le_borrowIndex s who hc
    have hle_new : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrualStart_new_le _ _ _ hle_mem hge
    have hle_t1 : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.acct who).borrowerIndex)) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)) := hle_new
    simp [hupd, distribBorrow_succeed _ _ hle_t1]
  | claim who =>
    unfold comptroller claimComp
    have hle_b : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hupd_b := updateBorrow_some_of_le s hle_b
    have hge_b : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrue_index_ge _ _ _
    have hle_mem_b := mem_le_borrowIndex s who hc
    have hle_new_b : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrualStart_new_le _ _ _ hle_mem_b hge_b
    have hle_t1 : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.acct who).borrowerIndex)) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)) := hle_new_b
    have hdist_b := distribBorrow_eq ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who hle_t1
    have ht1 : updateCompBorrowIndex s = some ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := hupd_b
    have ht2 : distributeBorrowerComp ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who = some ({ ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) with accts := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a => { a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) } }) := hdist_b
    simp [ht1, ht2]
    have hle_s : (({ ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) with accts := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a => { a with borrowerIndex := ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index))) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)) } }).supplyState.block)) ≤ (((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) with accts := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a => { a with borrowerIndex := ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index))) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)) } }).blockNumber)) := by simpa using hc.1
    simp [updateSupply_some_of_le _ hle_s]
    sorry
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed
    by_cases heq1 : s.supplyState.speed = a
    · simp [heq1]
      by_cases heq2 : s.borrowState.speed = b
      · simp [heq2]
      · have hne2 : s.borrowState.speed ≠ b := by simp [heq2]
        simp [hne2]
        have hle2 : s.borrowState.block ≤ s.blockNumber := hc.2.1
        simp [updateBorrow_some_of_le s hle2]
    · have hne1 : s.supplyState.speed ≠ a := by simp [heq1]
      simp [hne1]
      have hle1 : s.supplyState.block ≤ s.blockNumber := hc.1
      simp [updateSupply_some_of_le s hle1]
      have hle2 : s.borrowState.block ≤ s.blockNumber := hc.2.1
      simp [updateBorrow_some_of_le _ hle2]

end CompRewards
