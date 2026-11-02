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
  if 0 < (s.acct user).accrued ∧ (s.acct user).accrued ≤ s.reserve then
    { s with reserve := s.reserve - (s.acct user).accrued,
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

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := rfl

theorem accrualStart_le (recorded index : Nat) (hle : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr, hle]

theorem supplierStart_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then
      compInitialIndex else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ s.supplyState.index
    · simp [hr, hi]
    · simp [hr, hi]
  · simp only [hr, ↓reduceIte]
    have : ¬ ((s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index) := by
      simp [hr]
    simp [this, hr]

theorem borrowerStart_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then
      compInitialIndex else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ s.borrowState.index
    · simp [hr, hi]
    · simp [hr, hi]
  · simp only [hr, ↓reduceIte]
    have : ¬ ((s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index) := by
      simp [hr]
    simp [this, hr]

theorem updateSupply_some (s : St) (s' : St)
    (h : updateCompSupplyIndex s = some s') :
    s.supplyState.block ≤ s.blockNumber ∧
    s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked at h
  dsimp only at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp [hb] at h
    by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · simp [hd] at h
      cases h
      refine ⟨hb, ?_⟩
      unfold accrueSide fraction
      have h1 : 0 < s.blockNumber - s.supplyState.block := hd.1
      have h2 : 0 < s.supplyState.speed := hd.2
      by_cases ht : 0 < totalSupply s
      · simp [h1, h2, ht]
      · have ht0 : totalSupply s = 0 := by omega
        simp [h1, h2, ht, ht0, accrueSide]
    · simp [hd] at h
      by_cases hd2 : s.blockNumber - s.supplyState.block > 0
      · simp [hd2] at h
        cases h
        refine ⟨hb, ?_⟩
        have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧
            0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
          intro hcon; exact hd ⟨hcon.1, hcon.2.1⟩
        simp [accrueSide, hneg]
      · simp [hd2] at h
        cases h
        have hbeq : s.supplyState.block = s.blockNumber := by omega
        have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
        refine ⟨hb, ?_⟩
        have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) = s.supplyState := by
          cases hside : s.supplyState with
          | mk idx blk spd =>
            simp [hside] at hbeq hzero ⊢
            unfold accrueSide
            simp [hzero, hbeq]
        simp [hacc]
  · simp [hb] at h

theorem updateBorrow_some (s : St) (s' : St)
    (h : updateCompBorrowIndex s = some s') :
    s.borrowState.block ≤ s.blockNumber ∧
    s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked at h
  dsimp only at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp [hb] at h
    by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · simp [hd] at h
      cases h
      refine ⟨hb, ?_⟩
      unfold accrueSide fraction
      have h1 : 0 < s.blockNumber - s.borrowState.block := hd.1
      have h2 : 0 < s.borrowState.speed := hd.2
      by_cases ht : 0 < totalBorrows s
      · simp [h1, h2, ht]
      · have ht0 : totalBorrows s = 0 := by omega
        simp [h1, h2, ht, ht0, accrueSide]
    · simp [hd] at h
      by_cases hd2 : s.blockNumber - s.borrowState.block > 0
      · simp [hd2] at h
        cases h
        refine ⟨hb, ?_⟩
        have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧
            0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          intro hcon; exact hd ⟨hcon.1, hcon.2.1⟩
        simp [accrueSide, hneg]
      · simp [hd2] at h
        cases h
        have hbeq : s.borrowState.block = s.blockNumber := by omega
        have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
        refine ⟨hb, ?_⟩
        have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) = s.borrowState := by
          cases hside : s.borrowState with
          | mk idx blk spd =>
            simp [hside] at hbeq hzero ⊢
            unfold accrueSide
            simp [hzero, hbeq]
        simp [hacc]
  · simp [hb] at h

theorem modify_congr_at (l : List Acct) (n : Nat) (d : Acct) (f g : Acct → Acct)
    (h : f (l.getD n d) = g (l.getD n d)) : l.modify n f = l.modify n g := by
  induction l generalizing n with
  | nil =>
    simp
  | cons x xs ih =>
    cases n with
    | zero =>
      simp at h ⊢
      rw [h]
    | succ n =>
      simp
      apply ih
      exact h

theorem distributeSupply_eq (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp subChecked at h
  dsimp only at h
  have hst : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then
      compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    supplierStart_eq s who
  rw [hst] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [hle, ↓reduceIte] at h
    cases h
    refine ⟨hle, ?_⟩
    show s.withAcct who _ = _
    unfold St.withAcct
    congr 1
    apply modify_congr_at (d := noAcct)
    simp only [St.acct, creditFor, mulDouble]
  · simp only [hle, ↓reduceIte] at h
    cases h

theorem distributeBorrow_eq (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp subChecked at h
  dsimp only at h
  have hst : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then
      compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    borrowerStart_eq s who
  rw [hst] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h
    cases h
    refine ⟨hle, ?_⟩
    show s.withAcct who _ = _
    unfold St.withAcct
    congr 1
    apply modify_congr_at (d := noAcct)
    simp only [St.acct, creditFor, mulDouble]
  · simp only [hle, ↓reduceIte] at h
    cases h

theorem recorded_le_supply (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  unfold St.acct
  have heq : s.accts.getD who noAcct = (s.accts[who]?).getD noAcct := rfl
  rw [heq]
  match hm : s.accts[who]? with
  | none =>
    simp [hm, noAcct]
  | some a =>
    simp [hm]
    have hmem := List.mem_of_getElem? hm
    have h2 := hall a hmem
    exact h2.1

theorem recorded_le_borrow (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  unfold St.acct
  have heq : s.accts.getD who noAcct = (s.accts[who]?).getD noAcct := rfl
  rw [heq]
  match hm : s.accts[who]? with
  | none =>
    simp [hm, noAcct]
  | some a =>
    simp [hm]
    have hmem := List.mem_of_getElem? hm
    have h2 := hall a hmem
    exact h2.2

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, Nat.le_add_right]
  · simp [h]

theorem consistent_accrual_supply (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  apply accrualStart_le
  calc (s.acct who).supplierIndex ≤ s.supplyState.index := recorded_le_supply s who hc
    _ ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
        accrueSide_index_ge _ _ _

theorem consistent_accrual_borrow (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  apply accrualStart_le
  calc (s.acct who).borrowerIndex ≤ s.borrowState.index := recorded_le_borrow s who hc
    _ ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
        accrueSide_index_ge _ _ _

theorem supplyUpdate_exists (s : St) (hc : Consistent s) :
    ∃ t, updateCompSupplyIndex s = some t := by
  unfold updateCompSupplyIndex subChecked
  simp [hc.1]
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp [hd]
  · simp [hd]
    by_cases hd2 : s.blockNumber - s.supplyState.block > 0
    · simp [hd2]
    · simp [hd2]

theorem borrowUpdate_exists (s : St) (hc : Consistent s) :
    ∃ t, updateCompBorrowIndex s = some t := by
  unfold updateCompBorrowIndex subChecked
  simp [hc.2.1]
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp [hd]
  · simp [hd]
    by_cases hd2 : s.blockNumber - s.borrowState.block > 0
    · simp [hd2]
    · simp [hd2]

theorem supplyHook_some (s : St) (who : Account) (hc : Consistent s) :
    ∃ s', comptroller s (.supplyHook who) = some s' := by
  unfold comptroller
  simp only
  obtain ⟨t, ht⟩ := supplyUpdate_exists s hc
  simp [ht]
  have hut := (updateSupply_some s t ht).2
  have haccts : t.accts = s.accts := by simp [hut]
  have hblock : t.blockNumber = s.blockNumber := by simp [hut]
  have hidx : t.supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by simp [hut]
  have hacct : (t.acct who).supplierIndex = (s.acct who).supplierIndex := by
    simp [St.acct, haccts]
  have h2 := consistent_accrual_supply s who hc
  have h2t : accrualStart (t.acct who).supplierIndex t.supplyState.index ≤ t.supplyState.index := by
    rw [hacct, hidx]; exact h2
  unfold distributeSupplierComp subChecked
  dsimp only
  rw [supplierStart_eq t who]
  simp [h2t]

theorem borrowHook_some (s : St) (who : Account) (hc : Consistent s) :
    ∃ s', comptroller s (.borrowHook who) = some s' := by
  unfold comptroller
  simp only
  obtain ⟨t, ht⟩ := borrowUpdate_exists s hc
  simp [ht]
  have hut := (updateBorrow_some s t ht).2
  have haccts : t.accts = s.accts := by simp [hut]
  have hblock : t.blockNumber = s.blockNumber := by simp [hut]
  have hidx : t.borrowState.index =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hut]
  have hacct : (t.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
    simp [St.acct, haccts]
  have h2 := consistent_accrual_borrow s who hc
  have h2t : accrualStart (t.acct who).borrowerIndex t.borrowState.index ≤ t.borrowState.index := by
    rw [hacct, hidx]; exact h2
  unfold distributeBorrowerComp subChecked
  dsimp only
  rw [borrowerStart_eq t who]
  simp [h2t]

-- Per-account and global potentials for boundedness.
def unindexedSupply (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def unindexedBorrow (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
def pendSupAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)
def pendBorAcct (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)
def pendAcct (s : St) (a : Acct) : Nat := pendSupAcct s a + pendBorAcct s a
def Hwho (s : St) (who : Account) : Nat :=
  (s.creditedTo who) * doubleScale + pendAcct s (s.acct who) +
  (if (s.acct who).supply > 0 then unindexedSupply s * doubleScale else 0) +
  (if (s.acct who).borrow > 0 then unindexedBorrow s * doubleScale else 0)

theorem accrualStart_mono_idx (r idx idx' : Nat) (hle : idx ≤ idx') :
    accrualStart r idx ≤ accrualStart r idx' := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ idx
    · have hi' : compInitialIndex ≤ idx' := by omega
      simp [hi, hi']
    · by_cases hi' : compInitialIndex ≤ idx'
      · simp [hi, hi']
      · simp [hi, hi']
  · simp [hr]

theorem pendSup_step_le (sv rv idx idx' : Nat) (hle : idx ≤ idx') :
    sv * (idx' - accrualStart rv idx') ≤ sv * (idx - accrualStart rv idx) + sv * (idx' - idx) := by
  have hstart : accrualStart rv idx ≤ accrualStart rv idx' :=
    accrualStart_mono_idx rv idx idx' hle
  have hidx : idx' - accrualStart rv idx' ≤ (idx - accrualStart rv idx) + (idx' - idx) := by
    omega
  calc sv * (idx' - accrualStart rv idx')
      ≤ sv * ((idx - accrualStart rv idx) + (idx' - idx)) :=
        Nat.mul_le_mul_left sv hidx
    _ = sv * (idx - accrualStart rv idx) + sv * (idx' - idx) := by
        rw [Nat.mul_add]

theorem pendBor_step_le (sv rv idx idx' : Nat) (hle : idx ≤ idx') :
    sv * (idx' - accrualStart rv idx') ≤ sv * (idx - accrualStart rv idx) + sv * (idx' - idx) := by
  have hstart : accrualStart rv idx ≤ accrualStart rv idx' :=
    accrualStart_mono_idx rv idx idx' hle
  have hidx : idx' - accrualStart rv idx' ≤ (idx - accrualStart rv idx) + (idx' - idx) := by
    omega
  calc sv * (idx' - accrualStart rv idx')
      ≤ sv * ((idx - accrualStart rv idx) + (idx' - idx)) :=
        Nat.mul_le_mul_left sv hidx
    _ = sv * (idx - accrualStart rv idx) + sv * (idx' - idx) := by
        rw [Nat.mul_add]

theorem mem_supply_le_sum (l : List Acct) (a : Acct) (hm : a ∈ l) :
    a.supply ≤ (l.map Acct.supply).sum := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    simp at hm ⊢
    cases hm with
    | inl heq =>
      rw [heq]
      exact Nat.le_add_right _ _
    | inr hmem =>
      have h1 := ih hmem
      calc a.supply ≤ (xs.map Acct.supply).sum := h1
        _ ≤ x.supply + (xs.map Acct.supply).sum := Nat.le_add_left _ _
        _ = ((x :: xs).map Acct.supply).sum := by simp

theorem mem_borrow_le_sum (l : List Acct) (a : Acct) (hm : a ∈ l) :
    a.borrow ≤ (l.map Acct.borrow).sum := by
  induction l with
  | nil => simp at hm
  | cons x xs ih =>
    simp at hm ⊢
    cases hm with
    | inl heq =>
      rw [heq]
      exact Nat.le_add_right _ _
    | inr hmem =>
      have h1 := ih hmem
      calc a.borrow ≤ (xs.map Acct.borrow).sum := h1
        _ ≤ x.borrow + (xs.map Acct.borrow).sum := Nat.le_add_left _ _
        _ = ((x :: xs).map Acct.borrow).sum := by simp

theorem supply_le_total (s : St) (who : Account) : (s.acct who).supply ≤ totalSupply s := by
  unfold totalSupply St.acct
  have heq : s.accts.getD who noAcct = (s.accts[who]?).getD noAcct := rfl
  rw [heq]
  match hm : s.accts[who]? with
  | none =>
    simp [hm, noAcct]
  | some a =>
    simp [hm]
    have hmem := List.mem_of_getElem? hm
    exact mem_supply_le_sum s.accts a hmem

theorem borrow_le_total (s : St) (who : Account) : (s.acct who).borrow ≤ totalBorrows s := by
  unfold totalBorrows St.acct
  have heq : s.accts.getD who noAcct = (s.accts[who]?).getD noAcct := rfl
  rw [heq]
  match hm : s.accts[who]? with
  | none =>
    simp [hm, noAcct]
  | some a =>
    simp [hm]
    have hmem := List.mem_of_getElem? hm
    exact mem_borrow_le_sum s.accts a hmem

theorem div_mul_le (x S : Nat) : x / S * S ≤ x := Nat.div_mul_le_self x S

theorem credit_scaled_le (units delta : Nat) :
    (units * delta / doubleScale) * doubleScale ≤ units * delta :=
  Nat.div_mul_le_self _ _

theorem index_growth_bound (deltaB speed total : Nat) :
    (deltaB * speed * doubleScale / total) * total ≤ deltaB * speed * doubleScale := by
  by_cases ht : total = 0
  · simp [ht]
  · exact Nat.div_mul_le_self _ _

theorem getD_oob (l : List Acct) (n : Nat) (d : Acct) (h : ¬ n < l.length) :
    l.getD n d = d := by
  have hle : l.length ≤ n := by omega
  have hnone : l[n]? = none := List.getElem?_eq_none hle
  simp [List.getD, hnone]

theorem getD_modify_ne (l : List Acct) (tgt who : Nat) (d : Acct) (f : Acct → Acct)
    (hne : tgt ≠ who) : (l.modify tgt f).getD who d = l.getD who d := by
  induction l generalizing tgt who with
  | nil => simp
  | cons x xs ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => simp at hne
      | succ who => simp
    | succ tgt =>
      cases who with
      | zero => simp
      | succ who =>
        simp
        apply ih
        omega

theorem getD_modify_eq (l : List Acct) (n : Nat) (d : Acct) (f : Acct → Acct)
    (h : n < l.length) : (l.modify n f).getD n d = f (l.getD n d) := by
  have hlen : n < (l.modify n f).length := by
    rw [List.length_modify]
    exact h
  have h1 : (l.modify n f).getD n d = (l.modify n f)[n] := by
    symm
    apply List.getElem_eq_getD
  have h2 : l.getD n d = l[n] := by
    symm
    apply List.getElem_eq_getD
  rw [h1, h2]
  have h3 : (l.modify n f)[n] = f (l[n]) := by
    simpa using List.getElem_modify f n l n hlen
  exact h3

theorem supply_after_supplyDistrib (s : St) (tgt who : Account) (s' : St)
    (h : SupplyDistributed s tgt s') : (s'.acct who).supply = (s.acct who).supply := by
  unfold SupplyDistributed at h
  obtain ⟨_, _, rfl⟩ := h
  simp only [St.acct]
  by_cases heq : tgt = who
  · rw [heq]
    by_cases hb : who < s.accts.length
    · rw [getD_modify_eq _ _ _ _ hb]
    · have h1 : ¬ who < (s.accts.modify who fun a =>
          { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex
                       (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).length := by
        rw [List.length_modify]
        exact hb
      rw [getD_oob _ _ _ h1, getD_oob _ _ _ hb]
  · rw [getD_modify_ne _ _ _ _ _ heq]

theorem borrow_after_supplyDistrib (s : St) (tgt who : Account) (s' : St)
    (h : SupplyDistributed s tgt s') : (s'.acct who).borrow = (s.acct who).borrow := by
  unfold SupplyDistributed at h
  obtain ⟨_, _, rfl⟩ := h
  simp only [St.acct]
  by_cases heq : tgt = who
  · rw [heq]
    by_cases hb : who < s.accts.length
    · rw [getD_modify_eq _ _ _ _ hb]
    · have h1 : ¬ who < (s.accts.modify who fun a =>
          { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex
                       (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).length := by
        rw [List.length_modify]
        exact hb
      rw [getD_oob _ _ _ h1, getD_oob _ _ _ hb]
  · rw [getD_modify_ne _ _ _ _ _ heq]

theorem borrow_mul_ratio_le (s : St) (who : Account) :
    (s.acct who).borrow *
      ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) ≤
      unindexedBorrow s * doubleScale := by
  unfold unindexedBorrow accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧
      0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp [h]
    have h1 : (s.acct who).borrow ≤ totalBorrows s := borrow_le_total s who
    have h2 : ((s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale /
        totalBorrows s) * totalBorrows s ≤
        (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale :=
      Nat.div_mul_le_self _ _
    calc (s.acct who).borrow *
          ((s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale /
            totalBorrows s)
        ≤ totalBorrows s *
          ((s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale /
            totalBorrows s) :=
          Nat.mul_le_mul_right _ h1
      _ = ((s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale /
          totalBorrows s) * totalBorrows s := by
          rw [Nat.mul_comm]
      _ ≤ (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale := h2
      _ = ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale := by
          rw [Nat.mul_assoc]
  · simp [h]

theorem wallet_after_supplyDistrib (s : St) (tgt who : Account) (s' : St)
    (h : SupplyDistributed s tgt s') : (s'.acct who).wallet = (s.acct who).wallet := by
  unfold SupplyDistributed at h
  obtain ⟨_, _, rfl⟩ := h
  simp only [St.acct]
  by_cases heq : tgt = who
  · rw [heq]
    by_cases hb : who < s.accts.length
    · rw [getD_modify_eq _ _ _ _ hb]
    · have h1 : ¬ who < (s.accts.modify who fun a =>
          { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex
                       (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).length := by
        rw [List.length_modify]
        exact hb
      rw [getD_oob _ _ _ h1, getD_oob _ _ _ hb]
  · rw [getD_modify_ne _ _ _ _ _ heq]

theorem borrowerIndex_after_supplyDistrib (s : St) (tgt who : Account) (s' : St)
    (h : SupplyDistributed s tgt s') :
    (s'.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
  unfold SupplyDistributed at h
  obtain ⟨_, _, rfl⟩ := h
  simp only [St.acct]
  by_cases heq : tgt = who
  · rw [heq]
    by_cases hb : who < s.accts.length
    · rw [getD_modify_eq _ _ _ _ hb]
    · have h1 : ¬ who < (s.accts.modify who fun a =>
          { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex
                       (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).length := by
        rw [List.length_modify]
        exact hb
      rw [getD_oob _ _ _ h1, getD_oob _ _ _ hb]
  · rw [getD_modify_ne _ _ _ _ _ heq]

theorem supply_mul_ratio_le (s : St) (who : Account) :
  unfold unindexedSupply accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧
      0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [h]
    have h1 : (s.acct who).supply ≤ totalSupply s := supply_le_total s who
    have h2 : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale /
        totalSupply s) * totalSupply s ≤
        (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale :=
      Nat.div_mul_le_self _ _
    calc (s.acct who).supply *
          ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale /
            totalSupply s)
        ≤ totalSupply s *
          ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale /
            totalSupply s) :=
          Nat.mul_le_mul_right _ h1
      _ = ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale /
          totalSupply s) * totalSupply s := by
          rw [Nat.mul_comm]
      _ ≤ (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale := h2
      _ = ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale := by
          rw [Nat.mul_assoc]
  · simp [h]

theorem Hwho_supply_le (s : St) (tgt who : Account) (s' : St)
    (h : SupplyDistributed s tgt s') : Hwho s' who ≤ Hwho s who := by
  have hsup := supply_after_supplyDistrib s tgt who s' h
  have hbor := borrow_after_supplyDistrib s tgt who s' h
  have hwal := wallet_after_supplyDistrib s tgt who s' h
  have hbidx := borrowerIndex_after_supplyDistrib s tgt who s' h
  obtain ⟨hblk, hstart, rfl⟩ := h
  -- After substitution, s' is the record; hsup etc. refer to it.
  have hidx_le : s.supplyState.index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_index_ge _ _ _
  have hstep : (s.acct who).supply *
      ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        accrualStart (s.acct who).supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) ≤
      (s.acct who).supply *
        (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) +
      (s.acct who).supply *
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := by
    have := pendSup_step_le (s.acct who).supply (s.acct who).supplierIndex
      s.supplyState.index (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
      (accrueSide_index_ge _ _ _)
    simp [pendSupAcct] at this ⊢
    exact this
  have hratio := supply_mul_ratio_le s who
  -- Case split on whether who's record was updated.
  by_cases happ : tgt = who ∧ who < s.accts.length
  · obtain ⟨heq, hb⟩ := happ
    cases heq.symm
    -- Applied: who's supplierIndex becomes new index, accrued grows by floor.
    have hget : ((s.accts.modify who fun a =>
        { a with supplierIndex :=
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                   (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).getD who
        noAcct) =
        (fun a =>
        { a with supplierIndex :=
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                   (accrueSide s.supplyState s.blockNumber (totalSupply s)).index })
        (s.accts.getD who noAcct) := getD_modify_eq _ _ _ _ hb
    have hself : accrualStart
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      unfold accrualStart
      by_cases hz : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index = 0
      · simp [hz]
        intro hc
        omega
      · simp [hz]
    have hfloor_le : (creditFor (s.acct who).supply
        (accrualStart (s.acct who).supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) * doubleScale ≤
        (s.acct who).supply *
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          accrualStart (s.acct who).supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) := by
      unfold creditFor
      exact Nat.div_mul_le_self _ _
    have hcomb : (s.acct who).supply *
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          accrualStart (s.acct who).supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) ≤
        (s.acct who).supply *
          (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) +
        (s.acct who).supply *
          ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) :=
      hstep
    have hrat := hratio
    -- Rewrite who's record via applied update.
    have hrewrite : ((s.accts.modify who fun a =>
        { a with supplierIndex :=
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                   (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).getD who
        noAcct) =
        { (s.accts.getD who noAcct) with supplierIndex :=
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                 accrued := (s.accts.getD who noAcct).accrued + creditFor
                   (s.accts.getD who noAcct).supply
                   (accrualStart (s.accts.getD who noAcct).supplierIndex
                     (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                   (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } := by
      rw [hget]
    unfold Hwho St.creditedTo pendAcct pendSupAcct pendBorAcct
      unindexedSupply unindexedBorrow St.acct
    simp only
    rw [hrewrite]
    simp only
    by_cases hsup0 : (s.accts.getD who noAcct).supply > 0
    · simp [hsup0]
      omega
    · simp [hsup0]
      have hzero : (s.accts.getD who noAcct).supply = 0 := by omega
      simp [hzero] at hfloor_le hcomb ⊢
      omega
  · sorry

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hut : updateCompSupplyIndex s with
  | none =>
    simp [hut] at h
  | some t =>
    simp [hut] at h
    obtain ⟨hblk, hut_eq⟩ := updateSupply_some s t hut
    obtain ⟨hstart, heq⟩ := distributeSupply_eq t who s' h
    unfold SupplyDistributed
    refine ⟨?_, ?_, ?_⟩
    · exact hblk
    · simpa [hut_eq, St.acct] using hstart
    · simp [hut_eq, heq]

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hut : updateCompBorrowIndex s with
  | none =>
    simp [hut] at h
  | some t =>
    simp [hut] at h
    obtain ⟨hblk, hut_eq⟩ := updateBorrow_some s t hut
    obtain ⟨hstart, heq⟩ := distributeBorrow_eq t who s' h
    unfold BorrowDistributed
    refine ⟨?_, ?_, ?_⟩
    · exact hblk
    · simpa [hut_eq, St.acct] using hstart
    · simp [hut_eq, heq]
