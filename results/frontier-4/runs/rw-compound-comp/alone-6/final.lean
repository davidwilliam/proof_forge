import CompRewards.Spec
namespace CompRewards

/-- `fraction(a, b)` (ExponentialNoError.sol): `Double(div_(mul_(a, doubleScale), b))`. -/
def fraction (a b : Nat) : Nat := a * doubleScale / b

/-- `mul_(uint a, Double b)` (ExponentialNoError.sol): `a * b.mantissa / doubleScale`. -/
def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

/-- `sub_(a, b)` (ExponentialNoError.sol): reverts on underflow. -/
def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

/-- `updateCompSupplyIndex(cToken)`: bring the supply index up to date. -/
def updateCompSupplyIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.supplyState.block with
  | none => none
  | some _ => some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }

/-- `updateCompBorrowIndex(cToken)`: bring the borrow index up to date. -/
def updateCompBorrowIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.borrowState.block with
  | none => none
  | some _ => some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }

/-- `distributeSupplierComp(cToken, supplier)`. Fixed: the default index is `compInitialIndex`
once the market index has reached it (`compInitialIndex ≤ index`), not only once it has
passed it. The strict `>` let an index equal to `compInitialIndex` (e.g. freshly initialized
by the upgrade) credit `index - 0` instead of `index - compInitialIndex`. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  let supplyIndex := s.supplyState.index
  let supplierIndex := accrualStart (s.acct supplier).supplierIndex supplyIndex
  match subChecked supplyIndex supplierIndex with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex supplyIndex) supplyIndex })

/-- `distributeBorrowerComp(cToken, borrower)`. Same fix as supply side. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex := accrualStart (s.acct borrower).borrowerIndex borrowIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some _ =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := borrowIndex,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex borrowIndex) borrowIndex })

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

theorem doubleScale_pos : 0 < doubleScale := by unfold doubleScale; decide
theorem compInitial_pos : 0 < compInitialIndex := by unfold compInitialIndex; decide
theorem scale_eq : doubleScale = compInitialIndex := by unfold doubleScale compInitialIndex; rfl

theorem subChecked_some (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem accrualStart_fix (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · simp [h]
  · simp [h]

theorem accrualStart_le_index_of (recorded index : Nat)
    (h : recorded = 0 ∨ recorded ≤ index) : accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · subst hr
    simp only
    by_cases h2 : compInitialIndex ≤ index
    · simp [h2]
    · simp [h2]
  · simp [hr]
    cases h with
    | inl h0 => omega
    | inr h1 => exact h1

theorem getD_supply_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) : (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp
      exact h x (by simp)
    | succ n =>
      simp
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem getD_borrow_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) : (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp
      exact h x (by simp)
    | succ n =>
      simp
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem accrualStart_le_of_consistent_supply (s : St) (who : Account)
    (hc : Consistent s) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  apply accrualStart_le_index_of
  by_cases h : (s.acct who).supplierIndex = 0
  · exact Or.inl h
  · exact Or.inr (by
      unfold St.acct at h ⊢
      have hall : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := by
        intro a ha
        exact (hc.2.2 a ha).1
      exact getD_supply_le s.accts who s.supplyState.index hall)

theorem accrualStart_le_of_consistent_borrow (s : St) (who : Account)
    (hc : Consistent s) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  apply accrualStart_le_index_of
  by_cases h : (s.acct who).borrowerIndex = 0
  · exact Or.inl h
  · exact Or.inr (by
      unfold St.acct at h ⊢
      have hall : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := by
        intro a ha
        exact (hc.2.2 a ha).2
      exact getD_borrow_le s.accts who s.borrowState.index hall)

theorem modify_congr (l : List Acct) (i : Nat) (f g : Acct → Acct)
    (h : f (l.getD i noAcct) = g (l.getD i noAcct)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp at h ⊢
      rw [h]
    | succ n =>
      simp at h ⊢
      exact ih n h

theorem modify_length (l : List Acct) (i : Nat) (f : Acct → Acct) :
    (l.modify i f).length = l.length := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n => simp [ih]

theorem updateSupply_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex
  simp [subChecked_some h]

theorem updateBorrow_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex
  simp [subChecked_some h]

theorem distributeSupply_of_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp St.withAcct
  have hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    subChecked_some h
  simp [hsub]

theorem distributeBorrow_of_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp St.withAcct
  have hsub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    subChecked_some h
  simp [hsub]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  rfl

theorem bind_some (x : Option St) (f : St → Option St) (y : St)
    (h : x.bind f = some y) : ∃ u, x = some u ∧ f u = some y := by
  cases x with
  | none =>
    simp at h
  | some u =>
    simp at h
    exact ⟨u, rfl, h⟩

theorem comptroller_supplyHook (s who s') (h : comptroller s (.supplyHook who) = some s') :
    ∃ u, updateCompSupplyIndex s = some u ∧ distributeSupplierComp u who = some s' := by
  unfold comptroller at h
  simp at h
  exact bind_some _ _ _ h

theorem comptroller_borrowHook (s who s') (h : comptroller s (.borrowHook who) = some s') :
    ∃ u, updateCompBorrowIndex s = some u ∧ distributeBorrowerComp u who = some s' := by
  unfold comptroller at h
  simp at h
  exact bind_some _ _ _ h

theorem updateSupply_none_of_gt (s : St) (h : s.supplyState.block > s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  simp [subChecked_none (by omega : ¬ s.supplyState.block ≤ s.blockNumber)]

theorem updateBorrow_none_of_gt (s : St) (h : s.borrowState.block > s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  simp [subChecked_none (by omega : ¬ s.borrowState.block ≤ s.blockNumber)]

theorem distributeSupply_none_of_gt (s : St) (who : Account)
    (h : s.supplyState.index < accrualStart (s.acct who).supplierIndex s.supplyState.index) :
    distributeSupplierComp s who = none := by
  unfold distributeSupplierComp
  simp only
  have : ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by omega
  simp [subChecked_none this]

theorem distributeBorrow_none_of_gt (s : St) (who : Account)
    (h : s.borrowState.index < accrualStart (s.acct who).borrowerIndex s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp
  simp only
  have : ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by omega
  simp [subChecked_none this]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrueSide_block_eq (sd : Side) (now total : Nat)
    (_h : sd.block ≤ now) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hc]
  · simp [hc]

theorem accrueSide_block_le (sd : Side) (now total : Nat)
    (h : sd.block ≤ now) : (accrueSide sd now total).block ≤ now := by
  rw [accrueSide_block_eq _ _ _ h]
  exact Nat.le_refl _

-- updating a side does not change accounts, totals, or the other side
theorem totalSupply_updateSupply (s : St) : totalSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = totalSupply s := by
  simp [totalSupply]

theorem totalBorrows_updateBorrow (s : St) : totalBorrows { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = totalBorrows s := by
  simp [totalBorrows]

theorem acct_updateSupply (s : St) (who : Account) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.acct who) = s.acct who := by
  simp [St.acct]

theorem acct_updateBorrow (s : St) (who : Account) :
    ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.acct who) = s.acct who := by
  simp [St.acct]

theorem map_supply_modify (l : List Acct) (i : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supply = a.supply) : (l.modify i f).map Acct.supply = l.map Acct.supply := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp [hf x]
    | succ n => simp [ih]

theorem map_borrow_modify (l : List Acct) (i : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).borrow = a.borrow) : (l.modify i f).map Acct.borrow = l.map Acct.borrow := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp [hf x]
    | succ n => simp [ih]

theorem totalSupply_distributeSupply (s : St) (who : Account) :
    totalSupply { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } =
      totalSupply s := by
  unfold totalSupply
  have h : ((s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }).map Acct.supply)
      = s.accts.map Acct.supply := by
    apply map_supply_modify
    intro a
    simp
  rw [h]

theorem totalBorrows_distributeBorrow (s : St) (who : Account) :
    totalBorrows { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } =
      totalBorrows s := by
  unfold totalBorrows
  have h : ((s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }).map Acct.borrow)
      = s.accts.map Acct.borrow := by
    apply map_borrow_modify
    intro a
    simp
  rw [h]

theorem totalSupply_distributeBorrow (s : St) (who : Account) :
    totalSupply { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } =
      totalSupply s := by
  unfold totalSupply
  have h : ((s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }).map Acct.supply)
      = s.accts.map Acct.supply := by
    apply map_supply_modify
    intro a
    simp
  rw [h]

theorem totalBorrows_distributeSupply (s : St) (who : Account) :
    totalBorrows { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } =
      totalBorrows s := by
  unfold totalBorrows
  have h : ((s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }).map Acct.borrow)
      = s.accts.map Acct.borrow := by
    apply map_borrow_modify
    intro a
    simp
  rw [h]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  obtain ⟨u, hu1, hu2⟩ := comptroller_supplyHook s who s' h
  have hBlock : s.supplyState.block ≤ s.blockNumber := by
    by_cases hb : s.supplyState.block ≤ s.blockNumber
    · exact hb
    · exfalso
      have hnone := updateSupply_none_of_gt s (by omega)
      rw [hnone] at hu1
      contradiction
  have hEqU : u = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
    have hEq := updateSupply_of_le s hBlock
    rw [hEq] at hu1
    cases hu1
    rfl
  have hAccU : accrualStart (u.acct who).supplierIndex u.supplyState.index ≤ u.supplyState.index := by
    by_cases ha : accrualStart (u.acct who).supplierIndex u.supplyState.index ≤ u.supplyState.index
    · exact ha
    · exfalso
      have hnone := distributeSupply_none_of_gt u who (by omega)
      rw [hnone] at hu2
      contradiction
  have hEqD : s' = { u with accts := u.accts.modify who fun a =>
      { a with supplierIndex := u.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex u.supplyState.index) u.supplyState.index } } := by
    have hEq := distributeSupply_of_le u who hAccU
    rw [hEq] at hu2
    cases hu2
    rfl
  subst hEqU
  refine ⟨hBlock, ?_, ?_⟩
  · simp [St.acct] at hAccU ⊢
    exact hAccU
  · simp at hEqD ⊢
    exact hEqD

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  obtain ⟨u, hu1, hu2⟩ := comptroller_borrowHook s who s' h
  have hBlock : s.borrowState.block ≤ s.blockNumber := by
    by_cases hb : s.borrowState.block ≤ s.blockNumber
    · exact hb
    · exfalso
      have hnone := updateBorrow_none_of_gt s (by omega)
      rw [hnone] at hu1
      contradiction
  have hEqU : u = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
    have hEq := updateBorrow_of_le s hBlock
    rw [hEq] at hu1
    cases hu1
    rfl
  have hAccU : accrualStart (u.acct who).borrowerIndex u.borrowState.index ≤ u.borrowState.index := by
    by_cases ha : accrualStart (u.acct who).borrowerIndex u.borrowState.index ≤ u.borrowState.index
    · exact ha
    · exfalso
      have hnone := distributeBorrow_none_of_gt u who (by omega)
      rw [hnone] at hu2
      contradiction
  have hEqD : s' = { u with accts := u.accts.modify who fun a =>
      { a with borrowerIndex := u.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex u.borrowState.index) u.borrowState.index } } := by
    have hEq := distributeBorrow_of_le u who hAccU
    rw [hEq] at hu2
    cases hu2
    rfl
  subst hEqU
  refine ⟨hBlock, ?_, ?_⟩
  · simp [St.acct] at hAccU ⊢
    exact hAccU
  · simp at hEqD ⊢
    exact hEqD

theorem claim_decomp (s : St) (who : Account) (s' : St) (h : claimComp s who = some s') :
    ∃ b1 s1 b2 s2, updateCompBorrowIndex s = some b1 ∧ distributeBorrowerComp b1 who = some s1 ∧
      updateCompSupplyIndex s1 = some b2 ∧ distributeSupplierComp b2 who = some s2 ∧
      grantCompInternal s2 who = s' := by
  unfold claimComp at h
  simp at h
  obtain ⟨b1, hb1, hr1⟩ := bind_some _ _ _ h
  obtain ⟨s1, hs1, hr2⟩ := bind_some _ _ _ hr1
  obtain ⟨b2, hb2, hr3⟩ := bind_some _ _ _ hr2
  obtain ⟨s2, hs2, hr4⟩ := bind_some _ _ _ hr3
  have hGr : grantCompInternal s2 who = s' := by
    simpa using hr4
  exact ⟨b1, s1, b2, s2, hb1, hs1, hb2, hs2, hGr⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp at h
  obtain ⟨b1, s1, b2, s2, hb1, hs1, hb2, hs2, hgr⟩ := claim_decomp s who s' h
  have hBlockB : s.borrowState.block ≤ s.blockNumber := by
    by_cases hb : s.borrowState.block ≤ s.blockNumber
    · exact hb
    · exfalso
      have hnone := updateBorrow_none_of_gt s (by omega)
      rw [hnone] at hb1
      contradiction
  have hEqB : b1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
    have hEq := updateBorrow_of_le s hBlockB
    rw [hEq] at hb1
    cases hb1
    rfl
  have hAccB : accrualStart (b1.acct who).borrowerIndex b1.borrowState.index ≤ b1.borrowState.index := by
    by_cases ha : accrualStart (b1.acct who).borrowerIndex b1.borrowState.index ≤ b1.borrowState.index
    · exact ha
    · exfalso
      have hnone := distributeBorrow_none_of_gt b1 who (by omega)
      rw [hnone] at hs1
      contradiction
  have hEqS1 : s1 = { b1 with accts := b1.accts.modify who fun a =>
      { a with borrowerIndex := b1.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index } } := by
    have hEq := distributeBorrow_of_le b1 who hAccB
    rw [hEq] at hs1
    cases hs1
    rfl
  have hBlockS : s1.supplyState.block ≤ s1.blockNumber := by
    by_cases hb : s1.supplyState.block ≤ s1.blockNumber
    · exact hb
    · exfalso
      have hnone := updateSupply_none_of_gt s1 (by omega)
      rw [hnone] at hb2
      contradiction
  have hEqB2 : b2 = { s1 with supplyState := accrueSide s1.supplyState s1.blockNumber (totalSupply s1) } := by
    have hEq := updateSupply_of_le s1 hBlockS
    rw [hEq] at hb2
    cases hb2
    rfl
  have hAccS : accrualStart (b2.acct who).supplierIndex b2.supplyState.index ≤ b2.supplyState.index := by
    by_cases ha : accrualStart (b2.acct who).supplierIndex b2.supplyState.index ≤ b2.supplyState.index
    · exact ha
    · exfalso
      have hnone := distributeSupply_none_of_gt b2 who (by omega)
      rw [hnone] at hs2
      contradiction
  have hEqS2 : s2 = { b2 with accts := b2.accts.modify who fun a =>
      { a with supplierIndex := b2.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex b2.supplyState.index) b2.supplyState.index } } := by
    have hEq := distributeSupply_of_le b2 who hAccS
    rw [hEq] at hs2
    cases hs2
    rfl
  refine ⟨s1, s2, ?_, ?_, ?_⟩
  · have hBor : BorrowDistributed s who s1 := by
      refine ⟨hBlockB, ?_, ?_⟩
      · have htmp := hAccB
        rw [hEqB] at htmp
        simp [St.acct] at htmp ⊢
        exact htmp
      · simp [hEqS1, hEqB]
    exact hBor
  · have hSup : SupplyDistributed s1 who s2 := by
      refine ⟨hBlockS, ?_, ?_⟩
      · have htmp := hAccS
        rw [hEqB2] at htmp
        simp [St.acct] at htmp ⊢
        exact htmp
      · simp [hEqS2, hEqB2]
    exact hSup
  · have hG : grant s2 who = s' := by
      rw [← grant_eq]
      exact hgr
    rw [hG]

theorem map_some (x : Option St) (f : St → St) (y : St)
    (h : x.map f = some y) : ∃ u, x = some u ∧ f u = y := by
  cases x with
  | none =>
    simp at h
  | some u =>
    simp at h
    exact ⟨u, rfl, h⟩

-- scaled accounting for global bounds
def supplyPend (s : St) : Nat :=
  (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum

def borrowPend (s : St) : Nat :=
  (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum

def totalPend (s : St) : Nat := supplyPend s + borrowPend s

def unindexed (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
    (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def scaledDebt (s : St) : Nat := s.credited * doubleScale + totalPend s + unindexed s * doubleScale

theorem div_mul_le_self (x k : Nat) : x / k * k ≤ x :=
  Nat.div_mul_le_self x k

theorem mul_div_le_of_le (u T R S : Nat) (h : u ≤ T) : u * R / S ≤ T * R / S :=
  Nat.div_le_div_right (Nat.mul_le_mul_right R h)

theorem getD_modify_supplier (l : List Acct) (i : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify i f).getD i noAcct).supplierIndex = (l.getD i noAcct).supplierIndex := by
  induction l generalizing i with
  | nil =>
    simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [hf x]
    | succ n =>
      simp
      cases h : xs[n]? with
      | none =>
        simp [h]
      | some a =>
        simp [h, hf a]

theorem getD_modify_supply (l : List Acct) (i : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supply = a.supply) :
    ((l.modify i f).getD i noAcct).supply = (l.getD i noAcct).supply := by
  induction l generalizing i with
  | nil =>
    simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [hf x]
    | succ n =>
      simp
      cases h : xs[n]? with
      | none =>
        simp [h]
      | some a =>
        simp [h, hf a]

theorem accrualStart_mono_index (rec i1 i2 : Nat) (h : i1 ≤ i2) :
    accrualStart rec i1 ≤ accrualStart rec i2 := by
  unfold accrualStart
  by_cases hr : rec = 0
  · simp [hr]
    by_cases h1 : compInitialIndex ≤ i1
    · have h2 : compInitialIndex ≤ i2 := Nat.le_trans h1 h
      simp [h1, h2]
    · by_cases h2 : compInitialIndex ≤ i2
      · simp [h1, h2]
      · simp [h1, h2]
  · simp [hr]

theorem accrualStart_mono_le (rec i1 i2 : Nat) (h0 : rec = 0 ∨ rec ≤ i1) (h : i1 ≤ i2) :
    accrualStart rec i1 ≤ i2 := by
  have h1 := accrualStart_mono_index rec i1 i2 h
  have h2 : accrualStart rec i2 ≤ i2 := by
    unfold accrualStart
    by_cases hr : rec = 0
    · simp [hr]
      by_cases h3 : compInitialIndex ≤ i2
      · simp [h3]
      · simp [h3]
    · simp [hr]
      cases h0 with
      | inl h00 => omega
      | inr hle => omega
  omega

theorem pending_term_le (u rec i1 i2 : Nat) (h0 : rec = 0 ∨ rec ≤ i1) (h : i1 ≤ i2) :
    u * (i2 - accrualStart rec i2) ≤ u * (i1 - accrualStart rec i1) + u * (i2 - i1) := by
  have hS1 : accrualStart rec i1 ≤ i1 := by
    unfold accrualStart
    by_cases hr : rec = 0
    · simp [hr]
      by_cases h3 : compInitialIndex ≤ i1
      · simp [h3]
      · simp [h3]
    · simp [hr]
      cases h0 with
      | inl h00 => omega
      | inr hle => exact hle
  have hS2 : accrualStart rec i2 ≤ i2 := by
    unfold accrualStart
    by_cases hr : rec = 0
    · simp [hr]
      by_cases h3 : compInitialIndex ≤ i2
      · simp [h3]
      · simp [h3]
    · simp [hr]
      cases h0 with
      | inl h00 => omega
      | inr hle => omega
  have hMono : accrualStart rec i1 ≤ accrualStart rec i2 :=
    accrualStart_mono_index _ _ _ h
  have h1 : i1 - accrualStart rec i1 + (i2 - i1) = i2 - accrualStart rec i1 := by omega
  have h2 : i2 - accrualStart rec i2 ≤ i2 - accrualStart rec i1 := by omega
  calc u * (i2 - accrualStart rec i2)
      ≤ u * (i2 - accrualStart rec i1) := Nat.mul_le_mul_left u h2
    _ = u * ((i1 - accrualStart rec i1) + (i2 - i1)) := by rw [h1]
    _ = u * (i1 - accrualStart rec i1) + u * (i2 - i1) := Nat.mul_add _ _ _

theorem setSupply_decomp (s : St) (a : Nat) (s' : St)
    (h : setSupplySpeed s a = some s') :
    (s.supplyState.speed = a ∧ s' = s) ∨
      (s.supplyState.speed ≠ a ∧ s.supplyState.block ≤ s.blockNumber ∧
        s' = { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
          supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) := by
  by_cases heq : s.supplyState.speed = a
  · left
    have hEq : setSupplySpeed s a = some s := by
      unfold setSupplySpeed
      rw [if_neg (by simp [heq])]
    rw [hEq] at h
    have hEs : s = s' := by simpa using h
    exact ⟨heq, hEs.symm⟩
  · right
    have hMap : (updateCompSupplyIndex s).map (fun t => { t with supplyState := { t.supplyState with speed := a } }) = some s' := by
      have hIf : setSupplySpeed s a = (updateCompSupplyIndex s).map (fun t => { t with supplyState := { t.supplyState with speed := a } }) := by
        unfold setSupplySpeed
        rw [if_pos heq]
      rw [hIf] at h
      exact h
    refine ⟨heq, ?_, ?_⟩
    · by_cases hb : s.supplyState.block ≤ s.blockNumber
      · exact hb
      · exfalso
        have hnone : updateCompSupplyIndex s = none := updateSupply_none_of_gt s (by omega)
        have hSetNone : setSupplySpeed s a = none := by
          unfold setSupplySpeed
          rw [if_pos heq, hnone]
          rfl
        rw [hSetNone] at h
        contradiction
    · have hBlock : s.supplyState.block ≤ s.blockNumber := by
        by_cases hb : s.supplyState.block ≤ s.blockNumber
        · exact hb
        · exfalso
          have hnone : updateCompSupplyIndex s = none := updateSupply_none_of_gt s (by omega)
          have hSetNone : setSupplySpeed s a = none := by
            unfold setSupplySpeed
            rw [if_pos heq, hnone]
            rfl
          rw [hSetNone] at h
          contradiction
      have hEq := updateSupply_of_le s hBlock
      obtain ⟨u, hu1, hu2⟩ := map_some _ _ _ hMap
      rw [hEq] at hu1
      cases hu1
      exact hu2.symm

theorem setBorrow_decomp (s : St) (b : Nat) (s' : St)
    (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed = b ∧ s' = s) ∨
      (s.borrowState.speed ≠ b ∧ s.borrowState.block ≤ s.blockNumber ∧
        s' = { { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with
          borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) := by
  by_cases heq : s.borrowState.speed = b
  · left
    have hEq : setBorrowSpeed s b = some s := by
      unfold setBorrowSpeed
      rw [if_neg (by simp [heq])]
    rw [hEq] at h
    have hEs : s = s' := by simpa using h
    exact ⟨heq, hEs.symm⟩
  · right
    have hMap : (updateCompBorrowIndex s).map (fun t => { t with borrowState := { t.borrowState with speed := b } }) = some s' := by
      have hIf : setBorrowSpeed s b = (updateCompBorrowIndex s).map (fun t => { t with borrowState := { t.borrowState with speed := b } }) := by
        unfold setBorrowSpeed
        rw [if_pos heq]
      rw [hIf] at h
      exact h
    refine ⟨heq, ?_, ?_⟩
    · by_cases hb : s.borrowState.block ≤ s.blockNumber
      · exact hb
      · exfalso
        have hnone : updateCompBorrowIndex s = none := updateBorrow_none_of_gt s (by omega)
        have hSetNone : setBorrowSpeed s b = none := by
          unfold setBorrowSpeed
          rw [if_pos heq, hnone]
          rfl
        rw [hSetNone] at h
        contradiction
    · have hBlock : s.borrowState.block ≤ s.blockNumber := by
        by_cases hb : s.borrowState.block ≤ s.blockNumber
        · exact hb
        · exfalso
          have hnone : updateCompBorrowIndex s = none := updateBorrow_none_of_gt s (by omega)
          have hSetNone : setBorrowSpeed s b = none := by
            unfold setBorrowSpeed
            rw [if_pos heq, hnone]
            rfl
          rw [hSetNone] at h
          contradiction
      have hEq := updateBorrow_of_le s hBlock
      obtain ⟨u, hu1, hu2⟩ := map_some _ _ _ hMap
      rw [hEq] at hu1
      cases hu1
      exact hu2.symm

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller at h
  simp at h
  obtain ⟨t, ht1, ht2⟩ := bind_some _ _ _ h
  obtain hSup := setSupply_decomp s a t ht1
  obtain hBor := setBorrow_decomp t b s' ht2
  cases hSup with
  | inl hEq =>
    obtain ⟨hEqS, rfl⟩ := hEq
    cases hBor with
    | inl hEq2 =>
      obtain ⟨hEqB, rfl⟩ := hEq2
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        contradiction
      · intro hne
        contradiction
      · simp [hEqS, hEqB]
    | inr hR =>
      obtain ⟨hneB, hBlockB, hEqB⟩ := hR
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        contradiction
      · intro _
        exact hBlockB
      · simp [hEqS, hEqB, hneB]
  | inr hR =>
    obtain ⟨hneS, hBlockS, hEqS⟩ := hR
    have hTbor : t.borrowState = s.borrowState := by simp [hEqS]
    have hTblk : t.blockNumber = s.blockNumber := by simp [hEqS]
    have hTacc : t.accts = s.accts := by simp [hEqS]
    have hTB : totalBorrows t = totalBorrows s := by simp [hEqS, totalBorrows]
    cases hBor with
    | inl hEq2 =>
      obtain ⟨hEqB, rfl⟩ := hEq2
      have hEqBs : s.borrowState.speed = b := by
        have := hEqB
        simp [hEqS] at this
        exact this
      refine ⟨?_, ?_, ?_⟩
      · intro _
        exact hBlockS
      · intro hne
        rw [hEqBs] at hne
        contradiction
      · simp [hneS, hEqBs, hEqS]
    | inr hR2 =>
      obtain ⟨hneB, hBlockB, hEqB⟩ := hR2
      have hneBs : s.borrowState.speed ≠ b := by
        have h1 : t.borrowState.speed ≠ b := hneB
        rw [hTbor] at h1
        exact h1
      refine ⟨?_, ?_, ?_⟩
      · intro _
        exact hBlockS
      · intro _
        have : t.borrowState.block ≤ t.blockNumber := hBlockB
        rw [hTbor, hTblk] at this
        exact this
      · have hEqB' : s' =
          { t with borrowState := { accrueSide t.borrowState t.blockNumber (totalBorrows s) with speed := b } } := by
          rw [hTB] at hEqB
          simpa using hEqB
        simp [hneS, hneBs, hEqS, hEqB']

theorem accrualStart_le_after_supply (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.acct who)).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  have hRec : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.acct who)).supplierIndex
      = (s.acct who).supplierIndex := by simp [St.acct]
  rw [hRec]
  apply accrualStart_le_index_of
  by_cases h0 : (s.acct who).supplierIndex = 0
  · exact Or.inl h0
  · exact Or.inr (by
      have h1 : (s.acct who).supplierIndex ≤ s.supplyState.index := by
        have hall : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := by
          intro a ha
          exact (hc.2.2 a ha).1
        unfold St.acct
        exact getD_supply_le s.accts who s.supplyState.index hall
      have h2 : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
        accrueSide_index_ge _ _ _
      omega)

theorem accrualStart_le_after_borrow (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.acct who)).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  have hRec : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.acct who)).borrowerIndex
      = (s.acct who).borrowerIndex := by simp [St.acct]
  rw [hRec]
  apply accrualStart_le_index_of
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · exact Or.inl h0
  · exact Or.inr (by
      have h1 : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
        have hall : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := by
          intro a ha
          exact (hc.2.2 a ha).2
        unfold St.acct
        exact getD_borrow_le s.accts who s.borrowState.index hall
      have h2 : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
        accrueSide_index_ge _ _ _
      omega)

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have hB : s.supplyState.block ≤ s.blockNumber := hc.1
    have hU := updateSupply_of_le s hB
    have hAcc := accrualStart_le_after_supply s who hc
    have hD := distributeSupply_of_le
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who hAcc
    have hEq : comptroller s (.supplyHook who) =
        some { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
          accts := ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).accts.modify who fun a =>
            { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
                     accrued := a.accrued + creditFor a.supply
                       (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
                       (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
      unfold comptroller
      simp [hU, hD]
    simp [hEq]
  | borrowHook who =>
    have hB : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hU := updateBorrow_of_le s hB
    have hAcc := accrualStart_le_after_borrow s who hc
    have hD := distributeBorrow_of_le
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who hAcc
    have hEq : comptroller s (.borrowHook who) =
        some { { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with
          accts := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
            { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
                     accrued := a.accrued + creditFor a.borrow
                       (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
                       (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
      unfold comptroller
      simp [hU, hD]
    simp [hEq]
  | claim who =>
    have hBB : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hAccB := accrualStart_le_after_borrow s who hc
    have hEqB : updateCompBorrowIndex s =
        some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
      updateBorrow_of_le s hBB
    have hEqS1 : distributeBorrowerComp
        { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who =
        some { { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with
          accts := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
            { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
                     accrued := a.accrued + creditFor a.borrow
                       (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
                       (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
      distributeBorrow_of_le _ _ hAccB
    let s1 : St := { { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with
      accts := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
        { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
                   (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }
    have hS1eq : s1.supplyState.block ≤ s1.blockNumber := by
      simp [s1, hc.1]
    have hUS : updateCompSupplyIndex s1 =
          some { s1 with supplyState := accrueSide s1.supplyState s1.blockNumber (totalSupply s1) } :=
      updateSupply_of_le s1 hS1eq
    let b2 : St := { s1 with supplyState := accrueSide s1.supplyState s1.blockNumber (totalSupply s1) }
    have hAccB2 : accrualStart (b2.acct who).supplierIndex b2.supplyState.index ≤ b2.supplyState.index := by
      have hRec1 : (b2.acct who).supplierIndex = (s1.acct who).supplierIndex := by simp [b2, St.acct]
      have hRec2 : (s1.acct who).supplierIndex = (s.acct who).supplierIndex := by
        simp only [s1, St.acct]
        exact getD_modify_supplier _ _ _ (by intro a; simp)
      have hRec : (b2.acct who).supplierIndex = (s.acct who).supplierIndex := hRec1.trans hRec2
      rw [hRec]
      have hS1Supply : s1.supplyState = s.supplyState := by simp [s1]
      have hS1Blk : s1.blockNumber = s.blockNumber := by simp [s1]
      have hIdx : s.supplyState.index ≤ b2.supplyState.index := by
        simp [b2, hS1Supply, hS1Blk]
        exact accrueSide_index_ge _ _ _
      apply accrualStart_le_index_of
      by_cases h0 : (s.acct who).supplierIndex = 0
      · exact Or.inl h0
      · exact Or.inr (by
          have h1 : (s.acct who).supplierIndex ≤ s.supplyState.index := by
            have hall : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := by
              intro a ha
              exact (hc.2.2 a ha).1
            unfold St.acct
            exact getD_supply_le s.accts who s.supplyState.index hall
          omega)
    have hDS : distributeSupplierComp b2 who =
        some { b2 with accts := b2.accts.modify who fun a =>
          { a with supplierIndex := b2.supplyState.index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex b2.supplyState.index) b2.supplyState.index } } :=
      distributeSupply_of_le b2 who hAccB2
    have hEq : comptroller s (.claim who) = some (grantCompInternal
        { b2 with accts := b2.accts.modify who fun a =>
          { a with supplierIndex := b2.supplyState.index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex b2.supplyState.index) b2.supplyState.index } } who) := by
      unfold comptroller claimComp
      simp [hEqB, hEqS1, s1, b2, hUS, hDS]
    simp [hEq]
  | setSpeeds a b =>
    have hSup : ∃ t, setSupplySpeed s a = some t := by
      by_cases heq : s.supplyState.speed = a
      · exact ⟨s, by unfold setSupplySpeed; simp [heq]⟩
      · have hB : s.supplyState.block ≤ s.blockNumber := hc.1
        have hEq := updateSupply_of_le s hB
        have : setSupplySpeed s a =
            some { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
              supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
          unfold setSupplySpeed
          rw [if_pos heq]
          simp [hEq]
        exact ⟨_, this⟩
    obtain ⟨t, ht⟩ := hSup
    have hConsT : t.supplyState.block ≤ t.blockNumber ∧ t.borrowState.block ≤ t.blockNumber := by
      have hEq := setSupply_decomp s a t ht
      cases hEq with
      | inl hEq =>
        obtain ⟨_, rfl⟩ := hEq
        exact ⟨hc.1, hc.2.1⟩
      | inr hEq =>
        obtain ⟨_, hB, hEt⟩ := hEq
        have hBlkEq : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber :=
          accrueSide_block_eq _ _ _ hB
        simp [hEt, hBlkEq, hc.2.1]
    have hBor : ∃ s', setBorrowSpeed t b = some s' := by
      by_cases heq : t.borrowState.speed = b
      · exact ⟨t, by unfold setBorrowSpeed; simp [heq]⟩
      · have hB : t.borrowState.block ≤ t.blockNumber := hConsT.2
        have hEq := updateBorrow_of_le t hB
        have : setBorrowSpeed t b =
            some { { t with borrowState := accrueSide t.borrowState t.blockNumber (totalBorrows t) } with
              borrowState := { accrueSide t.borrowState t.blockNumber (totalBorrows t) with speed := b } } := by
          unfold setBorrowSpeed
          rw [if_pos heq]
          simp [hEq]
        exact ⟨_, this⟩
    obtain ⟨s', hs'⟩ := hBor
    have hEq : comptroller s (.setSpeeds a b) = some s' := by
      unfold comptroller setCompSpeedInternal
      simp [ht, hs']
    simp [hEq]

theorem sum_map_mul (l : List Acct) (proj : Acct → Nat) (R : Nat) :
    ((l.map fun a => proj a * R).sum) = ((l.map proj).sum) * R := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [ih, Nat.add_mul]

theorem sum_getD_le_sum (l : List Nat) (i : Nat) (d : Nat) : (l.getD i d) ≤ l.sum := by
  induction l generalizing i with
  | nil =>
    simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp
    | succ n =>
      simp
      have := ih n
      omega

theorem credited_getD_le (s : St) (who : Account) :
    (s.acct who).accrued + (s.acct who).wallet ≤ s.credited := by
  unfold St.credited St.acct
  have h : ((s.accts.map fun a => a.accrued + a.wallet).getD who 0) ≤
      (s.accts.map fun a => a.accrued + a.wallet).sum := by
    apply sum_getD_le
  simpa using h
