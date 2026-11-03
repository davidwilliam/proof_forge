import CompRewards.Spec
import ProofForgeFin.Ledger
import ProofForgeFin.Accumulator.Market
/-!
Port of the COMP distribution of Compound's Comptroller as deployed by Proposal 62
with the Proposal 64 start fix (`>= compInitialIndex`): an account with no recorded
index starts at `compInitialIndex` once the market index has reached it.
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

/-- `distributeSupplierComp(cToken, supplier)`: the recorded index of 0 means no
interaction since rewards began; the account then starts at `compInitialIndex` once the
market's index has reached it (`accrualStart`). -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  let supplyIndex := s.supplyState.index
  let supplierIndex :=
    if (s.acct supplier).supplierIndex = 0 ∧ compInitialIndex ≤ supplyIndex then compInitialIndex
    else (s.acct supplier).supplierIndex
  match subChecked supplyIndex supplierIndex with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex supplyIndex) supplyIndex })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`: as above on the
borrow side. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex :=
    if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ borrowIndex then compInitialIndex
    else (s.acct borrower).borrowerIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some _ =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := borrowIndex, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex borrowIndex) borrowIndex })

/-- `grantCompInternal(user, compAccrued[user])`: pays `who` everything accrued when funded. -/
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

/-- The state after the supply hook for `who`: the supply index brought up to date and `who`
credited from its start (spec `SupplyDistributed` closed form). -/
def supplyNext (s : St) (who : Account) : St :=
  { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }

/-- The state after the borrow hook for `who` (spec `BorrowDistributed` closed form). -/
def borrowNext (s : St) (who : Account) : St :=
  { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }

/-- The state after a speed change to `a` and `b`: each side whose speed changes is first
brought up to date at its old speed (spec `SpeedsSet` closed form). -/
def setSpeedsNext (s : St) (a b : Nat) : St :=
  { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }), borrowState := (if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) }

/-- The Comptroller, with the Proposal 64 start fix (`accrualStart`): every call in the
specification's closed form. A hook brings its side's index up to date and credits the
account from its start; a claim does the borrow side, then the supply side, then pays
everything accrued; a speed change accrues at the old speed first. A call that would
underflow reverts (`none`). -/
def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => if s.supplyState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index then some (supplyNext s who) else none
  | .borrowHook who => if s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index then some (borrowNext s who) else none
  | .claim who => if s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index then if (borrowNext s who).supplyState.block ≤ (borrowNext s who).blockNumber ∧ accrualStart ((borrowNext s who).acct who).supplierIndex (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber (totalSupply (borrowNext s who))).index ≤ (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber (totalSupply (borrowNext s who))).index then some (grant (supplyNext (borrowNext s who) who) who) else none else none
  | .setSpeeds a b => if (¬ s.supplyState.speed = a → s.supplyState.block ≤ s.blockNumber) ∧ (¬ s.borrowState.speed = b → s.borrowState.block ≤ s.blockNumber) then some (setSpeedsNext s a b) else none

/-! ## Equation lemmas: each call in the spec's closed form -/

theorem updateSupply_eq (s : St) :
    updateCompSupplyIndex s =
      if s.supplyState.block ≤ s.blockNumber then
        some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
      else none := by
  by_cases h : s.supplyState.block ≤ s.blockNumber
  · simp only [h, ite_true]
    unfold updateCompSupplyIndex subChecked accrueSide fraction
    simp only [h, ite_true]
    by_cases hA : 0 < s.blockNumber - s.supplyState.block
    · by_cases hB : 0 < s.supplyState.speed
      · by_cases hC : 0 < totalSupply s
        · simp [hA, hB, hC]
        · simp [hA, hB, hC]
      · simp [hA, hB]
    · simp [hA]
      have hbb : s.supplyState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res ac =>
        cases sup with
        | mk ix bl sp =>
          simp at hbb ⊢
          simp [hbb]
  · simp only [h, ite_false]
    unfold updateCompSupplyIndex subChecked
    simp [h]

theorem updateBorrow_eq (s : St) :
    updateCompBorrowIndex s =
      if s.borrowState.block ≤ s.blockNumber then
        some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
      else none := by
  by_cases h : s.borrowState.block ≤ s.blockNumber
  · simp only [h, ite_true]
    unfold updateCompBorrowIndex subChecked accrueSide fraction
    simp only [h, ite_true]
    by_cases hA : 0 < s.blockNumber - s.borrowState.block
    · by_cases hB : 0 < s.borrowState.speed
      · by_cases hC : 0 < totalBorrows s
        · simp [hA, hB, hC]
        · simp [hA, hB, hC]
      · simp [hA, hB]
    · simp [hA]
      have hbb : s.borrowState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res ac =>
        cases bor with
        | mk ix bl sp =>
          simp at hbb ⊢
          simp [hbb]
  · simp only [h, ite_false]
    unfold updateCompBorrowIndex subChecked
    simp [h]

theorem distSup_start (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
     else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h1 : (s.acct who).supplierIndex = 0
  · by_cases h2 : compInitialIndex ≤ s.supplyState.index
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

theorem distBor_start (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
     else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h1 : (s.acct who).borrowerIndex = 0
  · by_cases h2 : compInitialIndex ≤ s.borrowState.index
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

theorem distributeSupply_eq (s : St) (who : Account) :
    distributeSupplierComp s who =
      if accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index then
        some (s.withAcct who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }))
      else none := by
  have hstart := distSup_start s who
  unfold distributeSupplierComp subChecked St.withAcct
  simp only [hstart]
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp [hle]
  · simp [hle]

theorem distributeBorrow_eq (s : St) (who : Account) :
    distributeBorrowerComp s who =
      if accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index then
        some (s.withAcct who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }))
      else none := by
  have hstart := distBor_start s who
  unfold distributeBorrowerComp subChecked St.withAcct
  simp only [hstart]
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp [hle]
  · simp [hle]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h1 : 0 < (s.acct who).accrued
  · by_cases h2 : (s.acct who).accrued ≤ s.reserve
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

theorem accrueSupply_le (s : St) :
    s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp only [h, ite_true]
    exact Nat.le_add_right _ _
  · simp only [h, ite_false]
    exact Nat.le_refl _

theorem accrueBorrow_le (s : St) :
    s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp only [h, ite_true]
    exact Nat.le_add_right _ _
  · simp only [h, ite_false]
    exact Nat.le_refl _

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hc : (s.supplyState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
  · simp [hc] at h
    cases h
    unfold SupplyDistributed
    exact ⟨hc.1, hc.2, rfl⟩
  · simp [hc] at h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hc : (s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
  · simp [hc] at h
    cases h
    unfold BorrowDistributed
    exact ⟨hc.1, hc.2, rfl⟩
  · simp [hc] at h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hB : (s.borrowState.block ≤ s.blockNumber ∧ accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
  · simp [hB] at h
    by_cases hS : ((borrowNext s who).supplyState.block ≤ (borrowNext s who).blockNumber ∧ accrualStart ((borrowNext s who).acct who).supplierIndex (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber (totalSupply (borrowNext s who))).index ≤ (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber (totalSupply (borrowNext s who))).index)
    · simp [hS] at h
      cases h
      have hBm : BorrowDistributed s who (borrowNext s who) := by
        unfold BorrowDistributed
        exact ⟨hB.1, hB.2, rfl⟩
      have hSm : SupplyDistributed (borrowNext s who) who (supplyNext (borrowNext s who) who) := by
        unfold SupplyDistributed
        exact ⟨hS.1, hS.2, rfl⟩
      exact ⟨borrowNext s who, supplyNext (borrowNext s who) who, hBm, hSm, rfl⟩
    · simp [hS] at h
  · simp [hB] at h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller] at h
  by_cases hc : ((¬ s.supplyState.speed = a → s.supplyState.block ≤ s.blockNumber) ∧ (¬ s.borrowState.speed = b → s.borrowState.block ≤ s.blockNumber))
  · rw [if_pos hc] at h
    cases h
    unfold SpeedsSet
    exact ⟨hc.1, hc.2, rfl⟩
  · rw [if_neg hc] at h
    simp at h

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hSupB, hBorB, hrec⟩ := hc
  have hsupIdx := accrueSupply_le s
  have hborIdx := accrueBorrow_le s
  have hrecS : ∀ who, (s.acct who).supplierIndex ≤ s.supplyState.index := by
    intro who
    rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
    · exact (hrec _ hm).1
    · simp only [St.acct]
      rw [hm]
      exact Nat.zero_le _
  have hrecB : ∀ who, (s.acct who).borrowerIndex ≤ s.borrowState.index := by
    intro who
    rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
    · exact (hrec _ hm).2
    · simp only [St.acct]
      rw [hm]
      exact Nat.zero_le _
  have hsup_le : ∀ who, accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    intro who
    by_cases hR : (s.acct who).supplierIndex = 0
    · unfold accrualStart
      simp [hR]
      by_cases hI : compInitialIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
      · simp [hI]
      · simp [hI]
    · unfold accrualStart
      simp [hR]
      have h1 := hrecS who
      omega
  have hbor_le : ∀ who, accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    intro who
    by_cases hR : (s.acct who).borrowerIndex = 0
    · unfold accrualStart
      simp [hR]
      by_cases hI : compInitialIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
      · simp [hI]
      · simp [hI]
    · unfold accrualStart
      simp [hR]
      have h1 := hrecB who
      omega
  cases c with
  | supplyHook who =>
    simp only [comptroller]
    simp [hSupB, hsup_le who]
  | borrowHook who =>
    simp only [comptroller]
    simp [hBorB, hbor_le who]
  | claim who =>
    have eblk : (borrowNext s who).supplyState.block = s.supplyState.block := by simp [borrowNext]
    have ebn : (borrowNext s who).blockNumber = s.blockNumber := by simp [borrowNext]
    have esup : ((borrowNext s who).acct who).supplierIndex = (s.acct who).supplierIndex :=
      ProofForgeFin.Ledger.getD_modify_of_keeps s.accts who who (f := fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) noAcct (fun a => a.supplierIndex) (fun _ => rfl)
    have eidx : (borrowNext s who).supplyState.index = s.supplyState.index := by simp [borrowNext]
    have hS1 : (borrowNext s who).supplyState.block ≤ (borrowNext s who).blockNumber := by
      rw [eblk, ebn]
      exact hSupB
    have hS2 : accrualStart ((borrowNext s who).acct who).supplierIndex (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber (totalSupply (borrowNext s who))).index ≤ (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber (totalSupply (borrowNext s who))).index := by
      rw [esup]
      by_cases hR : (s.acct who).supplierIndex = 0
      · unfold accrualStart
        simp [hR]
        by_cases hI : compInitialIndex ≤ (accrueSide (borrowNext s who).supplyState (borrowNext s who).blockNumber (totalSupply (borrowNext s who))).index
        · simp [hI]
        · simp [hI]
      · unfold accrualStart
        simp [hR]
        have h1 := hrecS who
        have h2 := accrueSupply_le (borrowNext s who)
        omega
    simp only [comptroller]
    simp [hBorB, hbor_le who, hS1, hS2]
  | setSpeeds a b =>
    have hc' : (¬ s.supplyState.speed = a → s.supplyState.block ≤ s.blockNumber) ∧ (¬ s.borrowState.speed = b → s.borrowState.block ≤ s.blockNumber) :=
      ⟨fun _ => hSupB, fun _ => hBorB⟩
    simp only [comptroller]
    rw [if_pos hc']
    trivial

/-! ## The market reading for the accumulator library -/

def M : ProofForgeFin.Accumulator.Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock s := ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed, s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts s := s.accts
  dflt := noAcct
  units₁ a := a.supply
  units₂ a := a.borrow
  rec₁ a := a.supplierIndex
  rec₂ a := a.borrowerIndex
  credited a := a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

def legacyClock (L : Legacy) : ProofForgeFin.Accumulator.Clock :=
  ⟨L.blockNumber, L.supplyIndex, L.supplyBlock, L.compSpeed, L.borrowIndex, L.borrowBlock, L.compSpeed⟩

theorem accrueSupply_index (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
    ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block s.supplyState.speed s.blockNumber (totalSupply s) := by
  have hM : M.one = doubleScale := rfl
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [h, hM]
  · simp [h, hM]

theorem accrueSupply_block (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [h]
  · simp [h]

theorem accrueBorrow_index (s : St) :
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
    ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block s.borrowState.speed s.blockNumber (totalBorrows s) := by
  have hM : M.one = doubleScale := rfl
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp [h, hM]
  · simp [h, hM]

theorem accrueBorrow_block (s : St) :
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp [h]
  · simp [h]

theorem accrualStart_first (r i : Nat) :
    accrualStart r i = ProofForgeFin.DeFi.Rewards.firstStart M.init r i := by
  have hM : M.init = compInitialIndex := rfl
  unfold accrualStart ProofForgeFin.DeFi.Rewards.firstStart
  by_cases h1 : r = 0
  · simp [h1, hM]
  · simp [h1]

theorem legacyStart_eff (g r : Nat) :
    legacyStart g r = ProofForgeFin.DeFi.Rewards.effStart g r := rfl

theorem totalSupply_M (s : St) : M.total₁ s = totalSupply s := rfl

theorem totalBorrows_M (s : St) : M.total₂ s = totalBorrows s := rfl

theorem credited_M (s : St) : M.creditSum s = St.credited s := rfl

theorem clock_upgrade (L : Legacy) :
    M.clock (upgrade L) = (legacyClock L).reinit M.init := by
  by_cases h1 : L.supplyIndex = 0
  · by_cases h2 : L.borrowIndex = 0
    · simp [M, upgrade, initSide, ProofForgeFin.Accumulator.Clock.reinit, legacyClock, h1, h2]
    · simp [M, upgrade, initSide, ProofForgeFin.Accumulator.Clock.reinit, legacyClock, h1, h2]
  · by_cases h2 : L.borrowIndex = 0
    · simp [M, upgrade, initSide, ProofForgeFin.Accumulator.Clock.reinit, legacyClock, h1, h2]
    · simp [M, upgrade, initSide, ProofForgeFin.Accumulator.Clock.reinit, legacyClock, h1, h2]

/-! ## Settlements and call equations for the run argument -/

theorem accrueSupply_speed (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = s.supplyState.speed := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [h]
  · simp [h]

theorem accrueBorrow_speed (s : St) :
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed = s.borrowState.speed := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp [h]
  · simp [h]

theorem settle₁ (s : St) (who : Nat) : M.Settle₁ who s (supplyNext s who) := by
  have e1 := accrueSupply_index s
  have e2 := accrueSupply_block s
  have e4 := accrueSupply_speed s
  have e3 : M.total₁ s = totalSupply s := rfl
  refine ⟨?_, ?_⟩
  · rw [e3]
    simp [M, supplyNext, e1, e2, e4, ProofForgeFin.Accumulator.Clock.catchUp₁]
  · refine ⟨(fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }), rfl, ?_⟩
    intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem settle₂ (s : St) (who : Nat) : M.Settle₂ who s (borrowNext s who) := by
  have e1 := accrueBorrow_index s
  have e2 := accrueBorrow_block s
  have e4 := accrueBorrow_speed s
  have e3 : M.total₂ s = totalBorrows s := rfl
  refine ⟨?_, ?_⟩
  · rw [e3]
    simp [M, borrowNext, e1, e2, e4, ProofForgeFin.Accumulator.Clock.catchUp₂]
  · refine ⟨(fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }), rfl, ?_⟩
    intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    exact Nat.le_of_eq (Nat.add_right_comm _ _ _)

theorem consistent_of_inv (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (hI : M.Inv g₁ g₂ sp s) :
    Consistent s := by
  unfold Consistent
  exact ⟨hI.1, hI.2, fun a ha => hI.3 a ha⟩

theorem supplyHook_next (s : St) (who : Account) (g₁ g₂ : Nat) (sp : Nat × Nat)
    (hI : M.Inv g₁ g₂ sp s) : comptroller s (.supplyHook who) = some (supplyNext s who) := by
  have hC := consistent_of_inv g₁ g₂ sp s hI
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.supplyHook who) hC)
  have hD := req_supply_hook s who s' hs'
  obtain ⟨_, _, heq⟩ := hD
  rw [hs']
  congr 1

theorem borrowHook_next (s : St) (who : Account) (g₁ g₂ : Nat) (sp : Nat × Nat)
    (hI : M.Inv g₁ g₂ sp s) : comptroller s (.borrowHook who) = some (borrowNext s who) := by
  have hC := consistent_of_inv g₁ g₂ sp s hI
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.borrowHook who) hC)
  have hD := req_borrow_hook s who s' hs'
  obtain ⟨_, _, heq⟩ := hD
  rw [hs']
  congr 1

theorem setSpeeds_next (s : St) (a b : Nat) (g₁ g₂ : Nat) (sp : Nat × Nat)
    (hI : M.Inv g₁ g₂ sp s) : comptroller s (.setSpeeds a b) = some (setSpeedsNext s a b) := by
  have hC := consistent_of_inv g₁ g₂ sp s hI
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.setSpeeds a b) hC)
  have hD := req_set_speeds s a b s' hs'
  obtain ⟨_, _, heq⟩ := hD
  rw [hs']
  congr 1

theorem claim_next (s : St) (who : Account) (g₁ g₂ : Nat) (sp : Nat × Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    comptroller s (.claim who) = some (grant (supplyNext (borrowNext s who) who) who) := by
  have hC := consistent_of_inv g₁ g₂ sp s hI
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.claim who) hC)
  have hD := req_claim s who s' hs'
  obtain ⟨m₁, m₂, hB, hS, heq⟩ := hD
  obtain ⟨_, _, heqB⟩ := hB
  obtain ⟨_, _, heqS⟩ := hS
  have e1 : m₁ = borrowNext s who := heqB
  have e2 : m₂ = supplyNext (borrowNext s who) who := by
    rw [e1] at heqS
    exact heqS
  rw [hs', heq, e2]

/-! ## Every operation is an accumulator action -/

theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  have hC := consistent_of_inv g₁ g₂ sp s hI
  cases op with
  | mint who x =>
    simp only [nextSpeeds, emittedBy]
    by_cases hlt : who < s.accts.length
    · have hn := supplyHook_next s who g₁ g₂ sp hI
      simp [exec, hn, hlt]
      exact .moves (ProofForgeFin.Accumulator.Market.Settle₁.then_adjust (settle₁ s who) rfl rfl (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
    · simp [exec, hlt]
      exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
  | redeem who x =>
    simp only [nextSpeeds, emittedBy]
    by_cases hlt : who < s.accts.length
    · have hn := supplyHook_next s who g₁ g₂ sp hI
      by_cases hx : x ≤ ((supplyNext s who).acct who).supply
      · simp [exec, hn, hlt, hx]
        exact .moves (ProofForgeFin.Accumulator.Market.Settle₁.then_adjust (settle₁ s who) rfl rfl (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
      · simp [exec, hn, hlt, hx]
        exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
    · simp [exec, hlt]
      exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
  | transfer src dst x =>
    simp only [nextSpeeds, emittedBy]
    by_cases hok : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · obtain ⟨hs, hd, hne⟩ := hok
      have hn₁ := supplyHook_next s src g₁ g₂ sp hI
      have hI₁ : M.Inv g₁ g₂ sp (supplyNext s src) :=
        (ProofForgeFin.Accumulator.Market.Step.bound (.settle₁ (settle₁ s src)) hI).1
      have hn₂ := supplyHook_next (supplyNext s src) dst g₁ g₂ sp hI₁
      by_cases hx : x ≤ ((supplyNext (supplyNext s src) dst).acct src).supply
      · simp [exec, hn₁, hn₂, hs, hd, hne, hx]
        exact .moves (ProofForgeFin.Accumulator.Market.Settle₁.transfer (settle₁ s src) (settle₁ (supplyNext s src) dst) rfl rfl (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl) (fun _ => rfl))
      · simp [exec, hn₁, hn₂, hs, hd, hne, hx]
        exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
    · simp [exec, hok]
      exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
  | borrow who x =>
    simp only [nextSpeeds, emittedBy]
    by_cases hlt : who < s.accts.length
    · have hn := borrowHook_next s who g₁ g₂ sp hI
      simp [exec, hn, hlt]
      exact .moves (ProofForgeFin.Accumulator.Market.Settle₂.then_adjust (settle₂ s who) rfl rfl (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
    · simp [exec, hlt]
      exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
  | repay who x =>
    simp only [nextSpeeds, emittedBy]
    by_cases hlt : who < s.accts.length
    · have hn := borrowHook_next s who g₁ g₂ sp hI
      by_cases hx : x ≤ ((borrowNext s who).acct who).borrow
      · simp [exec, hn, hlt, hx]
        exact .moves (ProofForgeFin.Accumulator.Market.Settle₂.then_adjust (settle₂ s who) rfl rfl (fun a => ⟨Nat.le_refl _, rfl, rfl⟩) (fun _ => rfl))
      · simp [exec, hn, hlt, hx]
        exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
    · simp [exec, hlt]
      exact .moves (ProofForgeFin.Accumulator.Market.Reach.refl s)
  | claim who =>
    simp only [nextSpeeds, emittedBy]
    have hn := claim_next s who g₁ g₂ sp hI
    simp [exec, hn]
    show M.Act sp s sp 0 (grant (supplyNext (borrowNext s who) who) who)
    by_cases hgc : 0 < ((supplyNext (borrowNext s who) who).acct who).accrued ∧ ((supplyNext (borrowNext s who) who).acct who).accrued ≤ (supplyNext (borrowNext s who) who).reserve
    · have hadj : M.Adjust who (supplyNext (borrowNext s who) who) (grant (supplyNext (borrowNext s who) who) who) :=
        { clock := by
            unfold grant
            split
            · rfl
            · rfl
          accts := ⟨(fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }),
            by unfold grant; simp only [hgc, ite_true]; rfl,
            fun a => ⟨by show 0 + (a.wallet + a.accrued) ≤ a.accrued + a.wallet; omega, rfl, rfl⟩,
            .inl fun _ => rfl,
            .inl fun _ => rfl⟩ }
      exact .moves (((ProofForgeFin.Accumulator.Market.Reach.single (.settle₂ (settle₂ s who))).tail (.settle₁ (settle₁ (borrowNext s who) who))).tail (.adjust hadj))
    · have hno : grant (supplyNext (borrowNext s who) who) who = supplyNext (borrowNext s who) who := by
        unfold grant
        simp [hgc]
      rw [hno]
      exact .moves ((ProofForgeFin.Accumulator.Market.Reach.single (.settle₂ (settle₂ s who))).tail (.settle₁ (settle₁ (borrowNext s who) who)))
  | setSpeeds a b =>
    simp only [nextSpeeds, emittedBy]
    have hn := setSpeeds_next s a b g₁ g₂ sp hI
    simp [exec, hn]
    show M.Act sp s (a, b) 0 (setSpeedsNext s a b)
    refine .retune ⟨?_, ?_, ?_, ?_⟩ ?_ ?_
    · rfl
    · rfl
    · by_cases hSeq : s.supplyState.speed = a
      · refine .inl ⟨?_, ?_, ?_⟩ <;> simp [M, setSpeedsNext, hSeq]
      · refine .inr ⟨?_, ?_⟩
        · have h9 := accrueSupply_index s
          rw [totalSupply_M]
          simp [M, setSpeedsNext, hSeq, h9]
        · simp [M, setSpeedsNext, hSeq, accrueSupply_block]
    · by_cases hBeq : s.borrowState.speed = b
      · refine .inl ⟨?_, ?_, ?_⟩ <;> simp [M, setSpeedsNext, hBeq]
      · refine .inr ⟨?_, ?_⟩
        · have h9 := accrueBorrow_index s
          rw [totalBorrows_M]
          simp [M, setSpeedsNext, hBeq, h9]
        · simp [M, setSpeedsNext, hBeq, accrueBorrow_block]
    · by_cases hSeq : s.supplyState.speed = a
      · simp [M, setSpeedsNext, hSeq]
      · simp [M, setSpeedsNext, hSeq]
    · by_cases hBeq : s.borrowState.speed = b
      · simp [M, setSpeedsNext, hBeq]
      · simp [M, setSpeedsNext, hBeq]
  | advance k =>
    simp only [nextSpeeds, emittedBy]
    simp only [exec]
    exact .advance k ⟨rfl, rfl⟩
  | drip x =>
    simp only [nextSpeeds, emittedBy]
    simp only [exec]
    exact .moves (ProofForgeFin.Accumulator.Market.Reach.single (.same rfl rfl))

/-! ## Start facts at the upgrade -/

theorem acct_M (s : St) (w : Nat) : M.acct s w = s.acct w := rfl

theorem un₁_legacy (L : Legacy) : (legacyClock L).un₁ = L.unindexedSupply := rfl

theorem un₂_legacy (L : Legacy) : (legacyClock L).un₂ = L.unindexedBorrow := rfl

theorem owed_pending (L : Legacy) (a : Acct) :
    M.owed L.supplyStart L.borrowStart (legacyClock L) a = L.pendingScaled a := rfl

theorem owedsum_pending (L : Legacy) :
    ((M.accts (upgrade L)).map (M.owed L.supplyStart L.borrowStart (legacyClock L))).sum =
    (L.accts.map L.pendingScaled).sum := rfl

theorem rewards_inv (L : Legacy) (hW : L.WellFormed) : M.Inv (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) (L.compSpeed, L.compSpeed) (upgrade L) := by
  unfold Legacy.WellFormed at hW
  obtain ⟨hSg0, hSgle, hBg0, hBgle, hSb, hBb, hrec⟩ := hW
  have hg₁ : L.supplyStart = 0 ∨ L.supplyStart = M.init := by
    rcases hSg0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hg₂ : L.borrowStart = 0 ∨ L.borrowStart = M.init := by
    rcases hBg0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hgi₁ : L.supplyStart ≤ (legacyClock L).index₁ := hSgle
  have hgi₂ : L.borrowStart ≤ (legacyClock L).index₂ := hBgle
  have hl₁ : (legacyClock L).last₁ ≤ (legacyClock L).now := hSb
  have hl₂ : (legacyClock L).last₂ ≤ (legacyClock L).now := hBb
  have hr : ∀ a ∈ M.accts (upgrade L), M.rec₁ a ≤ (legacyClock L).index₁ ∧ M.rec₂ a ≤ (legacyClock L).index₂ :=
    fun a ha => hrec a ha
  exact M.inv_reinit (clock_upgrade L) hg₁ hgi₁ hg₂ hgi₂ hl₁ hl₂ hr

theorem rewards_pot (L : Legacy) (hW : L.WellFormed) : M.pot (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) (upgrade L) ≤ M.creditSum (upgrade L) * M.one + ((M.accts (upgrade L)).map (M.owed L.supplyStart L.borrowStart (legacyClock L))).sum + M.one * ((legacyClock L).un₁ + (legacyClock L).un₂) := by
  unfold Legacy.WellFormed at hW
  obtain ⟨hSg0, hSgle, hBg0, hBgle, hSb, hBb, hrec⟩ := hW
  have hr : ∀ a ∈ M.accts (upgrade L), M.rec₁ a ≤ (legacyClock L).index₁ ∧ M.rec₂ a ≤ (legacyClock L).index₂ :=
    fun a ha => hrec a ha
  exact M.pot_reinit_le (s := upgrade L) (c := legacyClock L) L.supplyStart L.borrowStart (clock_upgrade L) hr

theorem rewards_act (L : Legacy) : ∀ sp s a, M.Inv (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) sp s → M.Act sp s (nextSpeeds sp a) (emittedBy sp a) (exec comptroller s a) :=
  fun sp s a hI => exec_act _ _ sp s a hI

theorem rewards_owed (L : Legacy) : ((M.accts (upgrade L)).map (M.owed L.supplyStart L.borrowStart (legacyClock L))).sum / M.one + (legacyClock L).un₁ + (legacyClock L).un₂ = L.owed := by
  have e1 := owedsum_pending L
  have e3 : M.one = doubleScale := rfl
  unfold Legacy.owed
  rw [e1, e3, un₁_legacy, un₂_legacy]

theorem req_rewards_bounded : RewardsBounded comptroller := by
  intro L ops hW
  have hone : 0 < M.one := by decide
  have hlib := M.rewards_bounded (run comptroller) emitted speedsAfter (rewards_act L) hone (rewards_inv L hW) (rewards_pot L hW) ops
  rw [credited_M, rewards_owed L] at hlib
  exact hlib

theorem req_account_bounded : AccountBounded comptroller := by
  intro L ops who hW
  unfold Legacy.WellFormed at hW
  obtain ⟨hSg0, hSgle, hBg0, hBgle, hSb, hBb, hrec⟩ := hW
  have hone : 0 < M.one := by decide
  have hg₁ : L.supplyStart = 0 ∨ L.supplyStart = M.init := by
    rcases hSg0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hg₂ : L.borrowStart = 0 ∨ L.borrowStart = M.init := by
    rcases hBg0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hgi₁ : L.supplyStart ≤ (legacyClock L).index₁ := hSgle
  have hgi₂ : L.borrowStart ≤ (legacyClock L).index₂ := hBgle
  have hl₁ : (legacyClock L).last₁ ≤ (legacyClock L).now := hSb
  have hl₂ : (legacyClock L).last₂ ≤ (legacyClock L).now := hBb
  have hr : ∀ a ∈ M.accts (upgrade L), M.rec₁ a ≤ (legacyClock L).index₁ ∧ M.rec₂ a ≤ (legacyClock L).index₂ :=
    fun a ha => hrec a ha
  have hI : M.Inv (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) (L.compSpeed, L.compSpeed) (upgrade L) :=
    M.inv_reinit (clock_upgrade L) hg₁ hgi₁ hg₂ hgi₂ hl₁ hl₂ hr
  have hrw : M.rec₁ (M.acct (upgrade L) who) ≤ (legacyClock L).index₁ ∧ M.rec₂ (M.acct (upgrade L) who) ≤ (legacyClock L).index₂ := by
    rcases ProofForgeFin.Ledger.getD_mem_or L.accts who noAcct with hm | hm
    · exact hrec _ hm
    · have e : M.acct (upgrade L) who = noAcct := hm
      rw [e]
      exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hsOf : M.potOf (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) who (upgrade L) ≤ M.credited (M.acct (upgrade L) who) * M.one + M.owed L.supplyStart L.borrowStart (legacyClock L) (M.acct (upgrade L) who) + M.one * ((if 0 < M.units₁ (M.acct (upgrade L) who) then (legacyClock L).un₁ else 0) + (if 0 < M.units₂ (M.acct (upgrade L) who) then (legacyClock L).un₂ else 0)) :=
    M.potOf_reinit_le L.supplyStart L.borrowStart who (clock_upgrade L) hrw
  have hact : ∀ sp s a, M.Inv (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) sp s → M.Act sp s (nextSpeeds sp a) (emittedBy sp a) (exec comptroller s a) :=
    fun sp s a hI => exec_act _ _ sp s a hI
  have howedTo : M.owed L.supplyStart L.borrowStart (legacyClock L) (M.acct (upgrade L) who) / M.one + (if 0 < M.units₁ (M.acct (upgrade L) who) then (legacyClock L).un₁ else 0) + (if 0 < M.units₂ (M.acct (upgrade L) who) then (legacyClock L).un₂ else 0) = L.owedTo who := by
    have e0 : M.owed L.supplyStart L.borrowStart (legacyClock L) (M.acct (upgrade L) who) = L.pendingScaled (L.accts.getD who noAcct) := owed_pending L _
    have e1 : M.units₁ (M.acct (upgrade L) who) = (L.accts.getD who noAcct).supply := rfl
    have e2 : M.units₂ (M.acct (upgrade L) who) = (L.accts.getD who noAcct).borrow := rfl
    have e3 : M.one = doubleScale := rfl
    unfold Legacy.owedTo
    rw [e0, e1, e2, e3, un₁_legacy, un₂_legacy]
  have hlib := M.account_rewards_bounded (run comptroller) emitted speedsAfter hact hone hI who hsOf ops
  have hC : M.credited (M.acct (upgrade L) who) = (upgrade L).creditedTo who := rfl
  have hR : M.credited (M.acct (run comptroller (upgrade L) ops) who) = (run comptroller (upgrade L) ops).creditedTo who := rfl
  rw [hR, hC, howedTo] at hlib
  exact hlib

theorem req_no_backdated : NoBackdatedRewards comptroller := by
  intro L history ops who hW hNP
  unfold Legacy.WellFormed at hW
  obtain ⟨hSg0, hSgle, hBg0, hBgle, hSb, hBb, hrec⟩ := hW
  unfold NoPosition at hNP
  obtain ⟨hN1, hN2⟩ := hNP
  have hone : 0 < M.one := by decide
  have hg₁ : L.supplyStart = 0 ∨ L.supplyStart = M.init := by
    rcases hSg0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hg₂ : L.borrowStart = 0 ∨ L.borrowStart = M.init := by
    rcases hBg0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hgi₁ : L.supplyStart ≤ (legacyClock L).index₁ := hSgle
  have hgi₂ : L.borrowStart ≤ (legacyClock L).index₂ := hBgle
  have hl₁ : (legacyClock L).last₁ ≤ (legacyClock L).now := hSb
  have hl₂ : (legacyClock L).last₂ ≤ (legacyClock L).now := hBb
  have hr : ∀ a ∈ M.accts (upgrade L), M.rec₁ a ≤ (legacyClock L).index₁ ∧ M.rec₂ a ≤ (legacyClock L).index₂ :=
    fun a ha => hrec a ha
  have hI : M.Inv (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) (L.compSpeed, L.compSpeed) (upgrade L) :=
    M.inv_reinit (clock_upgrade L) hg₁ hgi₁ hg₂ hgi₂ hl₁ hl₂ hr
  have hact : ∀ sp s a, M.Inv (ProofForgeFin.Accumulator.reinitStart M.init L.supplyIndex L.supplyStart) (ProofForgeFin.Accumulator.reinitStart M.init L.borrowIndex L.borrowStart) sp s → M.Act sp s (nextSpeeds sp a) (emittedBy sp a) (exec comptroller s a) :=
    fun sp s a hI => exec_act _ _ sp s a hI
  have h₁ : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := hN1
  have h₂ : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := hN2
  have hlib := M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter hact hone hI history ops who h₁ h₂
  exact hlib

end CompRewards
