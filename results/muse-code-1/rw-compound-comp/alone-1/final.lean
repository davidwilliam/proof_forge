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

-- Helper: subChecked succeeds iff bound holds.
theorem subChecked_eq_some {a b : Nat} : subChecked a b = some (a - b) ↔ b ≤ a := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

theorem subChecked_isSome {a b : Nat} : (subChecked a b).isSome = decide (b ≤ a) := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

theorem subChecked_some_iff {a b d : Nat} : subChecked a b = some d ↔ b ≤ a ∧ a - b = d := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

-- Helper: the fixed start computation equals the spec's accrualStart.
theorem startSupply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex)
    = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · by_cases h1 : compInitialIndex ≤ s.supplyState.index <;> simp [h0, h1]
  · simp [h0]

theorem startBorrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex)
    = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · by_cases h1 : compInitialIndex ≤ s.borrowState.index <;> simp [h0, h1]
  · simp [h0]

-- accrualStart is bounded by the index when the recorded index is.
theorem accrualStart_le_of_le (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases h0 : recorded = 0
  · by_cases h1 : compInitialIndex ≤ index
    · simp only [h0, if_pos h1]
      exact h1
    · simp only [h0, if_neg h1]
      exact Nat.zero_le _
  · simp only [h0, if_neg h0]
    exact h

-- updateCompSupplyIndex matches accrueSide.
theorem updateSupply_ok (s : St) (s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) ∧
    s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber ∧
    s1.reserve = s.reserve ∧ s1.accts = s.accts := by
  unfold updateCompSupplyIndex at h
  cases hd : subChecked s.blockNumber s.supplyState.block with
  | none =>
    simp [hd] at h
  | some deltaBlocks =>
    have hle : s.supplyState.block ≤ s.blockNumber := by
      unfold subChecked at hd
      by_cases hb : s.supplyState.block ≤ s.blockNumber
      · exact hb
      · simp [hb] at hd
    have hdelta : deltaBlocks = s.blockNumber - s.supplyState.block := by
      have h2 : subChecked s.blockNumber s.supplyState.block = some deltaBlocks := by
        simp [hd]
      exact (((subChecked_some_iff (a := s.blockNumber) (b := s.supplyState.block) (d := deltaBlocks)).mp h2).2).symm
    subst hdelta
    simp only [hd] at h
    unfold accrueSide
    by_cases hD : (s.blockNumber - s.supplyState.block) > 0
    · by_cases hS : s.supplyState.speed > 0
      · by_cases hT : totalSupply s > 0
        · have hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s :=
            ⟨hD, hS, hT⟩
          simp [hD, hS, hT] at h
          simp [hc1] at ⊢
          cases h
          exact ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
        · have hT0 : totalSupply s = 0 := by omega
          simp [hD, hS, hT0] at h
          have hc1 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
            simp [hT0]
          simp [hc1] at ⊢
          cases h
          exact ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
      · simp [hD, hS] at h
        have hc1 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
          simp [hS]
        simp [hc1] at ⊢
        cases h
        exact ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
    · have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have heq : s.blockNumber = s.supplyState.block := by omega
      simp [hD] at h
      have hc1 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        simp [hzero]
      simp [hc1] at ⊢
      cases h
      refine ⟨hle, ?_, rfl, rfl, rfl, rfl⟩
      simp [heq]

theorem updateBorrow_ok (s : St) (s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) ∧
    s1.supplyState = s.supplyState ∧ s1.blockNumber = s.blockNumber ∧
    s1.reserve = s.reserve ∧ s1.accts = s.accts := by
  unfold updateCompBorrowIndex at h
  cases hd : subChecked s.blockNumber s.borrowState.block with
  | none =>
    simp [hd] at h
  | some deltaBlocks =>
    have hle : s.borrowState.block ≤ s.blockNumber := by
      unfold subChecked at hd
      by_cases hb : s.borrowState.block ≤ s.blockNumber
      · exact hb
      · simp [hb] at hd
    have hdelta : deltaBlocks = s.blockNumber - s.borrowState.block := by
      have h2 : subChecked s.blockNumber s.borrowState.block = some deltaBlocks := by
        simp [hd]
      exact (((subChecked_some_iff (a := s.blockNumber) (b := s.borrowState.block) (d := deltaBlocks)).mp h2).2).symm
    subst hdelta
    simp only [hd] at h
    unfold accrueSide
    by_cases hD : (s.blockNumber - s.borrowState.block) > 0
    · by_cases hS : s.borrowState.speed > 0
      · by_cases hT : totalBorrows s > 0
        · have hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s :=
            ⟨hD, hS, hT⟩
          simp [hD, hS, hT] at h
          simp [hc1] at ⊢
          cases h
          exact ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
        · have hT0 : totalBorrows s = 0 := by omega
          simp [hD, hS, hT0] at h
          have hc1 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
            simp [hT0]
          simp [hc1] at ⊢
          cases h
          exact ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
      · simp [hD, hS] at h
        have hc1 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          simp [hS]
        simp [hc1] at ⊢
        cases h
        exact ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
    · have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have heq : s.blockNumber = s.borrowState.block := by omega
      simp [hD] at h
      have hc1 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [hzero]
      simp [hc1] at ⊢
      cases h
      refine ⟨hle, ?_, rfl, rfl, rfl, rfl⟩
      simp [heq]

theorem modify_supply_eq (l : List Acct) (who : Nat) (I : Nat) :
  l.modify who (fun a => { a with supplierIndex := I, accrued := a.accrued + (l.getD who noAcct).supply * (I - accrualStart (l.getD who noAcct).supplierIndex I) / doubleScale })
  = l.modify who (fun a => { a with supplierIndex := I, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex I) I }) := by
  apply List.ext_getElem
  · simp [List.length_modify]
  · intro i h1 h2
    have hi : i < l.length := by simpa [List.length_modify] using h1
    have hLf : (l.modify who (fun a => { a with supplierIndex := I, accrued := a.accrued + (l.getD who noAcct).supply * (I - accrualStart (l.getD who noAcct).supplierIndex I) / doubleScale }))[i] = if who = i then (fun a => { a with supplierIndex := I, accrued := a.accrued + (l.getD who noAcct).supply * (I - accrualStart (l.getD who noAcct).supplierIndex I) / doubleScale }) l[i] else l[i] := by
      have htmp := List.getElem_modify (f := (fun a => { a with supplierIndex := I, accrued := a.accrued + (l.getD who noAcct).supply * (I - accrualStart (l.getD who noAcct).supplierIndex I) / doubleScale })) (i := who) (l := l) (j := i) h1
      simpa using htmp
    have hRf : (l.modify who (fun a => { a with supplierIndex := I, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex I) I }))[i] = if who = i then (fun a => { a with supplierIndex := I, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex I) I }) l[i] else l[i] := by
      have htmp := List.getElem_modify (f := (fun a => { a with supplierIndex := I, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex I) I })) (i := who) (l := l) (j := i) h2
      simpa using htmp
    rw [hLf, hRf]
    by_cases heq : who = i
    · simp only [heq, ite_true]
      have hgi : l[i] = l.getD i noAcct := List.getElem_eq_getD noAcct
      have hsym : l.getD i noAcct = l[i] := hgi.symm
      have hgw : l.getD who noAcct = l.getD i noAcct := by rw [heq]
      have heq2 : l.getD who noAcct = l[i] := by rw [hgw, hsym]
      rw [hsym, creditFor]
    · simp [heq]

theorem modify_borrow_eq (l : List Acct) (who : Nat) (I : Nat) :
  l.modify who (fun a => { a with borrowerIndex := I, accrued := a.accrued + (l.getD who noAcct).borrow * (I - accrualStart (l.getD who noAcct).borrowerIndex I) / doubleScale })
  = l.modify who (fun a => { a with borrowerIndex := I, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex I) I }) := by
  apply List.ext_getElem
  · simp [List.length_modify]
  · intro i h1 h2
    have hi : i < l.length := by simpa [List.length_modify] using h1
    have hLf : (l.modify who (fun a => { a with borrowerIndex := I, accrued := a.accrued + (l.getD who noAcct).borrow * (I - accrualStart (l.getD who noAcct).borrowerIndex I) / doubleScale }))[i] = if who = i then (fun a => { a with borrowerIndex := I, accrued := a.accrued + (l.getD who noAcct).borrow * (I - accrualStart (l.getD who noAcct).borrowerIndex I) / doubleScale }) l[i] else l[i] := by
      have htmp := List.getElem_modify (f := (fun a => { a with borrowerIndex := I, accrued := a.accrued + (l.getD who noAcct).borrow * (I - accrualStart (l.getD who noAcct).borrowerIndex I) / doubleScale })) (i := who) (l := l) (j := i) h1
      simpa using htmp
    have hRf : (l.modify who (fun a => { a with borrowerIndex := I, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex I) I }))[i] = if who = i then (fun a => { a with borrowerIndex := I, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex I) I }) l[i] else l[i] := by
      have htmp := List.getElem_modify (f := (fun a => { a with borrowerIndex := I, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex I) I })) (i := who) (l := l) (j := i) h2
      simpa using htmp
    rw [hLf, hRf]
    by_cases heq : who = i
    · simp only [heq, ite_true]
      have hgi : l[i] = l.getD i noAcct := List.getElem_eq_getD noAcct
      have hsym : l.getD i noAcct = l[i] := hgi.symm
      have hgw : l.getD who noAcct = l.getD i noAcct := by rw [heq]
      have heq2 : l.getD who noAcct = l[i] := by rw [hgw, hsym]
      rw [hsym, creditFor]
    · simp [heq]

-- distributeSupplierComp matches the supply part of SupplyDistributed.
theorem distributeSupply_ok (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp at h
  simp only at h
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex)
      = accrualStart (s.acct who).supplierIndex s.supplyState.index := startSupply_eq s who
  rw [hstart] at h
  cases hd : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none =>
    simp [hd] at h
  | some deltaIndex =>
    have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
      have h2 : subChecked s.supplyState.index
          (accrualStart (s.acct who).supplierIndex s.supplyState.index) = some deltaIndex := by simp [hd]
      exact ((subChecked_some_iff (a := s.supplyState.index)
        (b := accrualStart (s.acct who).supplierIndex s.supplyState.index) (d := deltaIndex)).mp h2).1
    have hdelta : deltaIndex = s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index := by
      have h2 : subChecked s.supplyState.index
          (accrualStart (s.acct who).supplierIndex s.supplyState.index) = some deltaIndex := by simp [hd]
      exact (((subChecked_some_iff (a := s.supplyState.index)
        (b := accrualStart (s.acct who).supplierIndex s.supplyState.index) (d := deltaIndex)).mp h2).2).symm
    simp only [hd] at h
    subst hdelta
    simp only [mulDouble, creditFor] at h
    cases h
    refine ⟨hle, ?_⟩
    unfold St.withAcct St.acct at *
    have hmod := modify_supply_eq s.accts who s.supplyState.index
    rw [hmod]

theorem distributeBorrow_ok (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp at h
  simp only at h
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex)
      = accrualStart (s.acct who).borrowerIndex s.borrowState.index := startBorrow_eq s who
  rw [hstart] at h
  cases hd : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none =>
    simp [hd] at h
  | some deltaIndex =>
    have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
      have h2 : subChecked s.borrowState.index
          (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = some deltaIndex := by simp [hd]
      exact ((subChecked_some_iff (a := s.borrowState.index)
        (b := accrualStart (s.acct who).borrowerIndex s.borrowState.index) (d := deltaIndex)).mp h2).1
    have hdelta : deltaIndex = s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
      have h2 : subChecked s.borrowState.index
          (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = some deltaIndex := by simp [hd]
      exact (((subChecked_some_iff (a := s.borrowState.index)
        (b := accrualStart (s.acct who).borrowerIndex s.borrowState.index) (d := deltaIndex)).mp h2).2).symm
    simp only [hd] at h
    subst hdelta
    simp only [mulDouble, creditFor] at h
    cases h
    refine ⟨hle, ?_⟩
    unfold St.withAcct St.acct at *
    have hmod := modify_borrow_eq s.accts who s.borrowState.index
    rw [hmod]

-- accrueSide never decreases the index and brings the block up to date.
theorem accrueSide_mono_index (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

-- totalSupply / totalBorrows depend only on accts.
theorem totalSupply_congr {s1 s2 : St} (h : s1.accts = s2.accts) : totalSupply s1 = totalSupply s2 := by
  unfold totalSupply
  rw [h]

theorem totalBorrows_congr {s1 s2 : St} (h : s1.accts = s2.accts) : totalBorrows s1 = totalBorrows s2 := by
  unfold totalBorrows
  rw [h]

theorem acct_congr {s1 s2 : St} (h : s1.accts = s2.accts) (who : Nat) : s1.acct who = s2.acct who := by
  unfold St.acct
  rw [h]

-- Combined supply hook equals SupplyDistributed.
theorem supplyHook_ok (s : St) (who : Account) (s' : St)
    (h : (do let s1 ← updateCompSupplyIndex s; distributeSupplierComp s1 who) = some s') :
    SupplyDistributed s who s' := by
  cases h1 : updateCompSupplyIndex s with
  | none =>
    simp [h1] at h
  | some s1 =>
    simp [h1] at h
    obtain ⟨hble, hs1idx, hs1bor, hs1blk, hs1res, hs1accts⟩ := updateSupply_ok s s1 h1
    obtain ⟨hdle, hs'def⟩ := distributeSupply_ok s1 who s' h
    -- rewrite s1 fields to s-based accrueSide
    have hs1acct : s1.acct who = s.acct who := acct_congr hs1accts who
    have htot : totalSupply s1 = totalSupply s := totalSupply_congr hs1accts
    -- s1 supplyState is accrueSide s ...
    -- distribute's index is s1's index = accrueSide index
    -- Need to show SupplyDistributed conditions
    refine ⟨?_, ?_, ?_⟩
    · exact hble
    · -- accrualStart (s.acct).supplierIndex (accrue index) ≤ accrue index
      -- s1.acct = s.acct, s1 index = accrue index
      have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index ∨ ¬ ((s.acct who).supplierIndex ≤ s.supplyState.index) := by omega
      -- Actually need recorded ≤ new index to apply accrualStart_le_of_le.
      -- We only know hdle : accrualStart (s1.acct) (s1.index) ≤ s1.index.
      -- Rewrite s1.acct/index to s-based accrue values.
      rw [hs1acct, hs1idx] at hdle
      -- hdle is exactly needed second conjunct? Check spec: accrualStart (s.acct).supplierIndex (accrue...) ≤ accrue...
      -- But spec uses totalSupply s (same as s1 after rewrite?). Need to rewrite totalSupply?
      -- hs1idx already uses totalSupply s (since updateSupply_ok uses totalSupply s), good.
      -- So hdle matches required, after rewriting htot? Actually hdle's index is accrueSide ... (totalSupply s1)? Wait hs1idx : s1.supplyState = accrueSide ... (totalSupply s). And htot : totalSupply s1 = totalSupply s.
      -- distributeSupply_ok's index is s1.supplyState.index, which equals accrueSide ... index. Good.
      -- So hdle, after rewriting, is exactly the goal.
      have htot2 : totalSupply s1 = totalSupply s := htot
      -- s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
      have hidx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hs1idx]
      -- rewrite hdle's s1 parts to s-based? Already did hs1acct, hs1idx. Need to also handle totalSupply? No, hdle doesn't mention totalSupply.
      exact hdle
    · rw [hs'def, hs1idx, hs1bor, hs1blk, hs1res, hs1accts]

theorem borrowHook_ok (s : St) (who : Account) (s' : St)
    (h : (do let s1 ← updateCompBorrowIndex s; distributeBorrowerComp s1 who) = some s') :
    BorrowDistributed s who s' := by
  cases h1 : updateCompBorrowIndex s with
  | none =>
    simp [h1] at h
  | some s1 =>
    simp [h1] at h
    obtain ⟨hble, hs1idx, hs1sup, hs1blk, hs1res, hs1accts⟩ := updateBorrow_ok s s1 h1
    obtain ⟨hdle, hs'def⟩ := distributeBorrow_ok s1 who s' h
    have hs1acct : s1.acct who = s.acct who := acct_congr hs1accts who
    rw [hs1acct, hs1idx] at hdle
    refine ⟨hble, hdle, ?_⟩
    rw [hs'def, hs1idx, hs1sup, hs1blk, hs1res, hs1accts]
theorem modify_grant_eq (l : List Acct) (who : Nat) :
  l.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + (l.getD who noAcct).accrued } : Acct))
  = l.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) := by
  apply List.ext_getElem
  · simp [List.length_modify]
  · intro i h1 h2
    have hi : i < l.length := by simpa [List.length_modify] using h1
    have hLf : (l.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + (l.getD who noAcct).accrued } : Acct)))[i] = if who = i then (fun a => ({ a with accrued := 0, wallet := a.wallet + (l.getD who noAcct).accrued } : Acct)) l[i] else l[i] := by
      have htmp := List.getElem_modify (f := (fun a => ({ a with accrued := 0, wallet := a.wallet + (l.getD who noAcct).accrued } : Acct))) (i := who) (l := l) (j := i) h1
      simpa using htmp
    have hRf : (l.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)))[i] = if who = i then (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) l[i] else l[i] := by
      have htmp := List.getElem_modify (f := (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct))) (i := who) (l := l) (j := i) h2
      simpa using htmp
    rw [hLf, hRf]
    by_cases heq : who = i
    · simp only [heq, ite_true]
      have hgi : l[i] = l.getD i noAcct := List.getElem_eq_getD noAcct
      have hsym : l.getD i noAcct = l[i] := hgi.symm
      rw [hsym]
    · simp [heq]

-- grantCompInternal equals the spec's grant.
theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  by_cases h : (s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve
  · simp only [h, ite_true]
    have hmod := modify_grant_eq s.accts who
    simp only [hmod]
  · simp only [h, ite_false]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  exact supplyHook_ok s who s' h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  exact borrowHook_ok s who s' h

-- claim: borrow part then supply part then grant.
theorem claim_ok (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') : Claimed s who s' := by
  unfold claimComp at h
  cases hb1 : updateCompBorrowIndex s with
  | none =>
    simp [hb1] at h
  | some b1 =>
    simp [hb1] at h
    cases hb2 : distributeBorrowerComp b1 who with
    | none =>
      simp [hb2] at h
    | some m1 =>
      simp [hb2] at h
      cases hs1 : updateCompSupplyIndex m1 with
      | none =>
        simp [hs1] at h
      | some s1 =>
        simp [hs1] at h
        cases hs2 : distributeSupplierComp s1 who with
        | none =>
          simp [hs2] at h
        | some m2 =>
          simp [hs2] at h
          -- h : grantCompInternal m2 who = s'
          have hgrant : s' = grant m2 who := by
            have heq : grantCompInternal m2 who = s' := by simpa using h
            rw [grant_eq] at heq
            exact heq.symm
          -- m1 satisfies BorrowDistributed s who m1
          have hbor : BorrowDistributed s who m1 := borrowHook_ok s who m1 (by simp [hb1, hb2])
          -- m2 satisfies SupplyDistributed m1 who m2
          -- Need to show (do updateSupply m1; distributeSupply ...) = some m2, which holds by hs1, hs2
          have hsup : SupplyDistributed m1 who m2 := supplyHook_ok m1 who m2 (by simp [hs1, hs2])
          exact ⟨m1, m2, hbor, hsup, hgrant⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  exact claim_ok s who s' h

-- setSupplySpeed matches accrue + speed set.
theorem setSupply_ok (s : St) (sup : Nat) (s' : St) (h : setSupplySpeed s sup = some s') :
    (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    s' = { s with supplyState := if s.supplyState.speed = sup then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = sup
  · simp [heq] at h
    subst h
    refine ⟨?_, ?_⟩
    · intro hne
      omega
    · simp [heq]
  · simp [heq] at h
    cases hu : updateCompSupplyIndex s with
    | none =>
      simp [hu] at h
    | some s1 =>
      simp [hu] at h
      obtain ⟨hble, hs1idx, hs1bor, hs1blk, hs1res, hs1accts⟩ := updateSupply_ok s s1 hu
      cases h
      refine ⟨fun _ => hble, ?_⟩
      simp [heq, hs1idx, hs1bor, hs1blk, hs1res, hs1accts]

theorem setBorrow_ok (s : St) (bor : Nat) (s' : St) (h : setBorrowSpeed s bor = some s') :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    s' = { s with borrowState := if s.borrowState.speed = bor then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = bor
  · simp [heq] at h
    subst h
    refine ⟨?_, ?_⟩
    · intro hne
      omega
    · simp [heq]
  · simp [heq] at h
    cases hu : updateCompBorrowIndex s with
    | none =>
      simp [hu] at h
    | some s1 =>
      simp [hu] at h
      obtain ⟨hble, hs1idx, hs1sup, hs1blk, hs1res, hs1accts⟩ := updateBorrow_ok s s1 hu
      cases h
      refine ⟨fun _ => hble, ?_⟩
      simp [heq, hs1idx, hs1sup, hs1blk, hs1res, hs1accts]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  cases hsup : setSupplySpeed s a with
  | none =>
    simp [hsup] at h
  | some mid =>
    simp [hsup] at h
    cases hbor : setBorrowSpeed mid b with
    | none =>
      simp [hbor] at h
    | some fin =>
      simp [hbor] at h
      subst h
      obtain ⟨hsupBlk, hsupEq⟩ := setSupply_ok s a mid hsup
      obtain ⟨hborBlk, hborEq⟩ := setBorrow_ok mid b fin hbor
      -- Need SpeedsSet s a b fin
      -- SpeedsSet requires s blocks ≤ when speeds differ, and fin = {...}
      -- hsupEq : mid = {s with supplyState := ...}, hborEq : fin = {mid with borrowState := ...}
      -- Need to rewrite mid's fields in hborEq to s-based.
      -- mid.supplyState = ..., mid.borrowState = s.borrowState? Let's derive.
      have hmidSup : mid.supplyState = if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } := by rw [hsupEq]
      -- mid.borrowState = s.borrowState, etc. From hsupEq (which only changes supplyState) ?
      -- hsupEq says mid = {s with supplyState := ...}, so other fields equal s.
      have hmidBor : mid.borrowState = s.borrowState := by rw [hsupEq]
      have hmidBlk : mid.blockNumber = s.blockNumber := by rw [hsupEq]
      have hmidRes : mid.reserve = s.reserve := by rw [hsupEq]
      have hmidAccts : mid.accts = s.accts := by rw [hsupEq]
      have hmidTot : totalBorrows mid = totalBorrows s := totalBorrows_congr hmidAccts
      -- hborEq : fin = {mid with borrowState := ... totalBorrows mid ...}
      -- Rewrite totalBorrows mid to totalBorrows s, and mid fields to s-based where needed.
      rw [hmidTot] at hborEq
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exact hsupBlk hne
      · intro hne
        have hne' : mid.borrowState.speed ≠ b := by rw [hmidBor]; exact hne
        have hle := hborBlk hne'
        rw [hmidBor, hmidBlk] at hle
        exact hle
      · rw [hborEq, hsupEq]

-- update succeeds when block is not ahead.
theorem updateSupply_succeeds (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s1, updateCompSupplyIndex s = some s1 := by
  unfold updateCompSupplyIndex
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    (subChecked_eq_some.mpr h)
  -- Actually subChecked_eq_some : subChecked a b = some (a-b) ↔ b ≤ a, so mpr h gives equality.
  rw [hsub]
  by_cases hD : (s.blockNumber - s.supplyState.block) > 0
  · by_cases hS : s.supplyState.speed > 0
    · simp only [hD, hS, and_true, ite_true]
      exact ⟨_, rfl⟩
    · simp only [hD, hS, and_false, ite_false, hD, ite_true]
      -- second if (delta>0) true, so else-branch is some with block update
      exact ⟨_, rfl⟩
  · simp only [hD, false_and, ite_false, hD, ite_false]
    exact ⟨_, rfl⟩

theorem updateBorrow_succeeds (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s1, updateCompBorrowIndex s = some s1 := by
  unfold updateCompBorrowIndex
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    (subChecked_eq_some.mpr h)
  rw [hsub]
  by_cases hD : (s.blockNumber - s.borrowState.block) > 0
  · by_cases hS : s.borrowState.speed > 0
    · simp only [hD, hS, and_true, ite_true]
      exact ⟨_, rfl⟩
    · simp only [hD, hS, and_false, ite_false, hD, ite_true]
      exact ⟨_, rfl⟩
  · simp only [hD, false_and, ite_false, hD, ite_false]
    exact ⟨_, rfl⟩

-- distribute succeeds when recorded index is bounded.
theorem distributeSupply_succeeds (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by
  unfold distributeSupplierComp
  simp only
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex)
      = accrualStart (s.acct who).supplierIndex s.supplyState.index := startSupply_eq s who
  rw [hstart]
  have hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    (subChecked_eq_some.mpr h)
  rw [hsub]
  exact ⟨_, rfl⟩

theorem distributeBorrow_succeeds (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by
  unfold distributeBorrowerComp
  simp only
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex)
      = accrualStart (s.acct who).borrowerIndex s.borrowState.index := startBorrow_eq s who
  rw [hstart]
  have hsub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    (subChecked_eq_some.mpr h)
  rw [hsub]
  exact ⟨_, rfl⟩

theorem getD_out_of_bounds (l : List Acct) (who : Nat) (h : ¬ who < l.length) :
    l.getD who noAcct = noAcct := by
  induction l generalizing who with
  | nil =>
    simp [List.getD]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp at h
    | succ n =>
      simp [List.getD] at *
      exact ih n (by omega)

-- In a consistent state every recorded index is bounded, including out-of-bounds (0).
theorem consistent_supply_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  by_cases hlt : who < s.accts.length
  · have hget : s.accts.getD who noAcct = s.accts[who] := (List.getElem_eq_getD noAcct).symm
    have hmem2 : s.accts[who] ∈ s.accts := List.getElem_mem hlt
    have hle := hmem _ hmem2
    unfold St.acct
    rw [hget]
    exact hle.1
  · have hget : s.accts.getD who noAcct = noAcct := getD_out_of_bounds _ _ hlt
    unfold St.acct
    rw [hget]
    simp [noAcct]

theorem consistent_borrow_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  by_cases hlt : who < s.accts.length
  · have hget : s.accts.getD who noAcct = s.accts[who] := (List.getElem_eq_getD noAcct).symm
    have hmem2 : s.accts[who] ∈ s.accts := List.getElem_mem hlt
    have hle := hmem _ hmem2
    unfold St.acct
    rw [hget]
    exact hle.2
  · have hget : s.accts.getD who noAcct = noAcct := getD_out_of_bounds _ _ hlt
    unfold St.acct
    rw [hget]
    simp [noAcct]

-- Borrow distribute preserves supplierIndex for the target account.
theorem borrow_preserves_supply (b1 m1 : St) (who : Account)
    (hdef : m1 = { b1 with accts := b1.accts.modify who (fun a =>
      { a with borrowerIndex := b1.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index }) }) :
    (m1.acct who).supplierIndex = (b1.acct who).supplierIndex := by
  have hlen : (b1.accts.modify who (fun a =>
      { a with borrowerIndex := b1.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index })).length
      = b1.accts.length := by simp [List.length_modify]
  by_cases hlt : who < b1.accts.length
  · have hlt' : who < (b1.accts.modify who (fun a =>
        { a with borrowerIndex := b1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index })).length := by
      rw [hlen]
      exact hlt
    have e1 : m1.acct who = (b1.accts.modify who (fun a =>
        { a with borrowerIndex := b1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index }))[who] := by
      unfold St.acct
      rw [hdef]
      exact (List.getElem_eq_getD noAcct).symm
    have e2 : b1.acct who = b1.accts[who] := by
      unfold St.acct
      exact (List.getElem_eq_getD noAcct).symm
    rw [e1, e2]
    simp
  · have h1 : b1.accts.getD who noAcct = noAcct := getD_out_of_bounds _ _ hlt
    have h2 : (b1.accts.modify who (fun a =>
        { a with borrowerIndex := b1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index })).getD who noAcct = noAcct := by
      apply getD_out_of_bounds
      rw [hlen]
      exact hlt
    unfold St.acct
    rw [hdef]
    simp only
    rw [h1, h2]

theorem setSupply_succeeds (s : St) (sup : Nat)
    (h : s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) :
    ∃ s', setSupplySpeed s sup = some s' := by
  by_cases heq : s.supplyState.speed = sup
  · exact ⟨s, by simp [setSupplySpeed, heq]⟩
  · obtain ⟨s1, hs1⟩ := updateSupply_succeeds s (h heq)
    exact ⟨{ s1 with supplyState := { s1.supplyState with speed := sup } }, by simp [setSupplySpeed, heq, hs1]⟩

theorem setBorrow_succeeds (s : St) (bor : Nat)
    (h : s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) :
    ∃ s', setBorrowSpeed s bor = some s' := by
  by_cases heq : s.borrowState.speed = bor
  · exact ⟨s, by simp [setBorrowSpeed, heq]⟩
  · obtain ⟨s1, hs1⟩ := updateBorrow_succeeds s (h heq)
    exact ⟨{ s1 with borrowState := { s1.borrowState with speed := bor } }, by simp [setBorrowSpeed, heq, hs1]⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsupBlk, hborBlk, hmem⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    simp only
    obtain ⟨s1, hs1⟩ := updateSupply_succeeds s hsupBlk
    -- s1 has new index ≥ old, and same accts, so recorded ≤ new index
    obtain ⟨_, hs1idx, _, _, _, hs1accts⟩ := updateSupply_ok s s1 hs1
    have hrec : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
      have h0 : (s.acct who).supplierIndex ≤ s.supplyState.index := consistent_supply_le s ⟨hsupBlk, hborBlk, hmem⟩ who
      have hacct : s1.acct who = s.acct who := acct_congr hs1accts who
      have hmono : s.supplyState.index ≤ s1.supplyState.index := by rw [hs1idx]; exact accrueSide_mono_index _ _ _
      rw [hacct]
      omega
    have hstart := accrualStart_le_of_le _ _ hrec
    obtain ⟨s', hs'⟩ := distributeSupply_succeeds s1 who hstart
    simp [hs1, hs']
  | borrowHook who =>
    unfold comptroller
    simp only
    obtain ⟨s1, hs1⟩ := updateBorrow_succeeds s hborBlk
    obtain ⟨_, hs1idx, _, _, _, hs1accts⟩ := updateBorrow_ok s s1 hs1
    have hrec : (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
      have h0 : (s.acct who).borrowerIndex ≤ s.borrowState.index := consistent_borrow_le s ⟨hsupBlk, hborBlk, hmem⟩ who
      have hacct : s1.acct who = s.acct who := acct_congr hs1accts who
      have hmono : s.borrowState.index ≤ s1.borrowState.index := by rw [hs1idx]; exact accrueSide_mono_index _ _ _
      rw [hacct]
      omega
    have hstart := accrualStart_le_of_le _ _ hrec
    obtain ⟨s', hs'⟩ := distributeBorrow_succeeds s1 who hstart
    simp [hs1, hs']
  | claim who =>
    unfold comptroller claimComp
    simp only
    obtain ⟨b1, hb1⟩ := updateBorrow_succeeds s hborBlk
    obtain ⟨_, hb1idx, hb1sup, hb1blk, hb1res, hb1accts⟩ := updateBorrow_ok s b1 hb1
    have hrecB : (b1.acct who).borrowerIndex ≤ b1.borrowState.index := by
      have h0 := consistent_borrow_le s ⟨hsupBlk, hborBlk, hmem⟩ who
      have hacct : b1.acct who = s.acct who := acct_congr hb1accts who
      have hmono : s.borrowState.index ≤ b1.borrowState.index := by rw [hb1idx]; exact accrueSide_mono_index _ _ _
      rw [hacct]
      omega
    obtain ⟨m1, hm1⟩ := distributeBorrow_succeeds b1 who (accrualStart_le_of_le _ _ hrecB)
    obtain ⟨_, hm1def⟩ := distributeBorrow_ok b1 who m1 hm1
    -- m1 supply side equals b1 (= s) supply side, so supply block still ≤
    have hsupBlk' : m1.supplyState.block ≤ m1.blockNumber := by
      have e1 : m1.supplyState = b1.supplyState := by rw [hm1def]
      have e2 : m1.blockNumber = b1.blockNumber := by rw [hm1def]
      have e3 : b1.supplyState = s.supplyState := hb1sup
      have e4 : b1.blockNumber = s.blockNumber := hb1blk
      rw [e1, e2, e3, e4]
      exact hsupBlk
    obtain ⟨s1, hs1⟩ := updateSupply_succeeds m1 hsupBlk'
    obtain ⟨_, hs1idx, _, _, _, hs1accts⟩ := updateSupply_ok m1 s1 hs1
    have hrecS : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
      -- s1.acct = m1.acct, m1.acct supply recorded? Need bound.
      -- m1.accts = b1.accts.modify ..., b1.accts = s.accts, so m1's recorded supply?
      -- For supply side, m1's supply recorded is same as s's? Since borrow distribute only touches borrowerIndex/accrued, not supplierIndex.
      -- So (m1.acct who).supplierIndex = (s.acct who).supplierIndex ≤ s.supplyState.index ≤ s1.supplyState.index.
      have h0 := consistent_supply_le s ⟨hsupBlk, hborBlk, hmem⟩ who
      have hacct1 : b1.acct who = s.acct who := acct_congr hb1accts who
      -- m1.acct supplierIndex = b1.acct supplierIndex (since borrow distribute doesn't touch supplierIndex)
      have hacct2 : (m1.acct who).supplierIndex = (b1.acct who).supplierIndex :=
        borrow_preserves_supply b1 m1 who hm1def
      have hacct3 : s1.acct who = m1.acct who := acct_congr hs1accts who
      have hmono : m1.supplyState.index ≤ s1.supplyState.index := by rw [hs1idx]; exact accrueSide_mono_index _ _ _
      -- m1.supplyState = b1.supplyState = s.supplyState
      have hmidSup : m1.supplyState = s.supplyState := by rw [hm1def, hb1sup]
      rw [hacct3, hacct2, hacct1]
      have hle1 : (s.acct who).supplierIndex ≤ s.supplyState.index := h0
      have hle2 : s.supplyState.index ≤ s1.supplyState.index := by rw [hmidSup] at hmono; exact hmono
      omega
    obtain ⟨m2, hm2⟩ := distributeSupply_succeeds s1 who (accrualStart_le_of_le _ _ hrecS)
    simp [hb1, hm1, hs1, hm2]
  | setSpeeds a b =>
    unfold comptroller
    have hsup : ∃ mid, setSupplySpeed s a = some mid :=
      setSupply_succeeds s a (fun hne => hsupBlk)
    obtain ⟨mid, hmid⟩ := hsup
    have hmidBorBlk : mid.borrowState.block ≤ mid.blockNumber := by
      have hEq := setSupply_ok s a mid hmid
      -- hEq.2 : mid = {s with supplyState := ...}, so borrow/block unchanged
      have e1 : mid.borrowState = s.borrowState := by rw [hEq.2]
      have e2 : mid.blockNumber = s.blockNumber := by rw [hEq.2]
      rw [e1, e2]
      exact hborBlk
    have hbor : ∃ fin, setBorrowSpeed mid b = some fin :=
      setBorrow_succeeds mid b (fun hne => hmidBorBlk)
    obtain ⟨fin, hfin⟩ := hbor
    simp [hmid, hfin, setCompSpeedInternal]
-- Pending scaled sums and potentials for boundedness.
def supplyPendScaled (s : St) : Nat :=
  (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum
def borrowPendScaled (s : St) : Nat :=
  (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum
def unindexedSupply (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def unindexedBorrow (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
def K (s : St) : Nat :=
  s.credited * doubleScale + supplyPendScaled s + borrowPendScaled s
    + unindexedSupply s * doubleScale + unindexedBorrow s * doubleScale

def pendWhoSupply (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)
def pendWhoBorrow (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)
def unindexedWhoSupply (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).supply then (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0
def unindexedWhoBorrow (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).borrow then (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0
def Kwho (s : St) (who : Account) : Nat :=
  (s.creditedTo who) * doubleScale + pendWhoSupply s who + pendWhoBorrow s who
    + unindexedWhoSupply s who * doubleScale + unindexedWhoBorrow s who * doubleScale

-- accrualStart is monotone in the index.
theorem accrualStart_mono_index (r I I' : Nat) (h : I ≤ I') :
    accrualStart r I ≤ accrualStart r I' := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp only [hr, ite_true]
    by_cases h1 : compInitialIndex ≤ I
    · have h1' : compInitialIndex ≤ I' := by omega
      simp only [h1, h1', ite_true]
      exact Nat.le_refl _
    · by_cases h1' : compInitialIndex ≤ I'
      · simp only [h1, h1', ite_false, ite_true]
        exact Nat.zero_le _
      · simp only [h1, h1', ite_false]
        exact Nat.zero_le _
  · simp only [hr, ite_false]
    exact Nat.le_refl _

-- Self start is the index itself.
theorem accrualStart_self (I : Nat) : accrualStart I I = I := by
  unfold accrualStart
  by_cases h0 : I = 0
  · subst h0
    have hpos : 0 < compInitialIndex := by
      unfold compInitialIndex
      exact Nat.pow_pos (by decide)
    have hneg : ¬ compInitialIndex ≤ 0 := by omega
    simp [hneg]
  · simp [h0]

-- Sum distributive: Σ (g a * k) = (Σ g a) * k.
theorem sum_map_mul (l : List Acct) (g : Acct → Nat) (k : Nat) :
    ((l.map fun a => g a * k).sum) = ((l.map g).sum) * k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
