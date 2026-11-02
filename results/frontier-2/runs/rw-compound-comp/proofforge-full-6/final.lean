import CompRewards.Spec
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Index
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Ledger
import ProofForgeFin.Seq
namespace CompRewards
open ProofForgeFin ProofForgeFin.DeFi.Rewards ProofForgeFin.Accumulator

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

-- Helper: modify congruence
theorem modify_congr_acct (l : List Acct) (w : Nat) (f1 f2 : Acct → Acct)
    (h : f1 (l.getD w noAcct) = f2 (l.getD w noAcct)) : l.modify w f1 = l.modify w f2 := by
  induction l generalizing w with
  | nil =>
    cases w <;> rfl
  | cons hd tl ih =>
    cases w with
    | zero =>
      have h' : f1 hd = f2 hd := h
      show f1 hd :: tl = f2 hd :: tl
      rw [h']
    | succ w =>
      have h' : f1 (tl.getD w noAcct) = f2 (tl.getD w noAcct) := h
      show hd :: tl.modify w f1 = hd :: tl.modify w f2
      rw [ih w h']

theorem updateSupply_some (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide totalSupply subChecked fraction
  simp only [hle, ↓reduceIte]
  by_cases hd : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < (List.map Acct.supply s.accts).sum
  · obtain ⟨hd1, hd2, hd3⟩ := hd
    simp only [hd1, hd2, hd3, and_self, ↓reduceIte]
  · simp only [hd, ↓reduceIte]
    by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · obtain ⟨h1a, h1b⟩ := h1
      simp only [h1a, h1b, and_self, ↓reduceIte]
      by_cases h2 : 0 < (List.map Acct.supply s.accts).sum
      · exact absurd ⟨h1a, h1b, h2⟩ hd
      · have hz : (List.map Acct.supply s.accts).sum = 0 := by omega
        simp only [hz, Nat.lt_irrefl, ↓reduceIte, Nat.add_zero]
    · simp only [h1]
      by_cases h3 : s.blockNumber - s.supplyState.block > 0
      · simp only [h3, ↓reduceIte]
      · simp only [h3, ↓reduceIte]
        have heq : s.supplyState.block = s.blockNumber := by omega
        obtain ⟨bn, sup, bor, res, accts⟩ := s
        simp only at heq hle ⊢
        subst heq
        rfl

theorem updateBorrow_some (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide totalBorrows subChecked fraction
  simp only [hle, ↓reduceIte]
  by_cases hd : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < (List.map Acct.borrow s.accts).sum
  · obtain ⟨hd1, hd2, hd3⟩ := hd
    simp only [hd1, hd2, hd3, and_self, ↓reduceIte]
  · simp only [hd, ↓reduceIte]
    by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · obtain ⟨h1a, h1b⟩ := h1
      simp only [h1a, h1b, and_self, ↓reduceIte]
      by_cases h2 : 0 < (List.map Acct.borrow s.accts).sum
      · exact absurd ⟨h1a, h1b, h2⟩ hd
      · have hz : (List.map Acct.borrow s.accts).sum = 0 := by omega
        simp only [hz, Nat.lt_irrefl, ↓reduceIte, Nat.add_zero]
    · simp only [h1]
      by_cases h3 : s.blockNumber - s.borrowState.block > 0
      · simp only [h3, ↓reduceIte]
      · simp only [h3, ↓reduceIte]
        have heq : s.borrowState.block = s.blockNumber := by omega
        obtain ⟨bn, sup, bor, res, accts⟩ := s
        simp only at heq hle ⊢
        subst heq
        rfl

theorem updateSupply_of_some (s s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧ s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · have heq := updateSupply_some s hle
    rw [heq] at h
    refine ⟨hle, ?_⟩
    cases h
    rfl
  · unfold updateCompSupplyIndex subChecked at h
    simp only [hle, ↓reduceIte] at h
    cases h

theorem updateBorrow_of_some (s s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧ s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · have heq := updateBorrow_some s hle
    rw [heq] at h
    refine ⟨hle, ?_⟩
    cases h
    rfl
  · unfold updateCompBorrowIndex subChecked at h
    simp only [hle, ↓reduceIte] at h
    cases h

theorem supplyStart_eq (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) = accrualStart rec idx := by
  unfold accrualStart
  by_cases h0 : rec = 0 <;> simp [h0]

theorem borrowStart_eq (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) = accrualStart rec idx := supplyStart_eq rec idx

theorem distributeSupply_of_some (s1 : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s1 who = some s') :
    accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index ∧
    s' = { s1 with accts := s1.accts.modify who fun a => { a with supplierIndex := s1.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index) s1.supplyState.index } } := by
  unfold distributeSupplierComp subChecked St.acct at h
  simp only at h
  have hsup : (if (s1.accts.getD who noAcct).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.accts.getD who noAcct).supplierIndex) = accrualStart (s1.accts.getD who noAcct).supplierIndex s1.supplyState.index := supplyStart_eq _ _
  -- analyze the match
  by_cases hle : (if (s1.accts.getD who noAcct).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.accts.getD who noAcct).supplierIndex) ≤ s1.supplyState.index
  · simp only [hle, ↓reduceIte] at h
    have hle2 : accrualStart (s1.accts.getD who noAcct).supplierIndex s1.supplyState.index ≤ s1.supplyState.index := by
      rw [← hsup]; exact hle
    refine ⟨hle2, ?_⟩
    have hs' : s' = s1.withAcct who fun a => { a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.accts.getD who noAcct).supply (s1.supplyState.index - (if (s1.accts.getD who noAcct).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.accts.getD who noAcct).supplierIndex)) } := by
      cases h
      rfl
    rw [hs']
    unfold St.withAcct creditFor mulDouble
    congr 1
    apply modify_congr_acct
    have hdelta : (s1.supplyState.index - (if (s1.accts.getD who noAcct).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.accts.getD who noAcct).supplierIndex)) = (s1.supplyState.index - accrualStart (s1.accts.getD who noAcct).supplierIndex s1.supplyState.index) := by rw [hsup]
    have harg : (fun a : Acct => { a with supplierIndex := s1.supplyState.index, accrued := a.accrued + (s1.accts.getD who noAcct).supply * (s1.supplyState.index - (if (s1.accts.getD who noAcct).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.accts.getD who noAcct).supplierIndex)) / doubleScale }) (s1.accts.getD who noAcct) = (fun a : Acct => { a with supplierIndex := s1.supplyState.index, accrued := a.accrued + a.supply * (s1.supplyState.index - accrualStart a.supplierIndex s1.supplyState.index) / doubleScale }) (s1.accts.getD who noAcct) := by
      simp only [hdelta]
    exact harg
  · simp only [hle, ↓reduceIte] at h
    cases h

theorem distributeBorrow_of_some (s1 : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s1 who = some s') :
    accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index ∧
    s' = { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := by
  unfold distributeBorrowerComp subChecked St.acct at h
  simp only at h
  have hsup : (if (s1.accts.getD who noAcct).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.accts.getD who noAcct).borrowerIndex) = accrualStart (s1.accts.getD who noAcct).borrowerIndex s1.borrowState.index := borrowStart_eq _ _
  by_cases hle : (if (s1.accts.getD who noAcct).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.accts.getD who noAcct).borrowerIndex) ≤ s1.borrowState.index
  · simp only [hle, ↓reduceIte] at h
    have hle2 : accrualStart (s1.accts.getD who noAcct).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
      rw [← hsup]; exact hle
    refine ⟨hle2, ?_⟩
    have hs' : s' = s1.withAcct who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.accts.getD who noAcct).borrow (s1.borrowState.index - (if (s1.accts.getD who noAcct).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.accts.getD who noAcct).borrowerIndex)) } := by
      cases h
      rfl
    rw [hs']
    unfold St.withAcct creditFor mulDouble
    congr 1
    apply modify_congr_acct
    have hdelta : (s1.borrowState.index - (if (s1.accts.getD who noAcct).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.accts.getD who noAcct).borrowerIndex)) = (s1.borrowState.index - accrualStart (s1.accts.getD who noAcct).borrowerIndex s1.borrowState.index) := by rw [hsup]
    have harg : (fun a : Acct => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + (s1.accts.getD who noAcct).borrow * (s1.borrowState.index - (if (s1.accts.getD who noAcct).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.accts.getD who noAcct).borrowerIndex)) / doubleScale }) (s1.accts.getD who noAcct) = (fun a : Acct => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + a.borrow * (s1.borrowState.index - accrualStart a.borrowerIndex s1.borrowState.index) / doubleScale }) (s1.accts.getD who noAcct) := by
      simp only [hdelta]
    exact harg
  · simp only [hle, ↓reduceIte] at h
    cases h

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  by_cases h : 0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve
  · simp only [h, ↓reduceIte]
    have harg : (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.accts.getD who noAcct).accrued } : Acct)) (s.accts.getD who noAcct) = (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) (s.accts.getD who noAcct) := by rfl
    have hmod : s.accts.modify who (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.accts.getD who noAcct).accrued } : Acct)) = s.accts.modify who (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) :=
      modify_congr_acct _ _ _ _ harg
    simp only [hmod]
  · simp only [h, ↓reduceIte]

theorem accrueSupply_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrueBorrow_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index :=
  accrueSupply_ge sd now total

theorem recorded_supply_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  unfold St.acct
  have hor := ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct
  rcases hor with hm | heq
  · exact (hmem _ hm).1
  · rw [heq]
    exact Nat.zero_le _

theorem recorded_borrow_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  unfold St.acct
  have hor := ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct
  rcases hor with hm | heq
  · exact (hmem _ hm).2
  · rw [heq]
    exact Nat.zero_le _

theorem accrualStart_le_of_le (rec idx : Nat) (h : rec ≤ idx) :
    accrualStart rec idx ≤ idx := by
  unfold accrualStart
  by_cases h0 : rec = 0
  · simp only [h0, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi]
    · simp [hi]
  · simp only [h0, ↓reduceIte]
    exact h

theorem distributeSupply_isSome (s1 : St) (who : Account)
    (hle : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index) :
    (distributeSupplierComp s1 who).isSome = true := by
  have hsup : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) = accrualStart (s1.acct who).supplierIndex s1.supplyState.index := supplyStart_eq _ _
  have hcond : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by
    rw [hsup]; exact hle
  unfold distributeSupplierComp subChecked
  simp [hcond]

theorem distributeBorrow_isSome (s1 : St) (who : Account)
    (hle : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index) :
    (distributeBorrowerComp s1 who).isSome = true := by
  have hsup : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) = accrualStart (s1.acct who).borrowerIndex s1.borrowState.index := borrowStart_eq _ _
  have hcond : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by
    rw [hsup]; exact hle
  unfold distributeBorrowerComp subChecked
  simp [hcond]

theorem setSupply_isSome (s : St) (a : Nat) (hle : s.supplyState.block ≤ s.blockNumber) :
    (setSupplySpeed s a).isSome = true := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed = a
  · simp [heq]
  · simp [heq, updateSupply_some s hle]

theorem setBorrow_isSome (t : St) (b : Nat) (hle : t.borrowState.block ≤ t.blockNumber) :
    (setBorrowSpeed t b).isSome = true := by
  unfold setBorrowSpeed
  by_cases heq : t.borrowState.speed = b
  · simp [heq]
  · simp [heq, updateBorrow_some t hle]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompSupplyIndex s with
  | none =>
    simp only [hu] at h
    simp at h
  | some s1 =>
    simp only [hu] at h
    simp at h
    obtain ⟨hle, heq1⟩ := updateSupply_of_some s s1 hu
    obtain ⟨hle2, heq2⟩ := distributeSupply_of_some s1 who s' h
    unfold SupplyDistributed
    refine ⟨hle, ?_, ?_⟩
    · rw [heq1] at hle2
      simpa [St.acct] using hle2
    · rw [heq1] at heq2
      exact heq2

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompBorrowIndex s with
  | none =>
    simp only [hu] at h
    simp at h
  | some s1 =>
    simp only [hu] at h
    simp at h
    obtain ⟨hle, heq1⟩ := updateBorrow_of_some s s1 hu
    obtain ⟨hle2, heq2⟩ := distributeBorrow_of_some s1 who s' h
    unfold BorrowDistributed
    refine ⟨hle, ?_, ?_⟩
    · rw [heq1] at hle2
      simpa [St.acct] using hle2
    · rw [heq1] at heq2
      exact heq2

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
  cases hu1 : updateCompBorrowIndex s with
  | none =>
    simp only [hu1] at h
    simp at h
  | some s1 =>
    simp only [hu1] at h
    simp at h
    cases hd1 : distributeBorrowerComp s1 who with
    | none =>
      simp only [hd1] at h
      simp at h
    | some m1 =>
      simp only [hd1] at h
      simp at h
      cases hu2 : updateCompSupplyIndex m1 with
      | none =>
        simp only [hu2] at h
        simp at h
      | some s2 =>
        simp only [hu2] at h
        simp at h
        cases hd2 : distributeSupplierComp s2 who with
        | none =>
          simp only [hd2] at h
          simp at h
        | some m2 =>
          simp only [hd2] at h
          simp at h
          obtain ⟨hble, heq_b1⟩ := updateBorrow_of_some s s1 hu1
          obtain ⟨hble2, heq_b2⟩ := distributeBorrow_of_some s1 who m1 hd1
          obtain ⟨hsle, heq_s1⟩ := updateSupply_of_some m1 s2 hu2
          obtain ⟨hsle2, heq_s2⟩ := distributeSupply_of_some s2 who m2 hd2
          have hgrant : grantCompInternal m2 who = grant m2 who := grant_eq m2 who
          rw [hgrant] at h
          cases h
          -- Build Claimed witnesses
          refine ⟨m1, m2, ?_, ?_, rfl⟩
          · unfold BorrowDistributed
            refine ⟨hble, ?_, ?_⟩
            · rw [heq_b1] at hble2
              simpa [St.acct] using hble2
            · rw [heq_b1] at heq_b2
              exact heq_b2
          · unfold SupplyDistributed
            -- need totals: totalSupply m1 = totalSupply s? supply balances unchanged by borrow steps
            -- m1 accts = s1 accts modified on borrowerIndex/accrued only, so supply sum same
            -- s1 accts = s accts, so totalSupply m1 = totalSupply s; similarly s2 supplyState = accrue of m1
            -- We show m2 equation matches with m1 as base: heq_s2 already states m2 = {s2 with ...}
            -- and s2 = {m1 with supplyState := accrue ... (totalSupply m1)}
            -- Need to rewrite totalSupply m1 = totalSupply s? Actually BorrowDistributed uses totalBorrows s,
            -- SupplyDistributed uses totalSupply m1. Our heq_b1 uses totalBorrows s, heq_s1 uses totalSupply m1.
            -- So they already match the required statements with the right totals.
            -- heq_s1 : s2 = {m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1)}
            -- heq_s2 : m2 = {s2 with accts := ... (accrueSide s2... )}
            -- But SupplyDistributed m1 who m2 requires accrue over totalSupply m1 and s2's block = m1.blockNumber.
            -- Since s2.blockNumber = m1.blockNumber (update preserves blockNumber), this holds.
            -- heq_s1 already gives s2's supplyState = accrueSide ..., and blockNumber preserved.
            -- So we can use heq_s1/heq_s2 directly after showing blockNumber equalities.
            refine ⟨hsle, ?_, ?_⟩
            · have h2 := hsle2
              rw [heq_s1] at h2
              simpa [St.acct] using h2
            · rw [heq_s1] at heq_s2
              simpa using heq_s2

theorem setSupply_of_some (s t : St) (a : Nat) (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = (if s.supplyState.speed = a then s else { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    cases h
    refine ⟨fun hn => absurd heq hn, ?_⟩
    simp [heq]
  · simp [heq] at h
    cases hu : updateCompSupplyIndex s with
    | none =>
      simp only [hu] at h
      simp at h
    | some s1 =>
      simp only [hu] at h
      simp at h
      obtain ⟨hle, heq1⟩ := updateSupply_of_some s s1 hu
      cases h
      refine ⟨fun _ => hle, ?_⟩
      simp [heq, heq1]

theorem setBorrow_of_some (t s2 : St) (b : Nat) (h : setBorrowSpeed t b = some s2) :
    (t.borrowState.speed ≠ b → t.borrowState.block ≤ t.blockNumber) ∧
    s2 = (if t.borrowState.speed = b then t else { t with borrowState := { accrueSide t.borrowState t.blockNumber (totalBorrows t) with speed := b } }) := by
  unfold setBorrowSpeed at h
  by_cases heq : t.borrowState.speed = b
  · simp [heq] at h
    cases h
    refine ⟨fun hn => absurd heq hn, ?_⟩
    simp [heq]
  · simp [heq] at h
    cases hu : updateCompBorrowIndex t with
    | none =>
      simp only [hu] at h
      simp at h
    | some s1 =>
      simp only [hu] at h
      simp at h
      obtain ⟨hle, heq1⟩ := updateBorrow_of_some t s1 hu
      cases h
      refine ⟨fun _ => hle, ?_⟩
      simp [heq, heq1]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  cases hs : setSupplySpeed s a with
  | none =>
    simp only [hs] at h
    simp at h
  | some t =>
    simp only [hs] at h
    simp at h
    cases hb : setBorrowSpeed t b with
    | none =>
      simp only [hb] at h
      simp at h
    | some s2 =>
      simp only [hb] at h
      simp at h
      obtain ⟨hs_le, hs_eq⟩ := setSupply_of_some s t a hs
      obtain ⟨hb_le, hb_eq⟩ := setBorrow_of_some t s2 b hb
      cases h
      unfold SpeedsSet
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exact hs_le hne
      · intro hne_s
        have ht_bn : t.blockNumber = s.blockNumber := by
          rw [hs_eq]
          split
          · rfl
          · rfl
        have ht_bor : t.borrowState = s.borrowState := by
          rw [hs_eq]
          split
          · rfl
          · rfl
        have hspeed : t.borrowState.speed = s.borrowState.speed := by rw [ht_bor]
        have hne_t : t.borrowState.speed ≠ b := by simpa [hspeed] using hne_s
        have hle := hb_le hne_t
        simpa [ht_bn, ht_bor] using hle
      · by_cases heq_sup : s.supplyState.speed = a
        · simp [heq_sup] at hs_eq
          have ht : t = s := hs_eq
          rw [ht] at hb_eq
          by_cases heq_bor : s.borrowState.speed = b
          · simp [heq_sup, heq_bor] at hb_eq ⊢
            exact hb_eq
          · simp [heq_sup, heq_bor] at hb_eq ⊢
            exact hb_eq
        · simp [heq_sup] at hs_eq
          have ht_bn : t.blockNumber = s.blockNumber := by rw [hs_eq]
          have ht_bor : t.borrowState = s.borrowState := by rw [hs_eq]
          have ht_accts : t.accts = s.accts := by rw [hs_eq]
          have htot_bor : totalBorrows t = totalBorrows s := by simp [totalBorrows, ht_accts]
          have hspeed_eq : s.borrowState.speed = t.borrowState.speed := by rw [ht_bor]
          have hacc : accrueSide t.borrowState t.blockNumber (totalBorrows t) = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
            rw [ht_bor, ht_bn, htot_bor]
          by_cases heq_bor : t.borrowState.speed = b
          · simp [heq_bor] at hb_eq
            have heq_bor_s : s.borrowState.speed = b := hspeed_eq.trans heq_bor
            simp [heq_sup, heq_bor_s] at ⊢
            simp [hb_eq, hs_eq]
          · simp [heq_bor] at hb_eq
            have heq_bor_s : s.borrowState.speed ≠ b := by simpa [hspeed_eq] using heq_bor
            simp [heq_sup, heq_bor_s] at ⊢
            simp [hb_eq, hs_eq, hacc, totalBorrows, totalSupply]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsup, hbor, hmem⟩ := hc
  have hsup_le : ∀ who : Account, (s.acct who).supplierIndex ≤ s.supplyState.index := fun who => recorded_supply_le s who ⟨hsup, hbor, hmem⟩
  have hbor_le : ∀ who : Account, (s.acct who).borrowerIndex ≤ s.borrowState.index := fun who => recorded_borrow_le s who ⟨hsup, hbor, hmem⟩
  unfold comptroller
  cases c with
  | supplyHook who =>
    simp only [updateSupply_some s hsup]
    simp
    have hnew : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≥ s.supplyState.index :=
      accrueSupply_ge s.supplyState s.blockNumber (totalSupply s)
    have hrec : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      Nat.le_trans (hsup_le who) hnew
    have hstart' := accrualStart_le_of_le _ _ hrec
    have hsome := distributeSupply_isSome ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) who (by simpa [St.acct] using hstart')
    exact hsome
  | borrowHook who =>
    simp only [updateBorrow_some s hbor]
    simp
    have hnew := accrueBorrow_ge s.borrowState s.blockNumber (totalBorrows s)
    have hrec : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans (hbor_le who) hnew
    have hstart' := accrualStart_le_of_le _ _ hrec
    have hsome := distributeBorrow_isSome ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) who (by simpa [St.acct] using hstart')
    exact hsome
  | claim who =>
    -- Use intermediate states via isSome existence
    let s1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hs1 : updateCompBorrowIndex s = some s1 := updateBorrow_some s hbor
    have hnew_b := accrueBorrow_ge s.borrowState s.blockNumber (totalBorrows s)
    have hrec_b : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans (hbor_le who) hnew_b
    have hstart_b' := accrualStart_le_of_le _ _ hrec_b
    have hle_b : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
      simpa [s1, St.acct] using hstart_b'
    have hdist_b := distributeBorrow_isSome s1 who hle_b
    obtain ⟨m1, hm1⟩ := Option.isSome_iff_exists.mp hdist_b
    obtain ⟨_, heq_m1⟩ := distributeBorrow_of_some s1 who m1 hm1
    -- m1 preserves supply side and supplierIndex
    have hm1_sup : m1.supplyState = s.supplyState := by simp [heq_m1, s1]
    have hm1_bn : m1.blockNumber = s.blockNumber := by simp [heq_m1, s1]
    have hm1_suppIdx : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have hmod : (((s1.accts.modify who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } : Acct)).getD who noAcct).supplierIndex = (s1.accts.getD who noAcct).supplierIndex) := by
        rw [ProofForgeFin.Ledger.getD_modify]
        split
        · rfl
        · rfl
      have h1 : (m1.acct who).supplierIndex = (((s1.accts.modify who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } : Acct)).getD who noAcct).supplierIndex) := by
        rw [heq_m1]
        simp [St.withAcct, St.acct]
      have h2 : (s1.acct who).supplierIndex = (s1.accts.getD who noAcct).supplierIndex := by
        simp [St.acct]
      have h3 : (s1.acct who).supplierIndex = (s.acct who).supplierIndex := by
        simp [s1, St.acct]
      rw [h1, hmod, ←h2, h3]
    have hsup_m1 : m1.supplyState.block ≤ m1.blockNumber := by rw [hm1_sup, hm1_bn]; exact hsup
    let s2 : St := { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) }
    have hs2 : updateCompSupplyIndex m1 = some s2 :=
      updateSupply_some m1 hsup_m1
    have hnew_s : (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≥ m1.supplyState.index :=
      accrueSupply_ge _ _ _
    have hrec_s : (m1.acct who).supplierIndex ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
      have h0 : (m1.acct who).supplierIndex ≤ m1.supplyState.index := by
        rw [hm1_suppIdx]
        rw [hm1_sup]
        exact hsup_le who
      exact Nat.le_trans h0 hnew_s
    have hstart_s' := accrualStart_le_of_le _ _ hrec_s
    have hle_s : accrualStart (s2.acct who).supplierIndex s2.supplyState.index ≤ s2.supplyState.index := by
      simpa [s2, St.acct] using hstart_s'
    have hdist_s := distributeSupply_isSome s2 who hle_s
    obtain ⟨m2, hm2⟩ := Option.isSome_iff_exists.mp hdist_s
    simp [claimComp, hs1, hm1, hs2, hm2]
  | setSpeeds a b =>
    unfold setCompSpeedInternal
    have hs_some := setSupply_isSome s a hsup
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs_some
    have ht_bn : t.blockNumber = s.blockNumber := by
      obtain ⟨_, heq⟩ := setSupply_of_some s t a ht
      rw [heq]
      split
      · rfl
      · rfl
    have ht_bor : t.borrowState = s.borrowState := by
      obtain ⟨_, heq⟩ := setSupply_of_some s t a ht
      rw [heq]
      split
      · rfl
      · rfl
    have hbor_t : t.borrowState.block ≤ t.blockNumber := by rw [ht_bor, ht_bn]; exact hbor
    have hb_some := setBorrow_isSome t b hbor_t
    obtain ⟨s2, hs2⟩ := Option.isSome_iff_exists.mp hb_some
    simp [ht, hs2]
-- Potentials for boundedness
def pendSup (gS : Nat) (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - effStart gS a.supplierIndex)
def pendBor (gB : Nat) (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - effStart gB a.borrowerIndex)
def unindexedSup (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def unindexedBor (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
def Pot (gS gB : Nat) (s : St) : Nat :=
  (s.credited * doubleScale + ((s.accts.map (pendSup gS s)).sum + (s.accts.map (pendBor gB s)).sum) + doubleScale * (unindexedSup s + unindexedBor s))
def PotTo (gS gB : Nat) (s : St) (who : Account) : Nat :=
  ((s.creditedTo who) * doubleScale + (pendSup gS s (s.acct who) + pendBor gB s (s.acct who)) + doubleScale * ((if 0 < (s.acct who).supply then unindexedSup s else 0) + (if 0 < (s.acct who).borrow then unindexedBor s else 0)))

theorem legacyStart_eq_effStart (g rec : Nat) : legacyStart g rec = effStart g rec := by
  unfold legacyStart effStart
  rfl

theorem accrualStart_eq_firstStart (rec idx : Nat) :
    accrualStart rec idx = firstStart compInitialIndex rec idx := by
  unfold accrualStart firstStart
  rfl

theorem creditFor_eq_credit (u st idx : Nat) :
    creditFor u st idx = credit doubleScale u st idx := by
  unfold creditFor credit
  rfl

-- Invariant for runs from upgrade
def Inv (gS gB : Nat) (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ gS ≤ s.supplyState.index ∧ gB ≤ s.borrowState.index ∧
  s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2 ∧
  (gS = 0 ∨ gS = compInitialIndex) ∧ (gB = 0 ∨ gB = compInitialIndex)

theorem accrueSide_index_eq_catchUp (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index = catchUp doubleScale sd.index sd.block sd.speed now total := by
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, accrueSide, catchUp]
  · simp [h, accrueSide, catchUp]

theorem unindexedSup_eq (s : St) : unindexedSup s = unindexed s.supplyState.block s.supplyState.speed s.blockNumber := by
  unfold unindexedSup unindexed
  rfl

theorem unindexedBor_eq (s : St) : unindexedBor s = unindexed s.borrowState.block s.borrowState.speed s.blockNumber := by
  unfold unindexedBor unindexed
  rfl

theorem pot_supplyHook_le (gS gB : Nat) (s s' : St) (who : Account)
    (hgS_or : gS = 0 ∨ gS = compInitialIndex) (hgB_or : gB = 0 ∨ gB = compInitialIndex)
    (hgS_le : gS ≤ s.supplyState.index) (hgB_le : gB ≤ s.borrowState.index)
    (hDist : SupplyDistributed s who s') : Pot gS gB s' ≤ Pot gS gB s := by
  unfold SupplyDistributed at hDist
  obtain ⟨hblk, hstart_le, heq⟩ := hDist
  -- Explicit new index and settle function
  let newSupIdx : Nat := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
  have h_old_le_new : s.supplyState.index ≤ newSupIdx := accrueSupply_ge _ _ _
  have hgS_le_new : gS ≤ newSupIdx := Nat.le_trans hgS_le h_old_le_new
  -- Use library: define term t, units, etc.
  -- t idx a = (accrued+wallet)*one + supplyPending(idx) + borrowPending (fixed borrow idx)
  let t : Nat → Acct → Nat := fun idx a =>
    (a.accrued + a.wallet) * doubleScale + (a.supply * (idx - effStart gS a.supplierIndex) + a.borrow * (s.borrowState.index - effStart gB a.borrowerIndex))
  let f : Acct → Acct := fun a =>
    { a with supplierIndex := newSupIdx, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex newSupIdx) newSupIdx }
  have heq_accts : s'.accts = s.accts.modify who f := by
    rw [heq]
  have heq_supIdx : s'.supplyState.index = newSupIdx := by rw [heq]
  have heq_borIdx : s'.borrowState.index = s.borrowState.index := by rw [heq]
  have heq_bn : s'.blockNumber = s.blockNumber := by rw [heq]
  have heq_borBlk : s'.borrowState.block = s.borrowState.block := by rw [heq]
  have heq_supBlk : s'.supplyState.block = s.blockNumber := by
    rw [heq]
    unfold accrueSide
    split
    · rfl
    · rfl
  -- Pot equality rewrites
  have hPot_s : Pot gS gB s = ((s.accts.map (t s.supplyState.index)).sum + doubleScale * (unindexedSup s + unindexedBor s)) := by
    sorry
  have hPot_s' : Pot gS gB s' = (((s.accts.modify who f).map (t newSupIdx)).sum + doubleScale * (0 + unindexedBor s)) := by
    sorry
  have ht : ∀ a ∈ s.accts, t newSupIdx a ≤ t s.supplyState.index a + a.supply * (newSupIdx - s.supplyState.index) := by
    sorry
  have hU : (s.accts.map Acct.supply).sum * (newSupIdx - s.supplyState.index) + doubleScale * (0 + unindexedBor s) ≤ doubleScale * (unindexedSup s + unindexedBor s) := by
    sorry
  have hf : who < s.accts.length → t newSupIdx (f (s.accts.getD who noAcct)) ≤ t newSupIdx (s.accts.getD who noAcct) := by
    sorry
  have hpot := pot_accrue_settle_le s.accts who f noAcct t Acct.supply ht hU hf
  sorry

theorem pot_borrowHook_le (gS gB : Nat) (s s' : St) (who : Account)
    (hgS_or : gS = 0 ∨ gS = compInitialIndex) (hgB_or : gB = 0 ∨ gB = compInitialIndex)
    (hgS_le : gS ≤ s.supplyState.index) (hgB_le : gB ≤ s.borrowState.index)
    (hDist : BorrowDistributed s who s') : Pot gS gB s' ≤ Pot gS gB s := by
  sorry

theorem pot_advance (s : St) (k : Nat) (gS gB : Nat)
    (hsup : s.supplyState.block ≤ s.blockNumber) (hbor : s.borrowState.block ≤ s.blockNumber) :
    Pot gS gB ({ s with blockNumber := s.blockNumber + k } : St) = Pot gS gB s + doubleScale * (k * (s.supplyState.speed + s.borrowState.speed)) := by
  unfold Pot St.credited pendSup pendBor unindexedSup unindexedBor
  simp only
  have hsup_eq : (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed = (s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed := by
    rw [Nat.sub_add_comm hsup, Nat.add_mul]
  have hbor_eq : (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed = (s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed := by
    rw [Nat.sub_add_comm hbor, Nat.add_mul]
  simp only [hsup_eq, hbor_eq]
  grind

theorem pot_drip (s : St) (x : Nat) (gS gB : Nat) : Pot gS gB ({ s with reserve := s.reserve + x } : St) = Pot gS gB s := by
  rfl

theorem pot_exec_le (gS gB : Nat) (sp : Nat × Nat) (s : St) (op : Op) (hInv : Inv gS gB sp s) :
    Pot gS gB (exec comptroller s op) ≤ Pot gS gB s + doubleScale * emittedBy sp op ∧ Inv gS gB (nextSpeeds sp op) (exec comptroller s op) := by
  obtain ⟨hc, hgS_le, hgB_le, hsp1, hsp2, hgS_or, hgB_or⟩ := hInv
  unfold Consistent at hc
  obtain ⟨hsup_blk, hbor_blk, hmem⟩ := hc
  cases op with
  | advance k =>
    simp only [exec, emittedBy, nextSpeeds]
    have hPot := pot_advance s k gS gB hsup_blk hbor_blk
    rw [hPot, hsp1, hsp2]
    refine ⟨Nat.le_refl _, ?_⟩
    -- Inv preserved: blockNumber grows, others same
    unfold Inv Consistent
    simp only
    refine ⟨⟨?_, ?_, ?_⟩, hgS_le, hgB_le, hsp1, hsp2, hgS_or, hgB_or⟩
    · omega
    · omega
    · intro a ha
      have hm := hmem a ha
      exact hm
  | drip x =>
    simp only [exec, emittedBy, nextSpeeds]
    have hPot := pot_drip s x gS gB
    rw [hPot]
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ⟨Nat.le_refl _, ⟨⟨hsup_blk, hbor_blk, hmem⟩, hgS_le, hgB_le, hsp1, hsp2, hgS_or, hgB_or⟩⟩
  | setSpeeds a b =>
    -- In Inv states, comptroller succeeds via req_calls_succeed
    have hc_inv : Consistent s := ⟨hsup_blk, hbor_blk, hmem⟩
    have hsome : (comptroller s (.setSpeeds a b)).isSome = true := req_calls_succeed s _ ⟨hsup_blk, hbor_blk, hmem⟩
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hsome
    have hsSet := req_set_speeds s a b s' hs'
    -- exec returns s' (since getD with some)
    have hexec : exec comptroller s (.setSpeeds a b) = s' := by
      simp [exec, hs']
    rw [hexec]
    simp only [emittedBy, nextSpeeds, Nat.mul_zero, Nat.add_zero]
    -- Need Pot s' ≤ Pot s and Inv for (a,b)
    sorry
  | claim who =>
    sorry
  | mint who x =>
    sorry
  | redeem who x =>
    sorry
  | transfer src dst x =>
    sorry
  | borrow who x =>
    sorry
  | repay who x =>
    sorry

theorem upgrade_Consistent (L : Legacy) (h : L.WellFormed) : Consistent (upgrade L) := by
  unfold Legacy.WellFormed at h
  obtain ⟨hs_or, hs_le, hb_or, hb_le, hsup_blk, hbor_blk, hmem⟩ := h
  unfold Consistent upgrade initSide
  simp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases hs0 : L.supplyIndex = 0
    · simp [hs0]
    · simp [hs0]
      exact hsup_blk
  · by_cases hb0 : L.borrowIndex = 0
    · simp [hb0]
    · simp [hb0]
      exact hbor_blk
  · intro a ha
    have hm := hmem a ha
    obtain ⟨hs_rec, hb_rec⟩ := hm
    refine ⟨?_, ?_⟩
    · by_cases hs0 : L.supplyIndex = 0
      · simp [hs0] at hs_rec ⊢
        have : a.supplierIndex = 0 := by omega
        simp [this]
      · simp [hs0]
        exact hs_rec
    · by_cases hb0 : L.borrowIndex = 0
      · simp [hb0] at hb_rec ⊢
        have : a.borrowerIndex = 0 := by omega
        simp [this]
      · simp [hb0]
        exact hb_rec

theorem upgrade_Inv (L : Legacy) (h : L.WellFormed) :
    Inv L.supplyStart L.borrowStart (L.compSpeed, L.compSpeed) (upgrade L) := by
  have hc' : Consistent (upgrade L) := upgrade_Consistent L h
  unfold Legacy.WellFormed at h
  obtain ⟨hs_or, hs_le, hb_or, hb_le, hsup_blk, hbor_blk, hmem⟩ := h
  unfold Inv
  refine ⟨hc', ?_, ?_, ?_, ?_, hs_or, hb_or⟩
  · unfold upgrade initSide
    simp only
    by_cases hs0 : L.supplyIndex = 0
    · simp [hs0]
      rcases hs_or with h0 | h0
      · rw [h0]
        exact Nat.zero_le _
      · rw [h0]
        exact Nat.le_refl _
    · simp [hs0]
      exact hs_le
  · unfold upgrade initSide
    simp only
    by_cases hb0 : L.borrowIndex = 0
    · simp [hb0]
      rcases hb_or with h0 | h0
      · rw [h0]
        exact Nat.zero_le _
      · rw [h0]
        exact Nat.le_refl _
    · simp [hb0]
      exact hb_le
  · unfold upgrade initSide
    simp only
    by_cases hs0 : L.supplyIndex = 0
    · simp [hs0]
    · simp [hs0]
  · unfold upgrade initSide
    simp only
    by_cases hb0 : L.borrowIndex = 0
    · simp [hb0]
    · simp [hb0]

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
