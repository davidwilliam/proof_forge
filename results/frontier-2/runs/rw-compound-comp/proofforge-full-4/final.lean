import CompRewards.Spec
import ProofForgeFin.Ledger
import ProofForgeFin.Accumulator
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

/-- Every recorded index lies below the market index, so the accrual start does too. -/
theorem accrualStart_le (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr, h]

theorem supplierStart_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0
  · by_cases hi : compInitialIndex ≤ s.supplyState.index
    · simp [hr, hi]
    · simp [hr, hi]
  · simp [hr]

theorem borrowerStart_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0
  · by_cases hi : compInitialIndex ≤ s.borrowState.index
    · simp [hr, hi]
    · simp [hr, hi]
  · simp [hr]

theorem upd_supply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide totalSupply fraction subChecked
  simp only [h, ↓reduceIte]
  by_cases hd : s.blockNumber - s.supplyState.block > 0
  · by_cases hs : s.supplyState.speed > 0
    · by_cases ht : (s.accts.map Acct.supply).sum > 0
      · simp [hd, hs, ht]
      · have ht0 : (s.accts.map Acct.supply).sum = 0 := by omega
        simp [hd, hs, ht0]
    · simp [hd, hs]
  · have heq : s.blockNumber = s.supplyState.block := by omega
    have hss : ({ index := s.supplyState.index, block := s.blockNumber, speed := s.supplyState.speed } : Side) = s.supplyState := by
      rw [heq]
    simp [hd, hss]

theorem upd_borrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide totalBorrows fraction subChecked
  simp only [h, ↓reduceIte]
  by_cases hd : s.blockNumber - s.borrowState.block > 0
  · by_cases hs : s.borrowState.speed > 0
    · by_cases ht : (s.accts.map Acct.borrow).sum > 0
      · simp [hd, hs, ht]
      · have ht0 : (s.accts.map Acct.borrow).sum = 0 := by omega
        simp [hd, hs, ht0]
    · simp [hd, hs]
  · have heq : s.blockNumber = s.borrowState.block := by omega
    have hss : ({ index := s.borrowState.index, block := s.blockNumber, speed := s.borrowState.speed } : Side) = s.borrowState := by
      rw [heq]
    simp [hd, hss]

theorem modify_congr_eq (l : List Acct) (i : Nat) (f g : Acct → Acct)
    (h : f (l.getD i noAcct) = g (l.getD i noAcct)) :
    l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ j => rfl
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons, List.getD_cons_zero] at h ⊢
      rw [h]
    | succ j =>
      simp only [List.modify_succ_cons, List.getD_cons_succ] at h ⊢
      rw [ih _ h]

/-- `grantCompInternal` is `grant`. -/
theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  simp only
  by_cases h1 : 0 < (s.accts.getD who noAcct).accrued
  · by_cases h2 : (s.accts.getD who noAcct).accrued ≤ s.reserve
    · simp only [h1, h2]
      have hmod : s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + (s.accts.getD who noAcct).accrued }) =
          s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
        apply modify_congr_eq
        rfl
      rw [hmod]
    · have hcond : ¬ ((s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve) :=
        fun hc => h2 hc.2
      have hcond2 : ¬ (0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve) :=
        fun hc => h2 hc.2
      rw [if_neg hcond, if_neg hcond2]
  · have hcond : ¬ ((s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve) :=
      fun hc => h1 hc.1
    have hcond2 : ¬ (0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve) :=
      fun hc => h1 hc.1
    rw [if_neg hcond, if_neg hcond2]

theorem upd_supply_some (s : St) (s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧ s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hle : s.supplyState.block ≤ s.blockNumber := by
    unfold updateCompSupplyIndex subChecked at h
    by_cases hle : s.supplyState.block ≤ s.blockNumber
    · exact hle
    · simp [hle] at h
  refine ⟨hle, ?_⟩
  have e := upd_supply_eq s hle
  rw [h] at e
  cases e
  rfl

theorem upd_borrow_some (s : St) (s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧ s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hle : s.borrowState.block ≤ s.blockNumber := by
    unfold updateCompBorrowIndex subChecked at h
    by_cases hle : s.borrowState.block ≤ s.blockNumber
    · exact hle
    · simp [hle] at h
  refine ⟨hle, ?_⟩
  have e := upd_borrow_eq s hle
  rw [h] at e
  cases e
  rfl

theorem dist_supply_some (s : St) (who : Account) (s' : St) (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧ s' = { s with accts := s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct) } := by
  have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
    unfold distributeSupplierComp subChecked at h
    simp only at h
    rw [supplierStart_eq s who] at h
    by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
    · exact hle
    · simp [hle] at h
  refine ⟨hle, ?_⟩
  unfold distributeSupplierComp subChecked St.withAcct at h
  simp only at h
  rw [supplierStart_eq s who, if_pos hle] at h
  simp only at h
  cases h
  congr 1
  apply modify_congr_eq
  rfl

theorem dist_borrow_some (s : St) (who : Account) (s' : St) (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧ s' = { s with accts := s.accts.modify who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct) } := by
  have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
    unfold distributeBorrowerComp subChecked at h
    simp only at h
    rw [borrowerStart_eq s who] at h
    by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
    · exact hle
    · simp [hle] at h
  refine ⟨hle, ?_⟩
  unfold distributeBorrowerComp subChecked St.withAcct at h
  simp only at h
  rw [borrowerStart_eq s who, if_pos hle] at h
  simp only at h
  cases h
  congr 1
  apply modify_congr_eq
  rfl

theorem setSupply_some (s : St) (a : Nat) (s1 : St) (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧ s1 = (if s.supplyState.speed = a then s else { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h ⊢
    cases h
    rfl
  · simp [heq] at h ⊢
    cases hup : updateCompSupplyIndex s with
    | none => simp [hup] at h
    | some mid =>
      simp [hup] at h
      obtain ⟨hle, hmid⟩ := upd_supply_some s mid hup
      refine ⟨hle, ?_⟩
      cases h
      rw [hmid]

theorem setBorrow_some (s : St) (b : Nat) (s1 : St) (h : setBorrowSpeed s b = some s1) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧ s1 = (if s.borrowState.speed = b then s else { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h ⊢
    cases h
    rfl
  · simp [heq] at h ⊢
    cases hup : updateCompBorrowIndex s with
    | none => simp [hup] at h
    | some mid =>
      simp [hup] at h
      obtain ⟨hle, hmid⟩ := upd_borrow_some s mid hup
      refine ⟨hle, ?_⟩
      cases h
      rw [hmid]

theorem dist_supply_eq_of (s : St) (who : Account)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some { s with accts := s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct) } := by
  unfold distributeSupplierComp subChecked mulDouble creditFor St.withAcct
  simp only
  rw [supplierStart_eq s who, if_pos hle]
  simp only
  congr 1
  congr 1
  apply modify_congr_eq
  rfl

theorem dist_borrow_eq_of (s : St) (who : Account)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some { s with accts := s.accts.modify who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct) } := by
  unfold distributeBorrowerComp subChecked mulDouble creditFor St.withAcct
  simp only
  rw [borrowerStart_eq s who, if_pos hle]
  simp only
  congr 1
  congr 1
  apply modify_congr_eq
  rfl

theorem accrue_mono_supply (s : St) :
    s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp only [hc]
    exact Nat.le_add_right _ _
  · simp only [hc]
    exact Nat.le_refl _

theorem accrue_mono_borrow (s : St) :
    s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp only [hc]
    exact Nat.le_add_right _ _
  · simp only [hc]
    exact Nat.le_refl _

theorem modify_getD_supplierIndex (l : List Acct) (who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify who f).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex := by
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases h : who < l.length
  · simp [h, hf]
  · simp [h]

theorem modify_getD_borrowerIndex (l : List Acct) (who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((l.modify who f).getD who noAcct).borrowerIndex = (l.getD who noAcct).borrowerIndex := by
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases h : who < l.length
  · simp [h, hf]
  · simp [h]

theorem setSupply_eq_of (s : St) (a : Nat) (h : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) :
    setSupplySpeed s a = some (if s.supplyState.speed = a then s else { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed = a
  · simp [heq]
  · simp [heq, upd_supply_eq s (h heq)]

theorem setBorrow_eq_of (s : St) (b : Nat) (h : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :
    setBorrowSpeed s b = some (if s.borrowState.speed = b then s else { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) := by
  unfold setBorrowSpeed
  by_cases heq : s.borrowState.speed = b
  · simp [heq]
  · simp [heq, upd_borrow_eq s (h heq)]

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  obtain ⟨hsb, hbb, hrec⟩ := hc
  have hrecS : ∀ who, (s.acct who).supplierIndex ≤ s.supplyState.index := by
    intro who
    unfold St.acct
    rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
    · exact (hrec _ hm).1
    · rw [hm]; exact Nat.zero_le _
  have hrecB : ∀ who, (s.acct who).borrowerIndex ≤ s.borrowState.index := by
    intro who
    unfold St.acct
    rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
    · exact (hrec _ hm).2
    · rw [hm]; exact Nat.zero_le _
  cases c with
  | supplyHook who =>
    have hrecS' : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      Nat.le_trans (hrecS who) (accrue_mono_supply s)
    have e1 : updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
      upd_supply_eq s hsb
    have hle : accrualStart ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who)).supplierIndex ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) :=
      accrualStart_le _ _ hrecS'
    have e2 := dist_supply_eq_of ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) who hle
    unfold comptroller
    simp [e1, e2]
  | borrowHook who =>
    have hrecB' : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans (hrecB who) (accrue_mono_borrow s)
    have e1 : updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
      upd_borrow_eq s hbb
    have hle : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who)).borrowerIndex ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) :=
      accrualStart_le _ _ hrecB'
    have e2 := dist_borrow_eq_of ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who hle
    unfold comptroller
    simp [e1, e2]
  | claim who =>
    unfold comptroller claimComp
    cases hb : updateCompBorrowIndex s with
    | none =>
      have e := upd_borrow_eq s hbb
      rw [hb] at e
      cases e
    | some b1 =>
      cases hm1 : distributeBorrowerComp b1 who with
      | none =>
        obtain ⟨_, hb1eq⟩ := upd_borrow_some s b1 hb
        have hle : (b1.acct who).borrowerIndex ≤ b1.borrowState.index := by
          rw [hb1eq]
          exact Nat.le_trans (hrecB who) (accrue_mono_borrow s)
        have e := dist_borrow_eq_of b1 who (accrualStart_le _ _ hle)
        rw [hm1] at e
        cases e
      | some m1 =>
        cases hu : updateCompSupplyIndex m1 with
        | none =>
          obtain ⟨_, hb1eq⟩ := upd_borrow_some s b1 hb
          obtain ⟨_, hm1eq⟩ := dist_borrow_some b1 who m1 hm1
          have hblock : m1.supplyState.block ≤ m1.blockNumber := by
            rw [hm1eq, hb1eq]
            exact hsb
          have e := upd_supply_eq m1 hblock
          rw [hu] at e
          cases e
        | some u1 =>
          cases hm2 : distributeSupplierComp u1 who with
          | none =>
            obtain ⟨_, hb1eq⟩ := upd_borrow_some s b1 hb
            obtain ⟨_, hm1eq⟩ := dist_borrow_some b1 who m1 hm1
            obtain ⟨_, hueq⟩ := upd_supply_some m1 u1 hu
            have epresM : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by
              have h1 : (m1.acct who).supplierIndex = (b1.acct who).supplierIndex := by
                rw [hm1eq]
                show ((((b1.accts.modify who fun a => ({ a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index } : Acct))).getD who noAcct)).supplierIndex = (((b1.accts).getD who noAcct).supplierIndex)
                exact modify_getD_supplierIndex _ _ _ (fun a => rfl)
              have h2 : (b1.acct who).supplierIndex = (s.acct who).supplierIndex := by
                rw [hb1eq]
                rfl
              exact h1.trans h2
            have hrecU : (u1.acct who).supplierIndex ≤ u1.supplyState.index := by
              have h1 : (m1.acct who).supplierIndex ≤ m1.supplyState.index := by
                rw [epresM, hm1eq, hb1eq]
                exact hrecS who
              rw [hueq]
              exact Nat.le_trans h1 (accrue_mono_supply m1)
            have e := dist_supply_eq_of u1 who (accrualStart_le _ _ hrecU)
            rw [hm2] at e
            cases e
          | some m2 =>
            simp [hb, hm1, hu, hm2]
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal
    cases h1 : setSupplySpeed s a with
    | none =>
      have e := setSupply_eq_of s a (fun _ => hsb)
      rw [h1] at e
      cases e
    | some mid =>
      cases h2 : setBorrowSpeed mid b with
      | none =>
        obtain ⟨_, e1eq⟩ := setSupply_some s a mid h1
        have hblock : mid.borrowState.block ≤ mid.blockNumber := by
          rw [e1eq]
          by_cases heqA : s.supplyState.speed = a
          · simp [heqA, hbb]
          · simp [heqA, hbb]
        have e := setBorrow_eq_of mid b (fun _ => hblock)
        rw [h2] at e
        cases e
      | some s2 =>
        simp [h1, h2]
theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' hs'
  unfold comptroller at hs'
  cases hup : updateCompSupplyIndex s with
  | none => simp [hup] at hs'
  | some s1 =>
    simp [hup] at hs'
    obtain ⟨hle_upd, hs1⟩ := upd_supply_some s s1 hup
    obtain ⟨hle_dist, hs2⟩ := dist_supply_some s1 who s' hs'
    subst hs1
    unfold SupplyDistributed
    exact ⟨hle_upd, hle_dist, hs2⟩

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' hs'
  unfold comptroller at hs'
  cases hup : updateCompBorrowIndex s with
  | none => simp [hup] at hs'
  | some s1 =>
    simp [hup] at hs'
    obtain ⟨hle_upd, hs1⟩ := upd_borrow_some s s1 hup
    obtain ⟨hle_dist, hs2⟩ := dist_borrow_some s1 who s' hs'
    subst hs1
    unfold BorrowDistributed
    exact ⟨hle_upd, hle_dist, hs2⟩

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' hs'
  unfold comptroller claimComp at hs'
  cases hb : updateCompBorrowIndex s with
  | none => simp [hb] at hs'
  | some b1 =>
    simp [hb] at hs'
    cases hm1 : distributeBorrowerComp b1 who with
    | none => simp [hm1] at hs'
    | some m1 =>
      simp [hm1] at hs'
      cases hu : updateCompSupplyIndex m1 with
      | none => simp [hu] at hs'
      | some u1 =>
        simp [hu] at hs'
        cases hm2 : distributeSupplierComp u1 who with
        | none => simp [hm2] at hs'
        | some m2 =>
          simp [hm2] at hs'
          obtain ⟨hbb, hb1⟩ := upd_borrow_some s b1 hb
          obtain ⟨hmb, hm1'⟩ := dist_borrow_some b1 who m1 hm1
          obtain ⟨hub, hu1⟩ := upd_supply_some m1 u1 hu
          obtain ⟨hum, hm2'⟩ := dist_supply_some u1 who m2 hm2
          subst hb1
          subst hu1
          refine ⟨m1, m2, ?_, ?_, ?_⟩
          · unfold BorrowDistributed
            exact ⟨hbb, hmb, hm1'⟩
          · unfold SupplyDistributed
            exact ⟨hub, hum, hm2'⟩
          · cases hs'
            exact grant_eq _ _

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' hs'
  unfold comptroller setCompSpeedInternal at hs'
  cases h1 : setSupplySpeed s a with
  | none => simp [h1] at hs'
  | some mid =>
    simp [h1] at hs'
    cases h2 : setBorrowSpeed mid b with
    | none => simp [h2] at hs'
    | some s'' =>
      simp [h2] at hs'
      cases hs'
      obtain ⟨c1, e1⟩ := setSupply_some s a mid h1
      obtain ⟨c2, e2⟩ := setBorrow_some mid b s' h2
      unfold SpeedsSet
      by_cases heqA : s.supplyState.speed = a
      · have e1' : mid = s := by simp [heqA] at e1; exact e1
        rw [e1'] at c2 e2
        by_cases heqB : s.borrowState.speed = b
        · refine ⟨fun h => absurd heqA h, fun h => absurd heqB h, ?_⟩
          simp [heqA, heqB] at e2 ⊢
          rw [e2]
        · refine ⟨fun h => absurd heqA h, c2, ?_⟩
          simp [heqA, heqB] at e2 ⊢
          rw [e2]
      · have e1' : mid = { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
          simp [heqA] at e1
          exact e1
        rw [e1'] at c2
        simp only at c2
        have htb : totalBorrows mid = totalBorrows s := by
          have h2' : totalBorrows mid = totalBorrows { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := congrArg totalBorrows e1'
          exact h2'
        by_cases heqB : s.borrowState.speed = b
        · refine ⟨c1, fun h => absurd heqB h, ?_⟩
          rw [htb, e1'] at e2
          simp [heqA, heqB] at e2 ⊢
          exact e2
        · refine ⟨c1, c2, ?_⟩
          rw [htb, e1'] at e2
          simp [heqA, heqB] at e2 ⊢
          exact e2
/-- Pending supply rewards of an account at state `s`, at index scale. -/
def pendS (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)

/-- Pending borrow rewards of an account at state `s`, at index scale. -/
def pendB (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

/-- COMP emitted on the supply side and not yet in the index. -/
def unindexedS (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- COMP emitted on the borrow side and not yet in the index. -/
def unindexedB (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- Potential term of an account: credited COMP at index scale plus pending rewards. -/
def potTerm (s : St) (a : Acct) : Nat :=
  (a.accrued + a.wallet) * doubleScale + pendS s a + pendB s a

/-- Global potential: every account's term plus the scaled unindexed emission. -/
def pot (s : St) : Nat :=
  (s.accts.map (potTerm s)).sum + doubleScale * (unindexedS s + unindexedB s)

/-- Per-account potential: its term plus the scaled unindexed emission while it holds a position. -/
def potTo (s : St) (who : Account) : Nat :=
  potTerm s (s.acct who) + doubleScale * ((if 0 < (s.acct who).supply then unindexedS s else 0) + (if 0 < (s.acct who).borrow then unindexedB s else 0))

/-- The ghost speeds match the state's speeds and no side's block lies ahead. -/
def Inv (g : Nat × Nat) (s : St) : Prop :=
  s.supplyState.speed = g.1 ∧ s.borrowState.speed = g.2 ∧
    s.supplyState.block ≤ s.blockNumber ∧ s.borrowState.block ≤ s.blockNumber

theorem accrualStart_self (i : Nat) : accrualStart i i = i := by
  unfold accrualStart
  by_cases hr : i = 0
  · subst hr
    have hni : ¬ compInitialIndex ≤ 0 := by unfold compInitialIndex; omega
    simp [hni]
  · simp [hr]

theorem accrualStart_mono (rec : Nat) {i i' : Nat} (h : i ≤ i') :
    accrualStart rec i ≤ accrualStart rec i' := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ i
    · have hi' : compInitialIndex ≤ i' := Nat.le_trans hi h
      simp [hi, hi']
    · simp [hi]
  · simp [hr]

theorem accrueSide_block (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrueSide_index_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hc]
  · simp [hc]

theorem supplyDist_pot (s : St) (who : Account) (s' : St) (h : SupplyDistributed s who s') :
    pot s' ≤ pot s := by
  obtain ⟨hB, hS, hs'eq⟩ := h
  rw [hs'eq]
  unfold pot
  have hU0 : unindexedS { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } = 0 := by
    show (s.blockNumber - (accrueSide s.supplyState s.blockNumber (totalSupply s)).block) * (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = 0
    rw [accrueSide_block]
    simp
  rw [hU0]
  have hlib := ProofForgeFin.Accumulator.pot_accrue_settle_le
    (l := s.accts) (w := who)
    (f := fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index })
    (d := noAcct)
    (t := fun iS a => (a.accrued + a.wallet) * doubleScale + a.supply * (iS - accrualStart a.supplierIndex iS) + a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index))
    (units := fun a => a.supply)
    (i := s.supplyState.index) (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
    (U' := 0 + unindexedB s) (U := unindexedS s + unindexedB s)
    (one := doubleScale)
    (ht := by
      intro a ha
      have hmono := accrualStart_mono a.supplierIndex (accrue_mono_supply s)
      have h := ProofForgeFin.Accumulator.owed_le_add (u := a.supply) (i := s.supplyState.index) (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (s := accrualStart a.supplierIndex s.supplyState.index) (s' := accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) hmono
      omega)
    (hU := ProofForgeFin.Accumulator.accrue_budget (V := unindexedB s) (E := unindexedS s) (by
      have h := ProofForgeFin.Accumulator.covered_catchUp doubleScale s.supplyState.index s.supplyState.block s.supplyState.speed s.blockNumber (totalSupply s)
      rw [← accrueSide_index_eq] at h
      exact h))
    (hf := by
      intro hlen
      simp only []
      unfold creditFor
      rw [accrualStart_self]
      simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      have hset := ProofForgeFin.Accumulator.settle_scaled_le (one := doubleScale) (c := (s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) (u := (s.accts.getD who noAcct).supply) (i := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (q := accrualStart (s.accts.getD who noAcct).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (q' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (Nat.le_refl _)
      simp only [Nat.sub_self, Nat.mul_zero] at hset
      have hbridge : ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - accrualStart (s.accts.getD who noAcct).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale) + (s.accts.getD who noAcct).wallet = (((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) + (s.accts.getD who noAcct).supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - accrualStart (s.accts.getD who noAcct).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale) := by omega
      rw [hbridge]
      omega)
  exact hlib

theorem borrowDist_pot (s : St) (who : Account) (s' : St) (h : BorrowDistributed s who s') :
    pot s' ≤ pot s := by
  obtain ⟨hB, hS, hs'eq⟩ := h
  rw [hs'eq]
  unfold pot
  have hU0 : unindexedB { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } = 0 := by
    show (s.blockNumber - (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block) * (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed = 0
    rw [accrueSide_block]
    simp
  rw [hU0]
  have hlib := ProofForgeFin.Accumulator.pot_accrue_settle_le
    (l := s.accts) (w := who)
    (f := fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index })
    (d := noAcct)
    (t := fun iB a => (a.accrued + a.wallet) * doubleScale + a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) + a.borrow * (iB - accrualStart a.borrowerIndex iB))
    (units := fun a => a.borrow)
    (i := s.borrowState.index) (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
    (U' := unindexedS s + 0) (U := unindexedS s + unindexedB s)
    (one := doubleScale)
    (ht := by
      intro a ha
      have hmono := accrualStart_mono a.borrowerIndex (accrue_mono_borrow s)
      have h := ProofForgeFin.Accumulator.owed_le_add (u := a.borrow) (i := s.borrowState.index) (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (s := accrualStart a.borrowerIndex s.borrowState.index) (s' := accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) hmono
      omega)
    (hU := ProofForgeFin.Accumulator.accrue_budget' (V := unindexedS s) (E := unindexedB s) (by
      have h := ProofForgeFin.Accumulator.covered_catchUp doubleScale s.borrowState.index s.borrowState.block s.borrowState.speed s.blockNumber (totalBorrows s)
      rw [← accrueSide_index_eq] at h
      exact h))
    (hf := by
      intro hlen
      simp only []
      unfold creditFor
      rw [accrualStart_self]
      simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      have hset := ProofForgeFin.Accumulator.settle_scaled_le (one := doubleScale) (c := (s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) (u := (s.accts.getD who noAcct).borrow) (i := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (q := accrualStart (s.accts.getD who noAcct).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (q' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (Nat.le_refl _)
      simp only [Nat.sub_self, Nat.mul_zero] at hset
      have hbridge : ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.accts.getD who noAcct).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale) + (s.accts.getD who noAcct).wallet = (((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) + (s.accts.getD who noAcct).borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.accts.getD who noAcct).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale) := by omega
      rw [hbridge]
      omega)
  exact hlib

theorem grant_pot (s : St) (who : Account) : pot (grant s who) = pot s := by
  unfold grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · rw [if_pos hc]
    have hsum : ((s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }).map (potTerm s)).sum = (s.accts.map (potTerm s)).sum := by
      apply ProofForgeFin.Ledger.sum_map_modify_eq
      intro hlen
      unfold potTerm pendS pendB
      simp only []
      have hcred : (0 + ((s.accts.getD who noAcct).wallet + (s.accts.getD who noAcct).accrued)) = ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) := by omega
      rw [hcred]
    have hP : pot { s with reserve := s.reserve - (s.acct who).accrued, accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } = ((s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }).map (potTerm s)).sum + doubleScale * (unindexedS s + unindexedB s) := rfl
    rw [hP, hsum]
    rfl
  · rw [if_neg hc]

theorem claimed_pot (s : St) (who : Account) (s' : St) (h : Claimed s who s') :
    pot s' ≤ pot s := by
  obtain ⟨m1, m2, hB, hS, hs'eq⟩ := h
  rw [hs'eq, grant_pot]
  exact Nat.le_trans (supplyDist_pot _ _ _ hS) (borrowDist_pot _ _ _ hB)

theorem supplyAccrue_pot (s : St) :
    pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ pot s := by
  unfold pot
  have hU0 : unindexedS { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = 0 := by
    show (s.blockNumber - (accrueSide s.supplyState s.blockNumber (totalSupply s)).block) * (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = 0
    rw [accrueSide_block]
    simp
  rw [hU0]
  have hlib := ProofForgeFin.Accumulator.pot_accrue_le
    (l := s.accts)
    (t := fun iS a => (a.accrued + a.wallet) * doubleScale + a.supply * (iS - accrualStart a.supplierIndex iS) + a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index))
    (units := fun a => a.supply)
    (i := s.supplyState.index) (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
    (U' := 0 + unindexedB s) (U := unindexedS s + unindexedB s)
    (one := doubleScale)
    (ht := by
      intro a ha
      have hmono := accrualStart_mono a.supplierIndex (accrue_mono_supply s)
      have h := ProofForgeFin.Accumulator.owed_le_add (u := a.supply) (i := s.supplyState.index) (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (s := accrualStart a.supplierIndex s.supplyState.index) (s' := accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) hmono
      omega)
    (hU := ProofForgeFin.Accumulator.accrue_budget (V := unindexedB s) (E := unindexedS s) (by
      have h := ProofForgeFin.Accumulator.covered_catchUp doubleScale s.supplyState.index s.supplyState.block s.supplyState.speed s.blockNumber (totalSupply s)
      rw [← accrueSide_index_eq] at h
      exact h))
  exact hlib

theorem borrowAccrue_pot (s : St) :
    pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤ pot s := by
  unfold pot
  have hU0 : unindexedB { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = 0 := by
    show (s.blockNumber - (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block) * (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed = 0
    rw [accrueSide_block]
    simp
  rw [hU0]
  have hlib := ProofForgeFin.Accumulator.pot_accrue_le
    (l := s.accts)
    (t := fun iB a => (a.accrued + a.wallet) * doubleScale + a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) + a.borrow * (iB - accrualStart a.borrowerIndex iB))
    (units := fun a => a.borrow)
    (i := s.borrowState.index) (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
    (U' := unindexedS s + 0) (U := unindexedS s + unindexedB s)
    (one := doubleScale)
    (ht := by
      intro a ha
      have hmono := accrualStart_mono a.borrowerIndex (accrue_mono_borrow s)
      have h := ProofForgeFin.Accumulator.owed_le_add (u := a.borrow) (i := s.borrowState.index) (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (s := accrualStart a.borrowerIndex s.borrowState.index) (s' := accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) hmono
      omega)
    (hU := ProofForgeFin.Accumulator.accrue_budget' (V := unindexedS s) (E := unindexedB s) (by
      have h := ProofForgeFin.Accumulator.covered_catchUp doubleScale s.borrowState.index s.borrowState.block s.borrowState.speed s.blockNumber (totalBorrows s)
      rw [← accrueSide_index_eq] at h
      exact h))
  exact hlib

theorem supplyBranch_pot (s : St) (a : Nat) :
    pot { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) } ≤ pot s := by
  by_cases heq : s.supplyState.speed = a
  · simp [heq]
  · simp only [heq, ↓reduceIte]
    have eQ : pot { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } = pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      have z1 : unindexedS { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } = 0 := by
        show (s.blockNumber - (accrueSide s.supplyState s.blockNumber (totalSupply s)).block) * a = 0
        rw [accrueSide_block]
        simp
      have z0 : unindexedS { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = 0 := by
        show (s.blockNumber - (accrueSide s.supplyState s.blockNumber (totalSupply s)).block) * (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = 0
        rw [accrueSide_block]
        simp
      unfold pot
      rw [z1, z0]
      rfl
    rw [eQ]
    exact supplyAccrue_pot s

theorem borrowBranch_pot (s : St) (b : Nat) :
    pot { s with borrowState := (if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) } ≤ pot s := by
  by_cases heq : s.borrowState.speed = b
  · simp [heq]
  · simp only [heq, ↓reduceIte]
    have eQ : pot { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } = pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have z1 : unindexedB { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } = 0 := by
        show (s.blockNumber - (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block) * b = 0
        rw [accrueSide_block]
        simp
      have z0 : unindexedB { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = 0 := by
        show (s.blockNumber - (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block) * (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed = 0
        rw [accrueSide_block]
        simp
      unfold pot
      rw [z1, z0]
      rfl
    rw [eQ]
    exact borrowAccrue_pot s

theorem speedsSet_pot (s : St) (a b : Nat) (s' : St) (h : SpeedsSet s a b s') :
    pot s' ≤ pot s := by
  obtain ⟨_, _, hs'eq⟩ := h
  rw [hs'eq]
  have hmid : pot { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) } ≤ pot s :=
    supplyBranch_pot s a
  have hfin : pot { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }), borrowState := (if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) } ≤ pot { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) } :=
    borrowBranch_pot { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) } b
  exact Nat.le_trans hfin hmid

theorem accrueSide_noop {sd : Side} {now total : Nat} (h : sd.block = now) :
    accrueSide sd now total = { sd with block := now } := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · omega
  · simp [hc]

theorem pot_supply_add (s : St) (who x : Nat)
    (hset : (s.acct who).supplierIndex = s.supplyState.index) :
    pot (s.withAcct who fun a => { a with supply := a.supply + x }) = pot s := by
  have hset' : ((s.accts[who]?.getD noAcct).supplierIndex) = s.supplyState.index := hset
  have hst : accrualStart ((s.accts[who]?.getD noAcct).supplierIndex) s.supplyState.index = s.supplyState.index := by
    rw [hset']; exact accrualStart_self _
  have hsum : (((s.accts.modify who fun a => { a with supply := a.supply + x }).map (potTerm s))).sum = (s.accts.map (potTerm s)).sum := by
    apply ProofForgeFin.Ledger.sum_map_modify_eq (d := noAcct)
    intro _
    unfold potTerm pendS pendB
    simp [hst]
  have hP : pot (s.withAcct who fun a => { a with supply := a.supply + x }) = (((s.accts.modify who fun a => { a with supply := a.supply + x }).map (potTerm s))).sum + doubleScale * (unindexedS s + unindexedB s) := rfl
  unfold St.withAcct at hP ⊢
  rw [hP, hsum]
  rfl

theorem pot_supply_sub (s : St) (who x : Nat)
    (hset : (s.acct who).supplierIndex = s.supplyState.index) :
    pot (s.withAcct who fun a => { a with supply := a.supply - x }) = pot s := by
  have hset' : ((s.accts[who]?.getD noAcct).supplierIndex) = s.supplyState.index := hset
  have hst : accrualStart ((s.accts[who]?.getD noAcct).supplierIndex) s.supplyState.index = s.supplyState.index := by
    rw [hset']; exact accrualStart_self _
  have hsum : (((s.accts.modify who fun a => { a with supply := a.supply - x }).map (potTerm s))).sum = (s.accts.map (potTerm s)).sum := by
    apply ProofForgeFin.Ledger.sum_map_modify_eq (d := noAcct)
    intro _
    unfold potTerm pendS pendB
    simp [hst]
  have hP : pot (s.withAcct who fun a => { a with supply := a.supply - x }) = (((s.accts.modify who fun a => { a with supply := a.supply - x }).map (potTerm s))).sum + doubleScale * (unindexedS s + unindexedB s) := rfl
  unfold St.withAcct at hP ⊢
  rw [hP, hsum]
  rfl

theorem pot_borrow_add (s : St) (who x : Nat)
    (hset : (s.acct who).borrowerIndex = s.borrowState.index) :
    pot (s.withAcct who fun a => { a with borrow := a.borrow + x }) = pot s := by
  have hset' : ((s.accts[who]?.getD noAcct).borrowerIndex) = s.borrowState.index := hset
  have hst : accrualStart ((s.accts[who]?.getD noAcct).borrowerIndex) s.borrowState.index = s.borrowState.index := by
    rw [hset']; exact accrualStart_self _
  have hsum : (((s.accts.modify who fun a => { a with borrow := a.borrow + x }).map (potTerm s))).sum = (s.accts.map (potTerm s)).sum := by
    apply ProofForgeFin.Ledger.sum_map_modify_eq (d := noAcct)
    intro _
    unfold potTerm pendS pendB
    simp [hst]
  have hP : pot (s.withAcct who fun a => { a with borrow := a.borrow + x }) = (((s.accts.modify who fun a => { a with borrow := a.borrow + x }).map (potTerm s))).sum + doubleScale * (unindexedS s + unindexedB s) := rfl
  unfold St.withAcct at hP ⊢
  rw [hP, hsum]
  rfl

theorem pot_borrow_sub (s : St) (who x : Nat)
    (hset : (s.acct who).borrowerIndex = s.borrowState.index) :
    pot (s.withAcct who fun a => { a with borrow := a.borrow - x }) = pot s := by
  have hset' : ((s.accts[who]?.getD noAcct).borrowerIndex) = s.borrowState.index := hset
  have hst : accrualStart ((s.accts[who]?.getD noAcct).borrowerIndex) s.borrowState.index = s.borrowState.index := by
    rw [hset']; exact accrualStart_self _
  have hsum : (((s.accts.modify who fun a => { a with borrow := a.borrow - x }).map (potTerm s))).sum = (s.accts.map (potTerm s)).sum := by
    apply ProofForgeFin.Ledger.sum_map_modify_eq (d := noAcct)
    intro _
    unfold potTerm pendS pendB
    simp [hst]
  have hP : pot (s.withAcct who fun a => { a with borrow := a.borrow - x }) = (((s.accts.modify who fun a => { a with borrow := a.borrow - x }).map (potTerm s))).sum + doubleScale * (unindexedS s + unindexedB s) := rfl
  unfold St.withAcct at hP ⊢
  rw [hP, hsum]
  rfl

theorem pot_transfer_moves (s s₁ s₂ : St) (src dst x : Nat) (hne : src ≠ dst)
    (hlenS : src < s.accts.length) (hlenD : dst < s₁.accts.length)
    (h1 : SupplyDistributed s src s₁) (h2 : SupplyDistributed s₁ dst s₂) :
    pot ((s₂.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst fun a => { a with supply := a.supply + x }) = pot s₂ := by
  obtain ⟨_, _, hs1eq⟩ := h1
  obtain ⟨_, _, hs2eq⟩ := h2
  have hdst_ne_src : dst ≠ src := fun h => hne h.symm
  have hsrc1 : (s₁.acct src).supplierIndex = s₁.supplyState.index := by
    rw [hs1eq]
    show (((s.accts.modify src fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).getD src noAcct).supplierIndex) = ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlenS]
  have hblk1 : s₁.supplyState.block = s₁.blockNumber := by
    rw [hs1eq]
    show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber
    rw [accrueSide_block]
  have hnoop : (accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index = s₁.supplyState.index := by
    have h := accrueSide_noop (sd := s₁.supplyState) (total := totalSupply s₁) (h := hblk1)
    rw [h]
  have hsrc2 : (s₂.acct src).supplierIndex = s₂.supplyState.index := by
    have e1 : (s₂.acct src).supplierIndex = (s₁.acct src).supplierIndex := by
      rw [hs2eq]
      show (((s₁.accts.modify dst fun a => { a with supplierIndex := (accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index) (accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index }).getD src noAcct).supplierIndex) = (((s₁.accts).getD src noAcct).supplierIndex)
      rw [ProofForgeFin.Ledger.getD_modify_ne _ _ _ hdst_ne_src]
    have e2 : s₂.supplyState.index = s₁.supplyState.index := by
      rw [hs2eq]
      exact hnoop
    rw [e1]
    exact hsrc1.trans e2.symm
  have hsub : pot (s₂.withAcct src fun a => { a with supply := a.supply - x }) = pot s₂ := pot_supply_sub s₂ src x hsrc2
  have hdst3 : (((s₂.withAcct src fun a => { a with supply := a.supply - x }).acct dst).supplierIndex) = ((s₂.withAcct src fun a => { a with supply := a.supply - x }).supplyState.index) := by
    have e1 : (((s₂.withAcct src fun a => { a with supply := a.supply - x }).acct dst).supplierIndex) = ((s₂.acct dst).supplierIndex) := by
      unfold St.withAcct St.acct
      rw [ProofForgeFin.Ledger.getD_modify_ne _ _ _ hne]
    have e2 : (s₂.acct dst).supplierIndex = s₂.supplyState.index := by
      rw [hs2eq]
      show (((s₁.accts.modify dst fun a => { a with supplierIndex := (accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index) (accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index }).getD dst noAcct).supplierIndex) = ((accrueSide s₁.supplyState s₁.blockNumber (totalSupply s₁)).index)
      rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlenD]
    rw [e1]
    exact e2
  have hadd : pot ((s₂.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst fun a => { a with supply := a.supply + x }) = pot (s₂.withAcct src fun a => { a with supply := a.supply - x }) := pot_supply_add _ dst x hdst3
  rw [hadd, hsub]

theorem pot_advance (s : St) (k : Nat) (hsb : s.supplyState.block ≤ s.blockNumber) (hbb : s.borrowState.block ≤ s.blockNumber) :
    pot { s with blockNumber := s.blockNumber + k } = pot s + doubleScale * (k * s.supplyState.speed + k * s.borrowState.speed) := by
  have hU : unindexedS { s with blockNumber := s.blockNumber + k } = unindexedS s + k * s.supplyState.speed := by
    show (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed = (s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed
    rw [Nat.sub_add_comm hsb, Nat.add_mul]
  have hU2 : unindexedB { s with blockNumber := s.blockNumber + k } = unindexedB s + k * s.borrowState.speed := by
    show (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed = (s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed
    rw [Nat.sub_add_comm hbb, Nat.add_mul]
  have hsum : ((({ s with blockNumber := s.blockNumber + k }).accts.map (potTerm { s with blockNumber := s.blockNumber + k })).sum) = ((s.accts.map (potTerm s))).sum := by
    apply ProofForgeFin.Ledger.sum_map_congr
    intro a _
    rfl
  unfold pot
  rw [hsum, hU, hU2]
  simp only [Nat.mul_add]
  omega

theorem hpot_step (g : Nat × Nat) (s : St) (a : Op) (hg : Inv g s) :
    pot (exec comptroller s a) ≤ pot s + doubleScale * emittedBy g a := by
  obtain ⟨hgS, hgB, hsb, hbb⟩ := hg
  cases a with
  | mint who x =>
    unfold exec
    by_cases hlen : who < s.accts.length
    · cases hhook : comptroller s (.supplyHook who) with
      | none =>
        simp [hlen, hhook]
      | some s' =>
        simp [hlen, hhook]
        obtain ⟨hB, hS, hs'eq⟩ := req_supply_hook s who s' hhook
        have hle : pot s' ≤ pot s := supplyDist_pot s who s' ⟨hB, hS, hs'eq⟩
        have hset : (s'.acct who).supplierIndex = s'.supplyState.index := by
          rw [hs'eq]
          show ((s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).getD who noAcct).supplierIndex = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
          rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
        have hbal : pot (s'.withAcct who fun a => { a with supply := a.supply + x }) = pot s' := pot_supply_add s' who x hset
        rw [hbal]
        exact Nat.le_trans hle (Nat.le_add_right _ _)
    · simp [hlen]
  | redeem who x =>
    unfold exec
    by_cases hlen : who < s.accts.length
    · cases hhook : comptroller s (.supplyHook who) with
      | none =>
        simp [hlen, hhook]
      | some s' =>
        simp [hlen, hhook]
        by_cases hleX : x ≤ (s'.acct who).supply
        · simp [hleX]
          obtain ⟨hB, hS, hs'eq⟩ := req_supply_hook s who s' hhook
          have hle : pot s' ≤ pot s := supplyDist_pot s who s' ⟨hB, hS, hs'eq⟩
          have hset : (s'.acct who).supplierIndex = s'.supplyState.index := by
            rw [hs'eq]
            show ((s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).getD who noAcct).supplierIndex = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
            rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
          have hbal : pot (s'.withAcct who fun a => { a with supply := a.supply - x }) = pot s' := pot_supply_sub s' who x hset
          rw [hbal]
          exact Nat.le_trans hle (Nat.le_add_right _ _)
        · simp [hleX]
    · simp [hlen]
  | transfer src dst x =>
    unfold exec
    by_cases hg12 : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · have hlenS : src < s.accts.length := hg12.1
      have hlenD : dst < s.accts.length := hg12.2.1
      have hne : src ≠ dst := hg12.2.2
      cases hhook1 : comptroller s (.supplyHook src) with
      | none =>
        simp [hg12, hhook1]
      | some s1 =>
        simp [hg12, hhook1]
        cases hhook2 : comptroller s1 (.supplyHook dst) with
        | none =>
          simp [hhook2]
        | some s2 =>
          simp [hhook2]
          by_cases hleX : x ≤ (s2.acct src).supply
          · simp [hleX]
            obtain ⟨hB1, hS1, hs1eq⟩ := req_supply_hook s src s1 hhook1
            obtain ⟨hB2, hS2, hs2eq⟩ := req_supply_hook s1 dst s2 hhook2
            have h1 : SupplyDistributed s src s1 := ⟨hB1, hS1, hs1eq⟩
            have h2 : SupplyDistributed s1 dst s2 := ⟨hB2, hS2, hs2eq⟩
            have hlenD1 : dst < s1.accts.length := by
              rw [hs1eq]
              simp only []
              rw [List.length_modify]
              exact hlenD
            have hmove : pot ((s2.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst fun a => { a with supply := a.supply + x }) = pot s2 :=
              pot_transfer_moves s s1 s2 src dst x hne hlenS hlenD1 h1 h2
            have hle1 : pot s1 ≤ pot s := supplyDist_pot s src s1 h1
            have hle2 : pot s2 ≤ pot s1 := supplyDist_pot s1 dst s2 h2
            rw [hmove]
            exact Nat.le_trans (Nat.le_trans hle2 hle1) (Nat.le_add_right _ _)
          · simp [hleX]
    · simp [hg12]
  | borrow who x =>
    unfold exec
    by_cases hlen : who < s.accts.length
    · cases hhook : comptroller s (.borrowHook who) with
      | none =>
        simp [hlen, hhook]
      | some s' =>
        simp [hlen, hhook]
        obtain ⟨hB, hS, hs'eq⟩ := req_borrow_hook s who s' hhook
        have hle : pot s' ≤ pot s := borrowDist_pot s who s' ⟨hB, hS, hs'eq⟩
        have hset : (s'.acct who).borrowerIndex = s'.borrowState.index := by
          rw [hs'eq]
          show ((s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).getD who noAcct).borrowerIndex = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
          rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
        have hbal : pot (s'.withAcct who fun a => { a with borrow := a.borrow + x }) = pot s' := pot_borrow_add s' who x hset
        rw [hbal]
        exact Nat.le_trans hle (Nat.le_add_right _ _)
    · simp [hlen]
  | repay who x =>
    unfold exec
    by_cases hlen : who < s.accts.length
    · cases hhook : comptroller s (.borrowHook who) with
      | none =>
        simp [hlen, hhook]
      | some s' =>
        simp [hlen, hhook]
        by_cases hleX : x ≤ (s'.acct who).borrow
        · simp [hleX]
          obtain ⟨hB, hS, hs'eq⟩ := req_borrow_hook s who s' hhook
          have hle : pot s' ≤ pot s := borrowDist_pot s who s' ⟨hB, hS, hs'eq⟩
          have hset : (s'.acct who).borrowerIndex = s'.borrowState.index := by
            rw [hs'eq]
            show ((s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).getD who noAcct).borrowerIndex = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
            rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
          have hbal : pot (s'.withAcct who fun a => { a with borrow := a.borrow - x }) = pot s' := pot_borrow_sub s' who x hset
          rw [hbal]
          exact Nat.le_trans hle (Nat.le_add_right _ _)
        · simp [hleX]
    · simp [hlen]
  | claim who =>
    unfold exec
    cases hhook : comptroller s (.claim who) with
    | none =>
      simp [hhook]
    | some s' =>
      simp [hhook]
      obtain ⟨m1, m2, hB, hS, hs'eq⟩ := req_claim s who s' hhook
      have hle : pot s' ≤ pot s := claimed_pot s who s' ⟨m1, m2, hB, hS, hs'eq⟩
      exact Nat.le_trans hle (Nat.le_add_right _ _)
  | setSpeeds a b =>
    unfold exec
    cases hhook : comptroller s (.setSpeeds a b) with
    | none =>
      simp [hhook]
    | some s' =>
      simp [hhook]
      obtain ⟨c1, c2, hs'eq⟩ := req_set_speeds s a b s' hhook
      have hle : pot s' ≤ pot s := speedsSet_pot s a b s' ⟨c1, c2, hs'eq⟩
      exact Nat.le_trans hle (Nat.le_add_right _ _)
  | advance k =>
    have hPs' := pot_advance s k hsb hbb
    have hexec : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := by simp [exec]
    rw [hexec, hPs', hgS, hgB]
    have hmul : k * (g.1 + g.2) = k * g.1 + k * g.2 := Nat.mul_add _ _ _
    have hemit : emittedBy g (Op.advance k) = k * (g.1 + g.2) := rfl
    rw [hemit, hmul]
    exact Nat.le_refl _
  | drip x =>
    have hexec : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := by simp [exec]
    have hP : pot { s with reserve := s.reserve + x } = pot s := rfl
    rw [hexec, hP]
    exact Nat.le_add_right _ _

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
