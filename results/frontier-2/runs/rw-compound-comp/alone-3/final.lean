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

/-- `distributeSupplierComp(cToken, supplier)`: fixed so an account with no recorded
index starts at `compInitialIndex` once the market index has reached it (`>=`), never
credited for rewards emitted before rewards began. -/
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

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`: fixed as above. -/
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

/-- An account with no recorded index starts at `compInitialIndex` once reached. -/
theorem choice_supply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h1 : (s.acct who).supplierIndex = 0
  · by_cases h2 : compInitialIndex ≤ s.supplyState.index <;> simp [h1, h2]
  · simp [h1]

/-- Same for the borrow side. -/
theorem choice_borrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h1 : (s.acct who).borrowerIndex = 0
  · by_cases h2 : compInitialIndex ≤ s.borrowState.index <;> simp [h1, h2]
  · simp [h1]

/-- The recorded index is below the market index, so the start is below it. -/
theorem accrualStart_le_of_le (r idx : Nat) (h : r ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
    by_cases hc : compInitialIndex ≤ idx <;> simp [hc] <;> omega
  · simp [hr, h]

/-- `subChecked` succeeds exactly when the subtrahend is below. -/
theorem subChecked_some (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none (a b : Nat) (h : a < b) : subChecked a b = none := by
  unfold subChecked; simp [Nat.not_le.mpr h]

theorem accrueSide_self (sd : Side) (now total : Nat) (h : sd.block = now) :
    accrueSide sd now total = sd := by
  unfold accrueSide
  have hc : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total) := by omega
  simp [hc]
  cases sd <;> simp_all

/-- The supply update brings the side up to date. -/
theorem updateSupply_ok (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
  unfold updateCompSupplyIndex
  rw [subChecked_some _ _ h]
  by_cases h1 : s.blockNumber - s.supplyState.block > 0
  · unfold accrueSide fraction
    by_cases h2 : s.supplyState.speed > 0
    · by_cases h3 : totalSupply s > 0 <;> simp [h1, h2, h3]
    · simp [h1, h2]
  · have hblk : s.supplyState.block = s.blockNumber := by omega
    have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) = s.supplyState :=
      accrueSide_self _ _ _ hblk
    simp [h1, hacc]

/-- The borrow update brings the side up to date. -/
theorem updateBorrow_ok (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
  unfold updateCompBorrowIndex
  rw [subChecked_some _ _ h]
  by_cases h1 : s.blockNumber - s.borrowState.block > 0
  · unfold accrueSide fraction
    by_cases h2 : s.borrowState.speed > 0
    · by_cases h3 : totalBorrows s > 0 <;> simp [h1, h2, h3]
    · simp [h1, h2]
  · have hblk : s.borrowState.block = s.blockNumber := by omega
    have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) = s.borrowState :=
      accrueSide_self _ _ _ hblk
    simp [h1, hacc]

theorem updateSupply_fail (s : St) (h : s.blockNumber < s.supplyState.block) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  rw [subChecked_none _ _ h]

theorem updateBorrow_fail (s : St) (h : s.blockNumber < s.borrowState.block) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  rw [subChecked_none _ _ h]

/-- `modify` beyond the list does nothing. -/
theorem modify_oob : ∀ (l : List Acct) (who : Nat) (f : Acct → Acct),
    l.length ≤ who → l.modify who f = l
  | [], _, _, _ => by simp
  | _ :: xs, 0, _, h => by simp at h
  | x :: xs, who + 1, f, h => by
    simp at h
    simp
    apply modify_oob
    omega

/-- `modify` with functions agreeing at the index gives the same list. -/
theorem modify_congr_at : ∀ (l : List Acct) (who : Nat) (f g : Acct → Acct),
    f (l.getD who noAcct) = g (l.getD who noAcct) → l.modify who f = l.modify who g
  | [], _, _, _, _ => by simp
  | x :: xs, 0, _, _, h => by simp_all
  | x :: xs, who + 1, _, _, h => by simp_all; apply modify_congr_at; exact h

/-- Supply distribution credits the account for its supply. -/
theorem distSupply_ok (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some (s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }))) := by
  have hc := choice_supply_eq s who
  unfold distributeSupplierComp mulDouble creditFor subChecked
  simp [hc, h]
  unfold St.withAcct
  apply congrArg
  apply modify_congr_at
  simp [St.acct]

/-- Borrow distribution credits the account for its borrow. -/
theorem distBorrow_ok (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some (s.withAcct who (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }))) := by
  have hc := choice_borrow_eq s who
  unfold distributeBorrowerComp mulDouble creditFor subChecked
  simp [hc, h]
  unfold St.withAcct
  apply congrArg
  apply modify_congr_at
  simp [St.acct]

theorem distSupply_fail (s : St) (who : Account)
    (h : s.supplyState.index < accrualStart (s.acct who).supplierIndex s.supplyState.index) :
    distributeSupplierComp s who = none := by
  have hc := choice_supply_eq s who
  unfold distributeSupplierComp subChecked
  simp [hc, Nat.not_le.mpr h]

theorem distBorrow_fail (s : St) (who : Account)
    (h : s.borrowState.index < accrualStart (s.acct who).borrowerIndex s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  have hc := choice_borrow_eq s who
  unfold distributeBorrowerComp subChecked
  simp [hc, Nat.not_le.mpr h]

/-- Reading back the modified element when in bounds. -/
theorem getD_modify_same_of_lt (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : who < l.length) : (l.modify who f).getD who noAcct = f (l.getD who noAcct) := by
  induction l generalizing who with
  | nil => simp at h
  | cons x xs ih =>
    cases who with
    | zero => simp
    | succ n =>
      simp at h
      have hmod : (x :: xs).modify (n + 1) f = x :: xs.modify n f := by simp
      have hget1 : ((x :: xs.modify n f : List Acct)).getD (n + 1) noAcct =
        (xs.modify n f).getD n noAcct := by simp
      have hget2 : (x :: xs).getD (n + 1) noAcct = xs.getD n noAcct := by simp
      rw [hmod, hget1, hget2]
      exact ih _ h

/-- A borrow distribution preserves the supply record of the same account. -/
theorem borrowDist_pres_supplier (s : St) (who : Account) (idx : Nat) (delta : Nat) :
    (((s.accts.modify who fun a => ({ a with borrowerIndex := idx, accrued := a.accrued + delta } : Acct))).getD who noAcct).supplierIndex =
    (s.accts.getD who noAcct).supplierIndex := by
  by_cases h : s.accts.length ≤ who
  · have hoob : s.accts.modify who (fun a => ({ a with borrowerIndex := idx, accrued := a.accrued + delta } : Acct)) = s.accts :=
      modify_oob _ _ _ h
    simp [hoob]
  · have hlt : who < s.accts.length := Nat.lt_of_not_le h
    rw [getD_modify_same_of_lt _ _ _ hlt]

/-- A borrow distribution preserves supply balance. -/
theorem borrowDist_pres_supply (s : St) (who : Account) (idx : Nat) (delta : Nat) :
    (((s.accts.modify who fun a => ({ a with borrowerIndex := idx, accrued := a.accrued + delta } : Acct))).getD who noAcct).supply =
    (s.accts.getD who noAcct).supply := by
  by_cases h : s.accts.length ≤ who
  · have hoob : s.accts.modify who (fun a => ({ a with borrowerIndex := idx, accrued := a.accrued + delta } : Acct)) = s.accts :=
      modify_oob _ _ _ h
    simp [hoob]
  · have hlt : who < s.accts.length := Nat.lt_of_not_le h
    rw [getD_modify_same_of_lt _ _ _ hlt]

/-- Any update preserving supply preserves the supplier record of the same account. -/
theorem pres_supplierIndex (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify who f).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex := by
  by_cases hle : l.length ≤ who
  · have hoob : l.modify who f = l := modify_oob _ _ _ hle
    simp [hoob]
  · have hlt : who < l.length := Nat.lt_of_not_le hle
    rw [getD_modify_same_of_lt _ _ _ hlt, h]

/-- Similarly for supply balance. -/
theorem pres_supply (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).supply = a.supply) :
    ((l.modify who f).getD who noAcct).supply = (l.getD who noAcct).supply := by
  by_cases hle : l.length ≤ who
  · have hoob : l.modify who f = l := modify_oob _ _ _ hle
    simp [hoob]
  · have hlt : who < l.length := Nat.lt_of_not_le hle
    rw [getD_modify_same_of_lt _ _ _ hlt, h]

/-- Similarly for borrower index and borrow balance. -/
theorem pres_borrowerIndex (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((l.modify who f).getD who noAcct).borrowerIndex = (l.getD who noAcct).borrowerIndex := by
  by_cases hle : l.length ≤ who
  · have hoob : l.modify who f = l := modify_oob _ _ _ hle
    simp [hoob]
  · have hlt : who < l.length := Nat.lt_of_not_le hle
    rw [getD_modify_same_of_lt _ _ _ hlt, h]

theorem pres_borrow (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).borrow = a.borrow) :
    ((l.modify who f).getD who noAcct).borrow = (l.getD who noAcct).borrow := by
  by_cases hle : l.length ≤ who
  · have hoob : l.modify who f = l := modify_oob _ _ _ hle
    simp [hoob]
  · have hlt : who < l.length := Nat.lt_of_not_le hle
    rw [getD_modify_same_of_lt _ _ _ hlt, h]

/-- Total supply is unchanged when only indices and rewards change. -/
theorem totalSupply_withAcct (s : St) (who : Account) (f : Acct → Acct)
    (h : ∀ a, (f a).supply = a.supply) : totalSupply (s.withAcct who f) = totalSupply s := by
  unfold totalSupply St.withAcct
  induction s.accts generalizing who with
  | nil => simp
  | cons x xs ih =>
    cases who with
    | zero => simp [h]
    | succ n => simp [ih]

/-- Total borrows unchanged similarly. -/
theorem totalBorrows_withAcct (s : St) (who : Account) (f : Acct → Acct)
    (h : ∀ a, (f a).borrow = a.borrow) : totalBorrows (s.withAcct who f) = totalBorrows s := by
  unfold totalBorrows St.withAcct
  induction s.accts generalizing who with
  | nil => simp
  | cons x xs ih =>
    cases who with
    | zero => simp [h]
    | succ n => simp [ih]

/-- Grant pays out exactly as specified. -/
theorem grant_ok (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp [hc]
    apply modify_congr_at
    simp [St.acct]
  · simp [hc]

/-- Accrued indices never decrease. -/
theorem accrueSide_mono (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- After accruing with a valid block, the side is up to date. -/
theorem accrueSide_block (sd : Side) (now total : Nat) (h : sd.block ≤ now) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

/-- A consistent account record is below the updated index. -/
theorem recorded_le_accrue (r : Nat) (sd : Side) (now total : Nat) (h1 : r ≤ sd.index)
    (h2 : sd.block ≤ now) : accrualStart r (accrueSide sd now total).index ≤
    (accrueSide sd now total).index := by
  apply accrualStart_le_of_le
  exact Nat.le_trans h1 (accrueSide_mono sd now total)

/-- Supply branch of speed change. -/
theorem setSupply_ok (s : St) (sup : Nat) (s' : St)
    (h : setSupplySpeed s sup = some s') :
    (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    s' = (if s.supplyState.speed = sup then s else
      ({ s with supplyState :=
        { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } : St)) := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = sup
  · simp [heq] at h
    cases h
    exact ⟨fun hne => absurd heq hne, by simp [heq]⟩
  · simp [heq] at h
    by_cases hblk : s.supplyState.block ≤ s.blockNumber
    · rw [updateSupply_ok s hblk] at h
      simp at h
      cases h
      exact ⟨fun _ => hblk, by simp [heq]⟩
    · have hlt := Nat.lt_of_not_le hblk
      rw [updateSupply_fail s hlt] at h
      simp at h

/-- Borrow branch of speed change. -/
theorem setBorrow_ok (s : St) (bor : Nat) (s' : St)
    (h : setBorrowSpeed s bor = some s') :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    s' = (if s.borrowState.speed = bor then s else
      ({ s with borrowState :=
        { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } : St)) := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = bor
  · simp [heq] at h
    cases h
    exact ⟨fun hne => absurd heq hne, by simp [heq]⟩
  · simp [heq] at h
    by_cases hblk : s.borrowState.block ≤ s.blockNumber
    · rw [updateBorrow_ok s hblk] at h
      simp at h
      cases h
      exact ⟨fun _ => hblk, by simp [heq]⟩
    · have hlt := Nat.lt_of_not_le hblk
      rw [updateBorrow_fail s hlt] at h
      simp at h

/-- Claim meets its specification. -/
theorem claim_ok (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') : Claimed s who s' := by
  have hcomp : claimComp s who =
    ((updateCompBorrowIndex s).bind fun s1 =>
      (distributeBorrowerComp s1 who).bind fun s2 =>
        (updateCompSupplyIndex s2).bind fun s3 =>
          (distributeSupplierComp s3 who).bind fun s4 =>
            some (grantCompInternal s4 who)) := rfl
  rw [hcomp] at h
  cases hb1 : updateCompBorrowIndex s with
  | none => simp [hb1] at h
  | some s1 =>
    simp [hb1] at h
    cases hd1 : distributeBorrowerComp s1 who with
    | none => simp [hd1] at h
    | some s2 =>
      simp [hd1] at h
      cases hs1 : updateCompSupplyIndex s2 with
      | none => simp [hs1] at h
      | some s3 =>
        simp [hs1] at h
        cases hd2 : distributeSupplierComp s3 who with
        | none => simp [hd2] at h
        | some s4 =>
          simp [hd2] at h
          have hbblk : s.borrowState.block ≤ s.blockNumber := by
            by_cases hb : s.borrowState.block ≤ s.blockNumber
            · exact hb
            · have hlt := Nat.lt_of_not_le hb
              rw [updateBorrow_fail s hlt] at hb1
              simp at hb1
          have hbstart : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤
              s1.borrowState.index := by
            by_cases hs : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤
                s1.borrowState.index
            · exact hs
            · have hlt := Nat.lt_of_not_le hs
              rw [distBorrow_fail s1 who hlt] at hd1
              simp at hd1
          have hsblk : s2.supplyState.block ≤ s2.blockNumber := by
            by_cases hb : s2.supplyState.block ≤ s2.blockNumber
            · exact hb
            · have hlt : s2.blockNumber < s2.supplyState.block := Nat.lt_of_not_le hb
              rw [updateSupply_fail s2 hlt] at hs1
              simp at hs1
          have hsstart : accrualStart (s3.acct who).supplierIndex s3.supplyState.index ≤
              s3.supplyState.index := by
            by_cases hs : accrualStart (s3.acct who).supplierIndex s3.supplyState.index ≤
                s3.supplyState.index
            · exact hs
            · have hlt := Nat.lt_of_not_le hs
              rw [distSupply_fail s3 who hlt] at hd2
              simp at hd2
          rw [updateBorrow_ok s hbblk] at hb1
          rw [distBorrow_ok s1 who hbstart] at hd1
          rw [updateSupply_ok s2 hsblk] at hs1
          rw [distSupply_ok s3 who hsstart] at hd2
          rw [grant_ok s4 who] at h
          cases hb1
          cases hd1
          cases hs1
          cases hd2
          cases h
          exact ⟨_, _, ⟨hbblk, hbstart, rfl⟩, ⟨hsblk, hsstart, rfl⟩, rfl⟩

/-- Set speeds meets its specification. -/
theorem setSpeeds_ok (s : St) (sup bor : Nat) (s' : St)
    (h : setCompSpeedInternal s sup bor = some s') : SpeedsSet s sup bor s' := by
  unfold setCompSpeedInternal setSupplySpeed setBorrowSpeed at h
  by_cases heq1 : s.supplyState.speed = sup
  · by_cases heq2 : s.borrowState.speed = bor
    · simp [heq1, heq2] at h
      cases h
      exact ⟨fun hne => absurd heq1 hne, fun hne => absurd heq2 hne, by simp [heq1, heq2]⟩
    · simp [heq1, heq2] at h
      cases hb : updateCompBorrowIndex s with
      | none => simp [hb] at h
      | some t =>
        simp [hb] at h
        cases h
        have hblk : s.borrowState.block ≤ s.blockNumber := by
          by_cases hb2 : s.borrowState.block ≤ s.blockNumber
          · exact hb2
          · have hlt := Nat.lt_of_not_le hb2
            rw [updateBorrow_fail s hlt] at hb
            simp at hb
        rw [updateBorrow_ok s hblk] at hb
        cases hb
        exact ⟨fun hne => absurd heq1 hne, fun _ => hblk, by simp [heq1, heq2]⟩
  · by_cases heq2 : s.borrowState.speed = bor
    · simp [heq1, heq2] at h
      cases hb : updateCompSupplyIndex s with
      | none => simp [hb] at h
      | some t =>
        simp [hb] at h
        cases h
        have hblk : s.supplyState.block ≤ s.blockNumber := by
          by_cases hb2 : s.supplyState.block ≤ s.blockNumber
          · exact hb2
          · have hlt := Nat.lt_of_not_le hb2
            rw [updateSupply_fail s hlt] at hb
            simp at hb
        rw [updateSupply_ok s hblk] at hb
        cases hb
        exact ⟨fun _ => hblk, fun hne => absurd heq2 hne, by simp [heq1, heq2]⟩
    · simp [heq1, heq2] at h
      cases hb1 : updateCompSupplyIndex s with
      | none => simp [hb1] at h
      | some t1 =>
        simp [hb1] at h
        cases hb2 : updateCompBorrowIndex t1 with
        | none => simp [hb2] at h
        | some t2 =>
          simp [hb2] at h
          cases h
          have hblk1 : s.supplyState.block ≤ s.blockNumber := by
            by_cases hb : s.supplyState.block ≤ s.blockNumber
            · exact hb
            · have hlt := Nat.lt_of_not_le hb
              rw [updateSupply_fail s hlt] at hb1
              simp at hb1
          have hblk2 : t1.borrowState.block ≤ t1.blockNumber := by
            by_cases hb : t1.borrowState.block ≤ t1.blockNumber
            · exact hb
            · have hlt : t1.blockNumber < t1.borrowState.block := Nat.lt_of_not_le hb
              rw [updateBorrow_fail t1 hlt] at hb2
              simp at hb2
          rw [updateSupply_ok s hblk1] at hb1
          cases hb1
          have hblk2' : s.borrowState.block ≤ s.blockNumber := hblk2
          rw [updateBorrow_ok _ hblk2'] at hb2
          cases hb2
          exact ⟨fun _ => hblk1, fun _ => hblk2', by rw [←h, if_neg heq1, if_neg heq2]⟩

/-- Supply hook meets its specification. -/
theorem hookSupply_ok (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') : SupplyDistributed s who s' := by
  have hcomp : comptroller s (.supplyHook who) =
    (updateCompSupplyIndex s).bind (fun s1 => distributeSupplierComp s1 who) := rfl
  rw [hcomp] at h
  cases hup : updateCompSupplyIndex s with
  | none => simp [hup] at h
  | some s1 =>
    simp [hup] at h
    by_cases hblk : s.supplyState.block ≤ s.blockNumber
    · by_cases hstart : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤
        s1.supplyState.index
      · rw [updateSupply_ok s hblk] at hup
        rw [distSupply_ok s1 who hstart] at h
        cases hup
        cases h
        exact ⟨hblk, hstart, rfl⟩
      · have hlt := Nat.lt_of_not_le hstart
        rw [distSupply_fail s1 who hlt] at h
        cases h
    · have hlt := Nat.lt_of_not_le hblk
      rw [updateSupply_fail s hlt] at hup
      cases hup

/-- Borrow hook meets its specification. -/
theorem hookBorrow_ok (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') : BorrowDistributed s who s' := by
  have hcomp : comptroller s (.borrowHook who) =
    (updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who) := rfl
  rw [hcomp] at h
  cases hup : updateCompBorrowIndex s with
  | none => simp [hup] at h
  | some s1 =>
    simp [hup] at h
    by_cases hblk : s.borrowState.block ≤ s.blockNumber
    · by_cases hstart : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤
        s1.borrowState.index
      · rw [updateBorrow_ok s hblk] at hup
        rw [distBorrow_ok s1 who hstart] at h
        cases hup
        cases h
        exact ⟨hblk, hstart, rfl⟩
      · have hlt := Nat.lt_of_not_le hstart
        rw [distBorrow_fail s1 who hlt] at h
        cases h
    · have hlt := Nat.lt_of_not_le hblk
      rw [updateBorrow_fail s hlt] at hup
      cases hup

theorem req_calls_succeed       : CallsSucceed comptroller := sorry
theorem req_supply_hook         : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook         : BorrowHookEffects comptroller := sorry
theorem req_claim               : ClaimEffects comptroller := sorry
theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
