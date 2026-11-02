import CompRewards.Spec
import ProofForgeFin
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

theorem modify_congr_hw (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  have hlen : (l.modify who f).length = (l.modify who g).length := by
    simp [List.length_modify]
  have hget : ∀ j : Nat, (l.modify who f).getD j noAcct = (l.modify who g).getD j noAcct := by
    intro j
    rw [ProofForgeFin.Ledger.getD_modify, ProofForgeFin.Ledger.getD_modify]
    by_cases hj : who = j ∧ j < l.length
    · simp only [hj, ↓reduceIte]
      have hjw : j = who := hj.1.symm
      subst hjw
      exact h
    · simp only [hj, ↓reduceIte]
  have e1 := ProofForgeFin.Sums.map_getD_range noAcct (l.modify who f)
  have e2 := ProofForgeFin.Sums.map_getD_range noAcct (l.modify who g)
  rw [hlen] at e1
  have emap : List.map (fun i => (l.modify who f).getD i noAcct) (List.range (l.modify who g).length) =
      List.map (fun i => (l.modify who g).getD i noAcct) (List.range (l.modify who g).length) := by
    apply List.map_congr_left
    intro i _hi
    exact hget i
  exact e1.symm.trans (emap.trans e2)

theorem supplierIndex_eq (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) =
      accrualStart rec idx := by
  unfold accrualStart
  by_cases h0 : rec = 0 <;> simp only [h0]
  · by_cases hi : compInitialIndex ≤ idx <;> simp [hi]
  · simp [h0]

theorem updSupply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked accrueSide totalSupply fraction
  simp only [h, ↓reduceIte]
  by_cases hd : 0 < s.blockNumber - s.supplyState.block
  · by_cases hr : 0 < s.supplyState.speed
    · by_cases ht : 0 < (s.accts.map Acct.supply).sum
      · simp only [hd, hr, ht]
        simp
      · simp only [hd, hr, ht]
        simp
    · by_cases ht : 0 < (s.accts.map Acct.supply).sum
      · simp only [hd, hr, ht]
        simp
      · simp only [hd, hr, ht]
        simp
  · have heq : s.blockNumber = s.supplyState.block := by omega
    by_cases hr : 0 < s.supplyState.speed
    · by_cases ht : 0 < (s.accts.map Acct.supply).sum
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]
    · by_cases ht : 0 < (s.accts.map Acct.supply).sum
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]

theorem updSupply_none (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex subChecked
  simp [h]

theorem updBorrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked accrueSide totalBorrows fraction
  simp only [h, ↓reduceIte]
  by_cases hd : 0 < s.blockNumber - s.borrowState.block
  · by_cases hr : 0 < s.borrowState.speed
    · by_cases ht : 0 < (s.accts.map Acct.borrow).sum
      · simp only [hd, hr, ht]
        simp
      · simp only [hd, hr, ht]
        simp
    · by_cases ht : 0 < (s.accts.map Acct.borrow).sum
      · simp only [hd, hr, ht]
        simp
      · simp only [hd, hr, ht]
        simp
  · have heq : s.blockNumber = s.borrowState.block := by omega
    by_cases hr : 0 < s.borrowState.speed
    · by_cases ht : 0 < (s.accts.map Acct.borrow).sum
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]
    · by_cases ht : 0 < (s.accts.map Acct.borrow).sum
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]
      · simp only [hd, hr, ht]
        simp [heq]
        cases s with | mk b sup bor r ac =>
          simp only at heq ⊢
          simp [heq]

theorem updBorrow_none (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex subChecked
  simp [h]

theorem distSupply_some (s : St) (who : Nat) (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) : distributeSupplierComp s who = some (s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct))) := by
  unfold distributeSupplierComp
  simp only [supplierIndex_eq]
  unfold subChecked
  simp only [hle, ↓reduceIte]
  have hfixed : mulDouble (s.accts.getD who noAcct).supply (s.supplyState.index - accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) = creditFor (s.accts.getD who noAcct).supply (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) s.supplyState.index := by
    unfold mulDouble creditFor
    rfl
  have hagree : (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).supply (s.supplyState.index - accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) } : Acct)) (s.accts.getD who noAcct) = (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) (s.accts.getD who noAcct) := by
    simp only [hfixed]
  have hmod := modify_congr_hw s.accts who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).supply (s.supplyState.index - accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) } : Acct)) (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) hagree
  simp only [St.withAcct, St.acct]
  rw [hmod]

theorem distSupply_none (s : St) (who : Nat) (hle : ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) : distributeSupplierComp s who = none := by
  unfold distributeSupplierComp
  simp only [supplierIndex_eq]
  unfold subChecked
  simp only [hle, ↓reduceIte]

theorem distBorrow_some (s : St) (who : Nat) (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) : distributeBorrowerComp s who = some (s.withAcct who (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct))) := by
  unfold distributeBorrowerComp
  simp only [supplierIndex_eq]
  unfold subChecked
  simp only [hle, ↓reduceIte]
  have hfixed : mulDouble (s.accts.getD who noAcct).borrow (s.borrowState.index - accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) = creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index := by
    unfold mulDouble creditFor
    rfl
  have hagree : (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).borrow (s.borrowState.index - accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) } : Acct)) (s.accts.getD who noAcct) = (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) (s.accts.getD who noAcct) := by
    simp only [hfixed]
  have hmod := modify_congr_hw s.accts who (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).borrow (s.borrowState.index - accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) } : Acct)) (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) hagree
  simp only [St.withAcct, St.acct]
  rw [hmod]

theorem distBorrow_none (s : St) (who : Nat) (hle : ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) : distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp
  simp only [supplierIndex_eq]
  unfold subChecked
  simp only [hle, ↓reduceIte]

theorem req_calls_succeed       : CallsSucceed comptroller := sorry
theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · rw [updSupply_eq s hb] at h
    simp at h
    have hacct : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex = (s.acct who).supplierIndex := by simp [St.acct]
    have hsup : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by simp
    by_cases hle : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    · have hle_s1 : accrualStart ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex) ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) := by rw [hacct, hsup]; exact hle
      rw [distSupply_some _ _ hle_s1] at h
      have hs' : s' = (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).withAcct who (fun a => ({ a with supplierIndex := ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)), accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index))) ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) } : Acct))) := by simpa [Option.some_inj] using h.symm
      refine ⟨hb, hle, ?_⟩
      rw [hs']
      cases s with | mk b sup bor r ac => rfl
    · have hle_s1 : ¬ accrualStart ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex) ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) := by rw [hacct, hsup]; exact hle
      rw [distSupply_none _ _ hle_s1] at h
      simp at h
  · rw [updSupply_none s hb] at h
    simp at h
theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · rw [updBorrow_eq s hb] at h
    simp at h
    have hacct : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex = (s.acct who).borrowerIndex := by simp [St.acct]
    have hsup : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp
    by_cases hle : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    · have hle_s1 : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) := by rw [hacct, hsup]; exact hle
      rw [distBorrow_some _ _ hle_s1] at h
      have hs' : s' = (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who (fun a => ({ a with borrowerIndex := ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index))) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) } : Acct))) := by simpa [Option.some_inj] using h.symm
      refine ⟨hb, hle, ?_⟩
      rw [hs']
      cases s with | mk b sup bor r ac => rfl
    · have hle_s1 : ¬ accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) := by rw [hacct, hsup]; exact hle
      rw [distBorrow_none _ _ hle_s1] at h
      simp at h
  · rw [updBorrow_none s hb] at h
    simp at h
theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [h, ↓reduceIte]
    have hagree : (fun a => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) (s.accts.getD who noAcct) = (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) (s.accts.getD who noAcct) := by simp [St.acct]
    have hmod := modify_congr_hw s.accts who (fun a => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) hagree
    cases s with | mk b sup bor r ac => simp [St.acct, St.withAcct] at h hmod ⊢; simp [h, hmod]
  · simp only [h, ↓reduceIte]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  by_cases hbb : s.borrowState.block ≤ s.blockNumber
  · rw [updBorrow_eq s hbb] at h
    simp at h
    generalize hsb : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)) = sb at h
    have hacct_b : (sb.acct who).borrowerIndex = (s.acct who).borrowerIndex := by simp [← hsb, St.acct]
    have hsup_b : sb.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [← hsb]
    by_cases hle_b : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    · have hle_b1 : accrualStart (sb.acct who).borrowerIndex sb.borrowState.index ≤ sb.borrowState.index := by rw [hacct_b, hsup_b]; exact hle_b
      rw [distBorrow_some _ _ hle_b1] at h
      simp at h
      generalize hm1 : ((sb.withAcct who (fun a => ({ a with borrowerIndex := sb.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex sb.borrowState.index) sb.borrowState.index } : Acct)))) = m1 at h
      have hm1_sup : m1.supplyState.block = s.supplyState.block := by rw [← hm1]; simp [← hsb, St.withAcct]
      have hm1_num : m1.blockNumber = s.blockNumber := by rw [← hm1]; simp [← hsb, St.withAcct]
      have hm1_bor : m1.borrowState.index = sb.borrowState.index := by rw [← hm1]; simp [St.withAcct]
      by_cases hsb2 : m1.supplyState.block ≤ m1.blockNumber
      · have hupd_s : updateCompSupplyIndex m1 = some ({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St) := updSupply_eq m1 hsb2
        rw [hupd_s] at h
        simp at h
        generalize hss : (({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St)) = ss at h
        have hss_acct : (ss.acct who).supplierIndex = (m1.acct who).supplierIndex := by simp [← hss, St.acct]
        have hss_idx : ss.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by simp [← hss]
        by_cases hle_s : accrualStart (m1.acct who).supplierIndex (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index
        · have hle_s1 : accrualStart (ss.acct who).supplierIndex ss.supplyState.index ≤ ss.supplyState.index := by rw [hss_acct, hss_idx]; exact hle_s
          rw [distSupply_some _ _ hle_s1] at h
          simp at h
          generalize hm2 : ((ss.withAcct who (fun a => ({ a with supplierIndex := ss.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex ss.supplyState.index) ss.supplyState.index } : Acct)))) = m2 at h
          rw [grant_eq] at h
          refine ⟨m1, m2, ?_, ?_, ?_⟩
          · refine ⟨hbb, hle_b, ?_⟩
            rw [← hm1, ← hsb]
            cases s with | mk b sup bor r ac => rfl
          · refine ⟨hsb2, hle_s, ?_⟩
            rw [← hm2, ← hss]
            cases m1 with | mk b sup bor r ac => rfl
          · exact h.symm
        · have hle_s1 : ¬ accrualStart (ss.acct who).supplierIndex ss.supplyState.index ≤ ss.supplyState.index := by rw [hss_acct, hss_idx]; exact hle_s
          rw [distSupply_none _ _ hle_s1] at h
          simp at h
      · have hnone : updateCompSupplyIndex m1 = none := updSupply_none m1 hsb2
        rw [hnone] at h
        simp at h
    · have hle_b1 : ¬ accrualStart (sb.acct who).borrowerIndex sb.borrowState.index ≤ sb.borrowState.index := by rw [hacct_b, hsup_b]; exact hle_b
      rw [distBorrow_none _ _ hle_b1] at h
      simp at h
  · rw [updBorrow_none s hbb] at h
    simp at h
theorem setSupply_some_eq (s : St) (a : Nat) (hne : s.supplyState.speed ≠ a) (hle : s.supplyState.block ≤ s.blockNumber) : setSupplySpeed s a = some ({ ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) with supplyState := ({ (accrueSide s.supplyState s.blockNumber (totalSupply s)) with speed := a } : Side) } : St) := by
  unfold setSupplySpeed
  simp [hne]
  rw [updSupply_eq s hle]
  simp

theorem setSupply_same (s : St) (a : Nat) (heq : s.supplyState.speed = a) : setSupplySpeed s a = some s := by
  unfold setSupplySpeed
  simp [heq]

theorem setBorrow_some_eq (s : St) (b : Nat) (hne : s.borrowState.speed ≠ b) (hle : s.borrowState.block ≤ s.blockNumber) : setBorrowSpeed s b = some ({ ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) with borrowState := ({ (accrueSide s.borrowState s.blockNumber (totalBorrows s)) with speed := b } : Side) } : St) := by
  unfold setBorrowSpeed
  simp [hne]
  rw [updBorrow_eq s hle]
  simp

theorem setBorrow_same (s : St) (b : Nat) (heq : s.borrowState.speed = b) : setBorrowSpeed s b = some s := by
  unfold setBorrowSpeed
  simp [heq]

theorem accrueSide_catchUp (sd : Side) (now total : Nat) : accrueSide sd now total = ({ sd with index := ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total, block := now } : Side) := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hc]
  · simp [hc]

theorem accrualStart_firstStart (rec idx : Nat) : accrualStart rec idx = ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex rec idx := by
  unfold accrualStart ProofForgeFin.DeFi.Rewards.firstStart
  by_cases h0 : rec = 0
  · simp [h0]
  · simp [h0]

theorem creditFor_credit (units start idx : Nat) : creditFor units start idx = ProofForgeFin.DeFi.Rewards.credit doubleScale units start idx := by
  unfold creditFor ProofForgeFin.DeFi.Rewards.credit
  rfl

def M : ProofForgeFin.Accumulator.Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock s := ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed, s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts s := s.accts
  dflt := noAcct
  units₁ := Acct.supply
  units₂ := Acct.borrow
  rec₁ := Acct.supplierIndex
  rec₂ := Acct.borrowerIndex
  credited a := a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

theorem req_set_speeds : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
