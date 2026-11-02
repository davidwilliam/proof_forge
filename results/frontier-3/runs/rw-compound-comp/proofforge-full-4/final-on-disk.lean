import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
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

theorem modify_congr_at {α : Type} (l : List α) (w : Nat) (f g : α → α) (d : α)
    (h : f (l.getD w d) = g (l.getD w d)) : l.modify w f = l.modify w g := by
  induction l generalizing w with
  | nil => simp
  | cons a l ih =>
    cases w with
    | zero => simp_all
    | succ w => simp_all [ih]

theorem start_supply_eq (rec index : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ index then compInitialIndex else rec) =
      accrualStart rec index := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr]

theorem start_borrow_eq (rec index : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ index then compInitialIndex else rec) =
      accrualStart rec index := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr]

theorem subChecked_some (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem upd_supply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hs : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := subChecked_some _ _ h
  unfold updateCompSupplyIndex accrueSide totalSupply fraction
  simp only [hs]
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [hd]
    by_cases ht : (s.accts.map Acct.supply).sum > 0
    · have hd3 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < (s.accts.map Acct.supply).sum := by omega
      simp only [hd3, ht]
      rfl
    · have hd3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < (s.accts.map Acct.supply).sum) := by omega
      simp only [hd3, ht]
      rfl
  · have hd3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < (s.accts.map Acct.supply).sum) := by omega
    simp only [hd, hd3]
    by_cases hdb : s.blockNumber - s.supplyState.block > 0
    · simp only [hdb]
      rfl
    · simp only [hdb]
      have hb : s.supplyState.block = s.blockNumber := by omega
      cases s with | mk bn sup bor res ac =>
        simp_all
        cases sup with | mk ix bl sp =>
          simp_all

theorem upd_supply_none (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  have hs : subChecked s.blockNumber s.supplyState.block = none :=
    subChecked_none _ _ h
  unfold updateCompSupplyIndex
  simp [hs]

theorem upd_borrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hs : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := subChecked_some _ _ h
  unfold updateCompBorrowIndex accrueSide totalBorrows fraction
  simp only [hs]
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [hd]
    by_cases ht : (s.accts.map Acct.borrow).sum > 0
    · have hd3 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < (s.accts.map Acct.borrow).sum := by omega
      simp only [hd3, ht]
      rfl
    · have hd3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < (s.accts.map Acct.borrow).sum) := by omega
      simp only [hd3, ht]
      rfl
  · have hd3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < (s.accts.map Acct.borrow).sum) := by omega
    simp only [hd, hd3]
    by_cases hdb : s.blockNumber - s.borrowState.block > 0
    · simp only [hdb]
      rfl
    · simp only [hdb]
      have hb : s.borrowState.block = s.blockNumber := by omega
      cases s with | mk bn sup bor res ac =>
        simp_all
        cases bor with | mk ix bl sp =>
          simp_all

theorem upd_borrow_none (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  have hs : subChecked s.blockNumber s.borrowState.block = none :=
    subChecked_none _ _ h
  unfold updateCompBorrowIndex
  simp [hs]

theorem subChecked_le_of_some (a b d : Nat) (h : subChecked a b = some d) : b ≤ a := by
  unfold subChecked at h
  by_cases hb : b ≤ a
  · exact hb
  · simp [hb] at h

theorem dist_supply_eq (s : St) (who : Nat)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := start_supply_eq _ _
  have hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := subChecked_some _ _ h
  unfold distributeSupplierComp
  simp only [hstart, hsub]
  have hmod : s.accts.modify who (fun (a : Acct) => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) = s.accts.modify who (fun (a : Acct) => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) := by
    apply modify_congr_at (d := noAcct)
    show ({ (s.acct who) with supplierIndex := s.supplyState.index, accrued := (s.acct who).accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct) = ({ (s.acct who) with supplierIndex := s.supplyState.index, accrued := (s.acct who).accrued + creditFor (s.acct who).supply (accrualStart (s.acct who).supplierIndex s.supplyState.index) s.supplyState.index } : Acct)
    rfl
  unfold St.withAcct
  rw [hmod]

theorem dist_supply_none (s : St) (who : Nat)
    (h : ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = none := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := start_supply_eq _ _
  have hsub : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = none := subChecked_none _ _ (by rw [hstart]; exact h)
  unfold distributeSupplierComp
  simp [hsub]

theorem dist_borrow_eq (s : St) (who : Nat)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := start_borrow_eq _ _
  have hsub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := subChecked_some _ _ h
  unfold distributeBorrowerComp
  simp only [hstart, hsub]
  have hmod : s.accts.modify who (fun (a : Acct) => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)) = s.accts.modify who (fun (a : Acct) => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) := by
    apply modify_congr_at (d := noAcct)
    show ({ (s.acct who) with borrowerIndex := s.borrowState.index, accrued := (s.acct who).accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct) = ({ (s.acct who) with borrowerIndex := s.borrowState.index, accrued := (s.acct who).accrued + creditFor (s.acct who).borrow (accrualStart (s.acct who).borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)
    rfl
  unfold St.withAcct
  rw [hmod]

theorem dist_borrow_none (s : St) (who : Nat)
    (h : ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := start_borrow_eq _ _
  have hsub : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = none := subChecked_none _ _ (by rw [hstart]; exact h)
  unfold distributeBorrowerComp
  simp [hsub]

theorem grant_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [h]
    have hmod : s.accts.modify who (fun (a : Acct) => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) = s.accts.modify who (fun (a : Acct) => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) := by
      apply modify_congr_at (d := noAcct)
      have hshow : ({ (s.acct who) with accrued := 0, wallet := (s.acct who).wallet + (s.acct who).accrued } : Acct) = ({ (s.acct who) with accrued := 0, wallet := (s.acct who).wallet + (s.acct who).accrued } : Acct) := rfl
      exact hshow
    simp [hmod]
  · simp [h]

theorem accrueSide_mono (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, Nat.le_add_right]
  · simp [h]

theorem accrualStart_le_new (rec oldIdx newIdx : Nat) (hrec : rec ≤ oldIdx) (hle : oldIdx ≤ newIdx) :
    accrualStart rec newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ newIdx
    · simp [hi]
    · simp [hi]
  · simp [hr]
    omega

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  obtain ⟨hsle, hble, hrec⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    have hmono := accrueSide_mono s.supplyState s.blockNumber (totalSupply s)
    have hwho : (s.acct who).supplierIndex ≤ s.supplyState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).1
      · rw [hm]; show (0 : Nat) ≤ _; omega
    have hle2 : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrualStart_le_new _ _ _ hwho hmono
    have hle2' : accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) ≤ (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) :=
      hle2
    simp [upd_supply_eq s hsle, dist_supply_eq _ _ hle2']
  | borrowHook who =>
    unfold comptroller
    have hwho : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).2
      · rw [hm]; show (0 : Nat) ≤ _; omega
    have hmono := accrueSide_mono s.borrowState s.blockNumber (totalBorrows s)
    have hle2 : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrualStart_le_new _ _ _ hwho hmono
    have hle2' : accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) ≤ (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) :=
      hle2
    simp [upd_borrow_eq s hble, dist_borrow_eq _ _ hle2']
  | claim who =>
    dsimp only [comptroller, claimComp]
    have hwho_s : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).2
      · rw [hm]; show (0 : Nat) ≤ _; omega
    have hmono_b := accrueSide_mono s.borrowState s.blockNumber (totalBorrows s)
    have hle_b : accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      show accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
      exact accrualStart_le_new _ _ _ hwho_s hmono_b
    have hsle_m1 : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).supplyState.block) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).blockNumber) := by
      show s.supplyState.block ≤ s.blockNumber
      exact hsle
    have hwho_sup : (s.acct who).supplierIndex ≤ s.supplyState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).1
      · rw [hm]
        show (0 : Nat) ≤ _
        omega
    have heq_sup : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).acct who).supplierIndex = (s.acct who).supplierIndex := by
      unfold St.acct St.withAcct
      simp [ProofForgeFin.Ledger.getD_modify]
      by_cases hw : who < s.accts.length
      · simp [hw]
      · simp [hw]
    have heq_st : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).supplyState.index) = s.supplyState.index := rfl
    have hwho_s2 : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).acct who).supplierIndex ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).supplyState.index) := by
      rw [heq_sup, heq_st]
      exact hwho_sup
    have hmono_s : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).supplyState.index) ≤ (accrueSide ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).supplyState) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).blockNumber) (totalSupply ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index })))).index :=
      accrueSide_mono _ _ _
    have hle_s : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).acct who).supplierIndex (accrueSide ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).supplyState) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).blockNumber) (totalSupply ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index })))).index ≤ (accrueSide ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).supplyState) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).blockNumber) (totalSupply ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index })))).index :=
      accrualStart_le_new _ _ _ hwho_s2 hmono_s
    simp [upd_borrow_eq s hble, dist_borrow_eq _ _ hle_b, upd_supply_eq _ hsle_m1, dist_supply_eq _ _ hle_s]
  | setSpeeds a b =>
    dsimp only [comptroller, setCompSpeedInternal, setSupplySpeed, setBorrowSpeed]
    by_cases hsa : s.supplyState.speed = a
    · have hna : ¬ s.supplyState.speed ≠ a := by simp [hsa]
      rw [if_neg hna]
      simp only [Option.bind_some]
      by_cases hba : s.borrowState.speed = b
      · have hnb : ¬ s.borrowState.speed ≠ b := by simp [hba]
        rw [if_neg hnb]
        simp
      · have hpos : s.borrowState.speed ≠ b := hba
        simp [hpos, upd_borrow_eq s hble]
    · have hpos : s.supplyState.speed ≠ a := hsa
      simp [hpos, upd_supply_eq s hsle]
      have hba_eq : (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.speed) = s.borrowState.speed := rfl
      by_cases hba : s.borrowState.speed = b
      · simp [hba_eq, hba]
      · have hpos2 : (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.speed ≠ b) := by simpa [hba_eq] using hba
        have hble2 : (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.block) ≤ (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).blockNumber) := by
          show s.borrowState.block ≤ s.blockNumber
          exact hble
        simp [hpos2, upd_borrow_eq _ hble2]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' hcomp
  unfold comptroller at hcomp
  cases hupd : updateCompSupplyIndex s with
  | none =>
    simp [hupd] at hcomp
  | some s1 =>
    simp [hupd] at hcomp
    have hle : s.supplyState.block ≤ s.blockNumber := by
      by_cases h : s.supplyState.block ≤ s.blockNumber
      · exact h
      · rw [upd_supply_none s h] at hupd
        contradiction
    have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      rw [upd_supply_eq s hle] at hupd
      exact (Option.some_inj.mp hupd).symm
    subst s1
    cases hsub : subChecked (accrueSide s.supplyState s.blockNumber (totalSupply s)).index (accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) with
    | none =>
      have hneg : ¬ accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        intro hle
        have hs := subChecked_some _ _ hle
        rw [hs] at hsub
        contradiction
      have hnone := dist_supply_none { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who hneg
      rw [hnone] at hcomp
      contradiction
    | some d =>
      have hle2 : accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
        subChecked_le_of_some _ _ _ hsub
      have hdist := dist_supply_eq { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who hle2
      rw [hdist] at hcomp
      have hs' : s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := (s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) } := by
        exact (Option.some_inj.mp hcomp).symm
      have hacct : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who) = s.acct who := rfl
      rw [hacct] at hle2
      exact ⟨hle, hle2, hs'⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' hcomp
  unfold comptroller at hcomp
  cases hupd : updateCompBorrowIndex s with
  | none =>
    simp [hupd] at hcomp
  | some s1 =>
    simp [hupd] at hcomp
    have hle : s.borrowState.block ≤ s.blockNumber := by
      by_cases h : s.borrowState.block ≤ s.blockNumber
      · exact h
      · rw [upd_borrow_none s h] at hupd
        contradiction
    have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      rw [upd_borrow_eq s hle] at hupd
      exact (Option.some_inj.mp hupd).symm
    subst s1
    cases hsub : subChecked (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index (accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) with
    | none =>
      have hneg : ¬ accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        intro hle
        have hs := subChecked_some _ _ hle
        rw [hs] at hsub
        contradiction
      have hnone := dist_borrow_none { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who hneg
      rw [hnone] at hcomp
      contradiction
    | some d =>
      have hle2 : accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
        subChecked_le_of_some _ _ _ hsub
      have hdist := dist_borrow_eq { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who hle2
      rw [hdist] at hcomp
      have hs' : s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := (s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) } := by
        exact (Option.some_inj.mp hcomp).symm
      have hacct : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who) = s.acct who := rfl
      rw [hacct] at hle2
      exact ⟨hle, hle2, hs'⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' hcomp
  unfold comptroller claimComp at hcomp
  cases h1 : updateCompBorrowIndex s with
  | none => simp [h1] at hcomp
  | some t1 =>
    simp [h1] at hcomp
    cases h2 : distributeBorrowerComp t1 who with
    | none => simp [h2] at hcomp
    | some m1 =>
      simp [h2] at hcomp
      cases h3 : updateCompSupplyIndex m1 with
      | none => simp [h3] at hcomp
      | some t2 =>
        simp [h3] at hcomp
        cases h4 : distributeSupplierComp t2 who with
        | none => simp [h4] at hcomp
        | some m2 =>
          simp [h4, grant_eq] at hcomp
          have hb1 : BorrowDistributed s who m1 := by
            have := req_borrow_hook (s := s) (who := who) (s' := m1)
            apply this
            unfold comptroller
            simp [h1, h2]
          have hsup : SupplyDistributed m1 who m2 := by
            have := req_supply_hook (s := m1) (who := who) (s' := m2)
            apply this
            unfold comptroller
            simp [h3, h4]
          exact ⟨m1, m2, hb1, hsup, hcomp.symm⟩

theorem setSupply_same (s : St) (a : Nat) (h : s.supplyState.speed = a) :
    setSupplySpeed s a = some s := by
  unfold setSupplySpeed
  have hna : ¬ s.supplyState.speed ≠ a := by simp [h]
  simp [hna]

theorem setSupply_new (s : St) (a : Nat) (hne : s.supplyState.speed ≠ a)
    (hle : s.supplyState.block ≤ s.blockNumber) :
    setSupplySpeed s a = some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed
  simp [hne, upd_supply_eq s hle]

theorem setSupply_none (s : St) (a : Nat) (hne : s.supplyState.speed ≠ a)
    (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    setSupplySpeed s a = none := by
  unfold setSupplySpeed
  simp [hne, upd_supply_none s h]

theorem setBorrow_same (s : St) (b : Nat) (h : s.borrowState.speed = b) :
    setBorrowSpeed s b = some s := by
  unfold setBorrowSpeed
  have hnb : ¬ s.borrowState.speed ≠ b := by simp [h]
  simp [hnb]

theorem setBorrow_new (s : St) (b : Nat) (hne : s.borrowState.speed ≠ b)
    (hle : s.borrowState.block ≤ s.blockNumber) :
    setBorrowSpeed s b = some { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed
  simp [hne, upd_borrow_eq s hle]

theorem setBorrow_none (s : St) (b : Nat) (hne : s.borrowState.speed ≠ b)
    (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    setBorrowSpeed s b = none := by
  unfold setBorrowSpeed
  simp [hne, upd_borrow_none s h]

theorem req_set_speeds_aux : SetSpeedsEffects comptroller := by
  intro s a b s' hcomp
  unfold comptroller setCompSpeedInternal at hcomp
  cases hss : setSupplySpeed s a with
  | none =>
    simp [hss] at hcomp
  | some t =>
    simp [hss] at hcomp
    cases hbs : setBorrowSpeed t b with
    | none =>
      simp [hbs] at hcomp
    | some u =>
      simp [hbs] at hcomp
      have hs' : u = s' := hcomp
      subst u
      by_cases hsa : s.supplyState.speed = a
      · have ht : t = s := by
          rw [setSupply_same s a hsa] at hss
          exact Option.some_inj.mp hss.symm
        subst t
        by_cases hba : s.borrowState.speed = b
        · have hu : s' = s := by
            rw [setBorrow_same s b hba] at hbs
            exact (Option.some_inj.mp hbs).symm
          subst s'
          refine ⟨?_, ?_, ?_⟩
          · intro h; contradiction
          · intro h; contradiction
          · simp [hsa, hba]
          done
        · have hpos : s.borrowState.speed ≠ b := hba
          have hble : s.borrowState.block ≤ s.blockNumber := by
            by_cases h : s.borrowState.block ≤ s.blockNumber
            · exact h
            · rw [setBorrow_none s b hpos h] at hbs
              contradiction
          have hu : s' = { s with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
            rw [setBorrow_new s b hpos hble] at hbs
            exact (Option.some_inj.mp hbs).symm
          refine ⟨?_, ?_, ?_⟩
          · intro h; contradiction
          · intro _; exact hble
          · simp [hsa, hpos]
            exact hu
          done
      · have hpos : s.supplyState.speed ≠ a := hsa
        have hle : s.supplyState.block ≤ s.blockNumber := by
          by_cases h : s.supplyState.block ≤ s.blockNumber
          · exact h
          · rw [setSupply_none s a hpos h] at hss
            contradiction
        have ht : t = { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
          rw [setSupply_new s a hpos hle] at hss
          exact Option.some_inj.mp hss.symm
        subst ht
        have hba_simp : (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.speed) = s.borrowState.speed := rfl
        by_cases hba : s.borrowState.speed = b
        · have hu : s' = { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
            have hsame : setBorrowSpeed { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b = some { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
              apply setBorrow_same
              simpa using hba
            rw [hsame] at hbs
            exact (Option.some_inj.mp hbs).symm
          subst s'
          refine ⟨?_, ?_, ?_⟩
          · intro _; exact hle
          · intro h; rw [hba] at h; contradiction
          · simp [hsa, hba]
        · have hpos2 : (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState.speed ≠ b) := by simpa using hba
          have hble : s.borrowState.block ≤ s.blockNumber := by
            by_cases h : s.borrowState.block ≤ s.blockNumber
            · exact h
            · have hnone := setBorrow_none { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b hpos2 h
              rw [hnone] at hbs
              contradiction
          have hu : s' = { ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St) with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
            have hnew := setBorrow_new { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } b hpos2 (by show s.borrowState.block ≤ s.blockNumber; exact hble)
            have hborState : (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).borrowState) = s.borrowState := rfl
            have hblk : (({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St).blockNumber) = s.blockNumber := rfl
            have htot : totalBorrows ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St) = totalBorrows s := rfl
            rw [hborState, hblk, htot] at hnew
            rw [hnew] at hbs
            exact (Option.some_inj.mp hbs).symm
          refine ⟨?_, ?_, ?_⟩
          · intro _; exact hle
          · intro _; exact hble
          · simp only [hsa]
            have hne : s.borrowState.speed ≠ b := hba
            simp [hne]
            exact hu

theorem req_set_speeds : SetSpeedsEffects comptroller := req_set_speeds_aux
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
