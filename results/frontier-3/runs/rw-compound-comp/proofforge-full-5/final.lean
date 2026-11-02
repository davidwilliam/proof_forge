import CompRewards.Spec
import ProofForgeFin.Ledger
import ProofForgeFin.Accumulator.Market

open ProofForgeFin.Accumulator
open ProofForgeFin.Accumulator.Market
open ProofForgeFin.DeFi.Rewards
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

theorem modify_congr_at {α : Type} (l : List α) (i : Nat) (f1 f2 : α → α) (d : α)
    (h : f1 (l.getD i d) = f2 (l.getD i d)) : l.modify i f1 = l.modify i f2 := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero => simp only [List.modify_zero_cons, List.getD_cons_zero] at h ⊢; rw [h]
    | succ i => simp only [List.modify_succ_cons, List.getD_cons_succ] at h ⊢; rw [ih _ h]

theorem upd_supply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked accrueSide totalSupply fraction
  simp only [h, ↓reduceIte]
  by_cases hd : 0 < s.blockNumber - s.supplyState.block
  · by_cases hs : 0 < s.supplyState.speed
    · by_cases ht : 0 < (s.accts.map Acct.supply).sum
      · simp [hd, hs, ht]
      · simp [hd, hs, ht]
    · simp [hd, hs]
  · cases s with | mk bn sup bor res accts =>
      cases sup with | mk idx blk spd =>
        simp only at h hd ⊢
        simp [hd]
        omega

theorem start_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
    accrualStart recorded index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp only [hr, true_and]
    by_cases hc : compInitialIndex ≤ index <;> simp [hc]
  · simp [hr]

theorem accrue_supply_le (s : St) :
    s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [hc]
  · simp [hc]

theorem accrue_borrow_le (s : St) :
    s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp [hc]
  · simp [hc]

theorem dist_supply_le (s1 : St) (who : Nat) (s' : St)
    (h : distributeSupplierComp s1 who = some s') :
    accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index := by
  simp only [distributeSupplierComp, subChecked] at h
  by_cases hle : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index
  · exact hle
  · have hle2 : ¬ (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by
      rw [start_eq]
      exact hle
    simp [hle2] at h

theorem dist_supply_eq4 (s1 : St) (who : Nat) (s' : St)
    (h : distributeSupplierComp s1 who = some s') :
    s' = { s1 with accts := s1.accts.modify who fun a => { a with supplierIndex := s1.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index) s1.supplyState.index } } := by
  have hle2 : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by
    by_cases hle : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index
    · rw [start_eq]
      exact hle
    · exfalso
      simp only [distributeSupplierComp, subChecked] at h
      have hle3 : ¬ (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by
        rw [start_eq]
        exact hle
      simp [hle3] at h
  simp only [distributeSupplierComp, subChecked, hle2, ↓reduceIte] at h
  simp at h
  subst h
  unfold St.withAcct
  congr 1
  refine modify_congr_at _ _ _ _ noAcct ?_
  unfold St.acct mulDouble creditFor
  rw [start_eq]

theorem dist_borrow_le (s1 : St) (who : Nat) (s' : St)
    (h : distributeBorrowerComp s1 who = some s') :
    accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
  simp only [distributeBorrowerComp, subChecked] at h
  by_cases hle : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index
  · exact hle
  · have hle2 : ¬ (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by
      rw [start_eq]
      exact hle
    simp [hle2] at h

theorem dist_borrow_eq4 (s1 : St) (who : Nat) (s' : St)
    (h : distributeBorrowerComp s1 who = some s') :
    s' = { s1 with accts := s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } := by
  have hle2 : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by
    by_cases hle : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index
    · rw [start_eq]
      exact hle
    · exfalso
      simp only [distributeBorrowerComp, subChecked] at h
      have hle3 : ¬ (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by
        rw [start_eq]
        exact hle
      simp [hle3] at h
  simp only [distributeBorrowerComp, subChecked, hle2, ↓reduceIte] at h
  simp at h
  subst h
  unfold St.withAcct
  congr 1
  refine modify_congr_at _ _ _ _ noAcct ?_
  unfold St.acct mulDouble creditFor
  rw [start_eq]

theorem upd_borrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked accrueSide totalBorrows fraction
  simp only [h, ↓reduceIte]
  by_cases hd : 0 < s.blockNumber - s.borrowState.block
  · by_cases hs : 0 < s.borrowState.speed
    · by_cases ht : 0 < (s.accts.map Acct.borrow).sum
      · simp [hd, hs, ht]
      · simp [hd, hs, ht]
    · simp [hd, hs]
  · cases s with | mk bn sup bor res accts =>
      cases bor with | mk idx blk spd =>
        simp only at h hd ⊢
        simp [hd]
        omega

theorem dist_supply_isSome (s1 : St) (who : Nat)
    (hle : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index) :
    ∃ s', distributeSupplierComp s1 who = some s' := by
  have hle2 : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by
    rw [start_eq]
    exact hle
  simp only [distributeSupplierComp, subChecked, hle2, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem dist_borrow_isSome (s1 : St) (who : Nat)
    (hle : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index) :
    ∃ s', distributeBorrowerComp s1 who = some s' := by
  have hle2 : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by
    rw [start_eq]
    exact hle
  simp only [distributeBorrowerComp, subChecked, hle2, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem setSupply_eq (s : St) (a : Nat) (hle : s.supplyState.block ≤ s.blockNumber) :
    ∃ mid, setSupplySpeed s a = some mid ∧ mid = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed
  by_cases hsa : s.supplyState.speed = a
  · simp [hsa]
  · simp [hsa, upd_supply_eq s hle]

theorem setBorrow_eq (s : St) (b : Nat) (hle : s.borrowState.block ≤ s.blockNumber) :
    ∃ mid, setBorrowSpeed s b = some mid ∧ mid = { s with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed
  by_cases hsb : s.borrowState.speed = b
  · simp [hsb]
  · simp [hsb, upd_borrow_eq s hle]

theorem dist_borrow_keeps (s1 : St) (who v : Nat) (s' : St) (h : distributeBorrowerComp s1 who = some s') : (s'.acct v).supply = (s1.acct v).supply ∧ (s'.acct v).supplierIndex = (s1.acct v).supplierIndex := by
  have heq := dist_borrow_eq4 _ _ _ h
  have hac : s'.accts = s1.accts.modify who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } := by
    simp [heq]
  unfold St.acct
  rw [hac, ProofForgeFin.Ledger.getD_modify]
  by_cases hm : who = v ∧ v < s1.accts.length
  · simp [hm]
  · simp [hm]

theorem accrualStart_le (r oldI newI : Nat) (hle : r ≤ oldI) (hm : oldI ≤ newI) :
    accrualStart r newI ≤ newI := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp only [hr, ↓reduceIte]
    by_cases hc : compInitialIndex ≤ newI
    · simp [hc]
    · simp [hc]
  · simp only [hr, ↓reduceIte]
    exact Nat.le_trans hle hm

theorem rec_supply_le (s : St) (hc : Consistent s) (who : Nat) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  obtain ⟨-, -, hrec⟩ := hc
  show (s.accts.getD who noAcct).supplierIndex ≤ _
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hrec _ hm).1
  · rw [hm]; exact Nat.zero_le _

theorem rec_borrow_le (s : St) (hc : Consistent s) (who : Nat) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  obtain ⟨-, -, hrec⟩ := hc
  show (s.accts.getD who noAcct).borrowerIndex ≤ _
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hrec _ hm).2
  · rw [hm]; exact Nat.zero_le _

theorem grant_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [grantCompInternal, grant, hc]
    have hmod : s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) =
        s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) :=
      modify_congr_at _ _ _ _ noAcct rfl
    rw [hmod]
  · simp only [grantCompInternal, grant, hc, ↓reduceIte]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompSupplyIndex s with
  | none => simp [hu] at h
  | some s1 =>
    simp [hu] at h
    have hblk : s.supplyState.block ≤ s.blockNumber := by
      by_cases hle : s.supplyState.block ≤ s.blockNumber
      · exact hle
      · have hnone : updateCompSupplyIndex s = none := by
          unfold updateCompSupplyIndex subChecked
          simp [hle]
        rw [hnone] at hu
        simp at hu
    rw [upd_supply_eq s hblk] at hu
    simp at hu
    subst hu
    have hle := dist_supply_le _ _ _ h
    have heq := dist_supply_eq4 _ _ _ h
    exact ⟨hblk, hle, heq⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompBorrowIndex s with
  | none => simp [hu] at h
  | some s1 =>
    simp [hu] at h
    have hblk : s.borrowState.block ≤ s.blockNumber := by
      by_cases hle : s.borrowState.block ≤ s.blockNumber
      · exact hle
      · have hnone : updateCompBorrowIndex s = none := by
          unfold updateCompBorrowIndex subChecked
          simp [hle]
        rw [hnone] at hu
        simp at hu
    rw [upd_borrow_eq s hblk] at hu
    simp at hu
    subst hu
    have hle := dist_borrow_le _ _ _ h
    have heq := dist_borrow_eq4 _ _ _ h
    exact ⟨hblk, hle, heq⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  cases hb1 : updateCompBorrowIndex s with
  | none => simp [hb1] at h
  | some t1 =>
    simp [hb1] at h
    cases hb2 : distributeBorrowerComp t1 who with
    | none => simp [hb2] at h
    | some t2 =>
      simp [hb2] at h
      cases hs1 : updateCompSupplyIndex t2 with
      | none => simp [hs1] at h
      | some t3 =>
        simp [hs1] at h
        cases hs2 : distributeSupplierComp t3 who with
        | none => simp [hs2] at h
        | some t4 =>
          simp [hs2] at h
          subst h
          have hblk_b : s.borrowState.block ≤ s.blockNumber := by
            by_cases hle : s.borrowState.block ≤ s.blockNumber
            · exact hle
            · have hnone : updateCompBorrowIndex s = none := by
                unfold updateCompBorrowIndex subChecked
                simp [hle]
              rw [hnone] at hb1
              simp at hb1
          rw [upd_borrow_eq s hblk_b] at hb1
          simp at hb1
          subst hb1
          have hble := dist_borrow_le _ _ _ hb2
          have hbeq := dist_borrow_eq4 _ _ _ hb2
          have hblk_s : t2.supplyState.block ≤ t2.blockNumber := by
            by_cases hle : t2.supplyState.block ≤ t2.blockNumber
            · exact hle
            · have hnone : updateCompSupplyIndex t2 = none := by
                unfold updateCompSupplyIndex subChecked
                simp [hle]
              rw [hnone] at hs1
              simp at hs1
          rw [upd_supply_eq t2 hblk_s] at hs1
          simp at hs1
          subst hs1
          have hsle := dist_supply_le _ _ _ hs2
          have hseq := dist_supply_eq4 _ _ _ hs2
          exact ⟨t2, t4, ⟨hblk_b, hble, hbeq⟩, ⟨hblk_s, hsle, hseq⟩, grant_eq _ _⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  cases hsup : setSupplySpeed s a with
  | none => simp [hsup] at h
  | some mid =>
    simp [hsup] at h
    have hsa_blk : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber := by
      intro hne
      by_cases hle : s.supplyState.block ≤ s.blockNumber
      · exact hle
      · have hnone : updateCompSupplyIndex s = none := by
          unfold updateCompSupplyIndex subChecked
          simp [hle]
        unfold setSupplySpeed at hsup
        simp [hne, hnone] at hsup
    have hmid : mid = { s with supplyState :=
        if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
      unfold setSupplySpeed at hsup
      by_cases hsa : s.supplyState.speed = a
      · simp [hsa] at hsup
        subst hsup
        simp [hsa]
      · simp [hsa] at hsup
        have hle := hsa_blk hsa
        rw [upd_supply_eq s hle] at hsup
        simp at hsup
        subst hsup
        simp [hsa]
    subst hmid
    have hsb_blk : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
      intro hne
      by_cases hle : s.borrowState.block ≤ s.blockNumber
      · exact hle
      · have hnone : updateCompBorrowIndex
          { s with supplyState := if s.supplyState.speed = a then s.supplyState
            else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } = none := by
          unfold updateCompBorrowIndex subChecked
          simp [hle]
        unfold setBorrowSpeed at h
        simp [hne, hnone] at h
    have hmid_tot : totalBorrows { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } = totalBorrows s := rfl
    unfold setBorrowSpeed at h
    by_cases hsb : s.borrowState.speed = b
    · simp [hsb] at h
      subst h
      refine ⟨hsa_blk, hsb_blk, ?_⟩
      by_cases hsa : s.supplyState.speed = a <;> simp [hsa, hsb]
    · simp [hsb] at h
      have hle := hsb_blk hsb
      have hmid_blk : ({ s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).borrowState.block ≤
        ({ s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).blockNumber := hle
      rw [upd_borrow_eq _ hmid_blk, hmid_tot] at h
      simp at h
      subst h
      refine ⟨hsa_blk, hsb_blk, ?_⟩
      by_cases hsa : s.supplyState.speed = a <;> simp [hsa, hsb]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have hsup := upd_supply_eq s hc.1
    have hle : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrualStart_le _ _ _ (rec_supply_le s hc who) (accrue_supply_le s)
    have hle1 : accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).acct who).supplierIndex (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index) ≤ (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index) := hle
    obtain ⟨s2, hs2⟩ := dist_supply_isSome _ _ hle1
    unfold comptroller
    simp [hsup, hs2]
  | borrowHook who =>
    have hsup := upd_borrow_eq s hc.2.1
    have hle : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrualStart_le _ _ _ (rec_borrow_le s hc who) (accrue_borrow_le s)
    have hle1 : accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).acct who).borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ≤ (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) := hle
    obtain ⟨s2, hs2⟩ := dist_borrow_isSome _ _ hle1
    unfold comptroller
    simp [hsup, hs2]
  | claim who =>
    have hsup_b := upd_borrow_eq s hc.2.1
    have hle_b : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrualStart_le _ _ _ (rec_borrow_le s hc who) (accrue_borrow_le s)
    have hle_b1 : accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).acct who).borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ≤ (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) := hle_b
    obtain ⟨t2, ht2⟩ := dist_borrow_isSome _ _ hle_b1
    have ht2eq := dist_borrow_eq4 _ _ _ ht2
    have hblk_s : t2.supplyState.block ≤ t2.blockNumber := by
      have e1 : t2.supplyState.block = s.supplyState.block := by simp [ht2eq]
      have e2 : t2.blockNumber = s.blockNumber := by simp [ht2eq]
      rw [e1, e2]
      exact hc.1
    have hsup_s := upd_supply_eq t2 hblk_s
    have hrec_s : (t2.acct who).supplierIndex ≤ t2.supplyState.index := by
      have e : t2.supplyState.index = s.supplyState.index := by simp [ht2eq]
      have k : (t2.acct who).supplierIndex = (s.acct who).supplierIndex := (dist_borrow_keeps _ _ _ _ ht2).2
      rw [e, k]
      exact rec_supply_le s hc who
    have hle_s : accrualStart (t2.acct who).supplierIndex (accrueSide t2.supplyState t2.blockNumber (totalSupply t2)).index ≤ (accrueSide t2.supplyState t2.blockNumber (totalSupply t2)).index := accrualStart_le _ _ _ hrec_s (accrue_supply_le t2)
    have hle_s1 : accrualStart (({ t2 with supplyState := accrueSide t2.supplyState t2.blockNumber (totalSupply t2) }).acct who).supplierIndex (({ t2 with supplyState := accrueSide t2.supplyState t2.blockNumber (totalSupply t2) }).supplyState.index) ≤ (({ t2 with supplyState := accrueSide t2.supplyState t2.blockNumber (totalSupply t2) }).supplyState.index) := hle_s
    obtain ⟨t4, ht4⟩ := dist_supply_isSome _ _ hle_s1
    unfold comptroller claimComp
    simp [hsup_b, ht2, hsup_s, ht4]
  | setSpeeds a b =>
    obtain ⟨mid, hmid1, hmid2⟩ := setSupply_eq s a hc.1
    have hblk : mid.borrowState.block ≤ mid.blockNumber := by
      rw [hmid2]
      exact hc.2.1
    obtain ⟨mid2, hmid2a, hmid2b⟩ := setBorrow_eq mid b hblk
    unfold comptroller setCompSpeedInternal
    simp [hmid1, hmid2a]
/-- The market read for the accumulator library: supply is side 1, borrow is side 2. -/
def M : ProofForgeFin.Accumulator.Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock s := ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed,
    s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts s := s.accts
  dflt := noAcct
  units₁ a := a.supply
  units₂ a := a.borrow
  rec₁ a := a.supplierIndex
  rec₂ a := a.borrowerIndex
  credited a := a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

theorem M_one_eq : M.one = doubleScale := rfl

theorem M_init_eq : M.init = compInitialIndex := rfl

theorem M_total₁_eq (s : St) : M.total₁ s = totalSupply s := rfl

theorem M_total₂_eq (s : St) : M.total₂ s = totalBorrows s := rfl

theorem M_clock_eq (s : St) : M.clock s = ⟨s.blockNumber, s.supplyState.index, s.supplyState.block,
    s.supplyState.speed, s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩ := rfl

theorem M_accts_eq (s : St) : M.accts s = s.accts := rfl

theorem M_acct_eq (s : St) (w : Nat) : M.acct s w = St.acct s w := rfl

theorem M_rec₁_eq (a : Acct) : M.rec₁ a = a.supplierIndex := rfl

theorem M_rec₂_eq (a : Acct) : M.rec₂ a = a.borrowerIndex := rfl

theorem M_units₁_eq (a : Acct) : M.units₁ a = a.supply := rfl

theorem M_units₂_eq (a : Acct) : M.units₂ a = a.borrow := rfl

theorem M_credited_eq (a : Acct) : M.credited a = a.accrued + a.wallet := rfl

theorem M_dflt_eq : M.dflt = noAcct := rfl

theorem upgrade_block (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := rfl

theorem upgrade_supply_index (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upgrade_supply_block (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upgrade_supply_speed (L : Legacy) : (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upgrade_borrow_index (L : Legacy) :
    (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
  unfold upgrade initSide
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upgrade_borrow_block (L : Legacy) :
    (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
  unfold upgrade initSide
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upgrade_borrow_speed (L : Legacy) : (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upgrade_accts (L : Legacy) : (upgrade L).accts = L.accts := rfl

theorem catchUp₁_eq (c : ProofForgeFin.Accumulator.Clock) (one total : Nat) :
    c.catchUp₁ one total = ⟨c.now, ProofForgeFin.Accumulator.catchUp one c.index₁ c.last₁ c.rate₁ c.now total,
      c.now, c.rate₁, c.index₂, c.last₂, c.rate₂⟩ := rfl

theorem catchUp₂_eq (c : ProofForgeFin.Accumulator.Clock) (one total : Nat) :
    c.catchUp₂ one total = ⟨c.now, c.index₁, c.last₁, c.rate₁,
      ProofForgeFin.Accumulator.catchUp one c.index₂ c.last₂ c.rate₂ c.now total, c.now, c.rate₂⟩ := rfl

theorem accrueSide_eq_catchUp (sd : Side) (now total : Nat) :
    accrueSide sd now total = { sd with index := ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total, block := now } := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hc]
  · simp [hc]

theorem accrualStart_eq_firstStart (r idx : Nat) :
    accrualStart r idx = firstStart compInitialIndex r idx := by
  unfold accrualStart firstStart
  by_cases hr : r = 0
  · simp [hr]
  · simp [hr]

theorem settle₁_of_dist (s : St) (who : Nat) (s' : St) (h : SupplyDistributed s who s') : M.Settle₁ who s s' := by
  obtain ⟨hblk, hle, heq⟩ := h
  subst heq
  refine ⟨?_, fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }, ?_, ?_⟩
  · simp only [M_clock_eq, catchUp₁_eq, M_one_eq, M_total₁_eq, accrueSide_eq_catchUp]
  · simp only [M_accts_eq]
  · intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    show (a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) + a.wallet ≤ (a.accrued + a.wallet) + a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - firstStart M.init a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / M.one
    unfold creditFor
    rw [accrualStart_eq_firstStart, M_init_eq, M_one_eq]
    omega

theorem advance_eq (c : Clock) (k : Nat) : c.advance k = ⟨c.now + k, c.index₁, c.last₁, c.rate₁, c.index₂, c.last₂, c.rate₂⟩ := rfl

theorem retune_of_speeds (s : St) (a b : Nat) (t : St) (h : SpeedsSet s a b t) : M.Retune s t := by
  obtain ⟨h1, h2, heq⟩ := h
  subst heq
  refine ⟨rfl, rfl, ?_, ?_⟩
  · by_cases hsa : s.supplyState.speed = a
    · left
      simp only [M_clock_eq]
      simp [hsa]
    · right
      simp only [M_clock_eq, M_one_eq, M_total₁_eq, accrueSide_eq_catchUp]
      simp [hsa]
  · by_cases hsb : s.borrowState.speed = b
    · left
      simp only [M_clock_eq]
      simp [hsb]
    · right
      simp only [M_clock_eq, M_one_eq, M_total₂_eq, accrueSide_eq_catchUp]
      simp [hsb]

theorem settle₂_of_dist (s : St) (who : Nat) (s' : St) (h : BorrowDistributed s who s') : M.Settle₂ who s s' := by
  obtain ⟨hblk, hle, heq⟩ := h
  subst heq
  refine ⟨?_, fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }, ?_, ?_⟩
  · simp only [M_clock_eq, catchUp₂_eq, M_one_eq, M_total₂_eq, accrueSide_eq_catchUp]
  · simp only [M_accts_eq]
  · intro a
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    show (a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) + a.wallet ≤ (a.accrued + a.wallet) + a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - firstStart M.init a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / M.one
    unfold creditFor
    rw [accrualStart_eq_firstStart, M_init_eq, M_one_eq]
    omega

theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op) (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  cases op with
  | mint who x =>
    unfold exec
    by_cases hm : who < s.accts.length
    · simp only [hm, ↓reduceIte]
      cases hs : comptroller s (.supplyHook who) with
      | none =>
        simp
        exact Act.moves (Reach.refl s)
      | some s' =>
        simp
        have hset := settle₁_of_dist s who s' (req_supply_hook s who s' hs)
        have hreach : M.Reach s (s'.withAcct who fun a => { a with supply := a.supply + x }) :=
          hset.then_adjust rfl rfl
            (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
            (fun a => rfl)
        exact Act.moves hreach
    · simp only [hm, ↓reduceIte]
      exact Act.moves (Reach.refl s)
  | redeem who x =>
    unfold exec
    by_cases hm : who < s.accts.length
    · simp only [hm, ↓reduceIte]
      cases hs : comptroller s (.supplyHook who) with
      | none =>
        simp
        exact Act.moves (Reach.refl s)
      | some s' =>
        simp
        by_cases hx : x ≤ (s'.acct who).supply
        · simp [hx]
          have hset := settle₁_of_dist s who s' (req_supply_hook s who s' hs)
          have hreach : M.Reach s (s'.withAcct who fun a => { a with supply := a.supply - x }) :=
            hset.then_adjust rfl rfl
              (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
              (fun a => rfl)
          exact Act.moves hreach
        · simp [hx]
          exact Act.moves (Reach.refl s)
    · simp only [hm, ↓reduceIte]
      exact Act.moves (Reach.refl s)
  | transfer src dst x =>
    unfold exec
    by_cases hm : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · obtain ⟨hm1, hm2, hne⟩ := hm
      simp [hm1, hm2, hne]
      cases hs1 : comptroller s (.supplyHook src) with
      | none =>
        simp
        exact Act.moves (Reach.refl s)
      | some s₁ =>
        simp
        cases hs2 : comptroller s₁ (.supplyHook dst) with
        | none =>
          simp
          exact Act.moves (Reach.refl s)
        | some s₂ =>
          simp
          by_cases hx : x ≤ (s₂.acct src).supply
          · simp [hx]
            have hset1 := settle₁_of_dist s src s₁ (req_supply_hook s src s₁ hs1)
            have hset2 := settle₁_of_dist s₁ dst s₂ (req_supply_hook s₁ dst s₂ hs2)
            have hreach : M.Reach s ((s₂.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst fun a => { a with supply := a.supply + x }) :=
              hset1.transfer hset2 rfl rfl
                (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
                (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
                (fun a => rfl) (fun a => rfl)
            exact Act.moves hreach
          · simp [hx]
            exact Act.moves (Reach.refl s)
    · simp only [hm, ↓reduceIte]
      exact Act.moves (Reach.refl s)
  | borrow who x =>
    unfold exec
    by_cases hm : who < s.accts.length
    · simp only [hm, ↓reduceIte]
      cases hs : comptroller s (.borrowHook who) with
      | none =>
        simp
        exact Act.moves (Reach.refl s)
      | some s' =>
        simp
        have hset := settle₂_of_dist s who s' (req_borrow_hook s who s' hs)
        have hreach : M.Reach s (s'.withAcct who fun a => { a with borrow := a.borrow + x }) :=
          hset.then_adjust rfl rfl
            (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
            (fun a => rfl)
        exact Act.moves hreach
    · simp only [hm, ↓reduceIte]
      exact Act.moves (Reach.refl s)
  | repay who x =>
    unfold exec
    by_cases hm : who < s.accts.length
    · simp only [hm, ↓reduceIte]
      cases hs : comptroller s (.borrowHook who) with
      | none =>
        simp
        exact Act.moves (Reach.refl s)
      | some s' =>
        simp
        by_cases hx : x ≤ (s'.acct who).borrow
        · simp [hx]
          have hset := settle₂_of_dist s who s' (req_borrow_hook s who s' hs)
          have hreach : M.Reach s (s'.withAcct who fun a => { a with borrow := a.borrow - x }) :=
            hset.then_adjust rfl rfl
              (fun a => ⟨Nat.le_refl _, rfl, rfl⟩)
              (fun a => rfl)
          exact Act.moves hreach
        · simp [hx]
          exact Act.moves (Reach.refl s)
    · simp only [hm, ↓reduceIte]
      exact Act.moves (Reach.refl s)
  | claim who =>
    show M.Act sp s (nextSpeeds sp (.claim who)) (emittedBy sp (.claim who)) ((comptroller s (.claim who)).getD s)
    cases hc : comptroller s (.claim who) with
    | none =>
      simp
      exact Act.moves (Reach.refl s)
    | some t =>
      simp
      have hcl := req_claim s who t hc
      obtain ⟨m₁, m₂, hB, hS, hgrant⟩ := hcl
      have hset2 := settle₂_of_dist s who m₁ hB
      have hset1 := settle₁_of_dist m₁ who m₂ hS
      have hreach : M.Reach s (grant m₂ who) :=
        (Reach.single (Step.settle₂ hset2)).tail (Step.settle₁ hset1) |>.tail
          (by
            by_cases hpay : 0 < (m₂.acct who).accrued ∧ (m₂.acct who).accrued ≤ m₂.reserve
            · have ht : grant m₂ who = { m₂ with reserve := m₂.reserve - (m₂.acct who).accrued, accts := m₂.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
                unfold grant
                simp [hpay]
              rw [ht]
              exact Step.adjust ⟨rfl, _, rfl, (fun a => ⟨by show (0 : Nat) + (a.wallet + a.accrued) ≤ a.accrued + a.wallet; omega, rfl, rfl⟩), Or.inl (fun a => rfl), Or.inl (fun a => rfl)⟩
            · have ht : grant m₂ who = m₂ := by
                unfold grant
                simp [hpay]
              rw [ht]
              exact Step.same rfl rfl)
      rw [hgrant]
      exact Act.moves hreach
  | setSpeeds a b =>
    have hblk_s : s.supplyState.block ≤ s.blockNumber := hI.last₁
    obtain ⟨mid, hmid1, hmid2⟩ := setSupply_eq s a hblk_s
    have hblk_b : mid.borrowState.block ≤ mid.blockNumber := by
      rw [hmid2]
      exact hI.last₂
    obtain ⟨mid2, hmid2a, hmid2b⟩ := setBorrow_eq mid b hblk_b
    have hcomp : comptroller s (.setSpeeds a b) = some mid2 := by
      unfold comptroller setCompSpeedInternal
      simp [hmid1, hmid2a]
    have hexec : exec comptroller s (.setSpeeds a b) = mid2 := by
      unfold exec
      simp [hcomp]
    rw [hexec]
    have hss := req_set_speeds s a b mid2 hcomp
    have hret := retune_of_speeds s a b mid2 hss
    obtain ⟨_, _, heq⟩ := hss
    subst heq
    have hr1 : (M.clock { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }), borrowState := (if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) }).rate₁ = a := by
      by_cases hsa : s.supplyState.speed = a
      · simp [hsa, M_clock_eq]
      · simp [hsa, M_clock_eq]
    have hr2 : (M.clock { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }), borrowState := (if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) }).rate₂ = b := by
      by_cases hsb : s.borrowState.speed = b
      · simp [hsb, M_clock_eq]
      · simp [hsb, M_clock_eq]
    exact Act.retune hret hr1 hr2
  | advance k =>
    show M.Act sp s (nextSpeeds sp (.advance k)) (emittedBy sp (.advance k)) ({ s with blockNumber := s.blockNumber + k })
    exact Act.advance k ⟨by simp only [M_clock_eq, advance_eq], rfl⟩
  | drip x =>
    show M.Act sp s (nextSpeeds sp (.drip x)) (emittedBy sp (.drip x)) ({ s with reserve := s.reserve + x })
    exact Act.moves (Reach.single (Step.same rfl rfl))

theorem inv_upgrade (L : Legacy) (hL : L.WellFormed) :
    M.Inv (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
          (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
          (L.compSpeed, L.compSpeed) (upgrade L) := by
  obtain ⟨hs1, hs1le, hb1, hb1le, hblk_s, hblk_b, hrec⟩ := hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [M_clock_eq, upgrade_supply_block, upgrade_block]
    by_cases h : L.supplyIndex = 0
    · simp [h]
    · simp [h, hblk_s]
  · simp only [M_clock_eq, upgrade_borrow_block, upgrade_block]
    by_cases h : L.borrowIndex = 0
    · simp [h]
    · simp [h, hblk_b]
  · simp only [M_accts_eq, upgrade_accts, M_clock_eq, upgrade_supply_index, upgrade_borrow_index,
      M_rec₁_eq, M_rec₂_eq]
    intro a ha
    obtain ⟨hr1, hr2⟩ := hrec a ha
    constructor
    · by_cases h : L.supplyIndex = 0
      · simp only [h, ↓reduceIte]
        omega
      · simp only [h, ↓reduceIte]
        exact hr1
    · by_cases h : L.borrowIndex = 0
      · simp only [h, ↓reduceIte]
        omega
      · simp only [h, ↓reduceIte]
        exact hr2
  · simp only [M_init_eq, M_clock_eq, upgrade_supply_index]
    exact start_reinit hs1 hs1le
  · simp only [M_init_eq, M_clock_eq, upgrade_borrow_index]
    exact start_reinit hb1 hb1le
  · simp only [M_clock_eq, upgrade_supply_speed]
  · simp only [M_clock_eq, upgrade_borrow_speed]

theorem hone : 0 < M.one := by
  show 0 < doubleScale
  unfold doubleScale
  decide

theorem owed_upgrade_le (L : Legacy) (a : Acct) (hr1 : a.supplierIndex ≤ L.supplyIndex)
    (hr2 : a.borrowerIndex ≤ L.borrowIndex) (g₁ g₂ : Nat)
    (hg1 : g₁ = if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
    (hg2 : g₂ = if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) :
    M.owed g₁ g₂ (M.clock (upgrade L)) a ≤ L.pendingScaled a := by
  subst hg1
  subst hg2
  simp only [Market.owed, M_units₁_eq, M_units₂_eq, M_rec₁_eq, M_rec₂_eq, M_clock_eq,
    upgrade_supply_index, upgrade_borrow_index, Legacy.pendingScaled]
  exact Nat.add_le_add (owed_reinit_le _ hr1) (owed_reinit_le _ hr2)

theorem un₁_upgrade_le (L : Legacy) : (M.clock (upgrade L)).un₁ ≤ L.unindexedSupply := by
  simp only [Clock.un₁, M_clock_eq, upgrade_supply_block, upgrade_supply_speed, upgrade_block,
    Legacy.unindexedSupply]
  exact unindexed_reinit_le _ _ _ _

theorem un₂_upgrade_le (L : Legacy) : (M.clock (upgrade L)).un₂ ≤ L.unindexedBorrow := by
  simp only [Clock.un₂, M_clock_eq, upgrade_borrow_block, upgrade_borrow_speed, upgrade_block,
    Legacy.unindexedBorrow]
  exact unindexed_reinit_le _ _ _ _

theorem req_rewards_bounded : RewardsBounded comptroller := by
  intro L ops hL
  obtain ⟨hs1, hs1le, hb1, hb1le, hblk_s, hblk_b, hrec⟩ := hL
  have h0 := inv_upgrade L ⟨hs1, hs1le, hb1, hb1le, hblk_s, hblk_b, hrec⟩
  have hq : ∀ a ∈ M.accts (upgrade L),
      M.owed (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
        (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
        (M.clock (upgrade L)) a ≤ L.pendingScaled a := by
    intro a ha
    have ha' : a ∈ L.accts := by simpa [M_accts_eq, upgrade_accts] using ha
    obtain ⟨hr1, hr2⟩ := hrec a ha'
    exact owed_upgrade_le L a hr1 hr2 _ _ rfl rfl
  have hs := M.pot_le_of hq (un₁_upgrade_le L) (un₂_upgrade_le L)
  exact M.rewards_bounded (run comptroller) emitted speedsAfter
    (fun sp s a hI => exec_act _ _ sp s a hI) hone h0 hs ops

theorem req_account_bounded : AccountBounded comptroller := by
  intro L ops who hL
  obtain ⟨hs1, hs1le, hb1, hb1le, hblk_s, hblk_b, hrec⟩ := hL
  have h0 := inv_upgrade L ⟨hs1, hs1le, hb1, hb1le, hblk_s, hblk_b, hrec⟩
  have hmem2 : L.accts.getD who noAcct ∈ L.accts ∨ L.accts.getD who noAcct = noAcct := by
    have h := ProofForgeFin.Ledger.getD_mem_or (M.accts (upgrade L)) who M.dflt
    rwa [M_accts_eq, upgrade_accts, M_dflt_eq] at h
  have hac_eq : M.acct (upgrade L) who = L.accts.getD who noAcct := by
    rw [M_acct_eq]
    show (upgrade L).accts.getD who noAcct = L.accts.getD who noAcct
    rw [upgrade_accts]
  have hq : M.owed (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
      (M.clock (upgrade L)) (M.acct (upgrade L) who) ≤
      L.pendingScaled (L.accts.getD who noAcct) := by
    rw [hac_eq]
    rcases hmem2 with hm | hm
    · obtain ⟨hr1, hr2⟩ := hrec _ hm
      exact owed_upgrade_le L _ hr1 hr2 _ _ rfl rfl
    · rw [hm]
      simp [Market.owed, M_units₁_eq, M_units₂_eq, Legacy.pendingScaled, noAcct]
  have hs := M.potOf_le_of hq (un₁_upgrade_le L) (un₂_upgrade_le L)
  exact M.account_rewards_bounded (run comptroller) emitted speedsAfter
    (fun sp s a hI => exec_act _ _ sp s a hI) hone h0 who hs ops

theorem req_no_backdated : NoBackdatedRewards comptroller := by
  intro L history ops who hL hnpos
  obtain ⟨hs1, hs1le, hb1, hb1le, hblk_s, hblk_b, hrec⟩ := hL
  have h0 := inv_upgrade L ⟨hs1, hs1le, hb1, hb1le, hblk_s, hblk_b, hrec⟩
  obtain ⟨hn1, hn2⟩ := hnpos
  have h1 : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := hn1
  have h2 : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := hn2
  exact M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter
    (fun sp s a hI => exec_act _ _ sp s a hI) hone h0 history ops who h1 h2

end CompRewards
