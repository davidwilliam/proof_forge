import CompRewards.Spec
import ProofForgeFin.Ledger
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Index
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Accumulator.Runs
import ProofForgeFin.Seq
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

theorem updS_block_le (s : St) (t : St) (he1 : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  simp only [updateCompSupplyIndex, subChecked] at he1
  by_cases h : s.supplyState.block ≤ s.blockNumber
  · exact h
  · simp [h] at he1

theorem updS_eq (s : St) (t : St) (he1 : updateCompSupplyIndex s = some t) :
    t = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by
  have hle : s.supplyState.block ≤ s.blockNumber := updS_block_le s t he1
  simp only [updateCompSupplyIndex, subChecked, hle, ↓reduceIte] at he1
  simp only [accrueSide, fraction] at he1 ⊢
  by_cases hc : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hc] at he1
    by_cases ht : totalSupply s > 0
    · rw [if_pos ht] at he1
      have h3 : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := by obtain ⟨a, b⟩ := hc; omega
      rw [if_pos h3]
      cases he1
      rfl
    · rw [if_neg ht] at he1
      have h3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := by omega
      rw [if_neg h3]
      cases he1
      rfl
  · rw [if_neg hc] at he1
    by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · have hd' : s.blockNumber - s.supplyState.block > 0 := hd
      rw [if_pos hd'] at he1
      have h3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := by omega
      rw [if_neg h3]
      cases he1
      rfl
    · have hd' : ¬ s.blockNumber - s.supplyState.block > 0 := by omega
      rw [if_neg hd'] at he1
      have h3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := by omega
      rw [if_neg h3]
      cases he1
      have hb : s.supplyState.block = s.blockNumber := by omega
      cases s with
      | mk bn ss bs r ac =>
        simp only at hb ⊢
        cases ss with
        | mk idx blk spd =>
          simp only at hb ⊢
          subst hb
          rfl

theorem mod_congr_list {α : Type} (l : List α) (w : Nat) (f g : α → α) (d : α)
    (h : f (l.getD w d) = g (l.getD w d)) : l.modify w f = l.modify w g := by
  induction l generalizing w with
  | nil => simp
  | cons b l ih =>
    cases w with
    | zero => simpa using h
    | succ w => simp only [List.modify_succ_cons]; exact congrArg _ (ih w (by simpa using h))

theorem updB_block_le (s : St) (t : St) (he1 : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber := by
  simp only [updateCompBorrowIndex, subChecked] at he1
  by_cases h : s.borrowState.block ≤ s.blockNumber
  · exact h
  · simp [h] at he1

theorem updB_eq (s : St) (t : St) (he1 : updateCompBorrowIndex s = some t) :
    t = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by
  have hle : s.borrowState.block ≤ s.blockNumber := updB_block_le s t he1
  simp only [updateCompBorrowIndex, subChecked, hle, ↓reduceIte] at he1
  simp only [accrueSide, fraction] at he1 ⊢
  by_cases hc : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hc] at he1
    by_cases ht : totalBorrows s > 0
    · rw [if_pos ht] at he1
      have h3 : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := by obtain ⟨a, b⟩ := hc; omega
      rw [if_pos h3]
      cases he1
      rfl
    · rw [if_neg ht] at he1
      have h3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := by omega
      rw [if_neg h3]
      cases he1
      rfl
  · rw [if_neg hc] at he1
    by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · have hd' : s.blockNumber - s.borrowState.block > 0 := hd
      rw [if_pos hd'] at he1
      have h3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := by omega
      rw [if_neg h3]
      cases he1
      rfl
    · have hd' : ¬ s.blockNumber - s.borrowState.block > 0 := by omega
      rw [if_neg hd'] at he1
      have h3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := by omega
      rw [if_neg h3]
      cases he1
      have hb : s.borrowState.block = s.blockNumber := by omega
      cases s with
      | mk bn ss bs r ac =>
        simp only at hb ⊢
        cases bs with
        | mk idx blk spd =>
          simp only at hb ⊢
          subst hb
          rfl

theorem distS_eq (s : St) (who : Nat) (u : St) (he2 : distributeSupplierComp s who = some u) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    u = s.withAcct who fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } := by
  simp only [distributeSupplierComp, subChecked, mulDouble] at he2
  by_cases hr : (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
  · obtain ⟨hz, hle2⟩ := hr
    simp only [hz, ↓reduceIte, true_and] at he2
    simp [hle2] at he2
    have hstart : accrualStart (s.acct who).supplierIndex s.supplyState.index = compInitialIndex := by
      simp [accrualStart, hz, hle2]
    rw [hstart]
    refine ⟨hle2, ?_⟩
    cases he2 with
    | refl =>
      have hz2 : (s.accts.getD who noAcct).supplierIndex = 0 := by simpa [St.acct] using hz
      have hsup : (s.acct who).supply = (s.accts.getD who noAcct).supply := rfl
      have hacc : (s.acct who).supply * (s.supplyState.index - compInitialIndex) / doubleScale = creditFor (s.accts.getD who noAcct).supply (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) s.supplyState.index := by
        unfold creditFor accrualStart
        rw [hz2, hsup]
        simp [hle2]
      have hmod : s.accts.modify who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + (s.acct who).supply * (s.supplyState.index - compInitialIndex) / doubleScale }) = s.accts.modify who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
        apply mod_congr_list _ _ _ _ noAcct
        simp only [hacc]
      simp only [St.withAcct, hmod]
  · simp only [hr, ↓reduceIte] at he2
    by_cases hle2 : (s.acct who).supplierIndex ≤ s.supplyState.index
    · have hstart : accrualStart (s.acct who).supplierIndex s.supplyState.index = (s.acct who).supplierIndex := by
        unfold accrualStart
        by_cases hz : (s.acct who).supplierIndex = 0
        · simp [hz] at hr
          simp [hz]
          omega
        · simp [hz]
      rw [hstart]
      refine ⟨hle2, ?_⟩
      simp [hle2] at he2
      cases he2 with
      | refl =>
        have hsup : (s.acct who).supply = (s.accts.getD who noAcct).supply := rfl
        have hacct : (s.acct who).supplierIndex = (s.accts.getD who noAcct).supplierIndex := rfl
        have hstart2 : accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index = (s.accts.getD who noAcct).supplierIndex := by
          rw [←hacct]
          exact hstart
        have hacc : (s.acct who).supply * (s.supplyState.index - (s.acct who).supplierIndex) / doubleScale = creditFor (s.accts.getD who noAcct).supply (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) s.supplyState.index := by
          unfold creditFor
          rw [hsup, hacct, hstart2]
        have hmod : s.accts.modify who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + (s.acct who).supply * (s.supplyState.index - (s.acct who).supplierIndex) / doubleScale }) = s.accts.modify who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
          apply mod_congr_list _ _ _ _ noAcct
          simp only [hacc]
        simp only [St.withAcct, hmod]
    · have hle : ¬ (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
        simp [hr, hle2]
      have hneg : ¬ (s.acct who).supplierIndex ≤ s.supplyState.index := hle2
      simp only [hr, ↓reduceIte] at hle
      rw [if_neg hle2] at he2
      simp at he2

theorem distB_eq (s : St) (who : Nat) (u : St) (he2 : distributeBorrowerComp s who = some u) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    u = s.withAcct who fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } := by
  simp only [distributeBorrowerComp, subChecked, mulDouble] at he2
  by_cases hr : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · obtain ⟨hz, hle2⟩ := hr
    simp only [hz, ↓reduceIte, true_and] at he2
    simp [hle2] at he2
    have hstart : accrualStart (s.acct who).borrowerIndex s.borrowState.index = compInitialIndex := by
      simp [accrualStart, hz, hle2]
    rw [hstart]
    refine ⟨hle2, ?_⟩
    cases he2 with
    | refl =>
      have hz2 : (s.accts.getD who noAcct).borrowerIndex = 0 := by simpa [St.acct] using hz
      have hsup : (s.acct who).borrow = (s.accts.getD who noAcct).borrow := rfl
      have hacc : (s.acct who).borrow * (s.borrowState.index - compInitialIndex) / doubleScale = creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index := by
        unfold creditFor accrualStart
        rw [hz2, hsup]
        simp [hle2]
      have hmod : s.accts.modify who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + (s.acct who).borrow * (s.borrowState.index - compInitialIndex) / doubleScale }) = s.accts.modify who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
        apply mod_congr_list _ _ _ _ noAcct
        simp only [hacc]
      simp only [St.withAcct, hmod]
  · simp only [hr, ↓reduceIte] at he2
    by_cases hle2 : (s.acct who).borrowerIndex ≤ s.borrowState.index
    · have hstart : accrualStart (s.acct who).borrowerIndex s.borrowState.index = (s.acct who).borrowerIndex := by
        unfold accrualStart
        by_cases hz : (s.acct who).borrowerIndex = 0
        · simp [hz] at hr
          simp [hz]
          omega
        · simp [hz]
      rw [hstart]
      refine ⟨hle2, ?_⟩
      simp [hle2] at he2
      cases he2 with
      | refl =>
        have hsup : (s.acct who).borrow = (s.accts.getD who noAcct).borrow := rfl
        have hacct : (s.acct who).borrowerIndex = (s.accts.getD who noAcct).borrowerIndex := rfl
        have hstart2 : accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index = (s.accts.getD who noAcct).borrowerIndex := by
          rw [←hacct]
          exact hstart
        have hacc : (s.acct who).borrow * (s.borrowState.index - (s.acct who).borrowerIndex) / doubleScale = creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index := by
          unfold creditFor
          rw [hsup, hacct, hstart2]
        have hmod : s.accts.modify who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + (s.acct who).borrow * (s.borrowState.index - (s.acct who).borrowerIndex) / doubleScale }) = s.accts.modify who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
          apply mod_congr_list _ _ _ _ noAcct
          simp only [hacc]
        simp only [St.withAcct, hmod]
    · have hle : ¬ (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
        simp [hr, hle2]
      have hneg : ¬ (s.acct who).borrowerIndex ≤ s.borrowState.index := hle2
      simp only [hr, ↓reduceIte] at hle
      rw [if_neg hle2] at he2
      simp at he2

theorem le_accrueSide (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · simp only
    exact Nat.le_add_right _ _
  · simp only
    exact Nat.le_refl _

theorem accrualStart_le {recorded index : Nat} (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hz : recorded = 0
  · simp [hz]
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hz, h]

theorem grant_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  dsimp only
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · rw [if_pos h, if_pos h]
    congr 1
    apply mod_congr_list _ _ _ _ noAcct
    have hsup : (s.accts.getD who noAcct).accrued = (s.acct who).accrued := rfl
    have hwal : (s.accts.getD who noAcct).wallet = (s.acct who).wallet := rfl
    simp only [hsup, hwal, St.acct]
  · rw [if_neg h, if_neg h]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases he1 : updateCompSupplyIndex s with
  | none => simp [he1] at h
  | some t =>
    simp [he1] at h
    cases he2 : distributeSupplierComp t who with
    | none => simp [he2] at h
    | some u =>
      simp [he2] at h
      subst h
      have htle := updS_block_le s t he1
      have hteq := updS_eq s t he1
      have ⟨hdle, hueq⟩ := distS_eq t who u he2
      have hacct : t.acct who = s.acct who := by rw [hteq]; rfl
      have hidx : t.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        rw [hteq]
      have htle2 : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        rw [←hacct, ←hidx]; exact hdle
      refine ⟨htle, htle2, ?_⟩
      rw [hteq] at hueq
      simp only [St.withAcct] at hueq ⊢
      exact hueq

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases he1 : updateCompBorrowIndex s with
  | none => simp [he1] at h
  | some t =>
    simp [he1] at h
    cases he2 : distributeBorrowerComp t who with
    | none => simp [he2] at h
    | some u =>
      simp [he2] at h
      subst h
      have htle := updB_block_le s t he1
      have hteq := updB_eq s t he1
      have ⟨hdle, hueq⟩ := distB_eq t who u he2
      have hacct : t.acct who = s.acct who := by rw [hteq]; rfl
      have hidx : t.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        rw [hteq]
      have htle2 : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        rw [←hacct, ←hidx]; exact hdle
      refine ⟨htle, htle2, ?_⟩
      rw [hteq] at hueq
      simp only [St.withAcct] at hueq ⊢
      exact hueq

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
  cases he1 : updateCompBorrowIndex s with
  | none => simp [he1] at h
  | some b1 =>
    simp [he1] at h
    cases he2 : distributeBorrowerComp b1 who with
    | none => simp [he2] at h
    | some m1 =>
      simp [he2] at h
      cases he3 : updateCompSupplyIndex m1 with
      | none => simp [he3] at h
      | some s2 =>
        simp [he3] at h
        cases he4 : distributeSupplierComp s2 who with
        | none => simp [he4] at h
        | some m2 =>
          simp [he4, grant_eq] at h
          subst h
          have htleB := updB_block_le s b1 he1
          have hteqB := updB_eq s b1 he1
          have ⟨hdleB, hueqB⟩ := distB_eq b1 who m1 he2
          have hacctB : b1.acct who = s.acct who := by rw [hteqB]; rfl
          have hidxB : b1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
            rw [hteqB]
          have hbor : BorrowDistributed s who m1 := by
            refine ⟨htleB, ?_, ?_⟩
            · rw [←hacctB, ←hidxB]; exact hdleB
            · rw [hteqB] at hueqB
              simp only [St.withAcct] at hueqB ⊢
              exact hueqB
          have htleS := updS_block_le m1 s2 he3
          have hteqS := updS_eq m1 s2 he3
          have ⟨hdleS, hueqS⟩ := distS_eq s2 who m2 he4
          have hacctS : s2.acct who = m1.acct who := by rw [hteqS]; rfl
          have hidxS : s2.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
            rw [hteqS]
          have hsup : SupplyDistributed m1 who m2 := by
            refine ⟨htleS, ?_, ?_⟩
            · rw [←hacctS, ←hidxS]; exact hdleS
            · rw [hteqS] at hueqS
              simp only [St.withAcct] at hueqS ⊢
              exact hueqS
          exact ⟨m1, m2, hbor, hsup, rfl⟩

theorem setS_eq (s : St) (a : Nat) (t : St) (hs : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = ({ s with supplyState := if s.supplyState.speed = a then s.supplyState else {(accrueSide s.supplyState s.blockNumber (totalSupply s)) with speed := a} } : St) := by
  unfold setSupplySpeed at hs
  by_cases hsa : s.supplyState.speed ≠ a
  · simp [hsa] at hs
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at hs
    | some t1 =>
      simp [hu] at hs
      subst hs
      have hle := updS_block_le s t1 hu
      have heq := updS_eq s t1 hu
      refine ⟨fun _ => hle, ?_⟩
      rw [heq]
      by_cases heq2 : s.supplyState.speed = a
      · omega
      · simp [heq2]
  · simp [hsa] at hs
    subst hs
    refine ⟨fun h => absurd h hsa, ?_⟩
    have heq : s.supplyState.speed = a := by omega
    simp [heq]

theorem setB_eq (s : St) (b : Nat) (t : St) (hb : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = ({ s with borrowState := if s.borrowState.speed = b then s.borrowState else {(accrueSide s.borrowState s.blockNumber (totalBorrows s)) with speed := b} } : St) := by
  unfold setBorrowSpeed at hb
  by_cases hba : s.borrowState.speed ≠ b
  · simp [hba] at hb
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at hb
    | some t1 =>
      simp [hu] at hb
      subst hb
      have hle := updB_block_le s t1 hu
      have heq := updB_eq s t1 hu
      refine ⟨fun _ => hle, ?_⟩
      rw [heq]
      by_cases heq2 : s.borrowState.speed = b
      · omega
      · simp [heq2]
  · simp [hba] at hb
    subst hb
    refine ⟨fun h => absurd h hba, ?_⟩
    have heq : s.borrowState.speed = b := by omega
    simp [heq]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  cases hs : setSupplySpeed s a with
  | none => simp [hs] at h
  | some t1 =>
    simp [hs] at h
    cases hb : setBorrowSpeed t1 b with
    | none => simp [hb] at h
    | some t2 =>
      simp [hb] at h
      subst h
      have ⟨hsle, hseq⟩ := setS_eq s a t1 hs
      have ⟨hble, hbeq⟩ := setB_eq t1 b t2 hb
      have ht1_accts : t1.accts = s.accts := by rw [hseq]
      have ht1_bor : t1.borrowState = s.borrowState := by rw [hseq]
      have ht1_bn : t1.blockNumber = s.blockNumber := by rw [hseq]
      have htot : totalBorrows t1 = totalBorrows s := by simp [totalBorrows, ht1_accts]
      have hsup_le : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) := hsle
      have hbor_le : (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) := by
        intro hne
        have hne1 : t1.borrowState.speed ≠ b := by rw [ht1_bor]; exact hne
        have := hble hne1
        rw [ht1_bor, ht1_bn] at this
        exact this
      refine ⟨hsup_le, hbor_le, ?_⟩
      have hbeq_s : t2 = ({ t1 with borrowState := if s.borrowState.speed = b then s.borrowState else {(accrueSide s.borrowState s.blockNumber (totalBorrows s)) with speed := b} } : St) := by
        rw [hbeq, ht1_bor, ht1_bn, htot]
      rw [hbeq_s, hseq]

theorem acct_sup_le (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  simp only [St.acct]
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hmem | hdef
  · have h2 := hc.2.2 _ hmem
    simpa using h2.1
  · rw [hdef]
    exact Nat.zero_le _

theorem acct_bor_le (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  simp only [St.acct]
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hmem | hdef
  · have h2 := hc.2.2 _ hmem
    simpa using h2.2
  · rw [hdef]
    exact Nat.zero_le _

theorem updS_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ t, updateCompSupplyIndex s = some t := by
  unfold updateCompSupplyIndex subChecked
  simp [h]
  by_cases h1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
  · simp [h1]
  · simp [h1]
    by_cases h2 : 0 < s.blockNumber - s.supplyState.block
    · simp [h2]
    · simp [h2]

theorem updB_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ t, updateCompBorrowIndex s = some t := by
  unfold updateCompBorrowIndex subChecked
  simp [h]
  by_cases h1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
  · simp [h1]
  · simp [h1]
    by_cases h2 : 0 < s.blockNumber - s.borrowState.block
    · simp [h2]
    · simp [h2]

theorem distS_some (s : St) (who : Nat) (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    ∃ u, distributeSupplierComp s who = some u := by
  unfold distributeSupplierComp subChecked mulDouble
  by_cases hr : (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
  · obtain ⟨hz, hle⟩ := hr
    simp only [hz, hle, ↓reduceIte, true_and] at h ⊢
    simp [hle]
  · have heq : accrualStart (s.acct who).supplierIndex s.supplyState.index = (s.acct who).supplierIndex := by
      unfold accrualStart
      by_cases hz : (s.acct who).supplierIndex = 0
      · simp [hz] at hr
        simp [hz]
        omega
      · simp [hz]
    have hle : (s.acct who).supplierIndex ≤ s.supplyState.index := by rw [←heq]; exact h
    simp only [hr, ↓reduceIte] at h ⊢
    rw [if_pos hle]
    exact ⟨_, rfl⟩

theorem distB_some (s : St) (who : Nat) (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    ∃ u, distributeBorrowerComp s who = some u := by
  unfold distributeBorrowerComp subChecked mulDouble
  by_cases hr : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · obtain ⟨hz, hle⟩ := hr
    simp only [hz, hle, ↓reduceIte, true_and] at h ⊢
    simp [hle]
  · have heq : accrualStart (s.acct who).borrowerIndex s.borrowState.index = (s.acct who).borrowerIndex := by
      unfold accrualStart
      by_cases hz : (s.acct who).borrowerIndex = 0
      · simp [hz] at hr
        simp [hz]
        omega
      · simp [hz]
    have hle : (s.acct who).borrowerIndex ≤ s.borrowState.index := by rw [←heq]; exact h
    simp only [hr, ↓reduceIte] at h ⊢
    rw [if_pos hle]
    exact ⟨_, rfl⟩

theorem setS_some (s : St) (a : Nat) (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ t, setSupplySpeed s a = some t := by
  unfold setSupplySpeed
  by_cases hsa : s.supplyState.speed ≠ a
  · simp [hsa]
    obtain ⟨t, ht⟩ := updS_some s h
    simp [ht]
  · simp [hsa]

theorem setB_some (s : St) (b : Nat) (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ t, setBorrowSpeed s b = some t := by
  unfold setBorrowSpeed
  by_cases hba : s.borrowState.speed ≠ b
  · simp [hba]
    obtain ⟨t, ht⟩ := updB_some s h
    simp [ht]
  · simp [hba]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsb, hbb, hmem⟩ := hc
  cases c with
  | supplyHook who =>
    have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index := acct_sup_le s who ⟨hsb, hbb, hmem⟩
    obtain ⟨t, ht⟩ := updS_some s hsb
    have hteq := updS_eq s t ht
    have ht_acct : t.acct who = s.acct who := by rw [hteq]; rfl
    have ht_idx : s.supplyState.index ≤ t.supplyState.index := by
      rw [hteq]
      simpa using le_accrueSide s.supplyState s.blockNumber (totalSupply s)
    have hrec2 : (t.acct who).supplierIndex ≤ t.supplyState.index :=
      Nat.le_trans (by rw [ht_acct]; exact hrec) ht_idx
    obtain ⟨u, hu⟩ := distS_some t who (accrualStart_le hrec2)
    simp [comptroller, ht, hu]
  | borrowHook who =>
    have hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index := acct_bor_le s who ⟨hsb, hbb, hmem⟩
    obtain ⟨t, ht⟩ := updB_some s hbb
    have hteq := updB_eq s t ht
    have ht_acct : t.acct who = s.acct who := by rw [hteq]; rfl
    have ht_idx : s.borrowState.index ≤ t.borrowState.index := by
      rw [hteq]
      simpa using le_accrueSide s.borrowState s.blockNumber (totalBorrows s)
    have hrec2 : (t.acct who).borrowerIndex ≤ t.borrowState.index :=
      Nat.le_trans (by rw [ht_acct]; exact hrec) ht_idx
    obtain ⟨u, hu⟩ := distB_some t who (accrualStart_le hrec2)
    simp [comptroller, ht, hu]
  | claim who =>
    have hrecB : (s.acct who).borrowerIndex ≤ s.borrowState.index := acct_bor_le s who ⟨hsb, hbb, hmem⟩
    obtain ⟨b1, hb1⟩ := updB_some s hbb
    have hteqB := updB_eq s b1 hb1
    have ht_acctB : b1.acct who = s.acct who := by rw [hteqB]; rfl
    have ht_idxB : s.borrowState.index ≤ b1.borrowState.index := by
      rw [hteqB]
      simpa using le_accrueSide s.borrowState s.blockNumber (totalBorrows s)
    have hrecB2 : (b1.acct who).borrowerIndex ≤ b1.borrowState.index :=
      Nat.le_trans (by rw [ht_acctB]; exact hrecB) ht_idxB
    obtain ⟨m1, hm1⟩ := distB_some b1 who (accrualStart_le hrecB2)
    have hdistB := (distB_eq b1 who m1 hm1).2
    have hm1_sup : m1.supplyState = s.supplyState := by
      rw [hteqB] at hdistB
      simp [St.withAcct] at hdistB ⊢
      rw [hdistB]
    have hm1_acct_sup : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have h1 : (m1.acct who).supplierIndex = (b1.acct who).supplierIndex := by
        rw [hdistB]
        simp only [St.withAcct, St.acct]
        by_cases hm : who < b1.accts.length
        · rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hm]
        · have hle : b1.accts.length ≤ who := by simpa [Nat.not_lt] using hm
          rw [ProofForgeFin.Ledger.modify_of_length_le _ _ hle]
      rw [h1, ht_acctB]
    have hm1_bn : m1.blockNumber = s.blockNumber := by
      rw [hteqB] at hdistB
      simp [St.withAcct] at hdistB ⊢
      rw [hdistB]
    have hm1_sb : m1.supplyState.block ≤ m1.blockNumber := by
      rw [hm1_sup, hm1_bn]; exact hsb
    obtain ⟨s2, hs2⟩ := updS_some m1 hm1_sb
    have hteqS := updS_eq m1 s2 hs2
    have hrecS0 : (s.acct who).supplierIndex ≤ s.supplyState.index := acct_sup_le s who ⟨hsb, hbb, hmem⟩
    have ht_acctS : s2.acct who = m1.acct who := by rw [hteqS]; rfl
    have ht_idxS : m1.supplyState.index ≤ s2.supplyState.index := by
      rw [hteqS]
      simpa using le_accrueSide m1.supplyState m1.blockNumber (totalSupply m1)
    have hm1_idx_eq : m1.supplyState.index = s.supplyState.index := by rw [hm1_sup]
    have hrecS2 : (s2.acct who).supplierIndex ≤ s2.supplyState.index := by
      rw [ht_acctS, hm1_acct_sup]
      exact Nat.le_trans hrecS0 (by rw [←hm1_idx_eq]; exact ht_idxS)
    obtain ⟨m2, hm2⟩ := distS_some s2 who (accrualStart_le hrecS2)
    simp [comptroller, claimComp, hb1, hm1, hs2, hm2]
  | setSpeeds a b =>
    obtain ⟨t1, ht1⟩ := setS_some s a hsb
    have hteq1 := (setS_eq s a t1 ht1).2
    have ht1_bor : t1.borrowState = s.borrowState := by rw [hteq1]
    have ht1_bn : t1.blockNumber = s.blockNumber := by rw [hteq1]
    have hbb2 : t1.borrowState.block ≤ t1.blockNumber := by rw [ht1_bor, ht1_bn]; exact hbb
    obtain ⟨t2, ht2⟩ := setB_some t1 b hbb2
    simp [comptroller, setCompSpeedInternal, ht1, ht2]
def scale : Nat := doubleScale

theorem scale_pos : 0 < scale := by
  unfold scale doubleScale
  exact Nat.pow_pos (by decide)

def pendSup (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)

def pendBor (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def pend (s : St) (a : Acct) : Nat := pendSup s a + pendBor s a

def unindexedSup (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def unindexedBor (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def pot (s : St) : Nat :=
  (s.accts.map fun a => a.accrued + a.wallet).sum * scale +
  (s.accts.map (pend s)).sum + scale * (unindexedSup s + unindexedBor s)

def inv (g : Nat × Nat) (s : St) : Prop :=
  s.supplyState.speed = g.1 ∧ s.borrowState.speed = g.2 ∧
  s.supplyState.block ≤ s.blockNumber ∧ s.borrowState.block ≤ s.blockNumber ∧
  ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index

theorem scale_eq : scale = doubleScale := rfl

theorem pendSup_eq_pending (s : St) (a : Acct) :
    pendSup s a = ProofForgeFin.DeFi.Rewards.pending a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index := by
  simp [pendSup, ProofForgeFin.DeFi.Rewards.pending]

theorem creditFor_eq_credit (units start index : Nat) :
    creditFor units start index = ProofForgeFin.DeFi.Rewards.credit scale units start index := by
  simp [creditFor, ProofForgeFin.DeFi.Rewards.credit, scale]

theorem accrualStart_eq_firstStart (recorded index : Nat) :
    accrualStart recorded index = ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex recorded index := by
  simp [accrualStart, ProofForgeFin.DeFi.Rewards.firstStart]

theorem inv_upgrade (L : Legacy) (hw : L.WellFormed) :
    inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  sorry

theorem pot_upgrade_le (L : Legacy) (hw : L.WellFormed) :
    (Legacy.owed L) ≥ ((L.accts.map fun a => 0).sum) := by
  sorry

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
