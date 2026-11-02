import CompRewards.Spec
import ProofForgeFin.Ledger
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Potential

open ProofForgeFin.DeFi.Rewards
open ProofForgeFin.Accumulator
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

theorem modify_congr (l : List Acct) (w : Nat) (f g : Acct → Acct)
    (h : f (l.getD w noAcct) = g (l.getD w noAcct)) :
    l.modify w f = l.modify w g := by
  induction l generalizing w with
  | nil =>
    cases w <;> rfl
  | cons a as ih =>
    cases w with
    | zero => simp_all
    | succ n => simp_all

theorem updSup_some (s s' : St) (h : updateCompSupplyIndex s = some s') :
    s.supplyState.block ≤ s.blockNumber ∧
    s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  simp only [updateCompSupplyIndex, subChecked, accrueSide, totalSupply, fraction, doubleScale] at h ⊢
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    by_cases hd : s.blockNumber - s.supplyState.block > 0
    · simp only [hd, ↓reduceIte, true_and] at h ⊢
      by_cases hs : s.supplyState.speed > 0
      · simp only [hs, ↓reduceIte, true_and] at h ⊢
        by_cases ht : (List.map Acct.supply s.accts).sum > 0
        · simp only [ht, ↓reduceIte] at h ⊢
          exact (Option.some_inj.mp h).symm
        · simp only [ht, ↓reduceIte, Nat.add_zero] at h
          simp_all
      · simp only [hs, ↓reduceIte] at h
        have hs0 : ¬ 0 < s.supplyState.speed := by simpa using hs
        simp only [hs0, false_and] at ⊢
        exact (Option.some_inj.mp h).symm
    · simp only [hd, ↓reduceIte, false_and] at h ⊢
      have h2 : s = s' := Option.some_inj.mp h
      subst h2
      have hbb : s.supplyState.block = s.blockNumber := by omega
      obtain ⟨bn, sup, bor, res, accts⟩ := s
      obtain ⟨idx, blk, spd⟩ := sup
      simp_all
  · simp only [hle, ↓reduceIte] at h
    simp_all

theorem updBor_some (s s' : St) (h : updateCompBorrowIndex s = some s') :
    s.borrowState.block ≤ s.blockNumber ∧
    s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  simp only [updateCompBorrowIndex, subChecked, accrueSide, totalBorrows, fraction, doubleScale] at h ⊢
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    by_cases hd : s.blockNumber - s.borrowState.block > 0
    · simp only [hd, ↓reduceIte, true_and] at h ⊢
      by_cases hs : s.borrowState.speed > 0
      · simp only [hs, ↓reduceIte, true_and] at h ⊢
        by_cases ht : (List.map Acct.borrow s.accts).sum > 0
        · simp only [ht, ↓reduceIte] at h ⊢
          exact (Option.some_inj.mp h).symm
        · simp only [ht, ↓reduceIte, Nat.add_zero] at h
          simp_all
      · simp only [hs, ↓reduceIte] at h
        have hs0 : ¬ 0 < s.borrowState.speed := by simpa using hs
        simp only [hs0, false_and] at ⊢
        exact (Option.some_inj.mp h).symm
    · simp only [hd, ↓reduceIte, false_and] at h ⊢
      have h2 : s = s' := Option.some_inj.mp h
      subst h2
      have hbb : s.borrowState.block = s.blockNumber := by omega
      obtain ⟨bn, sup, bor, res, accts⟩ := s
      obtain ⟨idx, blk, spd⟩ := bor
      simp_all
  · simp only [hle, ↓reduceIte] at h
    simp_all

theorem distSup_accts (s : St) (who : Nat) :
    s.accts.modify who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) = s.accts.modify who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) := by
  apply modify_congr
  have e1 : (s.accts.getD who noAcct).supply = (s.acct who).supply := rfl
  have e2 : (s.accts.getD who noAcct).supplierIndex = (s.acct who).supplierIndex := rfl
  simp only [mulDouble, creditFor, doubleScale, e1, e2]

theorem distBor_accts (s : St) (who : Nat) :
    s.accts.modify who (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)) = s.accts.modify who (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) := by
  apply modify_congr
  have e1 : (s.accts.getD who noAcct).borrow = (s.acct who).borrow := rfl
  have e2 : (s.accts.getD who noAcct).borrowerIndex = (s.acct who).borrowerIndex := rfl
  simp only [mulDouble, creditFor, doubleScale, e1, e2]

theorem distSup_some (s s' : St) (who : Account) (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧ s' = { s with accts := s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct) } := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    unfold accrualStart compInitialIndex
    by_cases hr : (s.acct who).supplierIndex = 0
    · simp only [hr, ↓reduceIte, true_and]
    · simp only [hr, ↓reduceIte, false_and]
  simp only [distributeSupplierComp, subChecked, St.withAcct] at h
  rw [hstart] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    have h2 := Option.some_inj.mp h
    rw [← h2, distSup_accts]
  · simp only [hle, ↓reduceIte] at h
    simp_all

theorem accrueSup_le (s : St) : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrueBor_le (s : St) : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrualStart_le (recorded index : Nat) (h : recorded ≤ index) : accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp only [hr, ↓reduceIte]
    split
    · omega
    · omega
  · simp only [hr, ↓reduceIte]
    exact h

theorem updSup_isSome (s : St) (h : s.supplyState.block ≤ s.blockNumber) : (updateCompSupplyIndex s).isSome := by
  simp only [updateCompSupplyIndex, subChecked, h, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem updBor_isSome (s : St) (h : s.borrowState.block ≤ s.blockNumber) : (updateCompBorrowIndex s).isSome := by
  simp only [updateCompBorrowIndex, subChecked, h, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem grant_accts (s : St) (who : Nat) : s.accts.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) = s.accts.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) := by
  apply modify_congr
  have e : (s.accts.getD who noAcct).accrued = (s.acct who).accrued := rfl
  simp only [e]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  simp only [grantCompInternal, grant]
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [h]
    simp only [true_and, ↓reduceIte, grant_accts]
  · simp only [h]
    simp only [↓reduceIte] at *

theorem setSupply_ok (s t1 : St) (a : Nat) (h : setSupplySpeed s a = some t1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧ t1 = { s with supplyState := if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  simp only [setSupplySpeed] at h
  by_cases he : s.supplyState.speed ≠ a
  · rw [if_pos he] at h
    cases hU : updateCompSupplyIndex s with
    | none => simp [hU] at h
    | some u1 =>
      simp [hU] at h
      obtain ⟨hu1, hu2⟩ := updSup_some s u1 hU
      refine ⟨fun _ => hu1, ?_⟩
      have he2 : ¬ s.supplyState.speed = a := he
      rw [if_neg he2, ← h, hu2]
  · rw [if_neg he] at h
    have he2 : s.supplyState.speed = a := by simpa using he
    have h2 : t1 = s := (Option.some_inj.mp h).symm
    refine ⟨fun hc => absurd he2 hc, ?_⟩
    have hif : (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) = s.supplyState := if_pos he2
    rw [h2, hif]

theorem setBor_ok (s t1 : St) (b : Nat) (h : setBorrowSpeed s b = some t1) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧ t1 = { s with borrowState := if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  simp only [setBorrowSpeed] at h
  by_cases he : s.borrowState.speed ≠ b
  · rw [if_pos he] at h
    cases hU : updateCompBorrowIndex s with
    | none => simp [hU] at h
    | some u1 =>
      simp [hU] at h
      obtain ⟨hu1, hu2⟩ := updBor_some s u1 hU
      refine ⟨fun _ => hu1, ?_⟩
      have he2 : ¬ s.borrowState.speed = b := he
      rw [if_neg he2, ← h, hu2]
  · rw [if_neg he] at h
    have he2 : s.borrowState.speed = b := by simpa using he
    have h2 : t1 = s := (Option.some_inj.mp h).symm
    refine ⟨fun hc => absurd he2 hc, ?_⟩
    have hif : (if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) = s.borrowState := if_pos he2
    rw [h2, hif]

theorem distBor_some (s s' : St) (who : Account) (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧ s' = { s with accts := s.accts.modify who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct) } := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
    unfold accrualStart compInitialIndex
    by_cases hr : (s.acct who).borrowerIndex = 0
    · simp only [hr, ↓reduceIte, true_and]
    · simp only [hr, ↓reduceIte, false_and]
  simp only [distributeBorrowerComp, subChecked, St.withAcct] at h
  rw [hstart] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    have h2 := Option.some_inj.mp h
    rw [← h2, distBor_accts]
  · simp only [hle, ↓reduceIte] at h
    simp_all

theorem hookSupply_ok (s : St) (who : Account) :
    comptroller s (.supplyHook who) = (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) := rfl

theorem hookBorrow_ok (s : St) (who : Account) :
    comptroller s (.borrowHook who) = (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) := rfl

theorem modify_getD_field (l : List Acct) (w : Nat) (F : Acct → Acct) (get : Acct → Nat) (hF : ∀ a, get (F a) = get a) : get ((l.modify w F).getD w noAcct) = get (l.getD w noAcct) := by
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases hmem : w = w ∧ w < l.length
  · rw [if_pos hmem]
    exact hF _
  · rw [if_neg hmem]

theorem distBor_pres_supplierIdx (b1 b2 : St) (who : Account) (h : distributeBorrowerComp b1 who = some b2) : (b2.acct who).supplierIndex = (b1.acct who).supplierIndex := by
  obtain ⟨_, hE⟩ := distBor_some b1 b2 who h
  have hM : b2.accts = b1.accts.modify who fun a => ({ a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index } : Acct) := by rw [hE]
  simp only [St.acct, hM]
  apply modify_getD_field
  intro a
  rfl

theorem distBor_pres_supply (b1 b2 : St) (who : Account) (h : distributeBorrowerComp b1 who = some b2) : (b2.acct who).supply = (b1.acct who).supply := by
  obtain ⟨_, hE⟩ := distBor_some b1 b2 who h
  have hM : b2.accts = b1.accts.modify who fun a => ({ a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index } : Acct) := by rw [hE]
  simp only [St.acct, hM]
  apply modify_getD_field
  intro a
  rfl

theorem distSup_pres_borrow (c1 c2 : St) (who : Account) (h : distributeSupplierComp c1 who = some c2) : (c2.acct who).borrow = (c1.acct who).borrow := by
  obtain ⟨_, hE⟩ := distSup_some c1 c2 who h
  have hM : c2.accts = c1.accts.modify who fun a => ({ a with supplierIndex := c1.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex c1.supplyState.index) c1.supplyState.index } : Acct) := by rw [hE]
  simp only [St.acct, hM]
  apply modify_getD_field
  intro a
  rfl

theorem distSup_isSome (s : St) (who : Account) (h : (s.acct who).supplierIndex ≤ s.supplyState.index) : (distributeSupplierComp s who).isSome := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    unfold accrualStart compInitialIndex
    by_cases hr : (s.acct who).supplierIndex = 0
    · simp only [hr, ↓reduceIte, true_and]
    · simp only [hr, ↓reduceIte, false_and]
  have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := accrualStart_le _ _ h
  simp only [distributeSupplierComp, subChecked, hstart, hle, ↓reduceIte]
  rfl

theorem distBor_isSome (s : St) (who : Account) (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) : (distributeBorrowerComp s who).isSome := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
    unfold accrualStart compInitialIndex
    by_cases hr : (s.acct who).borrowerIndex = 0
    · simp only [hr, ↓reduceIte, true_and]
    · simp only [hr, ↓reduceIte, false_and]
  have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := accrualStart_le _ _ h
  simp only [distributeBorrowerComp, subChecked, hstart, hle, ↓reduceIte]
  rfl

theorem supIdx_le (s : St) (who : Account) (hc : Consistent s) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨h1, h2, h3⟩ := hc
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (h3 _ hm).1
  · rw [hm]
    exact Nat.zero_le _

theorem borIdx_le (s : St) (who : Account) (hc : Consistent s) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨h1, h2, h3⟩ := hc
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (h3 _ hm).2
  · rw [hm]
    exact Nat.zero_le _

theorem setSupply_isSome (s : St) (a : Nat) (h : s.supplyState.block ≤ s.blockNumber) : (setSupplySpeed s a).isSome := by
  simp only [setSupplySpeed]
  by_cases he : s.supplyState.speed ≠ a
  · rw [if_pos he]
    cases hU : updateCompSupplyIndex s with
    | none => have hI := updSup_isSome s h; simp [hU] at hI
    | some u1 => simp [hU]
  · simp only [he, ↓reduceIte]
    rfl

theorem setBor_isSome (s : St) (b : Nat) (h : s.borrowState.block ≤ s.blockNumber) : (setBorrowSpeed s b).isSome := by
  simp only [setBorrowSpeed]
  by_cases he : s.borrowState.speed ≠ b
  · rw [if_pos he]
    cases hU : updateCompBorrowIndex s with
    | none => have hI := updBor_isSome s h; simp [hU] at hI
    | some u1 => simp [hU]
  · simp only [he, ↓reduceIte]
    rfl

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hSupB, hBorB, hIdx⟩ := hc
  have hcC : Consistent s := ⟨hSupB, hBorB, hIdx⟩
  cases c with
  | supplyHook who =>
    have hcH : comptroller s (.supplyHook who) = (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) := rfl
    rw [hcH]
    cases hU : updateCompSupplyIndex s with
    | none => have hI := updSup_isSome s hSupB; simp [hU] at hI
    | some s1 =>
      have hIdx1 : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
        obtain ⟨_, hU2⟩ := updSup_some s s1 hU
        have eA : s1.accts = s.accts := by rw [hU2]
        have eS : s.supplyState.index ≤ s1.supplyState.index := by rw [hU2]; exact accrueSup_le s
        have h0 := supIdx_le s who hcC
        have eAcct : s1.acct who = s.acct who := by simp only [St.acct, eA]
        rw [eAcct]
        omega
      cases hD : distributeSupplierComp s1 who with
      | none => have hI := distSup_isSome s1 who hIdx1; simp [hD] at hI
      | some s2 => simp [hU, hD]
  | borrowHook who =>
    have hcH : comptroller s (.borrowHook who) = (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) := rfl
    rw [hcH]
    cases hU : updateCompBorrowIndex s with
    | none => have hI := updBor_isSome s hBorB; simp [hU] at hI
    | some s1 =>
      have hIdx1 : (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
        obtain ⟨_, hU2⟩ := updBor_some s s1 hU
        have eA : s1.accts = s.accts := by rw [hU2]
        have eS : s.borrowState.index ≤ s1.borrowState.index := by rw [hU2]; exact accrueBor_le s
        have h0 := borIdx_le s who hcC
        have eAcct : s1.acct who = s.acct who := by simp only [St.acct, eA]
        rw [eAcct]
        omega
      cases hD : distributeBorrowerComp s1 who with
      | none => have hI := distBor_isSome s1 who hIdx1; simp [hD] at hI
      | some s2 => simp [hU, hD]
  | claim who =>
    have hcH : comptroller s (.claim who) = claimComp s who := rfl
    rw [hcH]
    cases hb1 : updateCompBorrowIndex s with
    | none => have hI := updBor_isSome s hBorB; simp [hb1] at hI
    | some b1 =>
      have hIdxB : (b1.acct who).borrowerIndex ≤ b1.borrowState.index := by
        obtain ⟨_, hU2⟩ := updBor_some s b1 hb1
        have eA : b1.accts = s.accts := by rw [hU2]
        have eS : s.borrowState.index ≤ b1.borrowState.index := by rw [hU2]; exact accrueBor_le s
        have h0 := borIdx_le s who hcC
        have eAcct : b1.acct who = s.acct who := by simp only [St.acct, eA]
        rw [eAcct]
        omega
      cases hd1 : distributeBorrowerComp b1 who with
      | none => have hI := distBor_isSome b1 who hIdxB; simp [hd1] at hI
      | some b2 =>
        have hSupB2 : b2.supplyState.block ≤ b2.blockNumber := by
          obtain ⟨_, hE⟩ := distBor_some b1 b2 who hd1
          obtain ⟨_, hU2⟩ := updBor_some s b1 hb1
          have e1 : b2.supplyState = b1.supplyState := by rw [hE]
          have e2 : b1.supplyState = s.supplyState := by rw [hU2]
          have e3 : b2.blockNumber = b1.blockNumber := by rw [hE]
          have e4 : b1.blockNumber = s.blockNumber := by rw [hU2]
          rw [e1, e2, e3, e4]
          exact hSupB
        cases hu2 : updateCompSupplyIndex b2 with
        | none => have hI := updSup_isSome b2 hSupB2; simp [hu2] at hI
        | some c1 =>
          have hIdxS : (c1.acct who).supplierIndex ≤ c1.supplyState.index := by
            obtain ⟨_, hU2⟩ := updSup_some b2 c1 hu2
            obtain ⟨_, hEB⟩ := distBor_some b1 b2 who hd1
            obtain ⟨_, hUB⟩ := updBor_some s b1 hb1
            have eA : c1.accts = b2.accts := by rw [hU2]
            have eB2S : b2.supplyState = s.supplyState := by rw [hEB, hUB]
            have eS' : s.supplyState.index ≤ c1.supplyState.index := by
              rw [← eB2S, hU2]
              exact accrueSup_le b2
            have eB2A : (b2.acct who).supplierIndex = (s.acct who).supplierIndex := by
              have e1 := distBor_pres_supplierIdx b1 b2 who hd1
              have e2 : b1.accts = s.accts := by rw [hUB]
              have e3 : b1.acct who = s.acct who := by simp only [St.acct, e2]
              rw [e1, e3]
            have h0 := supIdx_le s who hcC
            have eAcct : c1.acct who = b2.acct who := by simp only [St.acct, eA]
            rw [eAcct, eB2A]
            omega
          cases hd2 : distributeSupplierComp c1 who with
          | none => have hI := distSup_isSome c1 who hIdxS; simp [hd2] at hI
          | some c2 => simp [claimComp, hb1, hd1, hu2, hd2]
  | setSpeeds a b =>
    have hcH : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl
    rw [hcH]
    simp only [setCompSpeedInternal]
    cases hS : setSupplySpeed s a with
    | none => have hI := setSupply_isSome s a hSupB; simp [hS] at hI
    | some t1 =>
      have hBorB1 : t1.borrowState.block ≤ t1.blockNumber := by
        obtain ⟨_, hE⟩ := setSupply_ok s t1 a hS
        have e1 : t1.borrowState = s.borrowState := by rw [hE]
        have e2 : t1.blockNumber = s.blockNumber := by rw [hE]
        rw [e1, e2]
        exact hBorB
      cases hB : setBorrowSpeed t1 b with
      | none => have hI := setBor_isSome t1 b hBorB1; simp [hB] at hI
      | some t2 => simp [hS, hB]
theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  rw [hookSupply_ok] at h
  cases hU : updateCompSupplyIndex s with
  | none => simp [hU] at h
  | some s1 =>
    simp [hU] at h
    obtain ⟨hU1, hU2⟩ := updSup_some s s1 hU
    obtain ⟨hD1, hD2⟩ := distSup_some s1 s' who h
    have eA : s1.accts = s.accts := by rw [hU2]
    have eS : s1.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by rw [hU2]
    have eB : s1.blockNumber = s.blockNumber := by rw [hU2]
    have eBo : s1.borrowState = s.borrowState := by rw [hU2]
    have eR : s1.reserve = s.reserve := by rw [hU2]
    have eAcct : s1.acct who = s.acct who := by simp only [St.acct, eA]
    unfold SupplyDistributed
    refine ⟨hU1, ?_, ?_⟩
    · rw [eAcct, eS] at hD1
      exact hD1
    · rw [hD2, eB, eS, eBo, eR, eA]
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  rw [hookBorrow_ok] at h
  cases hU : updateCompBorrowIndex s with
  | none => simp [hU] at h
  | some s1 =>
    simp [hU] at h
    obtain ⟨hU1, hU2⟩ := updBor_some s s1 hU
    obtain ⟨hD1, hD2⟩ := distBor_some s1 s' who h
    have eA : s1.accts = s.accts := by rw [hU2]
    have eS : s1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hU2]
    have eB : s1.blockNumber = s.blockNumber := by rw [hU2]
    have eSo : s1.supplyState = s.supplyState := by rw [hU2]
    have eR : s1.reserve = s.reserve := by rw [hU2]
    have eAcct : s1.acct who = s.acct who := by simp only [St.acct, eA]
    unfold BorrowDistributed
    refine ⟨hU1, ?_, ?_⟩
    · rw [eAcct, eS] at hD1
      exact hD1
    · rw [hD2, eB, eS, eSo, eR, eA]
theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  have hc : comptroller s (.claim who) = claimComp s who := rfl
  rw [hc] at h
  simp only [claimComp] at h
  cases hU1 : updateCompBorrowIndex s with
  | none => simp [hU1] at h
  | some b1 =>
    simp [hU1] at h
    cases hD1 : distributeBorrowerComp b1 who with
    | none => simp [hD1] at h
    | some b2 =>
      simp [hD1] at h
      cases hU2 : updateCompSupplyIndex b2 with
      | none => simp [hU2] at h
      | some c1 =>
        simp [hU2] at h
        cases hD2 : distributeSupplierComp c1 who with
        | none => simp [hD2] at h
        | some c2 =>
          simp [hD2] at h
          obtain ⟨huB1, huB2⟩ := updBor_some s b1 hU1
          obtain ⟨hdB1, hdB2⟩ := distBor_some b1 b2 who hD1
          obtain ⟨huS1, huS2⟩ := updSup_some b2 c1 hU2
          obtain ⟨hdS1, hdS2⟩ := distSup_some c1 c2 who hD2
          have eA : b1.accts = s.accts := by rw [huB2]
          have eBS : b1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [huB2]
          have eBB : b1.blockNumber = s.blockNumber := by rw [huB2]
          have eBSo : b1.supplyState = s.supplyState := by rw [huB2]
          have eBR : b1.reserve = s.reserve := by rw [huB2]
          have eBAcct : b1.acct who = s.acct who := by simp only [St.acct, eA]
          have fA : c1.accts = b2.accts := by rw [huS2]
          have fS : c1.supplyState = accrueSide b2.supplyState b2.blockNumber (totalSupply b2) := by rw [huS2]
          have fB : c1.blockNumber = b2.blockNumber := by rw [huS2]
          have fBo : c1.borrowState = b2.borrowState := by rw [huS2]
          have fR : c1.reserve = b2.reserve := by rw [huS2]
          have fAcct : c1.acct who = b2.acct who := by simp only [St.acct, fA]
          refine ⟨b2, c2, ?_, ?_, ?_⟩
          · unfold BorrowDistributed
            refine ⟨huB1, ?_, ?_⟩
            · rw [eBAcct, eBS] at hdB1
              exact hdB1
            · rw [hdB2, eBB, eBSo, eBS, eBR, eA]
          · unfold SupplyDistributed
            refine ⟨huS1, ?_, ?_⟩
            · rw [fAcct, fS] at hdS1
              exact hdS1
            · rw [hdS2, fB, fS, fBo, fR, fA]
          · rw [grant_eq] at h
            exact h.symm
theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  have hc : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl
  rw [hc] at h
  simp only [setCompSpeedInternal] at h
  cases hS : setSupplySpeed s a with
  | none => simp [hS] at h
  | some t1 =>
    simp [hS] at h
    cases hB : setBorrowSpeed t1 b with
    | none => simp [hB] at h
    | some t2 =>
      simp [hB] at h
      obtain ⟨hs1, hs2⟩ := setSupply_ok s t1 a hS
      obtain ⟨hb1, hb2⟩ := setBor_ok t1 t2 b hB
      have eB : t1.blockNumber = s.blockNumber := by rw [hs2]
      have eA : t1.accts = s.accts := by rw [hs2]
      have eBo : t1.borrowState = s.borrowState := by rw [hs2]
      have eR : t1.reserve = s.reserve := by rw [hs2]
      have eS : t1.supplyState = if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } := by rw [hs2]
      have eTot : totalBorrows t1 = totalBorrows s := by simp only [totalBorrows, eA]
      unfold SpeedsSet
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exact hs1 hne
      · intro hne
        rw [eBo, eB] at hb1
        exact hb1 hne
      · rw [← h, hb2, eB, eS, eBo, eR, eA, eTot]
/-- Supply-side pending rewards of an account for the potential: units times the index
gained since the protocol's start (`firstStart`), at index scale. -/
def ptermS (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index)

/-- Borrow-side pending rewards of an account for the potential. -/
def ptermB (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index)

/-- Scaled rewards credited to an account. -/
def ptermC (a : Acct) : Nat := (a.accrued + a.wallet) * doubleScale

/-- Potential term of an account. -/
def pterm (s : St) (a : Acct) : Nat := ptermC a + (ptermS s a + ptermB s a)

/-- COMP emitted on the supply side and not yet in the index. -/
def unidxS (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- COMP emitted on the borrow side and not yet in the index. -/
def unidxB (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- The potential: every account's term plus the scaled unindexed emission. -/
def pot (s : St) : Nat := (s.accts.map (pterm s)).sum + (unidxS s + unidxB s) * doubleScale

/-- Potential term of an account with the supply index varying: the borrow side is fixed
at `J`. Used for the per-step bounds, where one side accrues at a time. -/
def ptermAt (J idx : Nat) (a : Acct) : Nat :=
  (a.accrued + a.wallet) * doubleScale +
    (a.supply * (idx - firstStart compInitialIndex a.supplierIndex idx) +
      a.borrow * (J - firstStart compInitialIndex a.borrowerIndex J))

theorem pterm_eq (s : St) (a : Acct) : pterm s a = ptermAt s.borrowState.index s.supplyState.index a := by
  rfl

theorem accrue_index_add (sd : Side) (now total : Nat) (h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total) :
    (accrueSide sd now total).index = sd.index + (now - sd.block) * sd.speed * doubleScale / total := by
  unfold accrueSide
  rw [if_pos h]

theorem accrue_index_same (sd : Side) (now total : Nat) (h : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)) :
    (accrueSide sd now total).index = sd.index := by
  unfold accrueSide
  rw [if_neg h]

/-- The supply side brought up to date (abbreviation to keep proof terms small). -/
def supA (s : St) : Side := accrueSide s.supplyState s.blockNumber (totalSupply s)

/-- The borrow side brought up to date. -/
def borA (s : St) : Side := accrueSide s.borrowState s.blockNumber (totalBorrows s)

theorem supA_eq (s : St) : supA s = accrueSide s.supplyState s.blockNumber (totalSupply s) := rfl

theorem borA_eq (s : St) : borA s = accrueSide s.borrowState s.blockNumber (totalBorrows s) := rfl

theorem assoc_le_trans (a b c d e : Nat) (h : (a + b) + c ≤ (d + e) + c) :
    a + (b + c) ≤ d + (e + c) :=
  Nat.le_trans (Nat.le_trans (Nat.le_of_eq (Nat.add_assoc _ _ _).symm) h)
    (Nat.le_of_eq (Nat.add_assoc _ _ _))

theorem add_left_comm_le (a b c : Nat) : a + (b + c) ≤ b + (a + c) :=
  Nat.le_of_eq (Nat.add_left_comm _ _ _)

/-- The potential of one account: its term plus the scaled unindexed emission on each side
where it holds a position. -/
def potTo (s : St) (who : Account) : Nat :=
  pterm s (s.acct who) +
    ((if 0 < (s.acct who).supply then unidxS s else 0) +
      (if 0 < (s.acct who).borrow then unidxB s else 0)) * doubleScale

theorem firstStart_mono (rec i i' : Nat) (h : i ≤ i') : firstStart compInitialIndex rec i ≤ firstStart compInitialIndex rec i' := by
  unfold firstStart
  by_cases hr : rec = 0
  · subst hr
    simp only [↓reduceIte]
    by_cases h1 : compInitialIndex ≤ i
    · have h2 : compInitialIndex ≤ i' := Nat.le_trans h1 h
      rw [if_pos h1, if_pos h2]
      exact Nat.le_refl _
    · rw [if_neg h1]
      by_cases h2 : compInitialIndex ≤ i'
      · rw [if_pos h2]
        exact Nat.zero_le _
      · rw [if_neg h2]
        exact Nat.le_refl _
  · rw [if_neg hr, if_neg hr]
    exact Nat.le_refl _

theorem firstStart_self_ge (index : Nat) : index ≤ firstStart compInitialIndex index index := by
  by_cases hr : index = 0
  · subst hr
    unfold firstStart
    simp only [↓reduceIte]
    have hC : ¬ compInitialIndex ≤ 0 := by decide
    rw [if_neg hC]
    exact Nat.le_refl _
  · unfold firstStart
    rw [if_neg hr]
    exact Nat.le_refl _

theorem accrue_block (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrue_same (sd : Side) (now total : Nat) (h : sd.block = now) : accrueSide sd now total = sd := by
  unfold accrueSide
  split
  · rename_i hcond
    omega
  · rename_i hcond
    obtain ⟨idx, blk, spd⟩ := sd
    subst h
    rfl

theorem accrualStart_eq_firstStart (rec idx : Nat) : accrualStart rec idx = firstStart compInitialIndex rec idx := by
  rfl

theorem creditFor_eq_credit (units start index : Nat) : creditFor units start index = credit doubleScale units start index := by
  rfl

theorem doubleScale_pos : 0 < doubleScale := by
  decide

theorem le_of_mul_le (DS X Y : Nat) (hDS : 0 < DS) (h : X * DS ≤ Y * DS + (DS - 1)) : X ≤ Y := by
  by_cases hXY : X ≤ Y
  · exact hXY
  · exfalso
    have hYX : Y + 1 ≤ X := by omega
    have hle : (Y + 1) * DS ≤ X * DS := Nat.mul_le_mul_right _ hYX
    have e : (Y + 1) * DS = Y * DS + DS := by rw [Nat.add_mul, Nat.one_mul]
    omega

theorem pot_supply_hU (s : St) : totalSupply s * ((supA s).index - s.supplyState.index) + doubleScale * 0 ≤ doubleScale * unidxS s := by
  simp only [unidxS]
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · have hAi : (supA s).index = s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s := by
      rw [supA_eq]; exact accrue_index_add _ _ _ hc
    have hdel := total_mul_indexDelta_le doubleScale ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s)
    simp only [indexDelta] at hdel
    have hsub : (s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s) - s.supplyState.index = (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s := Nat.add_sub_cancel_left _ _
    rw [hAi, hsub, Nat.mul_zero, Nat.add_zero, Nat.mul_comm doubleScale ((s.blockNumber - s.supplyState.block) * s.supplyState.speed)]
    exact hdel
  · have hAi : (supA s).index = s.supplyState.index := by
      rw [supA_eq]; exact accrue_index_same _ _ _ hc
    rw [hAi]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    exact Nat.zero_le _

theorem pot_supply_ht (s : St) : ∀ a ∈ s.accts, ptermAt s.borrowState.index (supA s).index a ≤ ptermAt s.borrowState.index s.supplyState.index a + a.supply * ((supA s).index - s.supplyState.index) := by
  intro a ha
  have hi_le : s.supplyState.index ≤ (supA s).index := by rw [supA_eq]; exact accrueSup_le s
  simp only [ptermAt]
  have h1 := owed_le_add (u := a.supply) (i := s.supplyState.index) (i' := (supA s).index) (s := firstStart compInitialIndex a.supplierIndex s.supplyState.index) (s' := firstStart compInitialIndex a.supplierIndex (supA s).index) (firstStart_mono _ _ _ hi_le)
  have h2 := Nat.add_le_add_right h1 (a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index))
  have h2b : a.supply * ((supA s).index - firstStart compInitialIndex a.supplierIndex (supA s).index) + a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index) ≤ (a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index) + a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index)) + a.supply * ((supA s).index - s.supplyState.index) :=
    Nat.le_trans h2 (Nat.le_of_eq (Nat.add_right_comm _ _ _))
  have h4 := Nat.add_le_add_left h2b ((a.accrued + a.wallet) * doubleScale)
  have h5 : (a.accrued + a.wallet) * doubleScale + (a.supply * ((supA s).index - firstStart compInitialIndex a.supplierIndex (supA s).index) + a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index)) ≤ ((a.accrued + a.wallet) * doubleScale + (a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index) + a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index))) + a.supply * ((supA s).index - s.supplyState.index) :=
    Nat.le_trans h4 (Nat.le_of_eq (Nat.add_assoc _ _ _).symm)
  exact h5

theorem pot_supply_hf (s : St) (who : Account) : who < s.accts.length → ptermAt s.borrowState.index (supA s).index ((fun a => ({ a with supplierIndex := (supA s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supA s).index) (supA s).index } : Acct)) (s.accts.getD who noAcct)) ≤ ptermAt s.borrowState.index (supA s).index (s.accts.getD who noAcct) := by
  intro hmem
  simp only [ptermAt]
  have e1 : ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).supply * ((supA s).index - accrualStart (s.accts.getD who noAcct).supplierIndex (supA s).index) / doubleScale) + (s.accts.getD who noAcct).wallet = ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) + (s.accts.getD who noAcct).supply * ((supA s).index - accrualStart (s.accts.getD who noAcct).supplierIndex (supA s).index) / doubleScale :=
    Nat.add_right_comm _ _ _
  have hpq : firstStart compInitialIndex (s.accts.getD who noAcct).supplierIndex (supA s).index ≤ accrualStart (s.accts.getD who noAcct).supplierIndex (supA s).index := by
    rw [accrualStart_eq_firstStart]
    exact Nat.le_refl _
  have hq' : (supA s).index ≤ firstStart compInitialIndex (supA s).index (supA s).index := firstStart_self_ge _
  have hset := settle_scaled_le_of_le (one := doubleScale) (c := (s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) (u := (s.accts.getD who noAcct).supply) (i := (supA s).index) (p := firstStart compInitialIndex (s.accts.getD who noAcct).supplierIndex (supA s).index) (q := accrualStart (s.accts.getD who noAcct).supplierIndex (supA s).index) (q' := firstStart compInitialIndex (supA s).index (supA s).index) hpq hq'
  rw [creditFor_eq_credit]
  simp only [credit]
  rw [e1]
  have h2 := Nat.add_le_add_right hset ((s.accts.getD who noAcct).borrow * (s.borrowState.index - firstStart compInitialIndex (s.accts.getD who noAcct).borrowerIndex s.borrowState.index))
  exact assoc_le_trans _ _ _ _ _ h2

theorem pot_supply_hook (s m : St) (who : Account) (h : SupplyDistributed s who m) : pot m ≤ pot s := by
  obtain ⟨hB, hS, hE⟩ := h
  rw [← supA_eq] at hE hS
  have hpot := pot_accrue_settle_le s.accts who (fun a => ({ a with supplierIndex := (supA s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supA s).index) (supA s).index } : Acct)) noAcct (ptermAt s.borrowState.index) Acct.supply (pot_supply_ht s) (pot_supply_hU s) (pot_supply_hf s who)
  have hMaccts : m.accts = s.accts.modify who (fun a => ({ a with supplierIndex := (supA s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supA s).index) (supA s).index } : Acct)) := by rw [hE]
  have eSidx : m.supplyState.index = (supA s).index := by rw [hE]
  have eJidx : m.borrowState.index = s.borrowState.index := by rw [hE]
  have hSum1 : (m.accts.map (pterm m)).sum = ((s.accts.modify who (fun a => ({ a with supplierIndex := (supA s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supA s).index) (supA s).index } : Acct))).map (ptermAt s.borrowState.index (supA s).index)).sum := by
    rw [hMaccts]
    apply ProofForgeFin.Ledger.sum_map_congr
    intro a ha
    rw [pterm_eq, eSidx, eJidx]
  have hSum2 : (s.accts.map (pterm s)).sum = (s.accts.map (ptermAt s.borrowState.index s.supplyState.index)).sum := by
    apply ProofForgeFin.Ledger.sum_map_congr
    intro a ha
    exact pterm_eq s a
  have eB : m.blockNumber = s.blockNumber := by rw [hE]
  have eS : m.supplyState = supA s := by rw [hE]
  have eBo : m.borrowState = s.borrowState := by rw [hE]
  have hAblock : (supA s).block = s.blockNumber := by rw [supA_eq]; exact accrue_block _ _ _
  have hU0 : unidxS m = 0 := by
    simp only [unidxS, eB, eS, hAblock, Nat.sub_self, Nat.zero_mul]
  have hUB : unidxB m = unidxB s := by
    simp only [unidxB, eB, eBo]
  have hpot' : ((s.accts.modify who (fun a => ({ a with supplierIndex := (supA s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supA s).index) (supA s).index } : Acct))).map (ptermAt s.borrowState.index (supA s).index)).sum + 0 ≤ (s.accts.map (ptermAt s.borrowState.index s.supplyState.index)).sum + unidxS s * doubleScale := by
    have h2 := hpot
    rw [Nat.mul_zero, Nat.mul_comm doubleScale (unidxS s)] at h2
    exact h2
  have hfin := Nat.add_le_add_right hpot' (unidxB s * doubleScale)
  have hfin0 : ((s.accts.modify who (fun a => ({ a with supplierIndex := (supA s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supA s).index) (supA s).index } : Acct))).map (ptermAt s.borrowState.index (supA s).index)).sum + unidxB s * doubleScale ≤ (s.accts.map (ptermAt s.borrowState.index s.supplyState.index)).sum + (unidxS s * doubleScale + unidxB s * doubleScale) :=
    Nat.le_trans (Nat.le_trans (Nat.add_le_add_right (Nat.le_of_eq (Nat.add_zero _).symm) _) hfin) (Nat.le_of_eq (Nat.add_assoc _ _ _))
  clear hB hS hE hpot hMaccts eSidx eJidx eB eS eBo hAblock hpot' hfin
  simp only [pot]
  rw [hSum1, hU0, hUB, hSum2, Nat.zero_add, Nat.add_mul]
  exact hfin0

theorem pot_borrow_hU (s : St) : totalBorrows s * ((borA s).index - s.borrowState.index) + doubleScale * 0 ≤ doubleScale * unidxB s := by
  simp only [unidxB]
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · have hAi : (borA s).index = s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s := by
      rw [borA_eq]; exact accrue_index_add _ _ _ hc
    have hdel := total_mul_indexDelta_le doubleScale ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s)
    simp only [indexDelta] at hdel
    have hsub : (s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s) - s.borrowState.index = (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s := Nat.add_sub_cancel_left _ _
    rw [hAi, hsub, Nat.mul_zero, Nat.add_zero, Nat.mul_comm doubleScale ((s.blockNumber - s.borrowState.block) * s.borrowState.speed)]
    exact hdel
  · have hAi : (borA s).index = s.borrowState.index := by
      rw [borA_eq]; exact accrue_index_same _ _ _ hc
    rw [hAi]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]
    exact Nat.zero_le _

theorem pot_borrow_ht (s : St) : ∀ a ∈ s.accts, ptermAt (borA s).index s.supplyState.index a ≤ ptermAt s.borrowState.index s.supplyState.index a + a.borrow * ((borA s).index - s.borrowState.index) := by
  intro a ha
  have hj_le : s.borrowState.index ≤ (borA s).index := by rw [borA_eq]; exact accrueBor_le s
  simp only [ptermAt]
  have h1 := owed_le_add (u := a.borrow) (i := s.borrowState.index) (i' := (borA s).index) (s := firstStart compInitialIndex a.borrowerIndex s.borrowState.index) (s' := firstStart compInitialIndex a.borrowerIndex (borA s).index) (firstStart_mono _ _ _ hj_le)
  have h2 := Nat.add_le_add_left h1 (a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index))
  have h2b : a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index) + a.borrow * ((borA s).index - firstStart compInitialIndex a.borrowerIndex (borA s).index) ≤ (a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index) + a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index)) + a.borrow * ((borA s).index - s.borrowState.index) :=
    Nat.le_trans h2 (Nat.le_of_eq (Nat.add_assoc _ _ _).symm)
  have h4 := Nat.add_le_add_left h2b ((a.accrued + a.wallet) * doubleScale)
  have h5 : (a.accrued + a.wallet) * doubleScale + (a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index) + a.borrow * ((borA s).index - firstStart compInitialIndex a.borrowerIndex (borA s).index)) ≤ ((a.accrued + a.wallet) * doubleScale + (a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index) + a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index))) + a.borrow * ((borA s).index - s.borrowState.index) :=
    Nat.le_trans h4 (Nat.le_of_eq (Nat.add_assoc _ _ _).symm)
  exact h5

theorem pot_borrow_hf (s : St) (who : Account) : who < s.accts.length → ptermAt (borA s).index s.supplyState.index ((fun a => ({ a with borrowerIndex := (borA s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borA s).index) (borA s).index } : Acct)) (s.accts.getD who noAcct)) ≤ ptermAt (borA s).index s.supplyState.index (s.accts.getD who noAcct) := by
  intro hmem
  simp only [ptermAt]
  have e1 : ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).borrow * ((borA s).index - accrualStart (s.accts.getD who noAcct).borrowerIndex (borA s).index) / doubleScale) + (s.accts.getD who noAcct).wallet = ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) + (s.accts.getD who noAcct).borrow * ((borA s).index - accrualStart (s.accts.getD who noAcct).borrowerIndex (borA s).index) / doubleScale :=
    Nat.add_right_comm _ _ _
  have hpq : firstStart compInitialIndex (s.accts.getD who noAcct).borrowerIndex (borA s).index ≤ accrualStart (s.accts.getD who noAcct).borrowerIndex (borA s).index := by
    rw [accrualStart_eq_firstStart]
    exact Nat.le_refl _
  have hq' : (borA s).index ≤ firstStart compInitialIndex (borA s).index (borA s).index := firstStart_self_ge _
  have hset := settle_scaled_le_of_le (one := doubleScale) (c := (s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet) (u := (s.accts.getD who noAcct).borrow) (i := (borA s).index) (p := firstStart compInitialIndex (s.accts.getD who noAcct).borrowerIndex (borA s).index) (q := accrualStart (s.accts.getD who noAcct).borrowerIndex (borA s).index) (q' := firstStart compInitialIndex (borA s).index (borA s).index) hpq hq'
  rw [creditFor_eq_credit]
  simp only [credit]
  rw [e1]
  have h2 := Nat.add_le_add_left hset ((s.accts.getD who noAcct).supply * (s.supplyState.index - firstStart compInitialIndex (s.accts.getD who noAcct).supplierIndex s.supplyState.index))
  exact Nat.le_trans (add_left_comm_le _ _ _) (Nat.le_trans h2 (add_left_comm_le _ _ _))

theorem pot_borrow_hook (s m : St) (who : Account) (h : BorrowDistributed s who m) : pot m ≤ pot s := by
  obtain ⟨hB, hS, hE⟩ := h
  rw [← borA_eq] at hE hS
  have hpot := pot_accrue_settle_le s.accts who (fun a => ({ a with borrowerIndex := (borA s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borA s).index) (borA s).index } : Acct)) noAcct (fun j a => ptermAt j s.supplyState.index a) Acct.borrow (pot_borrow_ht s) (pot_borrow_hU s) (pot_borrow_hf s who)
  have hMaccts : m.accts = s.accts.modify who (fun a => ({ a with borrowerIndex := (borA s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borA s).index) (borA s).index } : Acct)) := by rw [hE]
  have eJidx : m.borrowState.index = (borA s).index := by rw [hE]
  have eSidx : m.supplyState.index = s.supplyState.index := by rw [hE]
  have hSum1 : (m.accts.map (pterm m)).sum = ((s.accts.modify who (fun a => ({ a with borrowerIndex := (borA s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borA s).index) (borA s).index } : Acct))).map (ptermAt (borA s).index s.supplyState.index)).sum := by
    rw [hMaccts]
    apply ProofForgeFin.Ledger.sum_map_congr
    intro a ha
    rw [pterm_eq, eSidx, eJidx]
  have hSum2 : (s.accts.map (pterm s)).sum = (s.accts.map (ptermAt s.borrowState.index s.supplyState.index)).sum := by
    apply ProofForgeFin.Ledger.sum_map_congr
    intro a ha
    exact pterm_eq s a
  have eB : m.blockNumber = s.blockNumber := by rw [hE]
  have eS : m.supplyState = s.supplyState := by rw [hE]
  have eBo : m.borrowState = borA s := by rw [hE]
  have hAblock : (borA s).block = s.blockNumber := by rw [borA_eq]; exact accrue_block _ _ _
  have hU0 : unidxB m = 0 := by
    simp only [unidxB, eB, eBo, hAblock, Nat.sub_self, Nat.zero_mul]
  have hUB : unidxS m = unidxS s := by
    simp only [unidxS, eB, eS]
  have hpot' : ((s.accts.modify who (fun a => ({ a with borrowerIndex := (borA s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borA s).index) (borA s).index } : Acct))).map (ptermAt (borA s).index s.supplyState.index)).sum + 0 ≤ (s.accts.map (ptermAt s.borrowState.index s.supplyState.index)).sum + unidxB s * doubleScale := by
    have h2 := hpot
    rw [Nat.mul_zero, Nat.mul_comm doubleScale (unidxB s)] at h2
    exact h2
  have hfin := Nat.add_le_add_right hpot' (unidxS s * doubleScale)
  have hfin2 : ((s.accts.modify who (fun a => ({ a with borrowerIndex := (borA s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borA s).index) (borA s).index } : Acct))).map (ptermAt (borA s).index s.supplyState.index)).sum + unidxS s * doubleScale ≤ (s.accts.map (ptermAt s.borrowState.index s.supplyState.index)).sum + (unidxS s * doubleScale + unidxB s * doubleScale) :=
    Nat.le_trans (Nat.le_trans (Nat.add_le_add_right (Nat.le_of_eq (Nat.add_zero _).symm) _) hfin) (Nat.le_trans (Nat.le_of_eq (Nat.add_assoc _ _ _)) (Nat.add_le_add_left (Nat.le_of_eq (Nat.add_comm _ _)) _))
  clear hB hS hE hpot hMaccts eSidx eJidx eB eS eBo hAblock hpot' hfin
  simp only [pot]
  rw [hSum1, hU0, hUB, hSum2, Nat.add_zero, Nat.add_mul]
  exact hfin2

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
