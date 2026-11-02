import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
import ProofForgeFin.Ledger
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Index

open ProofForgeFin.Accumulator.Market
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

/-! ## Helper lemmas: the implementation meets its specification -/

theorem acc_start_eq (r idx : Nat) :
    (if r = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else r) =
      accrualStart r idx := by
  unfold accrualStart
  by_cases h : r = 0
  · simp only [h, true_and]
    by_cases h2 : compInitialIndex ≤ idx <;> simp [h2]
  · simp [h]

theorem modify_congr {α : Type} {l : List α} {w : Nat} {f f' : α → α} {d : α}
    (h : f (l.getD w d) = f' (l.getD w d)) : l.modify w f = l.modify w f' := by
  induction l generalizing w with
  | nil =>
    cases w <;> rfl
  | cons b l ih =>
    cases w with
    | zero =>
      have hb : f b = f' b := by simpa using h
      simp [hb]
    | succ w =>
      have hw : f (l.getD w d) = f' (l.getD w d) := by simpa using h
      simp [ih hw]

theorem updateSupply_spec (s s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) ∧
    s1.blockNumber = s.blockNumber ∧ s1.borrowState = s.borrowState ∧
    s1.reserve = s.reserve ∧ s1.accts = s.accts := by
  unfold updateCompSupplyIndex at h
  cases hsub : subChecked s.blockNumber s.supplyState.block with
  | none =>
    simp [hsub] at h
  | some delta =>
    simp only [hsub] at h
    have hsub2 : s.supplyState.block ≤ s.blockNumber ∧ delta = s.blockNumber - s.supplyState.block := by
      unfold subChecked at hsub
      split at hsub
      · exact ⟨‹_›, (Option.some_inj.mp hsub).symm⟩
      · simp at hsub
    obtain ⟨hb, rfl⟩ := hsub2
    refine ⟨hb, ?_, ?_, ?_, ?_, ?_⟩
    · unfold accrueSide
      by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s
      · have hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed :=
          ⟨hc.1, hc.2.1⟩
        have hz : totalSupply s > 0 := hc.2.2
        simp only [hc, ↓reduceIte] at ⊢
        simp only [hc1, hz, fraction, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc, ↓reduceIte] at ⊢
        by_cases hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
        · simp only [hc1, ↓reduceIte] at h
          have hz : ¬ totalSupply s > 0 := fun hlt => hc ⟨hc1.1, hc1.2, hlt⟩
          simp only [hz, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc1, ↓reduceIte] at h
          by_cases hc2 : 0 < s.blockNumber - s.supplyState.block
          · simp only [hc2, ↓reduceIte] at h
            obtain rfl := Option.some_inj.mp h
            rfl
          · simp only [hc2, ↓reduceIte] at h
            obtain rfl := Option.some_inj.mp h
            have hbeq : s.supplyState.block = s.blockNumber := by omega
            rw [← hbeq]
    · by_cases hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.supplyState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
    · by_cases hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.supplyState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
    · by_cases hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.supplyState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
    · by_cases hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.supplyState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl

theorem St_updateSupply_eq (s s1 : St)
    (h1 : s1.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s))
    (h2 : s1.blockNumber = s.blockNumber) (h3 : s1.borrowState = s.borrowState)
    (h4 : s1.reserve = s.reserve) (h5 : s1.accts = s.accts) :
    s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  cases s <;> cases s1 <;> simp_all

theorem updateBorrow_spec (s s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) ∧
    s1.blockNumber = s.blockNumber ∧ s1.supplyState = s.supplyState ∧
    s1.reserve = s.reserve ∧ s1.accts = s.accts := by
  unfold updateCompBorrowIndex at h
  cases hsub : subChecked s.blockNumber s.borrowState.block with
  | none =>
    simp [hsub] at h
  | some delta =>
    simp only [hsub] at h
    have hsub2 : s.borrowState.block ≤ s.blockNumber ∧ delta = s.blockNumber - s.borrowState.block := by
      unfold subChecked at hsub
      split at hsub
      · exact ⟨‹_›, (Option.some_inj.mp hsub).symm⟩
      · simp at hsub
    obtain ⟨hb, rfl⟩ := hsub2
    refine ⟨hb, ?_, ?_, ?_, ?_, ?_⟩
    · unfold accrueSide
      by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s
      · have hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed :=
          ⟨hc.1, hc.2.1⟩
        have hz : totalBorrows s > 0 := hc.2.2
        simp only [hc, ↓reduceIte] at ⊢
        simp only [hc1, hz, fraction, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc, ↓reduceIte] at ⊢
        by_cases hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
        · simp only [hc1, ↓reduceIte] at h
          have hz : ¬ totalBorrows s > 0 := fun hlt => hc ⟨hc1.1, hc1.2, hlt⟩
          simp only [hz, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc1, ↓reduceIte] at h
          by_cases hc2 : 0 < s.blockNumber - s.borrowState.block
          · simp only [hc2, ↓reduceIte] at h
            obtain rfl := Option.some_inj.mp h
            rfl
          · simp only [hc2, ↓reduceIte] at h
            obtain rfl := Option.some_inj.mp h
            have hbeq : s.borrowState.block = s.blockNumber := by omega
            rw [← hbeq]
    · by_cases hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.borrowState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
    · by_cases hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.borrowState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
    · by_cases hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.borrowState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
    · by_cases hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
      · simp only [hc1, ↓reduceIte] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : 0 < s.blockNumber - s.borrowState.block
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl
        · simp only [hc2, ↓reduceIte] at h
          obtain rfl := Option.some_inj.mp h
          rfl

theorem St_updateBorrow_eq (s s1 : St)
    (h1 : s1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s))
    (h2 : s1.blockNumber = s.blockNumber) (h3 : s1.supplyState = s.supplyState)
    (h4 : s1.reserve = s.reserve) (h5 : s1.accts = s.accts) :
    s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  cases s <;> cases s1 <;> simp_all

theorem distSupplier_spec (s : St) (who : Nat) (s' : St) (start : Nat)
    (hs : start = (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex))
    (h : distributeSupplierComp s who = some s') :
    start ≤ s.supplyState.index ∧ s' = s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - start) } : Acct)) := by
  subst hs
  unfold distributeSupplierComp at h
  cases hsub : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
  | none =>
    simp only [hsub] at h
    cases h
  | some delta =>
    simp only [hsub] at h
    have hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index ∧ delta = s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) := by
      unfold subChecked at hsub
      by_cases hc : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index
      · simp only [hc, ↓reduceIte] at hsub
        exact ⟨hc, (Option.some_inj.mp hsub).symm⟩
      · simp only [hc, ↓reduceIte] at hsub
        cases hsub
    obtain ⟨hle, rfl⟩ := hle
    refine ⟨hle, ?_⟩
    obtain rfl := Option.some_inj.mp h
    rfl

theorem distBorrower_spec (s : St) (who : Nat) (s' : St) (start : Nat)
    (hs : start = (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex))
    (h : distributeBorrowerComp s who = some s') :
    start ≤ s.borrowState.index ∧ s' = s.withAcct who (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - start) } : Acct)) := by
  subst hs
  unfold distributeBorrowerComp at h
  cases hsub : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
  | none =>
    simp only [hsub] at h
    cases h
  | some delta =>
    simp only [hsub] at h
    have hle : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index ∧ delta = s.borrowState.index - (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) := by
      unfold subChecked at hsub
      by_cases hc : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index
      · simp only [hc, ↓reduceIte] at hsub
        exact ⟨hc, (Option.some_inj.mp hsub).symm⟩
      · simp only [hc, ↓reduceIte] at hsub
        cases hsub
    obtain ⟨hle, rfl⟩ := hle
    refine ⟨hle, ?_⟩
    obtain rfl := Option.some_inj.mp h
    rfl

theorem accrualStart_firstStart (r idx : Nat) :
    accrualStart r idx = ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex r idx := by
  unfold accrualStart ProofForgeFin.DeFi.Rewards.firstStart
  by_cases h : r = 0
  · simp only [h]
  · simp [h]

theorem accrueSide_catchUp (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index = ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total ∧ (accrueSide sd now total).block = now := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [if_pos hc]
  · simp [if_neg hc]

theorem accrueSide_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos hc]
    exact Nat.le_add_right _ _
  · rw [if_neg hc]
    exact Nat.le_refl _

theorem updateSupply_some (s : St) (hb : s.supplyState.block ≤ s.blockNumber) :
    ∃ s1, updateCompSupplyIndex s = some s1 := by
  unfold updateCompSupplyIndex subChecked
  simp only [hb, ↓reduceIte]
  by_cases hc1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [hc1, ↓reduceIte]
    exact ⟨_, rfl⟩
  · simp only [hc1, ↓reduceIte]
    by_cases hc2 : s.blockNumber - s.supplyState.block > 0
    · simp only [hc2, ↓reduceIte]
      exact ⟨_, rfl⟩
    · simp only [hc2, ↓reduceIte]
      exact ⟨s, rfl⟩

theorem updateBorrow_some (s : St) (hb : s.borrowState.block ≤ s.blockNumber) :
    ∃ s1, updateCompBorrowIndex s = some s1 := by
  unfold updateCompBorrowIndex subChecked
  simp only [hb, ↓reduceIte]
  by_cases hc1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [hc1, ↓reduceIte]
    exact ⟨_, rfl⟩
  · simp only [hc1, ↓reduceIte]
    by_cases hc2 : s.blockNumber - s.borrowState.block > 0
    · simp only [hc2, ↓reduceIte]
      exact ⟨_, rfl⟩
    · simp only [hc2, ↓reduceIte]
      exact ⟨s, rfl⟩

theorem distSupplier_some (s : St) (who : Nat)
    (hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by
  unfold distributeSupplierComp subChecked
  simp only [hle, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem distBorrower_some (s : St) (who : Nat)
    (hle : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by
  unfold distributeBorrowerComp subChecked
  simp only [hle, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem rec_le_supply (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  obtain ⟨-, -, hrec⟩ := hc
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hrec _ hm).1
  · rw [hm]
    exact Nat.zero_le _

theorem rec_le_borrow (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  obtain ⟨-, -, hrec⟩ := hc
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hrec _ hm).2
  · rw [hm]
    exact Nat.zero_le _

theorem start_le_new_supply (s : St) (who : Nat) (idx : Nat)
    (hidx : s.supplyState.index ≤ idx) (hc : Consistent s) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else (s.acct who).supplierIndex) ≤ idx := by
  have hle : (s.acct who).supplierIndex ≤ idx := Nat.le_trans (rec_le_supply s who hc) hidx
  rw [acc_start_eq, accrualStart_firstStart]
  exact ProofForgeFin.DeFi.Rewards.firstStart_le_index compInitialIndex hle

theorem start_le_new_borrow (s : St) (who : Nat) (idx : Nat)
    (hidx : s.borrowState.index ≤ idx) (hc : Consistent s) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else (s.acct who).borrowerIndex) ≤ idx := by
  have hle : (s.acct who).borrowerIndex ≤ idx := Nat.le_trans (rec_le_borrow s who hc) hidx
  rw [acc_start_eq, accrualStart_firstStart]
  exact ProofForgeFin.DeFi.Rewards.firstStart_le_index compInitialIndex hle

theorem setSupply_some (s : St) (a : Nat) (hb : s.supplyState.block ≤ s.blockNumber) :
    ∃ t, setSupplySpeed s a = some t := by
  unfold setSupplySpeed
  by_cases hne : s.supplyState.speed ≠ a
  · simp [hne] at ⊢
    obtain ⟨s1, hu⟩ := updateSupply_some s hb
    simp [hu]
  · simp [hne]

theorem setBorrow_some (s : St) (b : Nat) (hb : s.borrowState.block ≤ s.blockNumber) :
    ∃ t, setBorrowSpeed s b = some t := by
  unfold setBorrowSpeed
  by_cases hne : s.borrowState.speed ≠ b
  · simp [hne] at ⊢
    obtain ⟨s1, hu⟩ := updateBorrow_some s hb
    simp [hu]
  · simp [hne]

theorem modify_keep_supplier (l : List Acct) (who : Nat) (F : Acct → Acct)
    (hF : ∀ a, (F a).supplierIndex = a.supplierIndex) :
    ((l.modify who F).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex := by
  by_cases hw : who < l.length
  · rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hw, hF]
  · rw [ProofForgeFin.Ledger.modify_of_length_le _ _ (by omega)]

theorem modify_keep_borrower (l : List Acct) (who : Nat) (F : Acct → Acct)
    (hF : ∀ a, (F a).borrowerIndex = a.borrowerIndex) :
    ((l.modify who F).getD who noAcct).borrowerIndex = (l.getD who noAcct).borrowerIndex := by
  by_cases hw : who < l.length
  · rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hw, hF]
  · rw [ProofForgeFin.Ledger.modify_of_length_le _ _ (by omega)]

theorem distBorrower_keep_supplier (t1 m1 : St) (who : Nat)
    (h : distributeBorrowerComp t1 who = some m1) :
    (m1.acct who).supplierIndex = (t1.acct who).supplierIndex := by
  obtain ⟨hle, hdist⟩ := distBorrower_spec t1 who m1 _ rfl h
  rw [hdist]
  unfold St.withAcct St.acct
  by_cases hw : who < t1.accts.length
  · rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hw]
  · rw [ProofForgeFin.Ledger.modify_of_length_le _ _ (by omega)]

theorem distSupplier_keep_borrower (t1 m1 : St) (who : Nat)
    (h : distributeSupplierComp t1 who = some m1) :
    (m1.acct who).borrowerIndex = (t1.acct who).borrowerIndex := by
  obtain ⟨hle, hdist⟩ := distSupplier_spec t1 who m1 _ rfl h
  rw [hdist]
  unfold St.withAcct St.acct
  by_cases hw : who < t1.accts.length
  · rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hw]
  · rw [ProofForgeFin.Ledger.modify_of_length_le _ _ (by omega)]

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hu1 : updateCompSupplyIndex s with
  | none =>
    simp [hu1] at h
  | some s1 =>
    simp only [hu1] at h
    obtain ⟨hb, hs1, hbn, hbo, hr, ha⟩ := updateSupply_spec s s1 hu1
    have hs1eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
      St_updateSupply_eq s s1 hs1 hbn hbo hr ha
    obtain ⟨hle, hdist⟩ := distSupplier_spec s1 who s' _ rfl h
    have eAcct : s1.acct who = s.acct who := by simp only [St.acct, ha]
    have eIdx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hs1eq]
    have hstart : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [eAcct, eIdx, acc_start_eq]
    refine ⟨hb, ?_, ?_⟩
    · rw [hstart] at hle
      rw [eIdx] at hle
      exact hle
    · unfold St.withAcct at hdist
      rw [ha] at hdist
      have hFG : (s.accts.modify who fun a => ({ a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct)) = (s.accts.modify who fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct)) := by
        apply modify_congr (d := noAcct)
        have e0 : s1.acct who = s.accts.getD who noAcct := by simp only [St.acct, ha]
        show ({ (s.accts.getD who noAcct) with supplierIndex := s1.supplyState.index, accrued := (s.accts.getD who noAcct).accrued + mulDouble (s1.acct who).supply (s1.supplyState.index - (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex)) } : Acct) = ({ (s.accts.getD who noAcct) with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).supply (accrualStart (s.accts.getD who noAcct).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct)
        have e0s : (s1.acct who).supply = (s.accts.getD who noAcct).supply := by rw [e0]
        have e0i : (s1.acct who).supplierIndex = (s.accts.getD who noAcct).supplierIndex := by rw [e0]
        rw [eIdx, e0s, e0i, acc_start_eq, mulDouble, creditFor]
      rw [hFG, hs1eq] at hdist
      exact hdist
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hu1 : updateCompBorrowIndex s with
  | none =>
    simp [hu1] at h
  | some s1 =>
    simp only [hu1] at h
    obtain ⟨hb, hs1, hbn, hbo, hr, ha⟩ := updateBorrow_spec s s1 hu1
    have hs1eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
      St_updateBorrow_eq s s1 hs1 hbn hbo hr ha
    obtain ⟨hle, hdist⟩ := distBorrower_spec s1 who s' _ rfl h
    have eAcct : s1.acct who = s.acct who := by simp only [St.acct, ha]
    have eIdx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hs1eq]
    have hstart : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [eAcct, eIdx, acc_start_eq]
    refine ⟨hb, ?_, ?_⟩
    · rw [hstart] at hle
      rw [eIdx] at hle
      exact hle
    · unfold St.withAcct at hdist
      rw [ha] at hdist
      have hFG : (s.accts.modify who fun a => ({ a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct)) = (s.accts.modify who fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } : Acct)) := by
        apply modify_congr (d := noAcct)
        have e0 : s1.acct who = s.accts.getD who noAcct := by simp only [St.acct, ha]
        show ({ (s.accts.getD who noAcct) with borrowerIndex := s1.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + mulDouble (s1.acct who).borrow (s1.borrowState.index - (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex)) } : Acct) = ({ (s.accts.getD who noAcct) with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } : Acct)
        have e0s : (s1.acct who).borrow = (s.accts.getD who noAcct).borrow := by rw [e0]
        have e0i : (s1.acct who).borrowerIndex = (s.accts.getD who noAcct).borrowerIndex := by rw [e0]
        rw [eIdx, e0s, e0i, acc_start_eq, mulDouble, creditFor]
      rw [hFG, hs1eq] at hdist
      exact hdist
theorem grantComp_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · have hc2 : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve := ⟨hc.1, hc.2⟩
    simp only [hc, hc2, ↓reduceIte]
    have hmod : (s.accts.modify who fun a => ({ a with accrued := (0 : Nat), wallet := a.wallet + (s.acct who).accrued } : Acct)) = (s.accts.modify who fun a => ({ a with accrued := (0 : Nat), wallet := a.wallet + a.accrued } : Acct)) := by
      apply modify_congr (d := noAcct)
      simp only [St.acct]
    rw [hmod]
  · have hc2 : ¬ ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) := by
      intro hcon
      exact hc ⟨hcon.1, hcon.2⟩
    simp only [hc, hc2, ↓reduceIte]

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  unfold claimComp at h
  cases hu1 : updateCompBorrowIndex s with
  | none =>
    simp [hu1] at h
  | some t1 =>
    simp [hu1] at h
    cases hd1 : distributeBorrowerComp t1 who with
    | none =>
      simp [hd1] at h
    | some m1 =>
      simp [hd1] at h
      cases hu2 : updateCompSupplyIndex m1 with
      | none =>
        simp [hu2] at h
      | some t2 =>
        simp [hu2] at h
        cases hd2 : distributeSupplierComp t2 who with
        | none =>
          simp [hd2] at h
        | some m2 =>
          simp [hd2] at h
          have hborrow : comptroller s (.borrowHook who) = some m1 := by simp [comptroller, hu1, hd1]
          have hsupply : comptroller m1 (.supplyHook who) = some m2 := by simp [comptroller, hu2, hd2]
          have hgr : grantCompInternal m2 who = s' := h
          refine ⟨m1, m2, req_borrow_hook _ _ _ hborrow, req_supply_hook _ _ _ hsupply, ?_⟩
          rw [← hgr]
          exact grantComp_eq m2 who
theorem setSupply_spec (s t : St) (a : Nat) (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState := (if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) } ∧
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState ∧
    t.reserve = s.reserve ∧ t.accts = s.accts := by
  unfold setSupplySpeed at h
  by_cases hne : s.supplyState.speed ≠ a
  · simp [hne] at h
    obtain ⟨s1, hu, rfl⟩ := h
    obtain ⟨hb, hs1, hbn, hbo, hr, ha⟩ := updateSupply_spec s s1 hu
    have hs1eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
      St_updateSupply_eq s s1 hs1 hbn hbo hr ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _
      exact hb
    · rw [if_neg hne, hs1eq]
    · simp [hs1eq]
    · simp [hs1eq]
    · simp [hs1eq]
    · simp [hs1eq]
  · simp [hne] at h
    obtain rfl := h
    have heq : s.supplyState.speed = a := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hcon
      exact absurd heq hcon
    · rw [if_pos heq]
    · rfl
    · rfl
    · rfl
    · rfl

theorem setBorrow_spec (s t : St) (b : Nat) (h : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState := (if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) } ∧
    t.blockNumber = s.blockNumber ∧ t.supplyState = s.supplyState ∧
    t.reserve = s.reserve ∧ t.accts = s.accts := by
  unfold setBorrowSpeed at h
  by_cases hne : s.borrowState.speed ≠ b
  · simp [hne] at h
    obtain ⟨s1, hu, rfl⟩ := h
    obtain ⟨hb, hs1, hbn, hbo, hr, ha⟩ := updateBorrow_spec s s1 hu
    have hs1eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
      St_updateBorrow_eq s s1 hs1 hbn hbo hr ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _
      exact hb
    · rw [if_neg hne, hs1eq]
    · simp [hs1eq]
    · simp [hs1eq]
    · simp [hs1eq]
    · simp [hs1eq]
  · simp [hne] at h
    obtain rfl := h
    have heq : s.borrowState.speed = b := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hcon
      exact absurd heq hcon
    · rw [if_pos heq]
    · rfl
    · rfl
    · rfl
    · rfl

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller] at h
  unfold setCompSpeedInternal at h
  cases hs : setSupplySpeed s a with
  | none =>
    simp [hs] at h
  | some t =>
    simp [hs] at h
    cases hb : setBorrowSpeed t b with
    | none =>
      simp [hb] at h
    | some s'' =>
      simp only [hb] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨hc1, hteq, htbn, htbo, htr, hta⟩ := setSupply_spec s t a hs
      obtain ⟨hc2, hteq2, hbn2, hsp2, hr2, ha2⟩ := setBorrow_spec t s'' b hb
      have hbor : totalBorrows t = totalBorrows s := by simp only [totalBorrows, hta]
      refine ⟨hc1, ?_, ?_⟩
      · intro hne
        have hne2 : t.borrowState.speed ≠ b := by rw [htbo]; exact hne
        have hle := hc2 hne2
        rw [htbo, htbn] at hle
        exact hle
      · rw [htbo, htbn, hbor] at hteq2
        rw [hteq] at hteq2
        exact hteq2
theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    simp only [comptroller]
    obtain ⟨s1, hu⟩ := updateSupply_some s hc.1
    obtain ⟨hb, hs1, hbn, hbo, hr, ha⟩ := updateSupply_spec s s1 hu
    have hs1eq := St_updateSupply_eq s s1 hs1 hbn hbo hr ha
    have eAcct : (s1.acct who).supplierIndex = (s.acct who).supplierIndex := by simp only [St.acct, ha]
    have eIdx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hs1eq]
    have hle : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) ≤ s1.supplyState.index := by
      rw [eAcct, eIdx]
      exact start_le_new_supply s who _ (accrueSide_le _ _ _) hc
    obtain ⟨s', hd⟩ := distSupplier_some s1 who hle
    simp [hu, hd]
  | borrowHook who =>
    simp only [comptroller]
    obtain ⟨s1, hu⟩ := updateBorrow_some s hc.2.1
    obtain ⟨hb, hs1, hbn, hbo, hr, ha⟩ := updateBorrow_spec s s1 hu
    have hs1eq := St_updateBorrow_eq s s1 hs1 hbn hbo hr ha
    have eAcct : (s1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by simp only [St.acct, ha]
    have eIdx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hs1eq]
    have hle : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) ≤ s1.borrowState.index := by
      rw [eAcct, eIdx]
      exact start_le_new_borrow s who _ (accrueSide_le _ _ _) hc
    obtain ⟨s', hd⟩ := distBorrower_some s1 who hle
    simp [hu, hd]
  | claim who =>
    simp only [comptroller, claimComp]
    obtain ⟨t1, hu1⟩ := updateBorrow_some s hc.2.1
    obtain ⟨hb1, ht1, hbn1, hbo1, hr1, ha1⟩ := updateBorrow_spec s t1 hu1
    have ht1eq := St_updateBorrow_eq s t1 ht1 hbn1 hbo1 hr1 ha1
    have eAcct1 : (t1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by simp only [St.acct, ha1]
    have eIdx1 : t1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [ht1eq]
    have hle1 : (if (t1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t1.borrowState.index then compInitialIndex else (t1.acct who).borrowerIndex) ≤ t1.borrowState.index := by
      rw [eAcct1, eIdx1]
      exact start_le_new_borrow s who _ (accrueSide_le _ _ _) hc
    obtain ⟨m1, hd1⟩ := distBorrower_some t1 who hle1
    obtain ⟨-, hdist1⟩ := distBorrower_spec t1 who m1 _ rfl hd1
    have eS : m1.supplyState = s.supplyState := by rw [hdist1]; exact hbo1
    have eB : m1.blockNumber = s.blockNumber := by rw [hdist1]; exact hbn1
    have hb2 : m1.supplyState.block ≤ m1.blockNumber := by rw [eS, eB]; exact hc.1
    obtain ⟨t2, hu2⟩ := updateSupply_some m1 hb2
    obtain ⟨hb2', hs2, hbn2, hbo2, hr2, ha2⟩ := updateSupply_spec m1 t2 hu2
    have ht2eq := St_updateSupply_eq m1 t2 hs2 hbn2 hbo2 hr2 ha2
    have eRec2 : (t2.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have e1 : (t2.acct who).supplierIndex = (m1.acct who).supplierIndex := by simp only [St.acct, ha2]
      have e2 : (m1.acct who).supplierIndex = (t1.acct who).supplierIndex :=
        distBorrower_keep_supplier t1 m1 who hd1
      have e3 : (t1.acct who).supplierIndex = (s.acct who).supplierIndex := by simp only [St.acct, ha1]
      exact e1.trans (e2.trans e3)
    have eIdx2 : t2.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by rw [ht2eq]
    have hle2 : (if (t2.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ t2.supplyState.index then compInitialIndex else (t2.acct who).supplierIndex) ≤ t2.supplyState.index := by
      rw [eRec2, eIdx2]
      have hmono : s.supplyState.index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
        rw [eS]
        exact accrueSide_le _ _ _
      exact start_le_new_supply s who _ hmono hc
    obtain ⟨m2, hd2⟩ := distSupplier_some t2 who hle2
    simp [hu1, hd1, hu2, hd2]
  | setSpeeds a b =>
    simp only [comptroller, setCompSpeedInternal]
    obtain ⟨t, hs⟩ := setSupply_some s a hc.1
    obtain ⟨hc1, hteq, htbn, htbo, htr, hta⟩ := setSupply_spec s t a hs
    have hb_t : t.borrowState.block ≤ t.blockNumber := by rw [htbo, htbn]; exact hc.2.1
    obtain ⟨s', hb2⟩ := setBorrow_some t b hb_t
    simp [hs, hb2]

/-! ## Two-sided market view for the bounded requirements -/

def M : ProofForgeFin.Accumulator.Market St Acct :=
  { one := doubleScale,
    init := compInitialIndex,
    clock := fun s => ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed, s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩,
    accts := St.accts,
    dflt := noAcct,
    units₁ := Acct.supply,
    units₂ := Acct.borrow,
    rec₁ := Acct.supplierIndex,
    rec₂ := Acct.borrowerIndex,
    credited := fun a => a.accrued + a.wallet,
    dflt_units₁ := rfl,
    dflt_units₂ := rfl }

theorem M_one : M.one = doubleScale := rfl

theorem M_init : M.init = compInitialIndex := rfl

theorem M_clock (s : St) : M.clock s = ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed, s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩ := rfl

theorem M_total₁ (s : St) : M.total₁ s = totalSupply s := rfl

theorem M_total₂ (s : St) : M.total₂ s = totalBorrows s := rfl

theorem M_acct_eq (s : St) (w : Nat) : M.acct s w = s.acct w := rfl

theorem M_credited_eq (a : Acct) : M.credited a = a.accrued + a.wallet := rfl

theorem M_creditSum_eq (s : St) : M.creditSum s = St.credited s := rfl

theorem M_accts_eq (s : St) : M.accts s = s.accts := rfl

theorem invConsistent (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St)
    (hI : M.Inv g₁ g₂ sp s) : Consistent s := by
  obtain ⟨hl1, hl2, hrec, hs1, hs2, hr1, hr2⟩ := hI
  exact ⟨hl1, hl2, fun a ha => hrec a ha⟩

theorem withAcct_accts (s : St) (who : Nat) (f : Acct → Acct) :
    (s.withAcct who f).accts = s.accts.modify who f := rfl

theorem withAcct_clock (s : St) (who : Nat) (f : Acct → Acct) :
    M.clock (s.withAcct who f) = M.clock s := rfl

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos hc]
  · rw [if_neg hc]

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos hc]
  · rw [if_neg hc]

theorem supplySettle (s s' : St) (who : Nat) (h : SupplyDistributed s who s') :
    M.Settle₁ who s s' := by
  obtain ⟨hb, hle, heq⟩ := h
  refine ⟨?_, ?_⟩
  · rw [heq]
    simp only [M_clock]
    unfold ProofForgeFin.Accumulator.Clock.catchUp₁
    dsimp only
    rw [M_one, M_total₁]
    rw [(accrueSide_catchUp s.supplyState s.blockNumber (totalSupply s)).1]
    rw [accrueSide_block, accrueSide_speed]
  · refine ⟨(fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + mulDouble a.supply ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) } : Acct)), ?_, ?_⟩
    · rw [heq]
      simp only [M_accts_eq]
      apply modify_congr (d := noAcct)
      rfl
    · have hi : (M.clock s').index₁ = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        rw [heq]
        rfl
      rw [hi]
      intro a
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show (a.accrued + mulDouble a.supply ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) + a.wallet) ≤ (a.accrued + a.wallet) + a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale
      rw [accrualStart_firstStart]
      unfold mulDouble
      omega

theorem borrowSettle (s s' : St) (who : Nat) (h : BorrowDistributed s who s') :
    M.Settle₂ who s s' := by
  obtain ⟨hb, hle, heq⟩ := h
  refine ⟨?_, ?_⟩
  · rw [heq]
    simp only [M_clock]
    unfold ProofForgeFin.Accumulator.Clock.catchUp₂
    dsimp only
    rw [M_one, M_total₂]
    rw [(accrueSide_catchUp s.borrowState s.blockNumber (totalBorrows s)).1]
    rw [accrueSide_block, accrueSide_speed]
  · refine ⟨(fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + mulDouble a.borrow ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) } : Acct)), ?_, ?_⟩
    · rw [heq]
      simp only [M_accts_eq]
      apply modify_congr (d := noAcct)
      rfl
    · have hi : (M.clock s').index₂ = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        rw [heq]
        rfl
      rw [hi]
      intro a
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show (a.accrued + mulDouble a.borrow ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) + a.wallet) ≤ (a.accrued + a.wallet) + a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale
      rw [accrualStart_firstStart]
      unfold mulDouble
      omega

theorem act_mint (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.mint who x)) (emittedBy sp (.mint who x)) (exec comptroller s (.mint who x)) := by
  have hC : Consistent s := invConsistent g₁ g₂ sp s hI
  by_cases hwho : who < s.accts.length
  · obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.supplyHook who) hC)
    have hsd := req_supply_hook s who s1 hs1
    have hset : M.Settle₁ who s s1 := supplySettle s s1 who hsd
    have eexec : exec comptroller s (.mint who x) = s1.withAcct who (fun a => ({ a with supply := a.supply + x } : Acct)) := by
      simp only [exec, hwho, hs1, ↓reduceIte]
    have hg : M.AdjustsAt (fun a => ({ a with supply := a.supply + x } : Acct)) := by
      intro a
      exact ⟨Nat.le_refl _, rfl, rfl⟩
    have hu : ∀ a, M.units₂ ((fun a => ({ a with supply := a.supply + x } : Acct)) a) = M.units₂ a := fun a => rfl
    have ha : M.accts (exec comptroller s (.mint who x)) = (M.accts s1).modify who (fun a => ({ a with supply := a.supply + x } : Acct)) := by
      rw [eexec, M_accts_eq, withAcct_accts, M_accts_eq]
    have hc : M.clock (exec comptroller s (.mint who x)) = M.clock s1 := by
      rw [eexec, withAcct_clock]
    have hr : M.Reach s (exec comptroller s (.mint who x)) :=
      hset.then_adjust ha hc hg hu
    exact Act.moves hr
  · have eexec : exec comptroller s (.mint who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact Act.moves (Reach.refl s)

theorem act_redeem (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.redeem who x)) (emittedBy sp (.redeem who x)) (exec comptroller s (.redeem who x)) := by
  have hC : Consistent s := invConsistent g₁ g₂ sp s hI
  by_cases hwho : who < s.accts.length
  · obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.supplyHook who) hC)
    have hsd := req_supply_hook s who s1 hs1
    have hset : M.Settle₁ who s s1 := supplySettle s s1 who hsd
    by_cases hx : x ≤ (s1.acct who).supply
    · have eexec : exec comptroller s (.redeem who x) = s1.withAcct who (fun a => ({ a with supply := a.supply - x } : Acct)) := by
        simp [exec, hwho, hs1, hx]
      have hg : M.AdjustsAt (fun a => ({ a with supply := a.supply - x } : Acct)) := by
        intro a
        exact ⟨Nat.le_refl _, rfl, rfl⟩
      have hu : ∀ a, M.units₂ ((fun a => ({ a with supply := a.supply - x } : Acct)) a) = M.units₂ a := fun a => rfl
      have ha : M.accts (exec comptroller s (.redeem who x)) = (M.accts s1).modify who (fun a => ({ a with supply := a.supply - x } : Acct)) := by
        rw [eexec, M_accts_eq, withAcct_accts, M_accts_eq]
      have hc : M.clock (exec comptroller s (.redeem who x)) = M.clock s1 := by
        rw [eexec, withAcct_clock]
      have hr : M.Reach s (exec comptroller s (.redeem who x)) :=
        hset.then_adjust ha hc hg hu
      exact Act.moves hr
    · have eexec : exec comptroller s (.redeem who x) = s := by
        simp [exec, hwho, hs1, hx]
      rw [eexec]
      exact Act.moves (Reach.refl s)
  · have eexec : exec comptroller s (.redeem who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact Act.moves (Reach.refl s)

theorem act_transfer (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (src dst x : Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.transfer src dst x)) (emittedBy sp (.transfer src dst x)) (exec comptroller s (.transfer src dst x)) := by
  have hC : Consistent s := invConsistent g₁ g₂ sp s hI
  by_cases hcond : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
  · obtain ⟨sa, hsa⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.supplyHook src) hC)
    have hsd_a := req_supply_hook s src sa hsa
    have hset_a : M.Settle₁ src s sa := supplySettle s sa src hsd_a
    have hinv_a : M.Inv g₁ g₂ sp sa := hset_a.inv hI
    have hCa : Consistent sa := invConsistent g₁ g₂ sp sa hinv_a
    obtain ⟨sb, hsb⟩ := Option.isSome_iff_exists.mp (req_calls_succeed sa (.supplyHook dst) hCa)
    have hsd_b := req_supply_hook sa dst sb hsb
    have hset_b : M.Settle₁ dst sa sb := supplySettle sa sb dst hsd_b
    by_cases hx : x ≤ (sb.acct src).supply
    · have eexec : exec comptroller s (.transfer src dst x) = (sb.withAcct src (fun a => ({ a with supply := a.supply - x } : Acct))).withAcct dst (fun a => ({ a with supply := a.supply + x } : Acct)) := by
        simp [exec, hcond, hsa, hsb, hx]
      have hg₁ : M.AdjustsAt (fun a => ({ a with supply := a.supply - x } : Acct)) := by
        intro a
        exact ⟨Nat.le_refl _, rfl, rfl⟩
      have hg₂ : M.AdjustsAt (fun a => ({ a with supply := a.supply + x } : Acct)) := by
        intro a
        exact ⟨Nat.le_refl _, rfl, rfl⟩
      have hu₁ : ∀ a, M.units₂ ((fun a => ({ a with supply := a.supply - x } : Acct)) a) = M.units₂ a := fun a => rfl
      have hu₂ : ∀ a, M.units₂ ((fun a => ({ a with supply := a.supply + x } : Acct)) a) = M.units₂ a := fun a => rfl
      have ha : M.accts (exec comptroller s (.transfer src dst x)) = ((M.accts sb).modify src (fun a => ({ a with supply := a.supply - x } : Acct))).modify dst (fun a => ({ a with supply := a.supply + x } : Acct)) := by
        simp only [eexec, M_accts_eq, withAcct_accts]
      have hc : M.clock (exec comptroller s (.transfer src dst x)) = M.clock sb := by
        simp only [eexec, withAcct_clock]
      have hr : M.Reach s (exec comptroller s (.transfer src dst x)) :=
        hset_a.transfer hset_b ha hc hg₁ hg₂ hu₁ hu₂
      exact Act.moves hr
    · have eexec : exec comptroller s (.transfer src dst x) = s := by
        simp [exec, hcond, hsa, hsb, hx]
      rw [eexec]
      exact Act.moves (Reach.refl s)
  · have eexec : exec comptroller s (.transfer src dst x) = s := by
      simp [exec, hcond]
    rw [eexec]
    exact Act.moves (Reach.refl s)

theorem act_borrow (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.borrow who x)) (emittedBy sp (.borrow who x)) (exec comptroller s (.borrow who x)) := by
  have hC : Consistent s := invConsistent g₁ g₂ sp s hI
  by_cases hwho : who < s.accts.length
  · obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.borrowHook who) hC)
    have hsd := req_borrow_hook s who s1 hs1
    have hset : M.Settle₂ who s s1 := borrowSettle s s1 who hsd
    have eexec : exec comptroller s (.borrow who x) = s1.withAcct who (fun a => ({ a with borrow := a.borrow + x } : Acct)) := by
      simp only [exec, hwho, hs1, ↓reduceIte]
    have hg : M.AdjustsAt (fun a => ({ a with borrow := a.borrow + x } : Acct)) := by
      intro a
      exact ⟨Nat.le_refl _, rfl, rfl⟩
    have hu : ∀ a, M.units₁ ((fun a => ({ a with borrow := a.borrow + x } : Acct)) a) = M.units₁ a := fun a => rfl
    have ha : M.accts (exec comptroller s (.borrow who x)) = (M.accts s1).modify who (fun a => ({ a with borrow := a.borrow + x } : Acct)) := by
      rw [eexec, M_accts_eq, withAcct_accts, M_accts_eq]
    have hc : M.clock (exec comptroller s (.borrow who x)) = M.clock s1 := by
      rw [eexec, withAcct_clock]
    have hr : M.Reach s (exec comptroller s (.borrow who x)) :=
      hset.then_adjust ha hc hg hu
    exact Act.moves hr
  · have eexec : exec comptroller s (.borrow who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact Act.moves (Reach.refl s)

theorem act_repay (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (who x : Nat)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp (.repay who x)) (emittedBy sp (.repay who x)) (exec comptroller s (.repay who x)) := by
  have hC : Consistent s := invConsistent g₁ g₂ sp s hI
  by_cases hwho : who < s.accts.length
  · obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp (req_calls_succeed s (.borrowHook who) hC)
    have hsd := req_borrow_hook s who s1 hs1
    have hset : M.Settle₂ who s s1 := borrowSettle s s1 who hsd
    by_cases hx : x ≤ (s1.acct who).borrow
    · have eexec : exec comptroller s (.repay who x) = s1.withAcct who (fun a => ({ a with borrow := a.borrow - x } : Acct)) := by
        simp [exec, hwho, hs1, hx]
      have hg : M.AdjustsAt (fun a => ({ a with borrow := a.borrow - x } : Acct)) := by
        intro a
        exact ⟨Nat.le_refl _, rfl, rfl⟩
      have hu : ∀ a, M.units₁ ((fun a => ({ a with borrow := a.borrow - x } : Acct)) a) = M.units₁ a := fun a => rfl
      have ha : M.accts (exec comptroller s (.repay who x)) = (M.accts s1).modify who (fun a => ({ a with borrow := a.borrow - x } : Acct)) := by
        rw [eexec, M_accts_eq, withAcct_accts, M_accts_eq]
      have hc : M.clock (exec comptroller s (.repay who x)) = M.clock s1 := by
        rw [eexec, withAcct_clock]
      have hr : M.Reach s (exec comptroller s (.repay who x)) :=
        hset.then_adjust ha hc hg hu
      exact Act.moves hr
    · have eexec : exec comptroller s (.repay who x) = s := by
        simp [exec, hwho, hs1, hx]
      rw [eexec]
      exact Act.moves (Reach.refl s)
  · have eexec : exec comptroller s (.repay who x) = s := by
      simp [exec, hwho]
    rw [eexec]
    exact Act.moves (Reach.refl s)

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
