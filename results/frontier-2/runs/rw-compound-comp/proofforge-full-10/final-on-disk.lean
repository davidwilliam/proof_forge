import CompRewards.Spec
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Accumulator.Index
import ProofForgeFin.Accumulator.Runs
import ProofForgeFin.Ledger
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
def grantCompInternal (s : St) (user : Account) : St := grant s user

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

theorem modify_congr {α : Type} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons b l ih =>
    cases i with
    | zero =>
      simp at h ⊢
      rw [h]
    | succ i =>
      simp at h ⊢
      rw [ih _ h]

theorem start_supply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
     else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h : (s.acct who).supplierIndex = 0
  · simp [h]
  · simp [h]

theorem start_borrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
     else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h : (s.acct who).borrowerIndex = 0
  · simp [h]
  · simp [h]

theorem update_supply_eq (s : St) (t : St)
    (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber ∧
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    refine ⟨hb, ?_⟩
    by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · rw [if_pos hd] at h
      obtain rfl := Option.some_inj.mp h
      have hd0 : 0 < s.blockNumber - s.supplyState.block := hd.1
      have hdS : 0 < s.supplyState.speed := hd.2
      by_cases ht : 0 < totalSupply s
      · have hpos : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s :=
          ⟨hd0, hdS, ht⟩
        have e1 : accrueSide s.supplyState s.blockNumber (totalSupply s) =
          { s.supplyState with index := s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s, block := s.blockNumber } := by
          unfold accrueSide
          rw [if_pos hpos]
        rw [e1]
        by_cases ht2 : totalSupply s > 0
        · rw [if_pos ht2]
          simp only [fraction]
        · omega
      · have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
          intro hc; exact ht hc.2.2
        have e1 : accrueSide s.supplyState s.blockNumber (totalSupply s) =
          { s.supplyState with block := s.blockNumber } := by
          unfold accrueSide
          rw [if_neg hneg]
        rw [e1]
        by_cases ht2 : totalSupply s > 0
        · omega
        · rw [if_neg ht2]
          simp
    · rw [if_neg hd] at h
      have hd' : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed) := hd
      have hd2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        intro hc; exact hd' ⟨hc.1, hc.2.1⟩
      have e1 : accrueSide s.supplyState s.blockNumber (totalSupply s) =
        { s.supplyState with block := s.blockNumber } := by
        unfold accrueSide
        rw [if_neg hd2]
      rw [e1]
      by_cases hd3 : s.blockNumber - s.supplyState.block > 0
      · rw [if_pos hd3] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · rw [if_neg hd3] at h
        obtain rfl := Option.some_inj.mp h
        have heq : s.blockNumber = s.supplyState.block := by omega
        cases s with | mk bn sup bor res accts =>
          cases sup with | mk ix bl sp =>
          simp only at hb heq ⊢
          simp [heq]
  · simp only [show ¬ s.supplyState.block ≤ s.blockNumber from hb, ↓reduceIte] at h
    simp at h

theorem update_borrow_eq (s : St) (t : St)
    (h : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber ∧
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    refine ⟨hb, ?_⟩
    by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · rw [if_pos hd] at h
      obtain rfl := Option.some_inj.mp h
      have hd0 : 0 < s.blockNumber - s.borrowState.block := hd.1
      have hdS : 0 < s.borrowState.speed := hd.2
      by_cases ht : 0 < totalBorrows s
      · have hpos : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s :=
          ⟨hd0, hdS, ht⟩
        have e1 : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
          { s.borrowState with index := s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s, block := s.blockNumber } := by
          unfold accrueSide
          rw [if_pos hpos]
        rw [e1]
        by_cases ht2 : totalBorrows s > 0
        · rw [if_pos ht2]
          simp only [fraction]
        · omega
      · have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          intro hc; exact ht hc.2.2
        have e1 : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
          { s.borrowState with block := s.blockNumber } := by
          unfold accrueSide
          rw [if_neg hneg]
        rw [e1]
        by_cases ht2 : totalBorrows s > 0
        · omega
        · rw [if_neg ht2]
          simp
    · rw [if_neg hd] at h
      have hd' : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed) := hd
      have hd2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        intro hc; exact hd' ⟨hc.1, hc.2.1⟩
      have e1 : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
        { s.borrowState with block := s.blockNumber } := by
        unfold accrueSide
        rw [if_neg hd2]
      rw [e1]
      by_cases hd3 : s.blockNumber - s.borrowState.block > 0
      · rw [if_pos hd3] at h
        obtain rfl := Option.some_inj.mp h
        rfl
      · rw [if_neg hd3] at h
        obtain rfl := Option.some_inj.mp h
        have heq : s.blockNumber = s.borrowState.block := by omega
        cases s with | mk bn sup bor res accts =>
          cases bor with | mk ix bl sp =>
          simp only at hb heq ⊢
          simp [heq]
  · simp only [show ¬ s.borrowState.block ≤ s.blockNumber from hb, ↓reduceIte] at h
    simp at h

theorem dist_supply_eq (s : St) (who : Account) (t : St)
    (h : distributeSupplierComp s who = some t) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    t = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart := start_supply_eq s who
  unfold distributeSupplierComp subChecked at h
  simp only [hstart] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [hle, ↓reduceIte] at h
    obtain rfl := Option.some_inj.mp h
    refine ⟨hle, ?_⟩
    unfold St.withAcct
    congr 1
    apply modify_congr
    simp only [St.acct]
    unfold mulDouble creditFor
    rfl
  · simp only [show ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index from hle, ↓reduceIte] at h
    simp at h

theorem dist_borrow_eq (s : St) (who : Account) (t : St)
    (h : distributeBorrowerComp s who = some t) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    t = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart := start_borrow_eq s who
  unfold distributeBorrowerComp subChecked at h
  simp only [hstart] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h
    obtain rfl := Option.some_inj.mp h
    refine ⟨hle, ?_⟩
    unfold St.withAcct
    congr 1
    apply modify_congr
    simp only [St.acct]
    unfold mulDouble creditFor
    rfl
  · simp only [show ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index from hle, ↓reduceIte] at h
    simp at h

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := rfl

theorem set_supply_of (s t : St) (a : Nat) (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState := if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases hsa : s.supplyState.speed ≠ a
  · rw [if_pos hsa] at h
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some mid =>
      simp [hu] at h
      obtain ⟨hb, hmid⟩ := update_supply_eq s mid hu
      refine ⟨fun _ => hb, ?_⟩
      rw [if_neg hsa, ← h, hmid]
  · rw [if_neg hsa] at h
    simp at h
    obtain rfl := h
    have heq : s.supplyState.speed = a := by omega
    refine ⟨fun hc => absurd heq hc, ?_⟩
    rw [if_pos heq]

theorem set_borrow_of (s t : St) (b : Nat) (h : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState := if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases hsb : s.borrowState.speed ≠ b
  · rw [if_pos hsb] at h
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some mid =>
      simp [hu] at h
      obtain ⟨hb, hmid⟩ := update_borrow_eq s mid hu
      refine ⟨fun _ => hb, ?_⟩
      rw [if_neg hsb, ← h, hmid]
  · rw [if_neg hsb] at h
    simp at h
    obtain rfl := h
    have heq : s.borrowState.speed = b := by omega
    refine ⟨fun hc => absurd heq hc, ?_⟩
    rw [if_pos heq]

theorem accrualStart_le (r i : Nat) (h : r ≤ i) : accrualStart r i ≤ i := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ i
    · simp [hi]
    · simp [hi]
  · simp [hr, h]

theorem le_accrueSide_index (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos hc]
    exact Nat.le_add_right _ _
  · rw [if_neg hc]
    exact Nat.le_refl _

theorem getD_supply_le (l : List Acct) (idx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ idx) (who : Nat) :
    (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons b l ih =>
    cases who with
    | zero =>
      simp
      exact hall b (by simp)
    | succ w =>
      simp
      apply ih
      intro a ha
      exact hall a (by simp [ha])

theorem getD_borrow_le (l : List Acct) (idx : Nat)
    (hall : ∀ a ∈ l, a.borrowerIndex ≤ idx) (who : Nat) :
    (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons b l ih =>
    cases who with
    | zero =>
      simp
      exact hall b (by simp)
    | succ w =>
      simp
      apply ih
      intro a ha
      exact hall a (by simp [ha])

theorem update_supply_ok (s : St) (hb : s.supplyState.block ≤ s.blockNumber) :
    ∃ t, updateCompSupplyIndex s = some t := by
  unfold updateCompSupplyIndex subChecked
  simp only [hb, ↓reduceIte]
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hd]
    exact ⟨_, rfl⟩
  · rw [if_neg hd]
    by_cases hd3 : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos hd3]
      exact ⟨_, rfl⟩
    · rw [if_neg hd3]
      exact ⟨s, rfl⟩

theorem update_borrow_ok (s : St) (hb : s.borrowState.block ≤ s.blockNumber) :
    ∃ t, updateCompBorrowIndex s = some t := by
  unfold updateCompBorrowIndex subChecked
  simp only [hb, ↓reduceIte]
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hd]
    exact ⟨_, rfl⟩
  · rw [if_neg hd]
    by_cases hd3 : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos hd3]
      exact ⟨_, rfl⟩
    · rw [if_neg hd3]
      exact ⟨s, rfl⟩

theorem dist_supply_ok (s : St) (who : Account)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    ∃ t, distributeSupplierComp s who = some t := by
  have hstart := start_supply_eq s who
  unfold distributeSupplierComp subChecked
  simp only [hstart, hle, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem dist_borrow_ok (s : St) (who : Account)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    ∃ t, distributeBorrowerComp s who = some t := by
  have hstart := start_borrow_eq s who
  unfold distributeBorrowerComp subChecked
  simp only [hstart, hle, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem supplierModifyPreserve (l : List Acct) (i : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify i f).getD i noAcct).supplierIndex = (l.getD i noAcct).supplierIndex := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero => exact hf b
    | succ i => exact ih i

theorem supplierPreserve_dist (s : St) (who : Account) (b : St)
    (hd : distributeBorrowerComp s who = some b) :
    (b.acct who).supplierIndex = (s.acct who).supplierIndex := by
  obtain ⟨_, hdist⟩ := dist_borrow_eq s who b hd
  rw [hdist]
  simp only [St.acct]
  exact supplierModifyPreserve s.accts who _ (fun a => rfl)

theorem mapModifyPreserve (g : Acct → Nat) (l : List Acct) (i : Nat) (f : Acct → Acct)
    (hf : ∀ a, g (f a) = g a) : (l.modify i f).map g = l.map g := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons b l ih =>
    cases i with
    | zero => simp [hf]
    | succ i => simp [ih]

theorem totalSupply_dist_borrow (s : St) (who : Account) (b : St)
    (hd : distributeBorrowerComp s who = some b) : totalSupply b = totalSupply s := by
  obtain ⟨_, hdist⟩ := dist_borrow_eq s who b hd
  rw [hdist]
  unfold totalSupply
  simp only []
  rw [mapModifyPreserve]
  intro a
  rfl

theorem setSupply_ok (s : St) (a : Nat) (hb : s.supplyState.block ≤ s.blockNumber) :
    ∃ t, setSupplySpeed s a = some t := by
  unfold setSupplySpeed
  by_cases hsa : s.supplyState.speed ≠ a
  · rw [if_pos hsa]
    obtain ⟨mid, hu⟩ := update_supply_ok s hb
    rw [hu]
    exact ⟨_, rfl⟩
  · rw [if_neg hsa]
    exact ⟨s, rfl⟩

theorem setBorrow_ok (s : St) (b : Nat) (hb : s.borrowState.block ≤ s.blockNumber) :
    ∃ t, setBorrowSpeed s b = some t := by
  unfold setBorrowSpeed
  by_cases hsb : s.borrowState.speed ≠ b
  · rw [if_pos hsb]
    obtain ⟨mid, hu⟩ := update_borrow_ok s hb
    rw [hu]
    exact ⟨_, rfl⟩
  · rw [if_neg hsb]
    exact ⟨s, rfl⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsb, hbb, hall⟩ := hc
  have hsup : ∀ who, (s.acct who).supplierIndex ≤ s.supplyState.index :=
    fun who => getD_supply_le s.accts _ (fun a ha => (hall a ha).1) who
  have hbor : ∀ who, (s.acct who).borrowerIndex ≤ s.borrowState.index :=
    fun who => getD_borrow_le s.accts _ (fun a ha => (hall a ha).2) who
  cases c with
  | supplyHook who =>
    obtain ⟨mid, hu⟩ := update_supply_ok s hsb
    have hr : (mid.acct who).supplierIndex ≤ mid.supplyState.index := by
      obtain ⟨_, hmid⟩ := update_supply_eq s mid hu
      rw [hmid]
      simp only [St.acct]
      exact Nat.le_trans (hsup who) (le_accrueSide_index s.supplyState s.blockNumber (totalSupply s))
    obtain ⟨t, hd⟩ := dist_supply_ok mid who (accrualStart_le _ _ hr)
    have hres : comptroller s (.supplyHook who) = some t := by
      unfold comptroller
      simp [hu, hd]
    rw [hres]
    rfl
  | borrowHook who =>
    obtain ⟨mid, hu⟩ := update_borrow_ok s hbb
    have hr : (mid.acct who).borrowerIndex ≤ mid.borrowState.index := by
      obtain ⟨_, hmid⟩ := update_borrow_eq s mid hu
      rw [hmid]
      simp only [St.acct]
      exact Nat.le_trans (hbor who) (le_accrueSide_index s.borrowState s.blockNumber (totalBorrows s))
    obtain ⟨t, hd⟩ := dist_borrow_ok mid who (accrualStart_le _ _ hr)
    have hres : comptroller s (.borrowHook who) = some t := by
      unfold comptroller
      simp [hu, hd]
    rw [hres]
    rfl
  | claim who =>
    obtain ⟨mid1, hu1⟩ := update_borrow_ok s hbb
    obtain ⟨_, hmid1⟩ := update_borrow_eq s mid1 hu1
    have hr1 : (mid1.acct who).borrowerIndex ≤ mid1.borrowState.index := by
      rw [hmid1]
      simp only [St.acct]
      exact Nat.le_trans (hbor who) (le_accrueSide_index s.borrowState s.blockNumber (totalBorrows s))
    obtain ⟨b1, hd1⟩ := dist_borrow_ok mid1 who (accrualStart_le _ _ hr1)
    obtain ⟨_, hdist1⟩ := dist_borrow_eq mid1 who b1 hd1
    have hb2 : b1.supplyState.block ≤ b1.blockNumber := by
      rw [hdist1, hmid1]
      exact hsb
    obtain ⟨mid2, hu2⟩ := update_supply_ok b1 hb2
    obtain ⟨_, hmid2⟩ := update_supply_eq b1 mid2 hu2
    have e2 : b1.supplyState = s.supplyState := by rw [hdist1, hmid1]
    have e3 : b1.blockNumber = s.blockNumber := by rw [hdist1, hmid1]
    have e4 : totalSupply b1 = totalSupply s := by
      have m1t : totalSupply mid1 = totalSupply s := by unfold totalSupply; rw [hmid1]
      exact Eq.trans (totalSupply_dist_borrow mid1 who b1 hd1) m1t
    have hr2 : (mid2.acct who).supplierIndex ≤ mid2.supplyState.index := by
      rw [hmid2]
      simp only [St.acct]
      have e1 : (b1.accts.getD who noAcct).supplierIndex = (s.acct who).supplierIndex := by
        have a2 := supplierPreserve_dist mid1 who b1 hd1
        simp only [St.acct] at a2
        have a3 : (mid1.accts.getD who noAcct).supplierIndex = (s.acct who).supplierIndex := by
          rw [hmid1]
          simp only [St.acct]
        rw [a2, a3]
      rw [e1, e2, e3, e4]
      exact Nat.le_trans (hsup who) (le_accrueSide_index s.supplyState s.blockNumber (totalSupply s))
    obtain ⟨b2, hd2⟩ := dist_supply_ok mid2 who (accrualStart_le _ _ hr2)
    have hres : comptroller s (.claim who) = some (grantCompInternal b2 who) := by
      unfold comptroller claimComp
      simp [hu1, hd1, hu2, hd2]
    rw [hres]
    rfl
  | setSpeeds a b =>
    obtain ⟨s1, hs1⟩ := setSupply_ok s a hsb
    have hb1 : s1.borrowState.block ≤ s1.blockNumber := by
      obtain ⟨_, hs1eq⟩ := set_supply_of s s1 a hs1
      rw [hs1eq]
      exact hbb
    obtain ⟨t, hs2⟩ := setBorrow_ok s1 b hb1
    have hres : comptroller s (.setSpeeds a b) = some t := by
      unfold comptroller setCompSpeedInternal
      simp [hs1, hs2]
    rw [hres]
    rfl

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hu : updateCompSupplyIndex s with
  | none => simp [hu] at h
  | some mid =>
    simp [hu] at h
    obtain ⟨hblock, hmid⟩ := update_supply_eq s mid hu
    obtain ⟨hle, hdist⟩ := dist_supply_eq mid who s' h
    unfold SupplyDistributed
    refine ⟨hblock, ?_, ?_⟩
    · rw [hmid] at hle
      simpa only [St.acct] using hle
    · rw [hmid] at hdist
      simpa only [St.acct] using hdist

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hu : updateCompBorrowIndex s with
  | none => simp [hu] at h
  | some mid =>
    simp [hu] at h
    obtain ⟨hblock, hmid⟩ := update_borrow_eq s mid hu
    obtain ⟨hle, hdist⟩ := dist_borrow_eq mid who s' h
    unfold BorrowDistributed
    refine ⟨hblock, ?_, ?_⟩
    · rw [hmid] at hle
      simpa only [St.acct] using hle
    · rw [hmid] at hdist
      simpa only [St.acct] using hdist

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
  cases hu1 : updateCompBorrowIndex s with
  | none => simp [hu1] at h
  | some mid1 =>
    simp [hu1] at h
    cases hd1 : distributeBorrowerComp mid1 who with
    | none => simp [hd1] at h
    | some b1 =>
      simp [hd1] at h
      cases hu2 : updateCompSupplyIndex b1 with
      | none => simp [hu2] at h
      | some mid2 =>
        simp [hu2] at h
        cases hd2 : distributeSupplierComp mid2 who with
        | none => simp [hd2] at h
        | some b2 =>
          simp [hd2] at h
          obtain ⟨hb1, hmid1⟩ := update_borrow_eq s mid1 hu1
          obtain ⟨hle1, hdist1⟩ := dist_borrow_eq mid1 who b1 hd1
          obtain ⟨hb2, hmid2⟩ := update_supply_eq b1 mid2 hu2
          obtain ⟨hle2, hdist2⟩ := dist_supply_eq mid2 who b2 hd2
          refine ⟨b1, b2, ?_, ?_, ?_⟩
          · unfold BorrowDistributed
            refine ⟨hb1, ?_, ?_⟩
            · rw [hmid1] at hle1
              simpa only [St.acct] using hle1
            · rw [hmid1] at hdist1
              simpa only [St.acct] using hdist1
          · unfold SupplyDistributed
            refine ⟨hb2, ?_, ?_⟩
            · rw [hmid2] at hle2
              simpa only [St.acct] using hle2
            · rw [hmid2] at hdist2
              simpa only [St.acct] using hdist2
          · rw [← h, grant_eq]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  cases hs1 : setSupplySpeed s a with
  | none => simp [hs1] at h
  | some s1 =>
    simp [hs1] at h
    obtain ⟨hbS, hs1eq⟩ := set_supply_of s s1 a hs1
    obtain ⟨hbB, hsBeq⟩ := set_borrow_of s1 s' b h
    have hbor : s1.borrowState = s.borrowState := by rw [hs1eq]
    have hblk : s1.blockNumber = s.blockNumber := by rw [hs1eq]
    have haccts : s1.accts = s.accts := by rw [hs1eq]
    have htot : totalBorrows s1 = totalBorrows s := by unfold totalBorrows; rw [haccts]
    rw [hbor, hblk, htot] at hsBeq
    unfold SpeedsSet
    refine ⟨hbS, ?_, ?_⟩
    · intro hne
      have hne1 : s1.borrowState.speed ≠ b := by rw [hbor]; exact hne
      have hle := hbB hne1
      rw [hbor, hblk] at hle
      exact hle
    · rw [hsBeq, hs1eq]
/-- Supply pending of an account at the current supply index, counted from the safe
start (`firstStart`): what the fixed code credits from, and what the potential counts. -/
def supPend (s : St) (a : Acct) : Nat :=
  ProofForgeFin.DeFi.Rewards.pending a.supply
    (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex s.supplyState.index)
    s.supplyState.index

/-- Borrow pending of an account at the current borrow index. -/
def borPend (s : St) (a : Acct) : Nat :=
  ProofForgeFin.DeFi.Rewards.pending a.borrow
    (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex s.borrowState.index)
    s.borrowState.index

/-- Supply emission not yet in the supply index. -/
def unidxS (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- Borrow emission not yet in the borrow index. -/
def unidxB (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- Global potential: credited COMP at index scale, plus every account's pending rewards on
both sides, plus the unindexed emission at scale. No interaction raises it; time passing
raises it by exactly the emission at scale. -/
def pot (s : St) : Nat :=
  St.credited s * doubleScale + ((s.accts.map fun a => supPend s a + borPend s a).sum +
    doubleScale * (unidxS s + unidxB s))

/-- Per-account potential: what is credited to `who` at scale, plus its pending rewards, plus
the unindexed emission of each side counted only while it holds a position there. -/
def potAt (who : Account) (s : St) : Nat :=
  St.creditedTo s who * doubleScale + (supPend s (s.acct who) + borPend s (s.acct who)) +
    doubleScale * ((if 0 < (s.acct who).supply then unidxS s else 0) +
      (if 0 < (s.acct who).borrow then unidxB s else 0))

theorem bridge_start (r i : Nat) :
    accrualStart r i = ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex r i := rfl

theorem bridge_credit (u s i : Nat) :
    creditFor u s i = ProofForgeFin.DeFi.Rewards.credit doubleScale u s i := rfl

/-- Invariant over a run with ghost speeds `g`: the state's speeds match, no side's block lies
ahead, and no recorded index lies above its market index. -/
def Inv (g : Nat × Nat) (s : St) : Prop :=
  s.supplyState.speed = g.1 ∧ s.borrowState.speed = g.2 ∧
  s.supplyState.block ≤ s.blockNumber ∧ s.borrowState.block ≤ s.blockNumber ∧
  ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem covered_supply (s : St) :
    totalSupply s * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) ≤
    doubleScale * unidxS s := by
  unfold unidxS accrueSide
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · rw [if_pos hc]
    show totalSupply s * (s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s - s.supplyState.index) ≤ _
    rw [Nat.add_sub_cancel_left]
    calc totalSupply s * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s)
        = ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale) / totalSupply s * totalSupply s := Nat.mul_comm _ _
      _ ≤ (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale :=
        Nat.div_mul_le_self _ _
      _ = doubleScale * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) := Nat.mul_comm _ _
  · rw [if_neg hc]
    have h0 : ({ s.supplyState with block := s.blockNumber } : Side).index = s.supplyState.index := rfl
    rw [h0, Nat.sub_self, Nat.mul_zero]
    exact Nat.zero_le _

theorem covered_borrow (s : St) :
    totalBorrows s * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) ≤
    doubleScale * unidxB s := by
  unfold unidxB accrueSide
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · rw [if_pos hc]
    show totalBorrows s * (s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s - s.borrowState.index) ≤ _
    rw [Nat.add_sub_cancel_left]
    calc totalBorrows s * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s)
        = ((s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale) / totalBorrows s * totalBorrows s := Nat.mul_comm _ _
      _ ≤ (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale :=
        Nat.div_mul_le_self _ _
      _ = doubleScale * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) := Nat.mul_comm _ _
  · rw [if_neg hc]
    have h0 : ({ s.borrowState with block := s.blockNumber } : Side).index = s.borrowState.index := rfl
    rw [h0, Nat.sub_self, Nat.mul_zero]
    exact Nat.zero_le _

theorem pot_accrueSupply (s : St) :
    pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ pot s := by
  have hC : St.credited { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } =
      St.credited s := rfl
  have hac : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts =
      s.accts := rfl
  have hB : ((s.accts.map (borPend { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })).sum) =
      ((s.accts.map (borPend s)).sum) :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => rfl)
  have hUb : unidxB { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } =
      unidxB s := rfl
  have hU0 : unidxS { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = 0 := by
    unfold unidxS
    show (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.blockNumber -
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.block) *
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.speed) = 0
    rw [accrueSide_block]
    show (s.blockNumber - s.blockNumber) * _ = 0
    rw [Nat.sub_self, Nat.zero_mul]
  have ht : ∀ a ∈ s.accts, supPend { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } a ≤
      supPend s a + a.supply *
        ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.index -
          s.supplyState.index) := by
    intro a ha
    show ProofForgeFin.DeFi.Rewards.pending a.supply _ _ ≤
      ProofForgeFin.DeFi.Rewards.pending a.supply _ _ + a.supply * _
    exact ProofForgeFin.Accumulator.owed_le_add
      (ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.supplierIndex
        (le_accrueSide_index s.supplyState s.blockNumber (totalSupply s)))
  have hE : (s.accts.map fun a => a.supply).sum *
      ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.index -
        s.supplyState.index) ≤ doubleScale * unidxS s :=
    covered_supply s
  have hS := ProofForgeFin.DeFi.Rewards.sum_le_of_index_le s.accts
    (supPend s)
    (supPend { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
    (fun a => a.supply) ht hE
  unfold pot
  rw [hac, hC]
  simp only [ProofForgeFin.DeFi.Rewards.sum_map_add]
  rw [hB, hUb, hU0]
  simp only [Nat.mul_add, Nat.zero_add]
  omega

theorem pot_accrueBorrow (s : St) :
    pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤ pot s := by
  have hC : St.credited { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } =
      St.credited s := rfl
  have hac : ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).accts =
      s.accts := rfl
  have hS : ((s.accts.map (supPend { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })).sum) =
      ((s.accts.map (supPend s)).sum) :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => rfl)
  have hUs : unidxS { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } =
      unidxS s := rfl
  have hU0 : unidxB { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = 0 := by
    unfold unidxB
    show (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.blockNumber -
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.block) *
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.speed) = 0
    rw [accrueSide_block]
    show (s.blockNumber - s.blockNumber) * _ = 0
    rw [Nat.sub_self, Nat.zero_mul]
  have ht : ∀ a ∈ s.accts, borPend { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } a ≤
      borPend s a + a.borrow *
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.index -
          s.borrowState.index) := by
    intro a ha
    show ProofForgeFin.DeFi.Rewards.pending a.borrow _ _ ≤
      ProofForgeFin.DeFi.Rewards.pending a.borrow _ _ + a.borrow * _
    exact ProofForgeFin.Accumulator.owed_le_add
      (ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.borrowerIndex
        (le_accrueSide_index s.borrowState s.blockNumber (totalBorrows s)))
  have hE : (s.accts.map fun a => a.borrow).sum *
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.index -
        s.borrowState.index) ≤ doubleScale * unidxB s :=
    covered_borrow s
  have hB := ProofForgeFin.DeFi.Rewards.sum_le_of_index_le s.accts
    (borPend s)
    (borPend { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (fun a => a.borrow) ht hE
  unfold pot
  rw [hac, hC]
  simp only [ProofForgeFin.DeFi.Rewards.sum_map_add]
  rw [hS, hUs, hU0]
  simp only [Nat.mul_add, Nat.zero_add]
  omega

theorem pot_settleSupply_aux (sA : St) (who : Account) (F : Acct → Acct)
    (hFidx : ∀ a, (F a).supplierIndex = sA.supplyState.index)
    (hFacc : ∀ a, (F a).accrued = a.accrued + creditFor a.supply
      (accrualStart a.supplierIndex sA.supplyState.index) sA.supplyState.index)
    (hFbor : ∀ a, (F a).borrow = a.borrow)
    (hFborI : ∀ a, (F a).borrowerIndex = a.borrowerIndex)
    (hFwal : ∀ a, (F a).wallet = a.wallet)
    (hFsup : ∀ a, (F a).supply = a.supply) :
    pot { sA with accts := sA.accts.modify who F } ≤ pot sA := by
  have hUs : unidxS { sA with accts := sA.accts.modify who F } = unidxS sA := rfl
  have hUb : unidxB { sA with accts := sA.accts.modify who F } = unidxB sA := rfl
  have hC : ∀ s, St.credited s * doubleScale =
      ((s.accts.map fun a => (a.accrued + a.wallet) * doubleScale).sum) :=
    fun s => (ProofForgeFin.Ledger.sum_map_mul_right _ _ _).symm
  have nM : (({ sA with accts := sA.accts.modify who F }.accts.map
      fun a => supPend { sA with accts := sA.accts.modify who F } a +
        borPend { sA with accts := sA.accts.modify who F } a).sum) =
      ((sA.accts.modify who F).map fun a => supPend sA a + borPend sA a).sum :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => by rfl)
  unfold pot
  rw [hUs, hUb]
  simp only [hC]
  rw [nM]
  simp only [← Nat.add_assoc, ← ProofForgeFin.DeFi.Rewards.sum_map_add]
  refine Nat.add_le_add_right
    (ProofForgeFin.Ledger.sum_map_modify_le _ _ _ _ noAcct ?_) _
  intro hlt
  unfold supPend borPend
  rw [hFsup, hFidx, hFbor, hFborI, hFacc, hFwal]
  unfold creditFor
  rw [bridge_start]
  have e : ((sA.accts.getD who noAcct).accrued +
      (sA.accts.getD who noAcct).supply *
        (sA.supplyState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).supplierIndex sA.supplyState.index) / doubleScale +
      (sA.accts.getD who noAcct).wallet) =
      (((sA.accts.getD who noAcct).accrued + (sA.accts.getD who noAcct).wallet) +
      (sA.accts.getD who noAcct).supply *
        (sA.supplyState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).supplierIndex sA.supplyState.index) / doubleScale) := by
    omega
  rw [e]
  have hset : (((sA.accts.getD who noAcct).accrued + (sA.accts.getD who noAcct).wallet) +
      (sA.accts.getD who noAcct).supply *
        (sA.supplyState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).supplierIndex sA.supplyState.index) / doubleScale) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (sA.accts.getD who noAcct).supply
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex sA.supplyState.index sA.supplyState.index)
        sA.supplyState.index ≤
      ((sA.accts.getD who noAcct).accrued + (sA.accts.getD who noAcct).wallet) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (sA.accts.getD who noAcct).supply
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).supplierIndex sA.supplyState.index)
        sA.supplyState.index :=
    ProofForgeFin.DeFi.Rewards.settle_le rfl (Nat.le_refl _)
      (ProofForgeFin.Accumulator.le_firstStart_self _ _)
  omega

theorem pot_settleBorrow_aux (sA : St) (who : Account) (F : Acct → Acct)
    (hFidx : ∀ a, (F a).borrowerIndex = sA.borrowState.index)
    (hFacc : ∀ a, (F a).accrued = a.accrued + creditFor a.borrow
      (accrualStart a.borrowerIndex sA.borrowState.index) sA.borrowState.index)
    (hFsup : ∀ a, (F a).supply = a.supply)
    (hFsupI : ∀ a, (F a).supplierIndex = a.supplierIndex)
    (hFwal : ∀ a, (F a).wallet = a.wallet)
    (hFbor : ∀ a, (F a).borrow = a.borrow) :
    pot { sA with accts := sA.accts.modify who F } ≤ pot sA := by
  have hUs : unidxS { sA with accts := sA.accts.modify who F } = unidxS sA := rfl
  have hUb : unidxB { sA with accts := sA.accts.modify who F } = unidxB sA := rfl
  have hC : ∀ s, St.credited s * doubleScale =
      ((s.accts.map fun a => (a.accrued + a.wallet) * doubleScale).sum) :=
    fun s => (ProofForgeFin.Ledger.sum_map_mul_right _ _ _).symm
  have nM : (({ sA with accts := sA.accts.modify who F }.accts.map
      fun a => supPend { sA with accts := sA.accts.modify who F } a +
        borPend { sA with accts := sA.accts.modify who F } a).sum) =
      ((sA.accts.modify who F).map fun a => supPend sA a + borPend sA a).sum :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => by rfl)
  unfold pot
  rw [hUs, hUb]
  simp only [hC]
  rw [nM]
  simp only [← Nat.add_assoc, ← ProofForgeFin.DeFi.Rewards.sum_map_add]
  refine Nat.add_le_add_right
    (ProofForgeFin.Ledger.sum_map_modify_le _ _ _ _ noAcct ?_) _
  intro hlt
  unfold supPend borPend
  rw [hFsup, hFsupI, hFbor, hFidx, hFacc, hFwal]
  unfold creditFor
  rw [bridge_start]
  have e : ((sA.accts.getD who noAcct).accrued +
      (sA.accts.getD who noAcct).borrow *
        (sA.borrowState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).borrowerIndex sA.borrowState.index) / doubleScale +
      (sA.accts.getD who noAcct).wallet) =
      (((sA.accts.getD who noAcct).accrued + (sA.accts.getD who noAcct).wallet) +
      (sA.accts.getD who noAcct).borrow *
        (sA.borrowState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).borrowerIndex sA.borrowState.index) / doubleScale) := by
    omega
  rw [e]
  have hset : (((sA.accts.getD who noAcct).accrued + (sA.accts.getD who noAcct).wallet) +
      (sA.accts.getD who noAcct).borrow *
        (sA.borrowState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).borrowerIndex sA.borrowState.index) / doubleScale) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (sA.accts.getD who noAcct).borrow
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex sA.borrowState.index sA.borrowState.index)
        sA.borrowState.index ≤
      ((sA.accts.getD who noAcct).accrued + (sA.accts.getD who noAcct).wallet) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (sA.accts.getD who noAcct).borrow
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (sA.accts.getD who noAcct).borrowerIndex sA.borrowState.index)
        sA.borrowState.index :=
    ProofForgeFin.DeFi.Rewards.settle_le rfl (Nat.le_refl _)
      (ProofForgeFin.Accumulator.le_firstStart_self _ _)
  omega

theorem pot_balanceSupply_aux (s1 : St) (who : Account) (G : Acct → Acct)
    (hGacc : ∀ a, (G a).accrued = a.accrued)
    (hGwal : ∀ a, (G a).wallet = a.wallet)
    (hGbor : ∀ a, (G a).borrow = a.borrow)
    (hGborI : ∀ a, (G a).borrowerIndex = a.borrowerIndex)
    (hGsupI : ∀ a, (G a).supplierIndex = a.supplierIndex)
    (hrec : (s1.accts.getD who noAcct).supplierIndex = s1.supplyState.index) :
    pot { s1 with accts := s1.accts.modify who G } = pot s1 := by
  have hUs : unidxS { s1 with accts := s1.accts.modify who G } = unidxS s1 := rfl
  have hUb : unidxB { s1 with accts := s1.accts.modify who G } = unidxB s1 := rfl
  have hC : ∀ s, St.credited s * doubleScale =
      ((s.accts.map fun a => (a.accrued + a.wallet) * doubleScale).sum) :=
    fun s => (ProofForgeFin.Ledger.sum_map_mul_right _ _ _).symm
  have nM : (({ s1 with accts := s1.accts.modify who G }.accts.map
      fun a => supPend { s1 with accts := s1.accts.modify who G } a +
        borPend { s1 with accts := s1.accts.modify who G } a).sum) =
      ((s1.accts.modify who G).map fun a => supPend s1 a + borPend s1 a).sum :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => by rfl)
  have eAc : ({ s1 with accts := s1.accts.modify who G } : St).accts = s1.accts.modify who G := rfl
  have hmod : ((s1.accts.modify who G).map fun a => (a.accrued + a.wallet) * doubleScale +
      supPend s1 a + borPend s1 a).sum =
      ((s1.accts.map fun a => (a.accrued + a.wallet) * doubleScale +
      supPend s1 a + borPend s1 a).sum) := by
    apply ProofForgeFin.Ledger.sum_map_modify_eq _ _ _ _ noAcct (fun _ => ?_)
    unfold supPend borPend
    have z1 : ProofForgeFin.DeFi.Rewards.pending (G (s1.accts.getD who noAcct)).supply
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (G (s1.accts.getD who noAcct)).supplierIndex s1.supplyState.index)
        s1.supplyState.index = 0 := by
      rw [hGsupI, hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    have z2 : ProofForgeFin.DeFi.Rewards.pending (s1.accts.getD who noAcct).supply
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s1.accts.getD who noAcct).supplierIndex s1.supplyState.index)
        s1.supplyState.index = 0 := by
      rw [hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    rw [hGacc, hGwal, hGbor, hGborI, z1, z2]
  unfold pot
  rw [hUs, hUb, eAc]
  simp only [hC]
  rw [nM]
  simp only [← Nat.add_assoc, ← ProofForgeFin.DeFi.Rewards.sum_map_add]
  rw [hmod]

theorem pot_balanceBorrow_aux (s1 : St) (who : Account) (G : Acct → Acct)
    (hGacc : ∀ a, (G a).accrued = a.accrued)
    (hGwal : ∀ a, (G a).wallet = a.wallet)
    (hGsup : ∀ a, (G a).supply = a.supply)
    (hGsupI : ∀ a, (G a).supplierIndex = a.supplierIndex)
    (hGborI : ∀ a, (G a).borrowerIndex = a.borrowerIndex)
    (hrec : (s1.accts.getD who noAcct).borrowerIndex = s1.borrowState.index) :
    pot { s1 with accts := s1.accts.modify who G } = pot s1 := by
  have hUs : unidxS { s1 with accts := s1.accts.modify who G } = unidxS s1 := rfl
  have hUb : unidxB { s1 with accts := s1.accts.modify who G } = unidxB s1 := rfl
  have hC : ∀ s, St.credited s * doubleScale =
      ((s.accts.map fun a => (a.accrued + a.wallet) * doubleScale).sum) :=
    fun s => (ProofForgeFin.Ledger.sum_map_mul_right _ _ _).symm
  have nM : (({ s1 with accts := s1.accts.modify who G }.accts.map
      fun a => supPend { s1 with accts := s1.accts.modify who G } a +
        borPend { s1 with accts := s1.accts.modify who G } a).sum) =
      ((s1.accts.modify who G).map fun a => supPend s1 a + borPend s1 a).sum :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => by rfl)
  have eAc : ({ s1 with accts := s1.accts.modify who G } : St).accts = s1.accts.modify who G := rfl
  have hmod : ((s1.accts.modify who G).map fun a => (a.accrued + a.wallet) * doubleScale +
      supPend s1 a + borPend s1 a).sum =
      ((s1.accts.map fun a => (a.accrued + a.wallet) * doubleScale +
      supPend s1 a + borPend s1 a).sum) := by
    apply ProofForgeFin.Ledger.sum_map_modify_eq _ _ _ _ noAcct (fun _ => ?_)
    unfold supPend borPend
    have z1 : ProofForgeFin.DeFi.Rewards.pending (G (s1.accts.getD who noAcct)).borrow
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (G (s1.accts.getD who noAcct)).borrowerIndex s1.borrowState.index)
        s1.borrowState.index = 0 := by
      rw [hGborI, hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    have z2 : ProofForgeFin.DeFi.Rewards.pending (s1.accts.getD who noAcct).borrow
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s1.accts.getD who noAcct).borrowerIndex s1.borrowState.index)
        s1.borrowState.index = 0 := by
      rw [hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    rw [hGacc, hGwal, hGsup, hGsupI, z1, z2]
  unfold pot
  rw [hUs, hUb, eAc]
  simp only [hC]
  rw [nM]
  simp only [← Nat.add_assoc, ← ProofForgeFin.DeFi.Rewards.sum_map_add]
  rw [hmod]

/-- Paid-out form of `grant`: the result when `who` is actually paid. -/
def grantPaid (s : St) (who : Account) : St :=
  { s with reserve := s.reserve - (s.acct who).accrued, accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }

theorem pot_grant (s : St) (who : Account) : pot (grant s who) = pot s := by
  unfold grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · rw [if_pos hc]
    show pot (grantPaid s who) = pot s
    have eAc : (grantPaid s who).accts = s.accts.modify who fun b => ({ b with accrued := 0, wallet := b.wallet + b.accrued } : Acct) := rfl
    have hU : unidxS (grantPaid s who) + unidxB (grantPaid s who) = unidxS s + unidxB s := rfl
    have nM : ((s.accts.modify who fun b => ({ b with accrued := 0, wallet := b.wallet + b.accrued } : Acct)).map fun a => supPend (grantPaid s who) a + borPend (grantPaid s who) a).sum = ((s.accts.modify who fun b => ({ b with accrued := 0, wallet := b.wallet + b.accrued } : Acct)).map fun a => supPend s a + borPend s a).sum :=
      ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => by rfl)
    have hMeq : ((s.accts.modify who fun b => ({ b with accrued := 0, wallet := b.wallet + b.accrued } : Acct)).map fun a => supPend s a + borPend s a).sum = ((s.accts.map fun a => supPend s a + borPend s a).sum) :=
      ProofForgeFin.Ledger.sum_map_modify_eq _ _ _ _ noAcct (fun _ => rfl)
    have hCeq : ((s.accts.modify who fun b => ({ b with accrued := 0, wallet := b.wallet + b.accrued } : Acct)).map fun a => a.accrued + a.wallet).sum = ((s.accts.map fun a => a.accrued + a.wallet).sum) := by
      apply ProofForgeFin.Ledger.sum_map_modify_eq _ _ _ _ noAcct (fun _ => ?_)
      show (0 + ((s.accts.getD who noAcct).wallet + (s.accts.getD who noAcct).accrued)) =
        ((s.accts.getD who noAcct).accrued + (s.accts.getD who noAcct).wallet)
      omega
    unfold pot St.credited
    rw [eAc, nM, hMeq, hCeq, hU]
  · rw [if_neg hc]

theorem pot_advance (s : St) (k : Nat)
    (hsb : s.supplyState.block ≤ s.blockNumber) (hbb : s.borrowState.block ≤ s.blockNumber) :
    pot { s with blockNumber := s.blockNumber + k } =
      pot s + doubleScale * (k * s.supplyState.speed + k * s.borrowState.speed) := by
  have hC : St.credited { s with blockNumber := s.blockNumber + k } = St.credited s := rfl
  have hM : (({ s with blockNumber := s.blockNumber + k }).accts.map fun a =>
      supPend { s with blockNumber := s.blockNumber + k } a +
        borPend { s with blockNumber := s.blockNumber + k } a).sum =
      ((s.accts.map fun a => supPend s a + borPend s a).sum) :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun a ha => by rfl)
  have hUs : unidxS { s with blockNumber := s.blockNumber + k } =
      unidxS s + k * s.supplyState.speed := by
    unfold unidxS
    show ((s.blockNumber + k - s.supplyState.block) * s.supplyState.speed) =
      ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed)
    have e1 : s.blockNumber + k - s.supplyState.block =
        (s.blockNumber - s.supplyState.block) + k := by omega
    rw [e1, Nat.add_mul]
  have hUb : unidxB { s with blockNumber := s.blockNumber + k } =
      unidxB s + k * s.borrowState.speed := by
    unfold unidxB
    show ((s.blockNumber + k - s.borrowState.block) * s.borrowState.speed) =
      ((s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed)
    have e1 : s.blockNumber + k - s.borrowState.block =
        (s.blockNumber - s.borrowState.block) + k := by omega
    rw [e1, Nat.add_mul]
  unfold pot
  rw [hC, hM, hUs, hUb]
  simp only [Nat.mul_add]
  omega

theorem pot_drip (s : St) (x : Nat) : pot { s with reserve := s.reserve + x } = pot s := rfl

theorem pot_speedAssignSupply (sA : St) (a : Nat)
    (hblk : sA.supplyState.block = sA.blockNumber) :
    pot { sA with supplyState := { sA.supplyState with speed := a } } = pot sA := by
  have hC : St.credited { sA with supplyState := { sA.supplyState with speed := a } } =
      St.credited sA := rfl
  have hM : (({ sA with supplyState := { sA.supplyState with speed := a } }).accts.map fun x =>
      supPend { sA with supplyState := { sA.supplyState with speed := a } } x +
        borPend { sA with supplyState := { sA.supplyState with speed := a } } x).sum =
      ((sA.accts.map fun x => supPend sA x + borPend sA x).sum) :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun x hx => by rfl)
  have hUb : unidxB { sA with supplyState := { sA.supplyState with speed := a } } = unidxB sA := rfl
  have hU0a : unidxS sA = 0 := by
    unfold unidxS
    rw [hblk, Nat.sub_self, Nat.zero_mul]
  have hU0n : unidxS { sA with supplyState := { sA.supplyState with speed := a } } = 0 := by
    unfold unidxS
    show (sA.blockNumber - sA.supplyState.block) * _ = 0
    rw [hblk, Nat.sub_self, Nat.zero_mul]
  unfold pot
  rw [hC, hM, hUb, hU0n, hU0a]

theorem pot_settleSupply (s : St) (who : Account) (s' : St)
    (hd : distributeSupplierComp s who = some s') :
    pot s' ≤ pot s ∧
      ProofForgeFin.DeFi.Rewards.owed (s.acct who).supply (accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (s'.acct who).accrued - (s.acct who).accrued := by
  obtain ⟨hle, hdist⟩ := dist_supply_eq s who s' hd
  rw [hdist]
  simp only [St.acct]
  exact pot_settleSupply_aux s who hle

theorem pot_settleBorrow (s : St) (who : Account) (s' : St)
    (hd : distributeBorrowerComp s who = some s') :
    pot s' ≤ pot s ∧
      ProofForgeFin.DeFi.Rewards.owed (s.acct who).borrow (accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (s'.acct who).accrued - (s.acct who).accrued := by
  obtain ⟨hle, hdist⟩ := dist_borrow_eq s who s' hd
  rw [hdist]
  simp only [St.acct]
  exact pot_settleBorrow_aux s who hle

theorem Inv_supplyDist (g : Nat × Nat) (s : St) (who : Account) (s' : St)
    (hinv : Inv g s) (h : SupplyDistributed s who s') : Inv g s' := by
  unfold Inv at hinv
  obtain ⟨hsp1, hsp2, hsb, hbb, hall⟩ := hinv
  unfold SupplyDistributed at h
  obtain ⟨hb, hle, hs'⟩ := h
  have hspd : (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = s.supplyState.speed :=
    accrueSide_speed _ _ _
  have hblk : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber :=
    accrueSide_block _ _ _
  have hg : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    le_accrueSide_index _ _ _
  rw [hs']
  unfold Inv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    rw [hspd]
    exact hsp1
  · simp only []
    exact hsp2
  · simp only []
    rw [hblk]
    exact Nat.le_refl _
  · simp only []
    exact hbb
  · refine ProofForgeFin.DeFi.Rewards.forall_mem_modify ?_ ?_
    · intro a ha
      exact ⟨Nat.le_trans (hall a ha).1 hg, (hall a ha).2⟩
    · intro a ha
      exact ⟨Nat.le_refl _, (hall a ha).2⟩

theorem Inv_borrowDist (g : Nat × Nat) (s : St) (who : Account) (s' : St)
    (hinv : Inv g s) (h : BorrowDistributed s who s') : Inv g s' := by
  unfold Inv at hinv
  obtain ⟨hsp1, hsp2, hsb, hbb, hall⟩ := hinv
  unfold BorrowDistributed at h
  obtain ⟨hb, hle, hs'⟩ := h
  have hspd : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed = s.borrowState.speed :=
    accrueSide_speed _ _ _
  have hblk : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber :=
    accrueSide_block _ _ _
  have hg : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    le_accrueSide_index _ _ _
  rw [hs']
  unfold Inv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    exact hsp1
  · simp only []
    rw [hspd]
    exact hsp2
  · simp only []
    exact hsb
  · simp only []
    rw [hblk]
    exact Nat.le_refl _
  · refine ProofForgeFin.DeFi.Rewards.forall_mem_modify ?_ ?_
    · intro a ha
      exact ⟨(hall a ha).1, Nat.le_trans (hall a ha).2 hg⟩
    · intro a ha
      exact ⟨(hall a ha).1, Nat.le_refl _⟩

theorem Inv_grant (g : Nat × Nat) (s : St) (who : Account) (hinv : Inv g s) :
    Inv g (grant s who) := by
  unfold grant
  by_cases hc : 0 < (s.acct who).accrued
  · rw [if_pos hc]
    unfold Inv at hinv ⊢
    obtain ⟨hsp1, hsp2, hsb, hbb, hall⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only []
      exact hsp1
    · simp only []
      exact hsp2
    · simp only []
      exact hsb
    · simp only []
      exact hbb
    · refine ProofForgeFin.DeFi.Rewards.forall_mem_modify ?_ ?_
      · intro a ha
        exact hall a ha
      · intro a ha
        exact hall a ha
  · rw [if_neg hc]
    exact hinv

theorem Inv_balance (g : Nat × Nat) (s1 : St) (who : Account) (G : Acct → Acct)
    (hGs : ∀ a, (G a).supplierIndex = a.supplierIndex)
    (hGb : ∀ a, (G a).borrowerIndex = a.borrowerIndex)
    (hinv1 : Inv g s1) : Inv g { s1 with accts := s1.accts.modify who G } := by
  unfold Inv at hinv1 ⊢
  obtain ⟨hsp1, hsp2, hsb, hbb, hall⟩ := hinv1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    exact hsp1
  · simp only []
    exact hsp2
  · simp only []
    exact hsb
  · simp only []
    exact hbb
  · refine ProofForgeFin.DeFi.Rewards.forall_mem_modify ?_ ?_
    · intro a ha
      exact hall a ha
    · intro a ha
      obtain ⟨h1, h2⟩ := hall a ha
      rw [hGs, hGb]
      exact ⟨h1, h2⟩

theorem Inv_advance (g : Nat × Nat) (s : St) (k : Nat) (hinv : Inv g s) :
    Inv g { s with blockNumber := s.blockNumber + k } := by
  unfold Inv at hinv ⊢
  obtain ⟨hsp1, hsp2, hsb, hbb, hall⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    exact hsp1
  · simp only []
    exact hsp2
  · simp only []
    exact Nat.le_trans hsb (Nat.le_add_right _ _)
  · simp only []
    exact Nat.le_trans hbb (Nat.le_add_right _ _)
  · intro a ha
    exact hall a ha

theorem Inv_drip (g : Nat × Nat) (s : St) (x : Nat) (hinv : Inv g s) :
    Inv g { s with reserve := s.reserve + x } := by
  unfold Inv at hinv ⊢
  obtain ⟨hsp1, hsp2, hsb, hbb, hall⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only []
    exact hsp1
  · simp only []
    exact hsp2
  · simp only []
    exact hsb
  · simp only []
    exact hbb
  · intro a ha
    exact hall a ha

theorem hookRecSupply (mid : St) (who : Account) (s1 : St)
    (hd : distributeSupplierComp mid who = some s1) (hlen : who < mid.accts.length) :
    (s1.acct who).supplierIndex = s1.supplyState.index := by
  obtain ⟨hle, hdist⟩ := dist_supply_eq mid who s1 hd
  rw [hdist]
  simp only [St.acct]
  rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]

theorem hookRecBorrow (mid : St) (who : Account) (s1 : St)
    (hd : distributeBorrowerComp mid who = some s1) (hlen : who < mid.accts.length) :
    (s1.acct who).borrowerIndex = s1.borrowState.index := by
  obtain ⟨hle, hdist⟩ := dist_borrow_eq mid who s1 hd
  rw [hdist]
  simp only [St.acct]
  rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]

def potAt (who : Account) (s : St) : Nat :=
  St.creditedTo s who * doubleScale + supPend s (s.acct who) + borPend s (s.acct who) +
  doubleScale * ((if 0 < (s.acct who).supply then unidxS s else 0) +
                 (if 0 < (s.acct who).borrow then unidxB s else 0))

theorem potAt_accrueSupply (s : St) (who : Account) (mid : St)
    (hmid : updateCompSupplyIndex s = some mid) : potAt who mid ≤ potAt who s := by
  obtain ⟨hb, hmid_eq⟩ := update_supply_eq s mid hmid
  have eAC : mid.accts = s.accts := by rw [hmid_eq]
  have eB : mid.borrowState = s.borrowState := by rw [hmid_eq]
  have eBlk : mid.blockNumber = s.blockNumber := by rw [hmid_eq]
  have e1 : mid.supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hmid_eq]
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [eAC]
  have hC : St.creditedTo mid who = St.creditedTo s who := by unfold St.creditedTo; rw [hacct]
  have hB : borPend mid (s.acct who) = borPend s (s.acct who) := by
    unfold borPend; rw [eB]
  have hUb : unidxB mid = unidxB s := by unfold unidxB; rw [eBlk, eB]
  have hU0 : unidxS mid = 0 := by
    rw [hmid_eq]
    unfold unidxS
    show (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.blockNumber -
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.block) *
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.speed) = 0
    rw [accrueSide_block]
    show (s.blockNumber - s.blockNumber) * _ = 0
    rw [Nat.sub_self, Nat.zero_mul]
  have ht : supPend mid (s.acct who) ≤ supPend s (s.acct who) +
      (s.acct who).supply * (mid.supplyState.index - s.supplyState.index) := by
    unfold supPend
    rw [e1]
    exact ProofForgeFin.Accumulator.owed_le_add
      (ProofForgeFin.Accumulator.firstStart_mono compInitialIndex (s.acct who).supplierIndex
        (le_accrueSide_index s.supplyState s.blockNumber (totalSupply s)))
  have hle : (s.acct who).supply ≤ totalSupply s := supply_le_total _ _
  have hcov : (s.acct who).supply * (mid.supplyState.index - s.supplyState.index) ≤
      doubleScale * unidxS s := by
    have hcov0 := covered_supply s
    rw [← e1] at hcov0
    exact Nat.le_trans (Nat.mul_le_mul hle (Nat.le_refl _)) hcov0
  unfold potAt
  rw [hC, hacct, hB, hUb, hU0]
  by_cases hc : 0 < (s.acct who).supply
  · rw [if_pos hc, if_pos hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    omega
  · have h0 : (s.acct who).supply = 0 := by omega
    rw [if_neg hc, if_neg hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    rw [h0] at ht
    simp only [Nat.zero_mul, Nat.add_zero] at ht
    omega

theorem potAt_accrueBorrow (s : St) (who : Account) (mid : St)
    (hmid : updateCompBorrowIndex s = some mid) : potAt who mid ≤ potAt who s := by
  obtain ⟨hb, hmid_eq⟩ := update_borrow_eq s mid hmid
  have eAC : mid.accts = s.accts := by rw [hmid_eq]
  have eS : mid.supplyState = s.supplyState := by rw [hmid_eq]
  have eBlk : mid.blockNumber = s.blockNumber := by rw [hmid_eq]
  have e1 : mid.borrowState.index =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hmid_eq]
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [eAC]
  have hC : St.creditedTo mid who = St.creditedTo s who := by unfold St.creditedTo; rw [hacct]
  have hS : supPend mid (s.acct who) = supPend s (s.acct who) := by
    unfold supPend; rw [eS]
  have hUs : unidxS mid = unidxS s := by unfold unidxS; rw [eBlk, eS]
  have hU0 : unidxB mid = 0 := by
    rw [hmid_eq]
    unfold unidxB
    show (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.blockNumber -
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.block) *
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.speed) = 0
    rw [accrueSide_block]
    show (s.blockNumber - s.blockNumber) * _ = 0
    rw [Nat.sub_self, Nat.zero_mul]
  have ht : borPend mid (s.acct who) ≤ borPend s (s.acct who) +
      (s.acct who).borrow * (mid.borrowState.index - s.borrowState.index) := by
    unfold borPend
    rw [e1]
    exact ProofForgeFin.Accumulator.owed_le_add
      (ProofForgeFin.Accumulator.firstStart_mono compInitialIndex (s.acct who).borrowerIndex
        (le_accrueSide_index s.borrowState s.blockNumber (totalBorrows s)))
  have hle : (s.acct who).borrow ≤ totalBorrows s := borrow_le_total _ _
  have hcov : (s.acct who).borrow * (mid.borrowState.index - s.borrowState.index) ≤
      doubleScale * unidxB s := by
    have hcov0 := covered_borrow s
    rw [← e1] at hcov0
    exact Nat.le_trans (Nat.mul_le_mul hle (Nat.le_refl _)) hcov0
  unfold potAt
  rw [hC, hacct, hS, hUs, hU0]
  by_cases hc : 0 < (s.acct who).borrow
  · rw [if_pos hc, if_pos hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    omega
  · have h0 : (s.acct who).borrow = 0 := by omega
    rw [if_neg hc, if_neg hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    rw [h0] at ht
    simp only [Nat.zero_mul, Nat.add_zero] at ht
    omega

theorem potAt_supplyGrow (s s' : St) (v : Account)
    (hac : (s'.acct v) = (s.acct v))
    (hbs : s'.borrowState = s.borrowState)
    (hblk : s'.blockNumber = s.blockNumber)
    (hU0 : unidxS s' = 0)
    (hidx : s.supplyState.index ≤ s'.supplyState.index)
    (hle : (s.acct v).supply ≤ totalSupply s)
    (hcov : totalSupply s * (s'.supplyState.index - s.supplyState.index) ≤ doubleScale * unidxS s) :
    potAt v s' ≤ potAt v s := by
  have hC : St.creditedTo s' v = St.creditedTo s v := by unfold St.creditedTo; rw [hac]
  have hB : borPend s' (s.acct v) = borPend s (s.acct v) := by unfold borPend; rw [hbs]
  have hUb : unidxB s' = unidxB s := by unfold unidxB; rw [hblk, hbs]
  have ht : supPend s' (s.acct v) ≤ supPend s (s.acct v) +
      (s.acct v).supply * (s'.supplyState.index - s.supplyState.index) := by
    unfold supPend
    exact ProofForgeFin.Accumulator.owed_le_add
      (ProofForgeFin.Accumulator.firstStart_mono compInitialIndex (s.acct v).supplierIndex hidx)
  have hcov2 : (s.acct v).supply * (s'.supplyState.index - s.supplyState.index) ≤
      doubleScale * unidxS s :=
    Nat.le_trans (Nat.mul_le_mul hle (Nat.le_refl _)) hcov
  unfold potAt
  rw [hC, hac, hB, hUb, hU0]
  by_cases hc : 0 < (s.acct v).supply
  · rw [if_pos hc, if_pos hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    omega
  · have h0 : (s.acct v).supply = 0 := by omega
    rw [if_neg hc, if_neg hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    rw [h0] at ht
    simp only [Nat.zero_mul, Nat.add_zero] at ht
    omega

theorem potAt_settleSupply_self (s : St) (who : Account) (s' : St)
    (hd : distributeSupplierComp s who = some s') (hlen : who < s.accts.length) :
    potAt who s' ≤ potAt who s := by
  obtain ⟨hle, hdist⟩ := dist_supply_eq s who s' hd
  have hacc : (s'.acct who).accrued = (s.acct who).accrued + creditFor (s.acct who).supply
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) s.supplyState.index := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hwal : (s'.acct who).wallet = (s.acct who).wallet := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hsup : (s'.acct who).supply = (s.acct who).supply := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hbor : (s'.acct who).borrow = (s.acct who).borrow := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hborI : (s'.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hsupI : (s'.acct who).supplierIndex = s'.supplyState.index :=
    hookRecSupply s who s' hd hlen
  have eSS : s'.supplyState = s.supplyState := by rw [hdist]
  have eB : s'.borrowState = s.borrowState := by rw [hdist]
  have eBlk : s'.blockNumber = s.blockNumber := by rw [hdist]
  have hB : borPend s' (s'.acct who) = borPend s (s.acct who) := by
    unfold borPend; rw [hbor, hborI, eB]
  have hUb : unidxB s' = unidxB s := by unfold unidxB; rw [eBlk, eB]
  have hUs : unidxS s' = unidxS s := by unfold unidxS; rw [eBlk, eSS]
  have htermS : (if 0 < (s'.acct who).supply then unidxS s' else 0) =
      (if 0 < (s.acct who).supply then unidxS s else 0) := by rw [hsup, hUs]
  have htermB : (if 0 < (s'.acct who).borrow then unidxB s' else 0) =
      (if 0 < (s.acct who).borrow then unidxB s else 0) := by rw [hbor, hUb]
  have hCs : St.creditedTo s who = (s.acct who).accrued + (s.acct who).wallet := rfl
  have hC : St.creditedTo s' who =
      ((s.acct who).accrued + (s.acct who).wallet) +
      (s.acct who).supply *
        (s.supplyState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s.acct who).supplierIndex s.supplyState.index) / doubleScale := by
    unfold St.creditedTo
    rw [hacc, hwal, bridge_start]
    unfold creditFor
    omega
  have hset : (((s.acct who).accrued + (s.acct who).wallet) +
      (s.acct who).supply *
        (s.supplyState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s.acct who).supplierIndex s.supplyState.index) / doubleScale) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (s.acct who).supply
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex s.supplyState.index s.supplyState.index)
        s.supplyState.index ≤
      ((s.acct who).accrued + (s.acct who).wallet) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (s.acct who).supply
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s.acct who).supplierIndex s.supplyState.index)
        s.supplyState.index :=
    ProofForgeFin.DeFi.Rewards.settle_le rfl (Nat.le_refl _)
      (ProofForgeFin.Accumulator.le_firstStart_self _ _)
  unfold potAt
  rw [hC, hCs, hB, htermS, htermB]
  unfold supPend
  rw [hsup, hsupI, eSS]
  omega

theorem potAt_borrowGrow (s s' : St) (v : Account)
    (hac : (s'.acct v) = (s.acct v))
    (hss : s'.supplyState = s.supplyState)
    (hblk : s'.blockNumber = s.blockNumber)
    (hU0 : unidxB s' = 0)
    (hidx : s.borrowState.index ≤ s'.borrowState.index)
    (hle : (s.acct v).borrow ≤ totalBorrows s)
    (hcov : totalBorrows s * (s'.borrowState.index - s.borrowState.index) ≤ doubleScale * unidxB s) :
    potAt v s' ≤ potAt v s := by
  have hC : St.creditedTo s' v = St.creditedTo s v := by unfold St.creditedTo; rw [hac]
  have hS : supPend s' (s.acct v) = supPend s (s.acct v) := by unfold supPend; rw [hss]
  have hUs : unidxS s' = unidxS s := by unfold unidxS; rw [hblk, hss]
  have ht : borPend s' (s.acct v) ≤ borPend s (s.acct v) +
      (s.acct v).borrow * (s'.borrowState.index - s.borrowState.index) := by
    unfold borPend
    exact ProofForgeFin.Accumulator.owed_le_add
      (ProofForgeFin.Accumulator.firstStart_mono compInitialIndex (s.acct v).borrowerIndex hidx)
  have hcov2 : (s.acct v).borrow * (s'.borrowState.index - s.borrowState.index) ≤
      doubleScale * unidxB s :=
    Nat.le_trans (Nat.mul_le_mul hle (Nat.le_refl _)) hcov
  unfold potAt
  rw [hC, hac, hS, hUs, hU0]
  by_cases hc : 0 < (s.acct v).borrow
  · rw [if_pos hc, if_pos hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    omega
  · have h0 : (s.acct v).borrow = 0 := by omega
    rw [if_neg hc, if_neg hc]
    simp only [Nat.mul_add, Nat.mul_zero]
    rw [h0] at ht
    simp only [Nat.zero_mul, Nat.add_zero] at ht
    omega

theorem potAt_settleBorrow_self (s : St) (who : Account) (s' : St)
    (hd : distributeBorrowerComp s who = some s') (hlen : who < s.accts.length) :
    potAt who s' ≤ potAt who s := by
  obtain ⟨hle, hdist⟩ := dist_borrow_eq s who s' hd
  have hacc : (s'.acct who).accrued = (s.acct who).accrued + creditFor (s.acct who).borrow
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) s.borrowState.index := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hwal : (s'.acct who).wallet = (s.acct who).wallet := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hsup : (s'.acct who).supply = (s.acct who).supply := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hbor : (s'.acct who).borrow = (s.acct who).borrow := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hsupI : (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by
    rw [hdist]
    simp only [St.acct]
    rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
  have hborI : (s'.acct who).borrowerIndex = s'.borrowState.index :=
    hookRecBorrow s who s' hd hlen
  have eSS : s'.supplyState = s.supplyState := by rw [hdist]
  have eB : s'.borrowState = s.borrowState := by rw [hdist]
  have eBlk : s'.blockNumber = s.blockNumber := by rw [hdist]
  have hS : supPend s' (s'.acct who) = supPend s (s.acct who) := by
    unfold supPend; rw [hsup, hsupI, eSS]
  have hUb : unidxB s' = unidxB s := by unfold unidxB; rw [eBlk, eB]
  have hUs : unidxS s' = unidxS s := by unfold unidxS; rw [eBlk, eSS]
  have htermS : (if 0 < (s'.acct who).supply then unidxS s' else 0) =
      (if 0 < (s.acct who).supply then unidxS s else 0) := by rw [hsup, hUs]
  have htermB : (if 0 < (s'.acct who).borrow then unidxB s' else 0) =
      (if 0 < (s.acct who).borrow then unidxB s else 0) := by rw [hbor, hUb]
  have hCs : St.creditedTo s who = (s.acct who).accrued + (s.acct who).wallet := rfl
  have hC : St.creditedTo s' who =
      ((s.acct who).accrued + (s.acct who).wallet) +
      (s.acct who).borrow *
        (s.borrowState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s.acct who).borrowerIndex s.borrowState.index) / doubleScale := by
    unfold St.creditedTo
    rw [hacc, hwal, bridge_start]
    unfold creditFor
    omega
  have hset : (((s.acct who).accrued + (s.acct who).wallet) +
      (s.acct who).borrow *
        (s.borrowState.index - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s.acct who).borrowerIndex s.borrowState.index) / doubleScale) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (s.acct who).borrow
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex s.borrowState.index s.borrowState.index)
        s.borrowState.index ≤
      ((s.acct who).accrued + (s.acct who).wallet) * doubleScale +
      ProofForgeFin.DeFi.Rewards.pending (s.acct who).borrow
        (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex
          (s.acct who).borrowerIndex s.borrowState.index)
        s.borrowState.index :=
    ProofForgeFin.DeFi.Rewards.settle_le rfl (Nat.le_refl _)
      (ProofForgeFin.Accumulator.le_firstStart_self _ _)
  unfold potAt
  rw [hC, hCs, hS, htermS, htermB]
  unfold borPend
  rw [hbor, hborI, eB]
  omega

theorem potAt_hookSupply (s : St) (who tgt : Account) (mid s1 : St)
    (hu : updateCompSupplyIndex s = some mid) (hd : distributeSupplierComp mid who = some s1) :
    potAt tgt s1 ≤ potAt tgt s := by
  have hacc : potAt tgt mid ≤ potAt tgt s := potAt_accrueSupply s tgt mid hu
  have hsettle : potAt tgt s1 ≤ potAt tgt mid := by
    obtain ⟨hleD, hdist⟩ := dist_supply_eq mid who s1 hd
    obtain ⟨hbU, hmid_eqU⟩ := update_supply_eq s mid hu
    have eS : s1.supplyState = mid.supplyState := by rw [hdist]
    have hbs : s1.borrowState = mid.borrowState := by rw [hdist]
    have hblk : s1.blockNumber = mid.blockNumber := by rw [hdist]
    have eMidBlk : mid.supplyState.block = mid.blockNumber := by
      have h1 : mid.supplyState.block =
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).block := by rw [hmid_eqU]
      have h2 : mid.blockNumber = s.blockNumber := by rw [hmid_eqU]
      rw [h1, accrueSide_block, h2]
    have hU0s1 : unidxS s1 = 0 := by
      unfold unidxS
      rw [hblk, eS, eMidBlk, Nat.sub_self, Nat.zero_mul]
    have hidx : mid.supplyState.index ≤ s1.supplyState.index := by simp [eS]
    have hcov : totalSupply mid * (s1.supplyState.index - mid.supplyState.index) ≤
        doubleScale * unidxS mid := by
      rw [eS]
      simp
    by_cases htw : tgt = who
    · rw [htw]
      by_cases hlen : who < mid.accts.length
      · exact potAt_settleSupply_self mid who s1 hd hlen
      · have hac : (s1.acct who) = (mid.acct who) := by
          rw [hdist]
          simp only [St.acct]
          rw [ProofForgeFin.Ledger.getD_modify]
          rw [if_neg (fun h => hlen h.2)]
        have hle : (mid.acct who).supply ≤ totalSupply mid := supply_le_total _ _
        exact potAt_supplyGrow mid s1 who hac hbs hblk hU0s1 hidx hle hcov
    · have hac : (s1.acct tgt) = (mid.acct tgt) := by
        rw [hdist]
        simp only [St.acct]
        exact ProofForgeFin.Ledger.getD_modify_ne _ _ _ (Ne.symm htw)
      have hle : (mid.acct tgt).supply ≤ totalSupply mid := supply_le_total _ _
      exact potAt_supplyGrow mid s1 tgt hac hbs hblk hU0s1 hidx hle hcov
  exact Nat.le_trans hsettle hacc

theorem potAt_hookBorrow (s : St) (who tgt : Account) (mid s1 : St)
    (hu : updateCompBorrowIndex s = some mid) (hd : distributeBorrowerComp mid who = some s1) :
    potAt tgt s1 ≤ potAt tgt s := by
  have hacc : potAt tgt mid ≤ potAt tgt s := potAt_accrueBorrow s tgt mid hu
  have hsettle : potAt tgt s1 ≤ potAt tgt mid := by
    obtain ⟨hleD, hdist⟩ := dist_borrow_eq mid who s1 hd
    obtain ⟨hbU, hmid_eqU⟩ := update_borrow_eq s mid hu
    have eB : s1.borrowState = mid.borrowState := by rw [hdist]
    have hss : s1.supplyState = mid.supplyState := by rw [hdist]
    have hblk : s1.blockNumber = mid.blockNumber := by rw [hdist]
    have eMidBlk : mid.borrowState.block = mid.blockNumber := by
      have h1 : mid.borrowState.block =
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block := by rw [hmid_eqU]
      have h2 : mid.blockNumber = s.blockNumber := by rw [hmid_eqU]
      rw [h1, accrueSide_block, h2]
    have hU0s1 : unidxB s1 = 0 := by
      unfold unidxB
      rw [hblk, eB, eMidBlk, Nat.sub_self, Nat.zero_mul]
    have hidx : mid.borrowState.index ≤ s1.borrowState.index := by simp [eB]
    have hcov : totalBorrows mid * (s1.borrowState.index - mid.borrowState.index) ≤
        doubleScale * unidxB mid := by
      rw [eB]
      simp
    by_cases htw : tgt = who
    · rw [htw]
      by_cases hlen : who < mid.accts.length
      · exact potAt_settleBorrow_self mid who s1 hd hlen
      · have hac : (s1.acct who) = (mid.acct who) := by
          rw [hdist]
          simp only [St.acct]
          rw [ProofForgeFin.Ledger.getD_modify]
          rw [if_neg (fun h => hlen h.2)]
        have hle : (mid.acct who).borrow ≤ totalBorrows mid := borrow_le_total _ _
        exact potAt_borrowGrow mid s1 who hac hss hblk hU0s1 hidx hle hcov
    · have hac : (s1.acct tgt) = (mid.acct tgt) := by
        rw [hdist]
        simp only [St.acct]
        exact ProofForgeFin.Ledger.getD_modify_ne _ _ _ (Ne.symm htw)
      have hle : (mid.acct tgt).borrow ≤ totalBorrows mid := borrow_le_total _ _
      exact potAt_borrowGrow mid s1 tgt hac hss hblk hU0s1 hidx hle hcov
  exact Nat.le_trans hsettle hacc

theorem potAt_balanceSupply (s1 : St) (who tgt : Account) (G : Acct → Acct)
    (hlen : who < s1.accts.length)
    (hU : unidxS s1 = 0)
    (hrec : (s1.acct who).supplierIndex = s1.supplyState.index)
    (hGacc : ∀ a, (G a).accrued = a.accrued)
    (hGwal : ∀ a, (G a).wallet = a.wallet)
    (hGbor : ∀ a, (G a).borrow = a.borrow)
    (hGborI : ∀ a, (G a).borrowerIndex = a.borrowerIndex)
    (hGsupI : ∀ a, (G a).supplierIndex = a.supplierIndex) :
    potAt tgt { s1 with accts := s1.accts.modify who G } ≤ potAt tgt s1 := by
  by_cases htw : tgt = who
  · rw [htw]
    have hread : (({ s1 with accts := s1.accts.modify who G } : St).acct who) =
        G (s1.acct who) := by
      simp only [St.acct]
      rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
    have hC : St.creditedTo { s1 with accts := s1.accts.modify who G } who =
        St.creditedTo s1 who := by
      unfold St.creditedTo; rw [hread, hGacc, hGwal]
    have z1 : supPend { s1 with accts := s1.accts.modify who G } (G (s1.acct who)) = 0 := by
      unfold supPend
      rw [hGsupI, hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    have z2 : supPend s1 (s1.acct who) = 0 := by
      unfold supPend
      rw [hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    have hB : borPend { s1 with accts := s1.accts.modify who G } (G (s1.acct who)) =
        borPend s1 (s1.acct who) := by
      unfold borPend; rw [hGbor, hGborI]
    have hU0 : unidxS ({ s1 with accts := s1.accts.modify who G } : St) = unidxS s1 := rfl
    have htermS : doubleScale *
        (if 0 < (G (s1.acct who)).supply then
          unidxS { s1 with accts := s1.accts.modify who G } else 0) ≤
        doubleScale * (if 0 < (s1.acct who).supply then unidxS s1 else 0) := by
      rw [hU0, hU]
      by_cases hc : 0 < (G (s1.acct who)).supply <;> simp [hc]
    have hUb0 : unidxB ({ s1 with accts := s1.accts.modify who G } : St) = unidxB s1 := rfl
    have htermB : (if 0 < (G (s1.acct who)).borrow then
        unidxB { s1 with accts := s1.accts.modify who G } else 0) =
        (if 0 < (s1.acct who).borrow then unidxB s1 else 0) := by
      rw [show (G (s1.acct who)).borrow = (s1.acct who).borrow from hGbor _, hUb0]
    unfold potAt
    rw [hC, hread, z1, z2, hB, htermB]
    simp only [Nat.mul_add]
    omega
  · have hac : (({ s1 with accts := s1.accts.modify who G } : St).acct tgt) =
        (s1.acct tgt) := by
      simp only [St.acct]
      exact ProofForgeFin.Ledger.getD_modify_ne _ _ _ (Ne.symm htw)
    have hC' : St.creditedTo { s1 with accts := s1.accts.modify who G } tgt =
        St.creditedTo s1 tgt := by
      unfold St.creditedTo; rw [hac]
    have hS' : supPend { s1 with accts := s1.accts.modify who G } (s1.acct tgt) =
        supPend s1 (s1.acct tgt) := rfl
    have hB' : borPend { s1 with accts := s1.accts.modify who G } (s1.acct tgt) =
        borPend s1 (s1.acct tgt) := rfl
    have hUs0 : unidxS ({ s1 with accts := s1.accts.modify who G } : St) = unidxS s1 := rfl
    have hUb0 : unidxB ({ s1 with accts := s1.accts.modify who G } : St) = unidxB s1 := rfl
    simp only [potAt, hC', hac, hS', hB', hUs0, hUb0, Nat.le_refl]

theorem potAt_balanceBorrow (s1 : St) (who tgt : Account) (G : Acct → Acct)
    (hlen : who < s1.accts.length)
    (hU : unidxB s1 = 0)
    (hrec : (s1.acct who).borrowerIndex = s1.borrowState.index)
    (hGacc : ∀ a, (G a).accrued = a.accrued)
    (hGwal : ∀ a, (G a).wallet = a.wallet)
    (hGsup : ∀ a, (G a).supply = a.supply)
    (hGsupI : ∀ a, (G a).supplierIndex = a.supplierIndex)
    (hGborI : ∀ a, (G a).borrowerIndex = a.borrowerIndex) :
    potAt tgt { s1 with accts := s1.accts.modify who G } ≤ potAt tgt s1 := by
  by_cases htw : tgt = who
  · rw [htw]
    have hread : (({ s1 with accts := s1.accts.modify who G } : St).acct who) =
        G (s1.acct who) := by
      simp only [St.acct]
      rw [ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hlen]
    have hC : St.creditedTo { s1 with accts := s1.accts.modify who G } who =
        St.creditedTo s1 who := by
      unfold St.creditedTo; rw [hread, hGacc, hGwal]
    have z1 : borPend { s1 with accts := s1.accts.modify who G } (G (s1.acct who)) = 0 := by
      unfold borPend
      rw [hGborI, hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    have z2 : borPend s1 (s1.acct who) = 0 := by
      unfold borPend
      rw [hrec]
      exact ProofForgeFin.Accumulator.owed_firstStart_self _ _ _
    have hS : supPend { s1 with accts := s1.accts.modify who G } (G (s1.acct who)) =
        supPend s1 (s1.acct who) := by
      unfold supPend; rw [hGsup, hGsupI]
    have hU0 : unidxB ({ s1 with accts := s1.accts.modify who G } : St) = unidxB s1 := rfl
    have htermB : doubleScale *
        (if 0 < (G (s1.acct who)).borrow then
          unidxB { s1 with accts := s1.accts.modify who G } else 0) ≤
        doubleScale * (if 0 < (s1.acct who).borrow then unidxB s1 else 0) := by
      rw [hU0, hU]
      by_cases hc : 0 < (G (s1.acct who)).borrow <;> simp [hc]
    have hUs0 : unidxS ({ s1 with accts := s1.accts.modify who G } : St) = unidxS s1 := rfl
    have htermS : (if 0 < (G (s1.acct who)).supply then
        unidxS { s1 with accts := s1.accts.modify who G } else 0) =
        (if 0 < (s1.acct who).supply then unidxS s1 else 0) := by
      rw [show (G (s1.acct who)).supply = (s1.acct who).supply from hGsup _, hUs0]
    unfold potAt
    rw [hC, hread, z1, z2, hS, htermS]
    simp only [Nat.mul_add]
    omega
  · have hac : (({ s1 with accts := s1.accts.modify who G } : St).acct tgt) =
        (s1.acct tgt) := by
      simp only [St.acct]
      exact ProofForgeFin.Ledger.getD_modify_ne _ _ _ (Ne.symm htw)
    have hC' : St.creditedTo { s1 with accts := s1.accts.modify who G } tgt =
        St.creditedTo s1 tgt := by
      unfold St.creditedTo; rw [hac]
    have hS' : supPend { s1 with accts := s1.accts.modify who G } (s1.acct tgt) =
        supPend s1 (s1.acct tgt) := rfl
    have hB' : borPend { s1 with accts := s1.accts.modify who G } (s1.acct tgt) =
        borPend s1 (s1.acct tgt) := rfl
    have hUs0 : unidxS ({ s1 with accts := s1.accts.modify who G } : St) = unidxS s1 := rfl
    have hUb0 : unidxB ({ s1 with accts := s1.accts.modify who G } : St) = unidxB s1 := rfl
    simp only [potAt, hC', hac, hS', hB', hUs0, hUb0, Nat.le_refl]

theorem supply_le_total (l : List Acct) (who : Nat) :
    (l.getD who noAcct).supply ≤ (l.map Acct.supply).sum := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons b l ih =>
    cases who with
    | zero => simp
    | succ n =>
      simp only [List.getD, List.map_cons, List.sum_cons]
      exact Nat.le_trans (ih n) (Nat.le_add_left _ _)

theorem borrow_le_total (l : List Acct) (who : Nat) :
    (l.getD who noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons b l ih =>
    cases who with
    | zero => simp
    | succ n =>
      simp only [List.getD, List.map_cons, List.sum_cons]
      exact Nat.le_trans (ih n) (Nat.le_add_left _ _)

theorem upPendSupply (S I r u : Nat)
    (hS : S = 0 ∨ S = compInitialIndex) (hSI : S ≤ I) (hr : r ≤ I) :
    u * ((if I = 0 then compInitialIndex else I) - accrualStart r (if I = 0 then compInitialIndex else I)) ≤
    u * (I - legacyStart S r) := by
  unfold accrualStart legacyStart
  by_cases hr0 : r = 0
  · rw [if_pos hr0, if_pos hr0]
    rcases hS with rfl | rfl
    · rw [Nat.sub_zero]
      by_cases hI : I = 0
      · subst hI
        simp
      · rw [if_neg hI]
        by_cases hc : compInitialIndex ≤ I
        · rw [if_pos hc]
          exact Nat.mul_le_mul (Nat.le_refl _) (by omega)
        · rw [if_neg hc, Nat.sub_zero]
          exact Nat.le_refl _
    · have hpos : 0 < compInitialIndex := by decide
      have hI : I ≠ 0 := by omega
      rw [if_neg hI, if_pos hSI]
      exact Nat.le_refl _
  · rw [if_neg hr0, if_neg hr0]
    have hI : I ≠ 0 := by omega
    rw [if_neg hI]
    exact Nat.le_refl _

theorem upPendBorrow (S I r u : Nat)
    (hS : S = 0 ∨ S = compInitialIndex) (hSI : S ≤ I) (hr : r ≤ I) :
    u * ((if I = 0 then compInitialIndex else I) - accrualStart r (if I = 0 then compInitialIndex else I)) ≤
    u * (I - legacyStart S r) :=
  upPendSupply S I r u hS hSI hr

theorem pot_speedAssignBorrow (sA : St) (b : Nat)
    (hblk : sA.borrowState.block = sA.blockNumber) :
    pot { sA with borrowState := { sA.borrowState with speed := b } } = pot sA := by
  have hC : St.credited { sA with borrowState := { sA.borrowState with speed := b } } =
      St.credited sA := rfl
  have hM : (({ sA with borrowState := { sA.borrowState with speed := b } }).accts.map fun x =>
      supPend { sA with borrowState := { sA.borrowState with speed := b } } x +
        borPend { sA with borrowState := { sA.borrowState with speed := b } } x).sum =
      ((sA.accts.map fun x => supPend sA x + borPend sA x).sum) :=
    ProofForgeFin.Ledger.sum_map_congr _ (fun x hx => by rfl)
  have hUs : unidxS { sA with borrowState := { sA.borrowState with speed := b } } = unidxS sA := rfl
  have hU0a : unidxB sA = 0 := by
    unfold unidxB
    rw [hblk, Nat.sub_self, Nat.zero_mul]
  have hU0n : unidxB { sA with borrowState := { sA.borrowState with speed := b } } = 0 := by
    unfold unidxB
    show (sA.blockNumber - sA.borrowState.block) * _ = 0
    rw [hblk, Nat.sub_self, Nat.zero_mul]
  unfold pot
  rw [hC, hM, hUs, hU0n, hU0a]

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
