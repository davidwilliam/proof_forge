import CompRewards.Spec
import ProofForgeFin
import ProofForgeFin.DeFi.Distributor
import ProofForgeFin.DeFi.Rewards
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

def fooTest : Nat := 1

def testSt : St :=
  { blockNumber := 139,
    supplyState := { index := 1000000000000000000000000000000000000, block := 139, speed := 0 },
    borrowState := { index := 1000000000000000000000000000000000000, block := 0, speed := 0 },
    reserve := 100000000000000000000000000000000000000,
    accts := [{ supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def testOut : Option St := comptroller testSt (.claim 0)

def testCheck : Bool := match testOut with | some s' => decide ((s'.acct 0).wallet = 18977306140567618322762) | none => false

def testSt2 : St :=
  { blockNumber := 13322937,
    supplyState := { index := 1000000000000000000000000000000000000, block := 13322798, speed := 0 },
    borrowState := { index := 1000000000000000000000000000000000000, block := 13322798, speed := 0 },
    reserve := 1000000000000000000000000,
    accts := [{ supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

theorem test_thm : (claimComp testSt2 0).map (fun s' => (s'.acct 0).wallet) = some 0 := by native_decide

theorem fooLemma : 1 = 1 := rfl

def legacyEx : Legacy :=
  { blockNumber := 13322798,
    compSpeed := 0,
    supplyIndex := 0, supplyBlock := 13322798,
    borrowIndex := 0, borrowBlock := 13322798,
    supplyStart := 0, borrowStart := 0,
    reserve := 1000000000000000000000000,
    accts := [{ supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def upgradedEx : St := upgrade legacyEx

def opsEx : List Op := [Op.advance 139, Op.claim 0]

def finalEx : St := run comptroller upgradedEx opsEx

def walletEx : Nat := (finalEx.acct 0).wallet
#check walletEx

def checkEx : Bool := decide (walletEx = 0)

theorem myhelper2 : 1 = 1 := rfl

theorem updSupply_eq2 : 1 = 1 := rfl

open ProofForgeFin in theorem tmp_borrow_unfold : True := trivial

theorem updBorrow_aux (s : St) :
  updateCompBorrowIndex s =
    match (subChecked s.blockNumber s.borrowState.block) with
    | none => none
    | some db =>
      if db > 0 ∧ s.borrowState.speed > 0 then
        let tot := totalBorrows s
        let ratio := if tot > 0 then fraction (db * s.borrowState.speed) tot else 0
        some { s with borrowState := { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
      else if db > 0 then
        some { s with borrowState := { s.borrowState with block := s.blockNumber } }
      else some s := rfl

theorem acc_aux (s : St) :
  accrueSide s.borrowState s.blockNumber (totalBorrows s) =
    if 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s then
      { s.borrowState with index := s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s, block := s.blockNumber }
    else
      { s.borrowState with block := s.blockNumber } := by
  unfold accrueSide
  rfl

theorem tmp_check2 : True := trivial

theorem withBorrow_accts (s : St) (b : Side) : (({ s with borrowState := b } : St).accts = s.accts) := rfl

theorem withBorrow_supply (s : St) (b : Side) : (({ s with borrowState := b } : St).supplyState = s.supplyState) := rfl

theorem totalBorrows_withBorrow (s : St) (b : Side) : totalBorrows { s with borrowState := b } = totalBorrows s := rfl

theorem borrowAccrue_block_eq (s : St) : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem tmp_ok : True := trivial

theorem updS_eq (s : St) : updateCompSupplyIndex s =
    match subChecked s.blockNumber s.supplyState.block with
    | none => none
    | some db =>
      if db > 0 ∧ s.supplyState.speed > 0 then
        let tot := totalSupply s
        let ratio := if tot > 0 then fraction (db * s.supplyState.speed) tot else 0
        some { s with supplyState := { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
      else if db > 0 then
        some { s with supplyState := { s.supplyState with block := s.blockNumber } }
      else some s := rfl

theorem accS_eq (s : St) : accrueSide s.supplyState s.blockNumber (totalSupply s) =
    if 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s then
      { s.supplyState with index := s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s, block := s.blockNumber }
    else
      { s.supplyState with block := s.blockNumber } := by
  unfold accrueSide
  rfl

theorem updSupply_test (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
  (subChecked s.blockNumber s.supplyState.block) = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [h]

theorem updS_if (s : St) :
  updateCompSupplyIndex s =
    match (subChecked s.blockNumber s.supplyState.block) with
    | none => none
    | some db =>
      if db > 0 ∧ s.supplyState.speed > 0 then
        let tot := totalSupply s
        let ratio := if tot > 0 then fraction (db * s.supplyState.speed) tot else 0
        some { s with supplyState := { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
      else if db > 0 then
        some { s with supplyState := { s.supplyState with block := s.blockNumber } }
      else some s := by rfl

theorem updSup_is_acc (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
  updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked accrueSide fraction
  simp only [h, ↓reduceIte]
  by_cases hdb : 0 < s.blockNumber - s.supplyState.block
  · by_cases hsp : 0 < s.supplyState.speed
    · by_cases htot : 0 < totalSupply s
      · have c1 : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := And.intro hdb hsp
        have c2 : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := And.intro hdb (And.intro hsp htot)
        have c3 : (totalSupply s > 0) := htot
        simp only [if_pos c1, if_pos c2, if_pos c3]
      · have c1 : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := And.intro hdb hsp
        have c2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
          intro hc
          exact absurd hc.2.2 htot
        have c3 : ¬ (totalSupply s > 0) := by omega
        simp only [if_pos c1, if_neg c2, if_neg c3, Nat.add_zero]
    · have c1 : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by
        intro hc
        exact absurd hc.2 hsp
      have c2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        intro hc
        exact absurd hc.2.1 hsp
      have hdb2 : (s.blockNumber - s.supplyState.block > 0) := hdb
      simp only [if_neg c1, if_neg c2, if_pos hdb2]
  · have hdb2 : ¬ (s.blockNumber - s.supplyState.block > 0) := hdb
    have c2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
      intro hc
      exact absurd hc.1 hdb
    have c1 : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by
      intro hc
      exact absurd hc.1 hdb2
    simp only [if_neg c1, if_neg c2, if_neg hdb2]
    have hbn : s.supplyState.block = s.blockNumber := by omega
    cases s with
    | mk bn sup bor res acc =>
      cases sup with
      | mk idx blk spd =>
        simp only at hbn ⊢
        subst hbn
        rfl

theorem updBor_is_acc (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
  updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked accrueSide fraction
  simp only [h, ↓reduceIte]
  by_cases hdb : 0 < s.blockNumber - s.borrowState.block
  · by_cases hsp : 0 < s.borrowState.speed
    · by_cases htot : 0 < totalBorrows s
      · have c1 : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := And.intro hdb hsp
        have c2 : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := And.intro hdb (And.intro hsp htot)
        have c3 : (totalBorrows s > 0) := htot
        simp only [if_pos c1, if_pos c2, if_pos c3]
      · have c1 : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := And.intro hdb hsp
        have c2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          intro hc
          exact absurd hc.2.2 htot
        have c3 : ¬ (totalBorrows s > 0) := by omega
        simp only [if_pos c1, if_neg c2, if_neg c3, Nat.add_zero]
    · have c1 : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
        intro hc
        exact absurd hc.2 hsp
      have c2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        intro hc
        exact absurd hc.2.1 hsp
      have hdb2 : (s.blockNumber - s.borrowState.block > 0) := hdb
      simp only [if_neg c1, if_neg c2, if_pos hdb2]
  · have hdb2 : ¬ (s.blockNumber - s.borrowState.block > 0) := hdb
    have c2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
      intro hc
      exact absurd hc.1 hdb
    have c1 : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
      intro hc
      exact absurd hc.1 hdb2
    simp only [if_neg c1, if_neg c2, if_neg hdb2]
    have hbn : s.borrowState.block = s.blockNumber := by omega
    cases s with
    | mk bn sup bor res acc =>
      cases bor with
      | mk idx blk spd =>
        simp only at hbn ⊢
        subst hbn
        rfl

def fooDS : ProofForgeFin.DeFi.Distributor.State := { index := 0, unindexed := 0, accts := [] }
#check fooDS

theorem tmp_explore_list : True := trivial
#check List.get
#check List.getD
#check List.modify
#check List.length_modify

theorem probe_api : True := trivial
#check List.getD
#check List.modify
#check List.length
#check Option.isSome
#check List.sum

theorem tmp_print : True := trivial
#print List.getD
#print St.acct
#print Consistent

theorem getD_nil (n : Nat) : (List.nil : List Acct).getD n noAcct = noAcct := by cases n <;> rfl

theorem getD_cons_zero (hd : Acct) (tl : List Acct) : (hd :: tl).getD 0 noAcct = hd := by rfl

theorem getD_cons_succ (hd : Acct) (tl : List Acct) (n : Nat) : (hd :: tl).getD (n+1) noAcct = tl.getD n noAcct := by rfl

theorem learn_mem1 (hd : Acct) (tl : List Acct) : hd ∈ (hd :: tl) := by simp

theorem learn_le1 (a b : Nat) (h : a ≤ b) : a ≤ b := h

theorem learn_le_refl (n : Nat) : n ≤ n := Nat.le_refl n

theorem learn_zero_le (n : Nat) : 0 ≤ n := Nat.zero_le n

theorem learn_omega_test (a b : Nat) (h : a ≤ b) : a - b = 0 := by omega

theorem learn_if_test (a b : Nat) : (if a = 0 ∧ b ≤ a then 1 else 2) = (if a = 0 ∧ b ≤ a then 1 else 2) := rfl

theorem plan0_consistent_acct_indices (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hall⟩ := h
  have hallS : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (hall a ha).1
  have hallB : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := fun a ha => (hall a ha).2
  have keyS : ∀ (l : List Acct) (who : Nat) (I : Nat), (∀ a ∈ l, a.supplierIndex ≤ I) → (l.getD who noAcct).supplierIndex ≤ I := by
    intro l
    induction l with
    | nil =>
      intro who I _
      have hnil : ((List.nil : List Acct).getD who noAcct) = noAcct := by cases who <;> rfl
      rw [hnil]
      unfold noAcct
      simp
    | cons hd tl ih =>
      intro who I hh
      cases who with
      | zero =>
        have hz : (hd :: tl).getD 0 noAcct = hd := rfl
        rw [hz]
        exact hh hd (by simp)
      | succ n =>
        have hs : (hd :: tl).getD (n+1) noAcct = tl.getD n noAcct := rfl
        rw [hs]
        exact ih n I (fun a ha => hh a (by simp [ha]))
  have keyB : ∀ (l : List Acct) (who : Nat) (I : Nat), (∀ a ∈ l, a.borrowerIndex ≤ I) → (l.getD who noAcct).borrowerIndex ≤ I := by
    intro l
    induction l with
    | nil =>
      intro who I _
      have hnil : ((List.nil : List Acct).getD who noAcct) = noAcct := by cases who <;> rfl
      rw [hnil]
      unfold noAcct
      simp
    | cons hd tl ih =>
      intro who I hh
      cases who with
      | zero =>
        have hz : (hd :: tl).getD 0 noAcct = hd := rfl
        rw [hz]
        exact hh hd (by simp)
      | succ n =>
        have hs : (hd :: tl).getD (n+1) noAcct = tl.getD n noAcct := rfl
        rw [hs]
        exact ih n I (fun a ha => hh a (by simp [ha]))
  constructor
  · unfold St.acct
    exact keyS s.accts who s.supplyState.index hallS
  · unfold St.acct
    exact keyB s.accts who s.borrowState.index hallB


theorem plan0_accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
    exact Nat.le_add_right _ _
  · simp only [if_neg h]
    exact Nat.le_refl _


theorem plan0_updateSupply_some (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' :=
  ⟨_, updSup_is_acc s h⟩


theorem plan0_updateBorrow_some (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' :=
  ⟨_, updBor_is_acc s h⟩


theorem plan0_distributeSupplier_some (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by
  unfold distributeSupplierComp
  simp only
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
    by_cases hc : (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
    · simp only [if_pos hc]
      exact hc.2
    · simp only [if_neg hc]
      exact h
  have hsub : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = some (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) := by
    unfold subChecked
    simp only [if_pos hstart]
  rw [hsub]
  exact ⟨_, rfl⟩


theorem plan0_distributeBorrower_some (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by
  unfold distributeBorrowerComp
  simp only
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
    by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
    · simp only [if_pos hc]
      exact hc.2
    · simp only [if_neg hc]
      exact h
  have hsub : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = some (s.borrowState.index - (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)) := by
    unfold subChecked
    simp only [if_pos hstart]
  rw [hsub]
  exact ⟨_, rfl⟩


theorem plan0_consistent_acct_indices_aux_sup (l : List Acct) (who : Nat) (I : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ I) : (l.getD who noAcct).supplierIndex ≤ I := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    unfold noAcct
    simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero]
      exact h hd (by simp)
    | succ n =>
      simp only [List.getD_cons_succ]
      exact ih n (fun a ha => h a (by simp [ha]))

theorem plan0_consistent_acct_indices_aux_bor (l : List Acct) (who : Nat) (I : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ I) : (l.getD who noAcct).borrowerIndex ≤ I := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    unfold noAcct
    simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero]
      exact h hd (by simp)
    | succ n =>
      simp only [List.getD_cons_succ]
      exact ih n (fun a ha => h a (by simp [ha]))

theorem plan0_consistent_acct_indices_full (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hall⟩ := h
  have hallS : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (hall a ha).1
  have hallB : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := fun a ha => (hall a ha).2
  have keyS : ∀ (l : List Acct) (who : Nat) (I : Nat), (∀ a ∈ l, a.supplierIndex ≤ I) → (l.getD who noAcct).supplierIndex ≤ I := by
    intro l
    induction l with
    | nil =>
      intro who I _
      have hnil : ((List.nil : List Acct).getD who noAcct) = noAcct := by cases who <;> rfl
      rw [hnil]
      unfold noAcct
      simp
    | cons hd tl ih =>
      intro who I hh
      cases who with
      | zero =>
        have hz : (hd :: tl).getD 0 noAcct = hd := rfl
        rw [hz]
        exact hh hd (by simp)
      | succ n =>
        have hs : (hd :: tl).getD (n+1) noAcct = tl.getD n noAcct := rfl
        rw [hs]
        exact ih n I (fun a ha => hh a (by simp [ha]))
  have keyB : ∀ (l : List Acct) (who : Nat) (I : Nat), (∀ a ∈ l, a.borrowerIndex ≤ I) → (l.getD who noAcct).borrowerIndex ≤ I := by
    intro l
    induction l with
    | nil =>
      intro who I _
      have hnil : ((List.nil : List Acct).getD who noAcct) = noAcct := by cases who <;> rfl
      rw [hnil]
      unfold noAcct
      simp
    | cons hd tl ih =>
      intro who I hh
      cases who with
      | zero =>
        have hz : (hd :: tl).getD 0 noAcct = hd := rfl
        rw [hz]
        exact hh hd (by simp)
      | succ n =>
        have hs : (hd :: tl).getD (n+1) noAcct = tl.getD n noAcct := rfl
        rw [hs]
        exact ih n I (fun a ha => hh a (by simp [ha]))
  constructor
  · unfold St.acct
    exact keyS s.accts who s.supplyState.index hallS
  · unfold St.acct
    exact keyB s.accts who s.borrowState.index hallB

theorem plan0_updateBorrow_some_check (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' :=
  ⟨_, updBor_is_acc s h⟩

theorem acct_after_supplyUpdate (s : St) (X : Side) (who : Account) :
    (({ s with supplyState := X } : St).acct who) = s.acct who := rfl

theorem acct_after_borrowUpdate (s : St) (X : Side) (who : Account) :
    (({ s with borrowState := X } : St).acct who) = s.acct who := rfl

theorem supplyBlock_after_borrowUpdate (s : St) (X : Side) :
    (({ s with borrowState := X } : St).supplyState.block) = s.supplyState.block := rfl

theorem borrowBlock_after_supplyUpdate (s : St) (X : Side) :
    (({ s with supplyState := X } : St).borrowState.block) = s.borrowState.block := rfl

theorem blockNum_after_supplyUpdate (s : St) (X : Side) :
    (({ s with supplyState := X } : St).blockNumber) = s.blockNumber := rfl

theorem blockNum_after_borrowUpdate (s : St) (X : Side) :
    (({ s with borrowState := X } : St).blockNumber) = s.blockNumber := rfl

theorem supplyIndex_after_borrowUpdate (s : St) (X : Side) :
    (({ s with borrowState := X } : St).supplyState.index) = s.supplyState.index := rfl

theorem borrowIndex_after_supplyUpdate (s : St) (X : Side) :
    (({ s with supplyState := X } : St).borrowState.index) = s.borrowState.index := rfl

theorem req_calls_succeed_aux_supply2 (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.supplyHook who)).isSome := by
  have hSupBlk : s.supplyState.block ≤ s.blockNumber := h.1
  have hsupIdx : (s.acct who).supplierIndex ≤ s.supplyState.index :=
    (plan0_consistent_acct_indices s who h).1
  have hUpd : updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    updSup_is_acc s hSupBlk
  have hMono : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    plan0_accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
  have hAcctEq : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who) = s.acct who := rfl
  have hIdx' : ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)).acct who).supplierIndex ≤
      (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)).supplyState.index := by
    rw [hAcctEq]
    show (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    exact Nat.le_trans hsupIdx hMono
  obtain ⟨s2, hs2⟩ := plan0_distributeSupplier_some _ who hIdx'
  have hcomp : comptroller s (.supplyHook who) = distributeSupplierComp
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who := by
    unfold comptroller
    rw [hUpd]
    rfl
  rw [hcomp, hs2]
  rfl

theorem probe_modify1 : True := trivial
#check @List.modify
#check @List.get
#print List.modify

theorem list_modify_zero2 (hd : Acct) (tl : List Acct) (f : Acct → Acct) : ((hd :: tl).modify 0 f) = (f hd :: tl) := by rfl

theorem list_modify_succ2 (hd : Acct) (tl : List Acct) (n : Nat) (f : Acct → Acct) : ((hd :: tl).modify (n+1) f) = (hd :: tl.modify n f) := by rfl

theorem list_modify_getD_same2 (l : List Acct) (who : Nat) (f : Acct → Acct) (h : who < l.length) :
    (l.modify who f).getD who noAcct = f (l.getD who noAcct) := by
  induction l generalizing who with
  | nil =>
    simp at h
  | cons hd tl ih =>
    cases who with
    | zero =>
      rw [list_modify_zero2]
      rfl
    | succ n =>
      have hlen : n < tl.length := by simpa using h
      rw [list_modify_succ2]
      have e1 : (hd :: tl.modify n f).getD (n + 1) noAcct = (tl.modify n f).getD n noAcct := rfl
      have e2 : (hd :: tl).getD (n + 1) noAcct = tl.getD n noAcct := rfl
      rw [e1, e2]
      exact ih n hlen

theorem supplyHook_some_of (s : St) (who : Account)
    (hBlk : s.supplyState.block ≤ s.blockNumber)
    (hIdx : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (comptroller s (.supplyHook who)).isSome := by
  have hUpd : updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    updSup_is_acc s hBlk
  have hMono : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    plan0_accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
  have hAcctEq : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who) = s.acct who := rfl
  have hIdx' : ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)).acct who).supplierIndex ≤
      (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)).supplyState.index := by
    rw [hAcctEq]
    show (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    exact Nat.le_trans hIdx hMono
  obtain ⟨s2, hs2⟩ := plan0_distributeSupplier_some _ who hIdx'
  have hcomp : comptroller s (.supplyHook who) = distributeSupplierComp
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who := by
    unfold comptroller
    rw [hUpd]
    rfl
  rw [hcomp, hs2]
  rfl

theorem borrowHook_some_of (s : St) (who : Account)
    (hBlk : s.borrowState.block ≤ s.blockNumber)
    (hIdx : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (comptroller s (.borrowHook who)).isSome := by
  have hUpd : updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    updBor_is_acc s hBlk
  have hMono : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    plan0_accrueSide_index_ge s.borrowState s.blockNumber (totalBorrows s)
  have hAcctEq : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who) = s.acct who := rfl
  have hIdx' : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)).acct who).borrowerIndex ≤
      (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)).borrowState.index := by
    rw [hAcctEq]
    show (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    exact Nat.le_trans hIdx hMono
  obtain ⟨s2, hs2⟩ := plan0_distributeBorrower_some _ who hIdx'
  have hcomp : comptroller s (.borrowHook who) = distributeBorrowerComp
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who := by
    unfold comptroller
    rw [hUpd]
    rfl
  rw [hcomp, hs2]
  rfl

theorem updBorrow_accts_eq (s : St) :
    ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).accts = s.accts := rfl

theorem distBor_supplyState_eq (s : St) (who : Account) (f : Acct → Acct) :
    ((s.withAcct who f).supplyState) = s.supplyState := rfl

theorem distBor_block_eq (s : St) (who : Account) (f : Acct → Acct) :
    ((s.withAcct who f).blockNumber) = s.blockNumber := rfl

theorem withAcct_supplyState2 (s : St) (who : Nat) (f : Acct → Acct) :
    (s.withAcct who f).supplyState = s.supplyState := rfl

theorem withAcct_borrowState2 (s : St) (who : Nat) (f : Acct → Acct) :
    (s.withAcct who f).borrowState = s.borrowState := rfl

theorem withAcct_block2 (s : St) (who : Nat) (f : Acct → Acct) :
    (s.withAcct who f).blockNumber = s.blockNumber := rfl

theorem updSupply_accts (s : St) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts = s.accts := rfl

theorem updBorrow_accts (s : St) :
    ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).accts = s.accts := rfl

theorem subChecked_eq_some2 (a b d : Nat) (h : subChecked a b = some d) :
    b ≤ a ∧ d = a - b := by
  unfold subChecked at h
  by_cases hle : b ≤ a
  · simp only [hle, ↓reduceIte] at h
    cases h
    exact ⟨hle, rfl⟩
  · simp only [hle, ↓reduceIte] at h
    contradiction

theorem totalSupply_withSupply (s : St) (X : Side) : totalSupply { s with supplyState := X } = totalSupply s := by rfl

theorem totalBorrows_withSupply2 (s : St) (X : Side) : totalBorrows { s with supplyState := X } = totalBorrows s := by rfl

theorem acct_withSupply (s : St) (X : Side) (who : Account) : ({ s with supplyState := X } : St).acct who = s.acct who := by rfl

theorem accStart_eq_impl (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) = accrualStart rec idx := by
  unfold accrualStart
  by_cases h1 : rec = 0 <;> by_cases h2 : compInitialIndex ≤ idx <;> simp [h1, h2]

theorem mulDouble_eq_credit (u d : Nat) : mulDouble u d = u * d / doubleScale := by rfl

theorem creditFor_eq_mul (u st idx : Nat) : creditFor u st idx = u * (idx - st) / doubleScale := by rfl

theorem distSup_block (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).blockNumber = s.blockNumber := by rfl

theorem distSup_borrow (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).borrowState = s.borrowState := by rfl

theorem updSup_some_inv4 (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex at h
  cases hsc : subChecked s.blockNumber s.supplyState.block
  · simp [hsc] at h
  · have hle := subChecked_eq_some2 _ _ _ hsc
    exact hle.1

theorem probeModifyNil (f : Acct → Acct) : ((List.nil : List Acct).modify 0 f) = ([] : List Acct) := by rfl

theorem probeModifyNil2 (n : Nat) (f : Acct → Acct) : ((List.nil : List Acct).modify n f) = ([] : List Acct) := by cases n <;> rfl

theorem plan1_modify_congr_getD (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero] at h
      simp [h]
    | succ n =>
      simp only [List.getD_cons_succ] at h
      simp [ih n h]


theorem plan1_updateSupply_eq_accrue (s : St) (s₁ : St)
    (h : updateCompSupplyIndex s = some s₁) :
    s.supplyState.block ≤ s.blockNumber ∧
    s₁ = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hle : s.supplyState.block ≤ s.blockNumber := updSup_some_inv4 s s₁ h
  have heq : updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := updSup_is_acc s hle
  rw [heq] at h
  cases h
  exact ⟨hle, rfl⟩


theorem plan1_distributeSupplier_spec_form (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s.supplyState.index)
          s.supplyState.index } } := by
  have hStart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := accStart_eq_impl _ _
  have hUnfold : distributeSupplierComp s who =
    match subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply deltaIndex }) := by
    unfold distributeSupplierComp
    simp only
    rw [hStart]
  rw [hUnfold] at h
  cases hsc : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none =>
    simp [hsc] at h
  | some delta =>
    simp [hsc] at h
    have hle := (subChecked_eq_some2 _ _ _ hsc).1
    have hdeq := (subChecked_eq_some2 _ _ _ hsc).2
    constructor
    · exact hle
    · subst h
      unfold St.withAcct
      have h1 : mulDouble (s.acct who).supply delta = creditFor (s.acct who).supply (accrualStart (s.acct who).supplierIndex s.supplyState.index) s.supplyState.index := by
        unfold mulDouble creditFor
        rw [hdeq]
      have hacct : s.accts.getD who noAcct = s.acct who := rfl
      have hcongr : (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply delta } : Acct)) (s.accts.getD who noAcct)
          = (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) (s.accts.getD who noAcct) := by
        rw [hacct]
        simp only [h1]
      have hmod := plan1_modify_congr_getD s.accts who (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply delta } : Acct)) (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) hcongr
      exact congrArg (fun l => ({ s with accts := l } : St)) hmod




theorem probe_bind_extract (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ s1, updateCompSupplyIndex s = some s1 ∧ distributeSupplierComp s1 who = some s' := by
  have h2 : comptroller s (.supplyHook who) =
    (updateCompSupplyIndex s).bind (fun s1 => distributeSupplierComp s1 who) := rfl
  rw [h2] at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    simp [hU] at h
  | some s1 =>
    simp [hU] at h
    exact ⟨s1, rfl, h⟩

theorem probe_acct_rw2 (s : St) (s1 : St)
    (hs1eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
    (who : Account) : s1.acct who = s.acct who := by
  rw [hs1eq]
  rfl

theorem probe_acct_rw3 (s : St) (who : Account) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who = s.acct who := rfl

theorem probe_idx_rw (s : St) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl

theorem plan1_supplyHook_distributed_try3 (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' := by
  obtain ⟨s1, hU, hD⟩ := probe_bind_extract s who s' h
  obtain ⟨hle, hs1eq⟩ := plan1_updateSupply_eq_accrue s s1 hU
  obtain ⟨hle2, hs2eq⟩ := plan1_distributeSupplier_spec_form s1 who s' hD
  have hacct : s1.acct who = s.acct who := hs1eq ▸ (probe_acct_rw3 s who)
  have hidx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    hs1eq ▸ (probe_idx_rw s)
  have hstart : accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [← hacct, ← hidx]; exact hle2
  refine And.intro hle (And.intro hstart ?_)
  subst hs1eq
  simp only at hs2eq ⊢
  exact hs2eq

theorem plan2_update_supply_acct (s : St) (who : Account) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who =
      s.acct who := by
  exact probe_acct_rw3 s who


theorem plan2_update_supply_index (s : St) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  grind


theorem plan2_update_supply_accts (s : St) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts =
      s.accts := by
  grind


theorem plan2_nested_supply_accts_update (s : St) (x : Side) (l : List Acct) :
    ({ ({ s with supplyState := x } : St) with accts := l } : St) =
      ({ s with supplyState := x, accts := l } : St) := by
  grind


theorem plan2_supply_hook_unfold (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ s1, updateCompSupplyIndex s = some s1 ∧
      distributeSupplierComp s1 who = some s' := by
  exact probe_bind_extract s who s' h

theorem plan1_supplyHook_distributed (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' := by
  exact plan1_supplyHook_distributed_try3 s who s' h

theorem req_supply_hook_proof : SupplyHookEffects comptroller :=
  fun s who s' h => plan1_supplyHook_distributed s who s' h

theorem updBor_some_inv4 (s : St) (s1 : St)
    (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex at h
  cases hsc : subChecked s.blockNumber s.borrowState.block
  · simp [hsc] at h
  · have hle := subChecked_eq_some2 _ _ _ hsc
    exact hle.1

theorem plan1_updateBorrow_eq_accrue (s : St) (s₁ : St)
    (h : updateCompBorrowIndex s = some s₁) :
    s.borrowState.block ≤ s.blockNumber ∧
    s₁ = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hle : s.borrowState.block ≤ s.blockNumber := updBor_some_inv4 s s₁ h
  have heq : updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := updBor_is_acc s hle
  rw [heq] at h
  cases h
  exact ⟨hle, rfl⟩

theorem plan1_distributeBorrower_spec_form (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } } := by
  have hStart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := accStart_eq_impl _ _
  have hUnfold : distributeBorrowerComp s who =
    match subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex }) := by
    unfold distributeBorrowerComp
    simp only
    rw [hStart]
  rw [hUnfold] at h
  cases hsc : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none =>
    simp [hsc] at h
  | some delta =>
    simp [hsc] at h
    have hle := (subChecked_eq_some2 _ _ _ hsc).1
    have hdeq := (subChecked_eq_some2 _ _ _ hsc).2
    constructor
    · exact hle
    · subst h
      unfold St.withAcct
      have h1 : mulDouble (s.acct who).borrow delta = creditFor (s.acct who).borrow (accrualStart (s.acct who).borrowerIndex s.borrowState.index) s.borrowState.index := by
        unfold mulDouble creditFor
        rw [hdeq]
      have hacct : s.accts.getD who noAcct = s.acct who := rfl
      have hcongr : (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow delta } : Acct)) (s.accts.getD who noAcct)
          = (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) (s.accts.getD who noAcct) := by
        rw [hacct]
        simp only [h1]
      have hmod := plan1_modify_congr_getD s.accts who (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow delta } : Acct)) (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) hcongr
      exact congrArg (fun l => ({ s with accts := l } : St)) hmod

theorem probe_bind_extract_borrow (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ s1, updateCompBorrowIndex s = some s1 ∧ distributeBorrowerComp s1 who = some s' := by
  have h2 : comptroller s (.borrowHook who) =
    (updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who) := rfl
  rw [h2] at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    simp [hU] at h
  | some s1 =>
    simp [hU] at h
    exact ⟨s1, rfl, h⟩

theorem probe_acct_rw3_borrow (s : St) (who : Account) :
    ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who = s.acct who := rfl

theorem probe_idx_rw_borrow (s : St) :
    ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl

theorem plan1_borrowHook_distributed (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    BorrowDistributed s who s' := by
  obtain ⟨s1, hU, hD⟩ := probe_bind_extract_borrow s who s' h
  obtain ⟨hle, hs1eq⟩ := plan1_updateBorrow_eq_accrue s s1 hU
  obtain ⟨hle2, hs2eq⟩ := plan1_distributeBorrower_spec_form s1 who s' hD
  have hacct : s1.acct who = s.acct who := hs1eq ▸ (probe_acct_rw3_borrow s who)
  have hidx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    hs1eq ▸ (probe_idx_rw_borrow s)
  have hstart : accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hidx]; exact hle2
  refine And.intro hle (And.intro hstart ?_)
  subst hs1eq
  simp only at hs2eq ⊢
  exact hs2eq

theorem bind_some_inv (o : Option St) (f : St → Option St) (s' : St)
    (h : o.bind f = some s') : ∃ mid, o = some mid ∧ f mid = some s' := by
  cases o with
  | none =>
    simp only [Option.bind_none] at h
    contradiction
  | some mid =>
    simp only [Option.bind_some] at h
    exact ⟨mid, rfl, h⟩

theorem claim_unfold_eq (s : St) (who : Account) :
    claimComp s who =
      (updateCompBorrowIndex s).bind (fun b1 =>
        (distributeBorrowerComp b1 who).bind (fun d1 =>
          (updateCompSupplyIndex d1).bind (fun s1 =>
            (distributeSupplierComp s1 who).bind (fun d2 =>
              some (grantCompInternal d2 who))))) := by rfl

theorem claim_steps_of (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ b1 d1 s1 d2, updateCompBorrowIndex s = some b1 ∧ distributeBorrowerComp b1 who = some d1 ∧
      updateCompSupplyIndex d1 = some s1 ∧ distributeSupplierComp s1 who = some d2 ∧
      grantCompInternal d2 who = s' := by
  have heq := claim_unfold_eq s who
  rw [heq] at h
  obtain ⟨b1, hb1, hr1⟩ := bind_some_inv _ _ _ h
  obtain ⟨d1, hd1, hr2⟩ := bind_some_inv _ _ _ hr1
  obtain ⟨s1, hs1, hr3⟩ := bind_some_inv _ _ _ hr2
  obtain ⟨d2, hd2, hr4⟩ := bind_some_inv _ _ _ hr3
  simp only [Option.some.injEq] at hr4
  exact ⟨b1, d1, s1, d2, hb1, hd1, hs1, hd2, hr4⟩

theorem borrow_with_accts_combine (s : St) (b : Side) (l : List Acct) :
    ({ s with borrowState := b, accts := l } : St) =
    ({ ({ s with borrowState := b } : St) with accts := l } : St) := by
  cases s
  rfl

theorem supply_with_accts_combine (s : St) (sup : Side) (l : List Acct) :
    ({ s with supplyState := sup, accts := l } : St) =
    ({ ({ s with supplyState := sup } : St) with accts := l } : St) := by
  cases s
  rfl

theorem totalSupply_withAcct_keep2 (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supply = a.supply) :
    totalSupply (s.withAcct who f) = totalSupply s := by
  unfold totalSupply St.withAcct
  simp only
  have hmap : (s.accts.modify who f).map Acct.supply = s.accts.map Acct.supply := by
    induction s.accts generalizing who with
    | nil =>
      cases who with
      | zero => rfl
      | succ n => rfl
    | cons hd tl ih =>
      cases who with
      | zero =>
        rw [list_modify_zero2]
        simp only [List.map_cons, hf hd]
      | succ n =>
        rw [list_modify_succ2]
        simp only [List.map_cons, ih n]
  rw [hmap]

theorem totalBorrows_withAcct_keep2 (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).borrow = a.borrow) :
    totalBorrows (s.withAcct who f) = totalBorrows s := by
  unfold totalBorrows St.withAcct
  simp only
  have hmap : (s.accts.modify who f).map Acct.borrow = s.accts.map Acct.borrow := by
    induction s.accts generalizing who with
    | nil =>
      cases who with
      | zero => rfl
      | succ n => rfl
    | cons hd tl ih =>
      cases who with
      | zero =>
        rw [list_modify_zero2]
        simp only [List.map_cons, hf hd]
      | succ n =>
        rw [list_modify_succ2]
        simp only [List.map_cons, ih n]
  rw [hmap]

theorem plan3_borrow_step_distributed (s : St) (who : Account) (b1 d1 : St)
    (hU : updateCompBorrowIndex s = some b1)
    (hD : distributeBorrowerComp b1 who = some d1) :
    BorrowDistributed s who d1 := by
  obtain ⟨hleU, hb1eq⟩ := plan1_updateBorrow_eq_accrue s b1 hU
  obtain ⟨hleD, hd1eq⟩ := plan1_distributeBorrower_spec_form b1 who d1 hD
  subst hb1eq
  simp only at hleD hd1eq ⊢
  refine And.intro hleU (And.intro hleD ?_)
  -- hd1eq : d1 = nested update on top of {s with borrowState := ...}
  -- BorrowDistributed wants single nested record; collapse
  have hcomb : ∀ (l : List Acct),
      (({ ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) with accts := l } : St) =
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := l } : St)) := by
    intro l
    cases s with
    | mk bn sup bor res acc =>
      rfl
  rw [hcomb] at hd1eq
  exact hd1eq


theorem plan3_supply_step_distributed (s : St) (who : Account) (s1 d2 : St)
    (hU : updateCompSupplyIndex s = some s1)
    (hD : distributeSupplierComp s1 who = some d2) :
    SupplyDistributed s who d2 := by
  obtain ⟨hleU, hs1eq⟩ := plan1_updateSupply_eq_accrue s s1 hU
  obtain ⟨hleD, hd1eq⟩ := plan1_distributeSupplier_spec_form s1 who d2 hD
  subst hs1eq
  simp only at hleD hd1eq ⊢
  refine And.intro hleU (And.intro hleD ?_)
  have hcomb : ∀ (l : List Acct),
      (({ ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) with accts := l } : St) =
        ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := l } : St)) := by
    intro l
    cases s with
    | mk bn sup bor res acc =>
      rfl
  rw [hcomb] at hd1eq
  exact hd1eq


theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [hc]
    have hcongr : (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) (s.accts.getD who noAcct)
        = (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) (s.accts.getD who noAcct) := by
      have hacct : s.accts.getD who noAcct = s.acct who := rfl
      rw [hacct]
    have hmod := plan1_modify_congr_getD s.accts who
      (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct))
      (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) hcongr
    rw [hmod]
  · simp only [if_neg hc]


theorem plan3_claim_claimed (s : St) (who : Account) (s' : St) (h : comptroller s (.claim who) = some s') : Claimed s who s' := by
  have hclaim : claimComp s who = some s' := h
  obtain ⟨b1, d1, s1, d2, hb1, hd1, hs1, hd2, hg⟩ := claim_steps_of s who s' hclaim
  have hB : BorrowDistributed s who d1 := plan3_borrow_step_distributed s who b1 d1 hb1 hd1
  have hS : SupplyDistributed d1 who d2 := plan3_supply_step_distributed d1 who s1 d2 hs1 hd2
  have hGeq : grantCompInternal d2 who = grant d2 who := plan3_grantCompInternal_eq_grant d2 who
  have hfin : s' = grant d2 who := by rw [← hg, hGeq]
  exact ⟨d1, d2, hB, hS, hfin⟩


theorem plan3_supply_step_distributed_proof : ∀ (s : St) (who : Account) (s1 d2 : St),
    updateCompSupplyIndex s = some s1 →
    distributeSupplierComp s1 who = some d2 →
    SupplyDistributed s who d2 := by
  intro s who s1 d2 hU hD
  obtain ⟨hleU, hs1eq⟩ := plan1_updateSupply_eq_accrue s s1 hU
  obtain ⟨hleD, hd1eq⟩ := plan1_distributeSupplier_spec_form s1 who d2 hD
  subst hs1eq
  simp only at hleD hd1eq ⊢
  refine And.intro hleU (And.intro hleD ?_)
  have hcomb : ∀ (l : List Acct),
      (({ ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) with accts := l } : St) =
        ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := l } : St)) := by
    intro l
    cases s with
    | mk bn sup bor res acc =>
      rfl
  rw [hcomb] at hd1eq
  exact hd1eq

theorem plan3_claim_claimed_fix (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    Claimed s who s' := by
  have hclaim : claimComp s who = some s' := h
  obtain ⟨b1, d1, s1, d2, hb1, hd1, hs1, hd2, hg⟩ := claim_steps_of s who s' hclaim
  have hB : BorrowDistributed s who d1 := plan3_borrow_step_distributed s who b1 d1 hb1 hd1
  have hS : SupplyDistributed d1 who d2 := plan3_supply_step_distributed d1 who s1 d2 hs1 hd2
  have hGeq : grantCompInternal d2 who = grant d2 who := plan3_grantCompInternal_eq_grant d2 who
  have hfin : s' = grant d2 who := by rw [← hg, hGeq]
  exact ⟨d1, d2, hB, hS, hfin⟩

theorem plan3_claim_claimed_inline_test (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    Claimed s who s' := by
  have hclaim : claimComp s who = some s' := h
  obtain ⟨b1, d1, s1, d2, hb1, hd1, hs1, hd2, hg⟩ := claim_steps_of s who s' hclaim
  have hB : BorrowDistributed s who d1 := plan3_borrow_step_distributed s who b1 d1 hb1 hd1
  have hS : SupplyDistributed d1 who d2 := plan3_supply_step_distributed d1 who s1 d2 hs1 hd2
  have hGeq : grantCompInternal d2 who = grant d2 who := plan3_grantCompInternal_eq_grant d2 who
  have hfin : s' = grant d2 who := by rw [← hg, hGeq]
  exact ⟨d1, d2, hB, hS, hfin⟩

theorem plan3_claim_claimed_direct2 : True := trivial

theorem req_claim_pf : ClaimEffects comptroller :=
  fun s who s' h => plan3_claim_claimed s who s' h

theorem setSupply_mid_spec4 (s : St) (sup : Nat) (mid : St)
    (h : setSupplySpeed s sup = some mid) :
    (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by
  have hdef : setSupplySpeed s sup =
    if s.supplyState.speed ≠ sup then
      (updateCompSupplyIndex s).map fun t =>
        { t with supplyState := { t.supplyState with speed := sup } }
    else some s := rfl
  by_cases heq : s.supplyState.speed = sup
  · have hne : ¬ (s.supplyState.speed ≠ sup) := fun hne => hne heq
    rw [hdef, if_neg hne] at h
    have h2 : s = mid := Option.some.inj h
    have heta : ({ s with supplyState := s.supplyState } : St) = s := by cases s <;> rfl
    have hif : (if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup })
        = s.supplyState := by rw [if_pos heq]
    constructor
    · intro hne2; exact absurd heq hne2
    · rw [hif, heta]; exact h2.symm
  · have hne : s.supplyState.speed ≠ sup := heq
    rw [hdef, if_pos hne] at h
    cases hU : updateCompSupplyIndex s with
    | none =>
      simp [hU] at h
    | some sacc =>
      simp [hU] at h
      obtain ⟨hle, heqacc⟩ := plan1_updateSupply_eq_accrue s sacc hU
      subst heqacc
      cases h
      have hif : (if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup })
        = ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } : Side) := by
        rw [if_neg heq]
      rw [hif]
      constructor
      · intro _; exact hle
      · cases s with
        | mk bn ssd bor res acc =>
          rfl

theorem setBorrow_mid_spec4 (s : St) (bor : Nat) (mid : St)
    (h : setBorrowSpeed s bor = some mid) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    mid = { s with borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  have hdef : setBorrowSpeed s bor =
    if s.borrowState.speed ≠ bor then
      (updateCompBorrowIndex s).map fun t =>
        { t with borrowState := { t.borrowState with speed := bor } }
    else some s := rfl
  by_cases heq : s.borrowState.speed = bor
  · have hne : ¬ (s.borrowState.speed ≠ bor) := fun hne => hne heq
    rw [hdef, if_neg hne] at h
    have h2 : s = mid := Option.some.inj h
    have heta : ({ s with borrowState := s.borrowState } : St) = s := by cases s <;> rfl
    have hif : (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor })
        = s.borrowState := by rw [if_pos heq]
    constructor
    · intro hne2; exact absurd heq hne2
    · rw [hif, heta]; exact h2.symm
  · have hne : s.borrowState.speed ≠ bor := heq
    rw [hdef, if_pos hne] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      simp [hU] at h
    | some sacc =>
      simp [hU] at h
      obtain ⟨hle, heqacc⟩ := plan1_updateBorrow_eq_accrue s sacc hU
      subst heqacc
      cases h
      have hif : (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor })
        = ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } : Side) := by
        rw [if_neg heq]
      rw [hif]
      constructor
      · intro _; exact hle
      · cases s with
        | mk bn ssd bsd res acc =>
          rfl

theorem setSpeeds_totalSupply_after_supA (s mid : St) (sup : Nat)
    (hmid : mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }) :
    totalSupply mid = totalSupply s := by
  rw [hmid]
  rfl

theorem setSpeeds_bor_after_supA (s mid : St) (sup : Nat)
    (hmid : mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber := by
  rw [hmid]
  constructor <;> rfl

theorem plan4_setSpeeds_extract (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ mid, setSupplySpeed s a = some mid ∧ setBorrowSpeed mid b = some s' := by
  have heq : comptroller s (.setSpeeds a b) = (setSupplySpeed s a).bind (fun t => setBorrowSpeed t b) := rfl
  rw [heq] at h
  exact bind_some_inv _ _ _ h


theorem plan4_supply_mid_invariants (s mid : St) (sup : Nat)
    (hmid : mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧
    mid.accts = s.accts ∧ totalBorrows mid = totalBorrows s ∧
    totalSupply mid = totalSupply s := by
  subst hmid
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem plan4_compose_speedsSet (s mid s' : St) (a b : Nat)
    (hsup : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
      mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hbor : (mid.borrowState.speed ≠ b → mid.borrowState.block ≤ mid.blockNumber) ∧
      s' = { mid with borrowState := if mid.borrowState.speed = b then mid.borrowState
        else { accrueSide mid.borrowState mid.blockNumber (totalBorrows mid) with speed := b } }) :
    SpeedsSet s a b s' := by
  obtain ⟨hsupC, hsupE⟩ := hsup
  obtain ⟨hborC, hborE⟩ := hbor
  subst hsupE
  subst hborE
  refine And.intro hsupC (And.intro ?_ ?_)
  · intro hne
    exact hborC hne
  · cases s with
    | mk bn sup bor res acc =>
      rfl


theorem plan4_setSpeeds_effects : SetSpeedsEffects comptroller := by
  intro s a b s' h
  obtain ⟨mid, h1, h2⟩ := plan4_setSpeeds_extract s a b s' h
  obtain ⟨hsupC, hsupE⟩ := setSupply_mid_spec4 s a mid h1
  obtain ⟨hborC, hborE⟩ := setBorrow_mid_spec4 mid b s' h2
  exact plan4_compose_speedsSet s mid s' a b ⟨hsupC, hsupE⟩ ⟨hborC, hborE⟩


theorem plan4_setSpeeds_extract_test (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ mid, setSupplySpeed s a = some mid ∧ setBorrowSpeed mid b = some s' := by
  have heq : comptroller s (.setSpeeds a b) = (setSupplySpeed s a).bind (fun t => setBorrowSpeed t b) := rfl
  rw [heq] at h
  exact bind_some_inv _ _ _ h

theorem plan4_supply_mid_invariants_fix (s mid : St) (sup : Nat)
    (hmid : mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧
    mid.accts = s.accts ∧ totalBorrows mid = totalBorrows s ∧
    totalSupply mid = totalSupply s := by
  rw [hmid]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem plan4_supply_mid_invariants_helper (s : St) (sup : Nat) :
    ({ s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } : St).borrowState = s.borrowState ∧
    ({ s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } : St).blockNumber = s.blockNumber ∧
    ({ s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } : St).accts = s.accts := by
  exact ⟨rfl, rfl, rfl⟩

theorem plan4_mid_test (s mid : St) (sup : Nat)
    (hmid : mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧
    mid.accts = s.accts ∧ totalBorrows mid = totalBorrows s ∧
    totalSupply mid = totalSupply s := by
  rw [hmid]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem plan4_direct_check (s : St) (sup : Nat) :
    ({ s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } : St).borrowState = s.borrowState := by
  rfl

theorem plan4_direct_check2 (s : St) (sup : Nat) :
    totalBorrows ({ s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } : St) = totalBorrows s := by
  rfl

theorem plan4_direct_check3 (s : St) (sup : Nat) :
    totalSupply ({ s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } : St) = totalSupply s := by
  rfl

theorem plan4_supply_mid_invariants_alt (s mid : St) (sup : Nat)
    (hmid : mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧
    mid.accts = s.accts ∧ totalBorrows mid = totalBorrows s ∧
    totalSupply mid = totalSupply s := by
  subst hmid
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem plan4_setSpeeds_effects_proof : SetSpeedsEffects comptroller := by
  intro s a b s' h
  obtain ⟨mid, h1, h2⟩ := plan4_setSpeeds_extract s a b s' h
  obtain ⟨hsupC, hsupE⟩ := setSupply_mid_spec4 s a mid h1
  obtain ⟨hborC, hborE⟩ := setBorrow_mid_spec4 mid b s' h2
  exact plan4_compose_speedsSet s mid s' a b ⟨hsupC, hsupE⟩ ⟨hborC, hborE⟩

theorem plan4_setSpeeds_effects_check : SetSpeedsEffects comptroller := by
  intro s a b s' h
  obtain ⟨mid, h1, h2⟩ := plan4_setSpeeds_extract s a b s' h
  obtain ⟨hsupC, hsupE⟩ := setSupply_mid_spec4 s a mid h1
  obtain ⟨hborC, hborE⟩ := setBorrow_mid_spec4 mid b s' h2
  exact plan4_compose_speedsSet s mid s' a b ⟨hsupC, hsupE⟩ ⟨hborC, hborE⟩

theorem calls_succeed_helper_supply (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.supplyHook who)).isSome :=
  supplyHook_some_of s who h.1 (plan0_consistent_acct_indices s who h).1

theorem calls_succeed_helper_borrow (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.borrowHook who)).isSome :=
  borrowHook_some_of s who h.2.1 (plan0_consistent_acct_indices s who h).2

theorem probe_dist_state : True := trivial
#check ProofForgeFin.DeFi.Distributor.State
#check ProofForgeFin.DeFi.Distributor.Acct
#check ProofForgeFin.DeFi.Rewards.credit
#check ProofForgeFin.DeFi.Rewards.pending
#check ProofForgeFin.DeFi.Rewards.effStart
#check ProofForgeFin.DeFi.Distributor.State.owed
#check ProofForgeFin.DeFi.Distributor.pot
#check ProofForgeFin.DeFi.Distributor.emitted
#check ProofForgeFin.DeFi.Distributor.step

theorem probe_defs_eq : True := trivial
#check ProofForgeFin.DeFi.Rewards.pending
#check ProofForgeFin.DeFi.Rewards.credit
#check ProofForgeFin.DeFi.Rewards.effStart
#check ProofForgeFin.DeFi.Rewards.indexDelta
#print ProofForgeFin.DeFi.Rewards.pending
#print ProofForgeFin.DeFi.Rewards.credit
#print ProofForgeFin.DeFi.Rewards.effStart
#print ProofForgeFin.DeFi.Rewards.indexDelta

theorem probe_pot_def : True := trivial
#print ProofForgeFin.DeFi.Distributor.pot
#print ProofForgeFin.DeFi.Distributor.State.owed
#print ProofForgeFin.DeFi.Rewards.pending
#print ProofForgeFin.DeFi.Rewards.credit
#print ProofForgeFin.DeFi.Distributor.term

def pendSupply (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)

def pendBorrow (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def sumPendSupply (s : St) : Nat := (s.accts.map fun a => pendSupply s a).sum

def sumPendBorrow (s : St) : Nat := (s.accts.map fun a => pendBorrow s a).sum

def unindexedSupply (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def unindexedBorrow (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def Pot (s : St) : Nat :=
  s.credited * doubleScale + sumPendSupply s + sumPendBorrow s + (unindexedSupply s + unindexedBorrow s) * doubleScale

theorem Pot_credited_le (s : St) : s.credited * doubleScale ≤ Pot s := by
  unfold Pot
  omega





theorem plan5_supply_distributed_pot_le (s : St) (who : Account) (s' : St)
    (h : SupplyDistributed s who s') :
    Pot s' ≤ Pot s := by
  sorry

theorem plan5_borrow_distributed_pot_le (s : St) (who : Account) (s' : St)
    (h : BorrowDistributed s who s') :
    Pot s' ≤ Pot s := by
  sorry

theorem plan5_exec_step (s : St) (sp : Nat × Nat) (op : Op)
    (hCons : Consistent s)
    (hSpeed : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    Pot (exec comptroller s op) ≤
        Pot s + emittedBy sp op * doubleScale ∧
      Consistent (exec comptroller s op) ∧
      (exec comptroller s op).supplyState.speed = (nextSpeeds sp op).1 ∧
      (exec comptroller s op).borrowState.speed = (nextSpeeds sp op).2 := by
  sorry

theorem plan5_run_pot_bound (s : St) (sp : Nat × Nat) (ops : List Op)
    (hCons : Consistent s)
    (hSpeed : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    Pot (run comptroller s ops) ≤
        Pot s + emitted sp ops * doubleScale ∧
      Consistent (run comptroller s ops) ∧
      (run comptroller s ops).supplyState.speed = (speedsAfter sp ops).1 ∧
      (run comptroller s ops).borrowState.speed = (speedsAfter sp ops).2 := by
  sorry

theorem upb_DSpos2 : 0 < doubleScale := by unfold doubleScale; exact Nat.pow_pos (by decide)

theorem upb_DSge1 : 1 ≤ doubleScale := upb_DSpos2

theorem upb_Cle_idx_of_start (L : Legacy) (hL : L.WellFormed) (hstart : L.supplyStart = compInitialIndex) : compInitialIndex ≤ L.supplyIndex := by
  obtain ⟨_, hle, _, _, _, _, _⟩ := hL
  rw [hstart] at hle
  exact hle

theorem upb_upSupply_index (L : Legacy) : (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upb_upSupply_block (L : Legacy) : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upb_upSupply_speed (L : Legacy) : (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upb_upBorrow_index (L : Legacy) : (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upb_upBorrow_block (L : Legacy) : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upb_upBorrow_speed (L : Legacy) : (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upb_upAccts (L : Legacy) : (upgrade L).accts = L.accts := rfl

theorem upb_upBlock (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := rfl

theorem upb_CIpos : 0 < compInitialIndex := by unfold compInitialIndex; exact Nat.pow_pos (by decide)

theorem upb_legacy_supply_zero_idx2 (L : Legacy) (hL : L.WellFormed) (h0 : L.supplyIndex = 0) :
    L.supplyStart = 0 := by
  obtain ⟨hs0, hsle, _, _, _, _, _⟩ := hL
  rw [h0] at hsle
  cases hs0 with
  | inl h => exact h
  | inr h => rw [h] at hsle; have hc := upb_CIpos; omega

theorem upb_all_rec_zero_of_idx_zero2 (L : Legacy) (hL : L.WellFormed) (h0 : L.supplyIndex = 0) (a : Acct) (hmem : a ∈ L.accts) :
    a.supplierIndex = 0 := by
  obtain ⟨_, _, _, _, _, _, hall⟩ := hL
  have hac := (hall a hmem).1
  rw [h0] at hac
  omega

theorem upb_legacy_borrow_zero_idx2 (L : Legacy) (hL : L.WellFormed) (h0 : L.borrowIndex = 0) :
    L.borrowStart = 0 := by
  obtain ⟨_, _, hb0, hble, _, _, _⟩ := hL
  rw [h0] at hble
  cases hb0 with
  | inl h => exact h
  | inr h => rw [h] at hble; have hc := upb_CIpos; omega

theorem upb_all_recb_zero_of_idx_zero2 (L : Legacy) (hL : L.WellFormed) (h0 : L.borrowIndex = 0) (a : Acct) (hmem : a ∈ L.accts) :
    a.borrowerIndex = 0 := by
  obtain ⟨_, _, _, _, _, _, hall⟩ := hL
  have hac := (hall a hmem).2
  rw [h0] at hac
  omega

theorem plan6_pendSupply_upgrade_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    pendSupply (upgrade L) a ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  unfold pendSupply
  have hIdx : (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := upb_upSupply_index L
  by_cases h0 : L.supplyIndex = 0
  · have hStart0 : L.supplyStart = 0 := upb_legacy_supply_zero_idx2 L hL h0
    have hrec0 : a.supplierIndex = 0 := upb_all_rec_zero_of_idx_zero2 L hL h0 a ha
    have hIdx0 : (upgrade L).supplyState.index = compInitialIndex := by
      rw [hIdx, if_pos h0]
    rw [hIdx0, hrec0]
    have hacc : accrualStart 0 compInitialIndex = compInitialIndex := by
      unfold accrualStart
      rw [if_pos rfl, if_pos (Nat.le_refl _)]
    rw [hacc, Nat.sub_self]
    simp
  · have hIdx2 : (upgrade L).supplyState.index = L.supplyIndex := by
      rw [hIdx, if_neg h0]
    rw [hIdx2]
    have hle : legacyStart L.supplyStart a.supplierIndex ≤ accrualStart a.supplierIndex L.supplyIndex := by
      by_cases hrec : a.supplierIndex = 0
      · have eL : legacyStart L.supplyStart a.supplierIndex = L.supplyStart := by
          unfold legacyStart; rw [if_pos hrec]
        have eA : accrualStart a.supplierIndex L.supplyIndex = (if compInitialIndex ≤ L.supplyIndex then compInitialIndex else 0) := by
          unfold accrualStart; rw [if_pos hrec]
        rw [eL, eA]
        by_cases hCI : compInitialIndex ≤ L.supplyIndex
        · rw [if_pos hCI]
          obtain ⟨hs0, hsle, _, _, _, _, _⟩ := hL
          cases hs0 with
          | inl hz => rw [hz]; exact Nat.zero_le _
          | inr hz => rw [hz]; exact Nat.le_refl _
        · rw [if_neg hCI]
          have hss : L.supplyStart = 0 := by
            obtain ⟨hs0, hsle, _, _, _, _, _⟩ := hL
            cases hs0 with
            | inl hz => exact hz
            | inr hz =>
              exfalso
              apply hCI
              rw [hz] at hsle
              exact hsle
          rw [hss]; exact Nat.le_refl _
      · have eL : legacyStart L.supplyStart a.supplierIndex = a.supplierIndex := by
          unfold legacyStart; rw [if_neg hrec]
        have eA : accrualStart a.supplierIndex L.supplyIndex = a.supplierIndex := by
          unfold accrualStart; rw [if_neg hrec]
        rw [eL, eA]; exact Nat.le_refl _
    have hsub : L.supplyIndex - accrualStart a.supplierIndex L.supplyIndex ≤ L.supplyIndex - legacyStart L.supplyStart a.supplierIndex :=
      Nat.sub_le_sub_left hle _
    exact Nat.mul_le_mul_left a.supply hsub


theorem plan6_pendBorrow_upgrade_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    pendBorrow (upgrade L) a ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
  unfold pendBorrow
  have hIdx : (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := upb_upBorrow_index L
  by_cases h0 : L.borrowIndex = 0
  · have hStart0 : L.borrowStart = 0 := upb_legacy_borrow_zero_idx2 L hL h0
    have hrec0 : a.borrowerIndex = 0 := upb_all_recb_zero_of_idx_zero2 L hL h0 a ha
    have hIdx0 : (upgrade L).borrowState.index = compInitialIndex := by
      rw [hIdx, if_pos h0]
    rw [hIdx0, hrec0]
    have hacc : accrualStart 0 compInitialIndex = compInitialIndex := by
      unfold accrualStart
      rw [if_pos rfl, if_pos (Nat.le_refl _)]
    rw [hacc, Nat.sub_self]
    simp
  · have hIdx2 : (upgrade L).borrowState.index = L.borrowIndex := by
      rw [hIdx, if_neg h0]
    rw [hIdx2]
    have hle : legacyStart L.borrowStart a.borrowerIndex ≤ accrualStart a.borrowerIndex L.borrowIndex := by
      by_cases hrec : a.borrowerIndex = 0
      · have eL : legacyStart L.borrowStart a.borrowerIndex = L.borrowStart := by
          unfold legacyStart; rw [if_pos hrec]
        have eA : accrualStart a.borrowerIndex L.borrowIndex = (if compInitialIndex ≤ L.borrowIndex then compInitialIndex else 0) := by
          unfold accrualStart; rw [if_pos hrec]
        rw [eL, eA]
        by_cases hCI : compInitialIndex ≤ L.borrowIndex
        · rw [if_pos hCI]
          obtain ⟨_, _, hb0, hble, _, _, _⟩ := hL
          cases hb0 with
          | inl hz => rw [hz]; exact Nat.zero_le _
          | inr hz => rw [hz]; exact Nat.le_refl _
        · rw [if_neg hCI]
          have hss : L.borrowStart = 0 := by
            obtain ⟨_, _, hb0, hble, _, _, _⟩ := hL
            cases hb0 with
            | inl hz => exact hz
            | inr hz =>
              exfalso
              apply hCI
              rw [hz] at hble
              exact hble
          rw [hss]; exact Nat.le_refl _
      · have eL : legacyStart L.borrowStart a.borrowerIndex = a.borrowerIndex := by
          unfold legacyStart; rw [if_neg hrec]
        have eA : accrualStart a.borrowerIndex L.borrowIndex = a.borrowerIndex := by
          unfold accrualStart; rw [if_neg hrec]
        rw [eL, eA]; exact Nat.le_refl _
    have hsub : L.borrowIndex - accrualStart a.borrowerIndex L.borrowIndex ≤ L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex :=
      Nat.sub_le_sub_left hle _
    exact Nat.mul_le_mul_left a.borrow hsub


theorem plan6_sumPend_upgrade_le (L : Legacy) (hL : L.WellFormed) :
    sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum := by
  sorry

theorem plan6_unindexed_upgrade_le (L : Legacy) :
    unindexedSupply (upgrade L) + unindexedBorrow (upgrade L) ≤
      L.unindexedSupply + L.unindexedBorrow := by
  have hUpBlk : (upgrade L).blockNumber = L.blockNumber := upb_upBlock L
  have hSupBlk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := upb_upSupply_block L
  have hBorBlk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := upb_upBorrow_block L
  have hSupSpd : (upgrade L).supplyState.speed = L.compSpeed := upb_upSupply_speed L
  have hBorSpd : (upgrade L).borrowState.speed = L.compSpeed := upb_upBorrow_speed L
  unfold unindexedSupply unindexedBorrow Legacy.unindexedSupply Legacy.unindexedBorrow
  rw [hUpBlk, hSupBlk, hSupSpd, hBorBlk, hBorSpd]
  by_cases hS : L.supplyIndex = 0 <;> by_cases hB : L.borrowIndex = 0 <;> simp only [hS, hB, ↓reduceIte]
  · simp
  · have hz : L.blockNumber - L.blockNumber = 0 := Nat.sub_self _
    rw [hz, Nat.zero_mul]
    omega
  · have hz : L.blockNumber - L.blockNumber = 0 := Nat.sub_self _
    rw [hz, Nat.zero_mul]
    omega
  · exact Nat.le_refl _


theorem plan6_div_add_bound (n : Nat) :
    n ≤ doubleScale * (n / doubleScale) + (doubleScale - 1) := by
  have hpos : 0 < doubleScale := by unfold doubleScale; exact Nat.pow_pos (by decide)
  have hmod : n % doubleScale < doubleScale := Nat.mod_lt _ hpos
  have hdiv : doubleScale * (n / doubleScale) + n % doubleScale = n := Nat.div_add_mod n doubleScale
  omega


theorem plan6_pot_bound_of_bounds (L : Legacy)
    (hsum : sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum)
    (hun : unindexedSupply (upgrade L) + unindexedBorrow (upgrade L) ≤
      L.unindexedSupply + L.unindexedBorrow) :
    Pot (upgrade L) ≤
      doubleScale * ((upgrade L).credited + L.owed) + (doubleScale - 1) := by
  sorry

theorem plan6_aux_add (l : List Acct) (f g : Acct → Nat) :
    ((l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

theorem plan6_sumPend_upgrade_le_proof (L : Legacy) (hL : L.WellFormed) :
    sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum := by
  have hsup : ∀ a ∈ L.accts, pendSupply (upgrade L) a ≤ a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) :=
    fun a ha => plan6_pendSupply_upgrade_le L a hL ha
  have hbor : ∀ a ∈ L.accts, pendBorrow (upgrade L) a ≤ a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) :=
    fun a ha => plan6_pendBorrow_upgrade_le L a hL ha
  have haccts : (upgrade L).accts = L.accts := upb_upAccts L
  have hS : sumPendSupply (upgrade L) ≤ ((L.accts.map fun a => a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)).sum) := by
    unfold sumPendSupply
    rw [haccts]
    exact ProofForgeFin.Ledger.sum_map_le_sum_map L.accts hsup
  have hB : sumPendBorrow (upgrade L) ≤ ((L.accts.map fun a => a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex)).sum) := by
    unfold sumPendBorrow
    rw [haccts]
    exact ProofForgeFin.Ledger.sum_map_le_sum_map L.accts hbor
  have hsplit : (L.accts.map L.pendingScaled).sum =
      ((L.accts.map fun a => a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)).sum) +
      ((L.accts.map fun a => a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex)).sum) := by
    have heq : L.accts.map L.pendingScaled = L.accts.map (fun a => (a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)) + (a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex))) := by
      apply List.map_congr_left
      intro a _
      rfl
    rw [heq]
    exact plan6_aux_add L.accts _ _
  omega

theorem plan6_self_aux (l : List Acct) (f g : Acct → Nat) :
    ((l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

theorem plan6_self_contained (L : Legacy) (hL : L.WellFormed) :
    sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum := by
  have hsup : ∀ a ∈ L.accts, pendSupply (upgrade L) a ≤ a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) :=
    fun a ha => plan6_pendSupply_upgrade_le L a hL ha
  have hbor : ∀ a ∈ L.accts, pendBorrow (upgrade L) a ≤ a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) :=
    fun a ha => plan6_pendBorrow_upgrade_le L a hL ha
  have haccts : (upgrade L).accts = L.accts := upb_upAccts L
  have hS : sumPendSupply (upgrade L) ≤ ((L.accts.map fun a => a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)).sum) := by
    unfold sumPendSupply
    rw [haccts]
    exact ProofForgeFin.Ledger.sum_map_le_sum_map L.accts hsup
  have hB : sumPendBorrow (upgrade L) ≤ ((L.accts.map fun a => a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex)).sum) := by
    unfold sumPendBorrow
    rw [haccts]
    exact ProofForgeFin.Ledger.sum_map_le_sum_map L.accts hbor
  have hsplit : (L.accts.map L.pendingScaled).sum =
      ((L.accts.map fun a => a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)).sum) +
      ((L.accts.map fun a => a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex)).sum) := by
    have heq : L.accts.map L.pendingScaled = L.accts.map (fun a => (a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)) + (a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex))) := by
      apply List.map_congr_left
      intro a _
      rfl
    rw [heq]
    exact plan6_self_aux L.accts _ _
  omega

theorem plan6_check_lib (l : List Acct) (f g : Acct → Nat) :
    ((l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum) :=
  ProofForgeFin.DeFi.Rewards.sum_map_add l f g

theorem plan6_inline_final (L : Legacy) (hL : L.WellFormed) :
    sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum := by
  have hsup : ∀ a ∈ L.accts, pendSupply (upgrade L) a ≤ a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) :=
    fun a ha => plan6_pendSupply_upgrade_le L a hL ha
  have hbor : ∀ a ∈ L.accts, pendBorrow (upgrade L) a ≤ a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) :=
    fun a ha => plan6_pendBorrow_upgrade_le L a hL ha
  have haccts : (upgrade L).accts = L.accts := upb_upAccts L
  have hS : sumPendSupply (upgrade L) ≤ ((L.accts.map fun a => a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)).sum) := by
    unfold sumPendSupply
    rw [haccts]
    exact ProofForgeFin.Ledger.sum_map_le_sum_map L.accts hsup
  have hB : sumPendBorrow (upgrade L) ≤ ((L.accts.map fun a => a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex)).sum) := by
    unfold sumPendBorrow
    rw [haccts]
    exact ProofForgeFin.Ledger.sum_map_le_sum_map L.accts hbor
  have hsplit : (L.accts.map L.pendingScaled).sum =
      ((L.accts.map fun a => a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)).sum) +
      ((L.accts.map fun a => a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex)).sum) := by
    have heq : L.accts.map L.pendingScaled = L.accts.map (fun a => (a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex)) + (a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex))) := by
      apply List.map_congr_left
      intro a _
      rfl
    rw [heq]
    exact ProofForgeFin.DeFi.Rewards.sum_map_add L.accts _ _
  omega

theorem plan6_probe_order : True := trivial
#check plan6_pendSupply_upgrade_le
#check upb_upAccts
#check ProofForgeFin.Ledger.sum_map_le_sum_map
#check ProofForgeFin.DeFi.Rewards.sum_map_add

theorem arith_aux_test (c C S v1 v2 : Nat) :
    c * (C + (S / c + v1 + v2)) =
      c * C + (c * (S / c) + (c * v1 + c * v2)) := by
  simp only [Nat.mul_add]
  omega

theorem plan5_upgrade_pot_bound_aux_arith2 (c C P S Uu U : Nat)
    (hS : S ≤ P) (hU : Uu ≤ U)
    (hdiv : P ≤ c * (P / c) + (c - 1)) :
    C * c + S + Uu * c ≤ c * (C + (P / c + U)) + (c - 1) := by
  have h1 : Uu * c ≤ U * c := Nat.mul_le_mul_right c hU
  have h2 : C * c = c * C := Nat.mul_comm _ _
  have h5 : U * c = c * U := Nat.mul_comm _ _
  have h4 : c * (C + (P / c + U)) = c * C + (c * (P / c) + c * U) := by
    rw [Nat.mul_add, Nat.mul_add]
  omega

theorem plan5_upgrade_pot_bound (L : Legacy) (hL : L.WellFormed) :
    Pot (upgrade L) ≤
      doubleScale * ((upgrade L).credited + L.owed) + (doubleScale - 1) := by
  have hsum : sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum :=
    plan6_inline_final L hL
  have hun : unindexedSupply (upgrade L) + unindexedBorrow (upgrade L) ≤
      L.unindexedSupply + L.unindexedBorrow :=
    plan6_unindexed_upgrade_le L
  have hdiv : (L.accts.map L.pendingScaled).sum ≤
      doubleScale * ((L.accts.map L.pendingScaled).sum / doubleScale) + (doubleScale - 1) :=
    plan6_div_add_bound _
  have hOwed : L.owed =
      ((L.accts.map L.pendingScaled).sum / doubleScale +
        (L.unindexedSupply + L.unindexedBorrow)) := by
    unfold Legacy.owed
    omega
  have hPotEq : Pot (upgrade L) =
      (upgrade L).credited * doubleScale +
        (sumPendSupply (upgrade L) + sumPendBorrow (upgrade L)) +
        ((unindexedSupply (upgrade L) + unindexedBorrow (upgrade L)) * doubleScale) := by
    unfold Pot
    omega
  have hGoalEq : doubleScale * ((upgrade L).credited + L.owed) + (doubleScale - 1) =
      doubleScale * ((upgrade L).credited +
        ((L.accts.map L.pendingScaled).sum / doubleScale +
          (L.unindexedSupply + L.unindexedBorrow))) + (doubleScale - 1) := by
    rw [hOwed]
  rw [hPotEq, hGoalEq]
  exact plan5_upgrade_pot_bound_aux_arith2 doubleScale
    (upgrade L).credited ((L.accts.map L.pendingScaled).sum)
    (sumPendSupply (upgrade L) + sumPendBorrow (upgrade L))
    (unindexedSupply (upgrade L) + unindexedBorrow (upgrade L))
    (L.unindexedSupply + L.unindexedBorrow)
    hsum hun hdiv

theorem plan5_upgrade_consistent_speeds (L : Legacy) (hL : L.WellFormed) :
    Consistent (upgrade L) ∧
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by
  unfold Legacy.WellFormed at hL
  obtain ⟨hs0, hsle, hb0, hble, hsupBlk, hborBlk, hall⟩ := hL
  have hSidx : (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := upb_upSupply_index L
  have hSblk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := upb_upSupply_block L
  have hSspd : (upgrade L).supplyState.speed = L.compSpeed := upb_upSupply_speed L
  have hBidx : (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := upb_upBorrow_index L
  have hBblk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := upb_upBorrow_block L
  have hBspd : (upgrade L).borrowState.speed = L.compSpeed := upb_upBorrow_speed L
  have hAccts : (upgrade L).accts = L.accts := upb_upAccts L
  have hBlk : (upgrade L).blockNumber = L.blockNumber := upb_upBlock L
  have hSblk_le : (upgrade L).supplyState.block ≤ (upgrade L).blockNumber := by
    rw [hSblk, hBlk]
    by_cases h0 : L.supplyIndex = 0
    · simp [h0]
    · simp [h0, hsupBlk]
  have hBblk_le : (upgrade L).borrowState.block ≤ (upgrade L).blockNumber := by
    rw [hBblk, hBlk]
    by_cases h0 : L.borrowIndex = 0
    · simp [h0]
    · simp [h0, hborBlk]
  have hmem : ∀ a ∈ (upgrade L).accts, a.supplierIndex ≤ (upgrade L).supplyState.index ∧ a.borrowerIndex ≤ (upgrade L).borrowState.index := by
    rw [hAccts]
    intro a ha
    have haS := (hall a ha).1
    have haB := (hall a ha).2
    constructor
    · rw [hSidx]
      by_cases h0 : L.supplyIndex = 0
      · simp [h0]
        have hrec0 : a.supplierIndex = 0 := upb_all_rec_zero_of_idx_zero2 L ⟨hs0, hsle, hb0, hble, hsupBlk, hborBlk, hall⟩ h0 a ha
        rw [hrec0]
        exact Nat.zero_le _
      · simp [h0, haS]
    · rw [hBidx]
      by_cases h0 : L.borrowIndex = 0
      · simp [h0]
        have hrec0 : a.borrowerIndex = 0 := upb_all_recb_zero_of_idx_zero2 L ⟨hs0, hsle, hb0, hble, hsupBlk, hborBlk, hall⟩ h0 a ha
        rw [hrec0]
        exact Nat.zero_le _
      · simp [h0, haB]
  have hCons : Consistent (upgrade L) := ⟨hSblk_le, hBblk_le, hmem⟩
  exact ⟨hCons, hSspd, hBspd⟩

theorem lib_defs_probe : True := by
  have h1 : ProofForgeFin.DeFi.Rewards.pending 3 1 5 = 3 * (5 - 1) := rfl
  have h2 : ProofForgeFin.DeFi.Rewards.credit 10 3 1 5 = 3 * (5 - 1) / 10 := rfl
  have h3 : ProofForgeFin.DeFi.Rewards.effStart 100 0 = 100 := rfl
  trivial
#check ProofForgeFin.DeFi.Rewards.pending
#check ProofForgeFin.DeFi.Rewards.credit
#check ProofForgeFin.DeFi.Rewards.effStart
#check ProofForgeFin.DeFi.Rewards.indexDelta
#print ProofForgeFin.DeFi.Rewards.pending
#print ProofForgeFin.DeFi.Rewards.credit
#print ProofForgeFin.DeFi.Rewards.effStart
#print ProofForgeFin.DeFi.Rewards.indexDelta

theorem tmp_term_eq_probe2 (s : ProofForgeFin.DeFi.Distributor.State) (a : ProofForgeFin.DeFi.Distributor.Acct) :
    ProofForgeFin.DeFi.Distributor.term 10 20 s a = a.credited * 10 + ProofForgeFin.DeFi.Rewards.pending a.units (ProofForgeFin.DeFi.Rewards.effStart 20 a.checkpoint) s.index := rfl

theorem plan7_creditFor_scaled_le (units start idx : Nat) :
    doubleScale * creditFor units start idx ≤ units * (idx - start) := by
  unfold creditFor
  have h := Nat.div_mul_le_self (units * (idx - start)) doubleScale
  have heq : doubleScale * (units * (idx - start) / doubleScale) = units * (idx - start) / doubleScale * doubleScale := Nat.mul_comm _ _
  rw [heq]
  exact h


theorem plan7_accrueSide_index_mul_le (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤
      (now - sd.block) * sd.speed * doubleScale := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
    have hsub : sd.index + (now - sd.block) * sd.speed * doubleScale / total - sd.index =
        (now - sd.block) * sd.speed * doubleScale / total := Nat.add_sub_cancel_left _ _
    rw [hsub]
    calc total * ((now - sd.block) * sd.speed * doubleScale / total)
        = (now - sd.block) * sd.speed * doubleScale / total * total := by
          rw [Nat.mul_comm]
      _ ≤ (now - sd.block) * sd.speed * doubleScale := Nat.div_mul_le_self _ _
  · simp only [if_neg h]
    simp only [Nat.sub_self, Nat.mul_zero]
    exact Nat.zero_le _


theorem plan7_pendSupply_step_le (a : Acct) (oldIdx newIdx : Nat)
    (h : oldIdx ≤ newIdx) :
    a.supply * (newIdx - accrualStart a.supplierIndex newIdx) ≤
      a.supply * (oldIdx - accrualStart a.supplierIndex oldIdx) +
        a.supply * (newIdx - oldIdx) := by
  have hmono : accrualStart a.supplierIndex oldIdx ≤ accrualStart a.supplierIndex newIdx := by
    unfold accrualStart
    by_cases hr : a.supplierIndex = 0
    · rw [if_pos hr, if_pos hr]
      by_cases ho : compInitialIndex ≤ oldIdx
      · have hn : compInitialIndex ≤ newIdx := Nat.le_trans ho h
        rw [if_pos ho, if_pos hn]
        exact Nat.le_refl _
      · rw [if_neg ho]
        by_cases hn : compInitialIndex ≤ newIdx
        · rw [if_pos hn]
          exact Nat.zero_le _
        · rw [if_neg hn]
          exact Nat.le_refl _
    · rw [if_neg hr, if_neg hr]
      exact Nat.le_refl _
  have hsub : (newIdx - accrualStart a.supplierIndex newIdx) ≤
      (oldIdx - accrualStart a.supplierIndex oldIdx) + (newIdx - oldIdx) := by
    omega
  calc a.supply * (newIdx - accrualStart a.supplierIndex newIdx)
      ≤ a.supply * ((oldIdx - accrualStart a.supplierIndex oldIdx) + (newIdx - oldIdx)) :=
        Nat.mul_le_mul_left _ hsub
    _ = a.supply * (oldIdx - accrualStart a.supplierIndex oldIdx) +
        a.supply * (newIdx - oldIdx) := Nat.mul_add _ _ _




theorem plan7_pot_distributeSupply_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    Pot { s with
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s.supplyState.index)
            s.supplyState.index } } ≤
      Pot s := by
  sorry

theorem plan7_creditFor_scaled_le_test2 (units start idx : Nat) :
    doubleScale * creditFor units start idx ≤ units * (idx - start) := by
  unfold creditFor
  have h := Nat.div_mul_le_self (units * (idx - start)) doubleScale
  have heq : doubleScale * (units * (idx - start) / doubleScale) = units * (idx - start) / doubleScale * doubleScale := Nat.mul_comm _ _
  rw [heq]
  exact h

theorem plan7_accrueSide_index_mul_le_aux (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤
      (now - sd.block) * sd.speed * doubleScale := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
    have hsub : sd.index + (now - sd.block) * sd.speed * doubleScale / total - sd.index =
        (now - sd.block) * sd.speed * doubleScale / total := Nat.add_sub_cancel_left _ _
    rw [hsub]
    calc total * ((now - sd.block) * sd.speed * doubleScale / total)
        = (now - sd.block) * sd.speed * doubleScale / total * total := by
          rw [Nat.mul_comm]
      _ ≤ (now - sd.block) * sd.speed * doubleScale := Nat.div_mul_le_self _ _
  · simp only [if_neg h]
    simp only [Nat.sub_self, Nat.mul_zero]
    exact Nat.zero_le _

theorem plan7_accrueSide_index_mul_le2 (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤
      (now - sd.block) * sd.speed * doubleScale :=
  plan7_accrueSide_index_mul_le_aux sd now total

theorem plan7_accrueSide_index_mul_le_fix (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤
      (now - sd.block) * sd.speed * doubleScale := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
    have hsub : sd.index + (now - sd.block) * sd.speed * doubleScale / total - sd.index =
        (now - sd.block) * sd.speed * doubleScale / total := Nat.add_sub_cancel_left _ _
    rw [hsub]
    calc total * ((now - sd.block) * sd.speed * doubleScale / total)
        = (now - sd.block) * sd.speed * doubleScale / total * total := by
          rw [Nat.mul_comm]
      _ ≤ (now - sd.block) * sd.speed * doubleScale := Nat.div_mul_le_self _ _
  · simp only [if_neg h]
    simp only [Nat.sub_self, Nat.mul_zero]
    exact Nat.zero_le _

theorem plan7_supply_block_eqA (s : St) : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · rw [if_pos h]
  · rw [if_neg h]

theorem plan7_supply_speed_eqA (s : St) : (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = s.supplyState.speed := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · rw [if_pos h]
  · rw [if_neg h]

theorem plan7_sum_mul_rightA (l : List Acct) (K : Nat) :
    ((l.map fun a => a.supply * K).sum) = (l.map Acct.supply).sum * K := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.add_mul]

theorem plan7_pot_accrueSupply_le_proofA (s : St) :
    Pot { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤
      Pot s := by
  have hIdxGe : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    plan0_accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
  have hBlkEq : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber :=
    plan7_supply_block_eqA s
  have hSpdEq : (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = s.supplyState.speed :=
    plan7_supply_speed_eqA s
  have hCred : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).credited = s.credited :=
    rfl
  have hBorPend : sumPendBorrow { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = sumPendBorrow s := by
    unfold sumPendBorrow pendBorrow
    rfl
  have hUnBor : unindexedBorrow { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = unindexedBorrow s := by
    unfold unindexedBorrow
    rfl
  have hUnSup' : unindexedSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = 0 := by
    have h1 : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).blockNumber = s.blockNumber := rfl
    have h2 : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.block = s.blockNumber := hBlkEq
    have h3 : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.speed = s.supplyState.speed := hSpdEq
    unfold unindexedSupply
    rw [h1, h2, h3, Nat.sub_self, Nat.zero_mul]
  have hPoint : ∀ a ∈ s.accts, pendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } a ≤ pendSupply s a + a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := by
    intro a _
    unfold pendSupply
    have h := plan7_pendSupply_step_le a s.supplyState.index (accrueSide s.supplyState s.blockNumber (totalSupply s)).index hIdxGe
    exact h
  have hSumLe : sumPendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ sumPendSupply s + (totalSupply s) * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := by
    have hAccts : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts = s.accts := rfl
    have hAdd := ProofForgeFin.Ledger.sum_map_le_add s.accts
      (fun a => pendSupply s a) (fun a => pendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } a) (fun a => a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)) hPoint
    have hEq : ((s.accts.map fun a => a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)).sum) = (s.accts.map Acct.supply).sum * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) :=
      plan7_sum_mul_rightA s.accts _
    unfold sumPendSupply at hAdd ⊢
    rw [hAccts] at hAdd
    unfold totalSupply at hAdd hEq ⊢
    rw [hEq] at hAdd
    exact hAdd
  have hMul : totalSupply s * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) ≤ ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale :=
    plan7_accrueSide_index_mul_le s.supplyState s.blockNumber (totalSupply s)
  have hDist : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + unindexedBorrow s) * doubleScale =
      ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale + unindexedBorrow s * doubleScale := by
    rw [Nat.add_mul]
  have hPotL : Pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } =
      s.credited * doubleScale + sumPendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } + sumPendBorrow s + unindexedBorrow s * doubleScale := by
    unfold Pot
    rw [hCred, hBorPend, hUnBor, hUnSup']
    simp only [Nat.zero_add]
  have hPotR : Pot s = s.credited * doubleScale + sumPendSupply s + sumPendBorrow s + (((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale + unindexedBorrow s * doubleScale) := by
    unfold Pot unindexedSupply
    rw [hDist]
  rw [hPotL, hPotR]
  omega

theorem plan7_inline_testA (s : St) :
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · rw [if_pos h]
  · rw [if_neg h]

theorem plan7_pot_accrueSupply_le (s : St) :
    Pot { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤
      Pot s := by
  have hIdxGe : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    plan0_accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
  have hBlkEq : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber :=
    plan7_supply_block_eqA s
  have hSpdEq : (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = s.supplyState.speed :=
    plan7_supply_speed_eqA s
  have hCred : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).credited = s.credited :=
    rfl
  have hBorPend : sumPendBorrow { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = sumPendBorrow s := by
    unfold sumPendBorrow pendBorrow
    rfl
  have hUnBor : unindexedBorrow { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = unindexedBorrow s := by
    unfold unindexedBorrow
    rfl
  have hUnSup' : unindexedSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = 0 := by
    have h1 : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).blockNumber = s.blockNumber := rfl
    have h2 : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.block = s.blockNumber := hBlkEq
    have h3 : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.speed = s.supplyState.speed := hSpdEq
    unfold unindexedSupply
    rw [h1, h2, h3, Nat.sub_self, Nat.zero_mul]
  have hPoint : ∀ a ∈ s.accts, pendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } a ≤ pendSupply s a + a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := by
    intro a _
    unfold pendSupply
    have h := plan7_pendSupply_step_le a s.supplyState.index (accrueSide s.supplyState s.blockNumber (totalSupply s)).index hIdxGe
    exact h
  have hSumLe : sumPendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ sumPendSupply s + (totalSupply s) * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := by
    have hAccts : ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts = s.accts := rfl
    have hAdd := ProofForgeFin.Ledger.sum_map_le_add s.accts
      (fun a => pendSupply s a) (fun a => pendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } a) (fun a => a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)) hPoint
    have hEq : ((s.accts.map fun a => a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)).sum) = (s.accts.map Acct.supply).sum * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) :=
      plan7_sum_mul_rightA s.accts _
    unfold sumPendSupply at hAdd ⊢
    rw [hAccts] at hAdd
    unfold totalSupply at hAdd hEq ⊢
    rw [hEq] at hAdd
    exact hAdd
  have hMul : totalSupply s * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) ≤ ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale :=
    plan7_accrueSide_index_mul_le s.supplyState s.blockNumber (totalSupply s)
  have hDist : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + unindexedBorrow s) * doubleScale =
      ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale + unindexedBorrow s * doubleScale := by
    rw [Nat.add_mul]
  have hPotL : Pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } =
      s.credited * doubleScale + sumPendSupply { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } + sumPendBorrow s + unindexedBorrow s * doubleScale := by
    unfold Pot
    rw [hCred, hBorPend, hUnBor, hUnSup']
    simp only [Nat.zero_add]
  have hPotR : Pot s = s.credited * doubleScale + sumPendSupply s + sumPendBorrow s + (((s.blockNumber - s.supplyState.block) * s.supplyState.speed) * doubleScale + unindexedBorrow s * doubleScale) := by
    unfold Pot unindexedSupply
    rw [hDist]
  rw [hPotL, hPotR]
  omega

theorem aux_test_pot1 (s : St) (who : Account) :
    (({ s with accts := s.accts.modify who fun a => a } : St).accts = s.accts.modify who fun a => a) := rfl
#check ProofForgeFin.Ledger.sum_map_modify
#check ProofForgeFin.Ledger.sum_map_modify_le
#check @List.modify

theorem aux_CI_pos5 : 0 < compInitialIndex := by
  show 0 < 10 ^ 36
  exact Nat.pow_pos (by decide : 0 < 10)

theorem aux_accrual_self6 (idx : Nat) : accrualStart idx idx = idx := by
  unfold accrualStart
  by_cases h : idx = 0
  · subst h
    simp only [↓reduceIte]
    have hci : ¬ (compInitialIndex ≤ 0) := by
      have hp := aux_CI_pos5
      omega
    simp [hci]
  · simp [h]

theorem probe_rewards_defs_tmp_unique123 : True := by
  have h1 : ProofForgeFin.DeFi.Rewards.pending 3 1 5 = 3 * (5 - 1) := rfl
  trivial
#print ProofForgeFin.DeFi.Rewards.pending
#print ProofForgeFin.DeFi.Rewards.credit
#print ProofForgeFin.DeFi.Rewards.effStart
#print ProofForgeFin.DeFi.Rewards.settle_le
#print ProofForgeFin.Ledger.sum_map_modify
#print St.credited
#print pendSupply
#print sumPendSupply
#print Pot

theorem tmp_print_sigs_unique999 : True := by trivial
#check @ProofForgeFin.Ledger.sum_map_modify
#check @ProofForgeFin.Ledger.sum_map_modify_le
#check @ProofForgeFin.DeFi.Rewards.sum_map_add
#check @ProofForgeFin.DeFi.Rewards.settle_le
#print ProofForgeFin.DeFi.Rewards.settle_le
#print ProofForgeFin.DeFi.Rewards.credit
#print ProofForgeFin.DeFi.Rewards.pending
#print ProofForgeFin.DeFi.Rewards.effStart

theorem tmp_settle_term_le_unique772b (a : Acct) (I : Nat) :
    (((a.accrued + creditFor a.supply (accrualStart a.supplierIndex I) I) + a.wallet) * doubleScale +
      (a.supply * (I - accrualStart I I))) ≤
      ((a.accrued + a.wallet) * doubleScale +
        (a.supply * (I - accrualStart a.supplierIndex I))) := by
  have hself : accrualStart I I = I := aux_accrual_self6 I
  rw [hself, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  have hcred : doubleScale * creditFor a.supply (accrualStart a.supplierIndex I) I ≤
      a.supply * (I - accrualStart a.supplierIndex I) :=
    plan7_creditFor_scaled_le _ _ _
  have hcomm : creditFor a.supply (accrualStart a.supplierIndex I) I * doubleScale =
      doubleScale * creditFor a.supply (accrualStart a.supplierIndex I) I := Nat.mul_comm _ _
  have hperm : (a.accrued + creditFor a.supply (accrualStart a.supplierIndex I) I + a.wallet) =
      (a.accrued + a.wallet) + creditFor a.supply (accrualStart a.supplierIndex I) I := by omega
  rw [hperm, Nat.add_mul, hcomm]
  exact Nat.add_le_add_left hcred _

theorem tmp_sum_mul_dist_unique773 (l : List Nat) (k : Nat) : (l.sum * k = (l.map fun x => x * k).sum) := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih, Nat.add_mul]

theorem tmp_cred_scaled_eq_unique774 (l : List Acct) (k : Nat) :
    ((l.map fun a => a.accrued + a.wallet).sum * k = (l.map fun a => (a.accrued + a.wallet) * k).sum) := by
  have h : (l.map fun a => a.accrued + a.wallet).sum * k = ((l.map fun a => a.accrued + a.wallet).map fun x => x * k).sum := by
    exact tmp_sum_mul_dist_unique773 _ _
  rw [h]
  have heq : ((l.map fun a => a.accrued + a.wallet).map fun x => x * k) = (l.map fun a => (a.accrued + a.wallet) * k) := by
    simp [List.map_map]
  rw [heq]

theorem plan7_pendBorrow_step_le_aux7 (a : Acct) (oldIdx newIdx : Nat)
    (h : oldIdx ≤ newIdx) :
    a.borrow * (newIdx - accrualStart a.borrowerIndex newIdx) ≤
      a.borrow * (oldIdx - accrualStart a.borrowerIndex oldIdx) +
        a.borrow * (newIdx - oldIdx) := by
  have hmono : accrualStart a.borrowerIndex oldIdx ≤ accrualStart a.borrowerIndex newIdx := by
    unfold accrualStart
    by_cases hr : a.borrowerIndex = 0
    · rw [if_pos hr, if_pos hr]
      by_cases ho : compInitialIndex ≤ oldIdx
      · have hn : compInitialIndex ≤ newIdx := Nat.le_trans ho h
        rw [if_pos ho, if_pos hn]
        exact Nat.le_refl _
      · rw [if_neg ho]
        by_cases hn : compInitialIndex ≤ newIdx
        · rw [if_pos hn]; exact Nat.zero_le _
        · rw [if_neg hn]; exact Nat.le_refl _
    · rw [if_neg hr, if_neg hr]; exact Nat.le_refl _
  have hsub : (newIdx - accrualStart a.borrowerIndex newIdx) ≤
      (oldIdx - accrualStart a.borrowerIndex oldIdx) + (newIdx - oldIdx) := by
    omega
  calc a.borrow * (newIdx - accrualStart a.borrowerIndex newIdx)
      ≤ a.borrow * ((oldIdx - accrualStart a.borrowerIndex oldIdx) + (newIdx - oldIdx)) :=
        Nat.mul_le_mul_left _ hsub
    _ = a.borrow * (oldIdx - accrualStart a.borrowerIndex oldIdx) +
        a.borrow * (newIdx - oldIdx) := Nat.mul_add _ _ _

theorem plan7_borrow_block_eqD (s : St) : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · rw [if_pos h]
  · rw [if_neg h]

theorem plan7_borrow_speed_eqD (s : St) : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed = s.borrowState.speed := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · rw [if_pos h]
  · rw [if_neg h]

theorem plan7_sum_mul_rightD (l : List Acct) (K : Nat) :
    ((l.map fun a => a.borrow * K).sum) = (l.map Acct.borrow).sum * K := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.add_mul]

theorem plan7_pot_accrueBorrow_le4 (s : St) :
    Pot { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤
      Pot s := by
  have hIdxGe : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    plan0_accrueSide_index_ge s.borrowState s.blockNumber (totalBorrows s)
  have hBlkEq : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber :=
    plan7_borrow_block_eqD s
  have hSpdEq : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed = s.borrowState.speed :=
    plan7_borrow_speed_eqD s
  have hPoint : ∀ a ∈ s.accts, pendBorrow { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } a ≤ pendBorrow s a + a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) := by
    intro a _
    unfold pendBorrow
    exact plan7_pendBorrow_step_le_aux7 a s.borrowState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index hIdxGe
  have hAccts : ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).accts = s.accts := rfl
  have hAdd := ProofForgeFin.Ledger.sum_map_le_add s.accts
      (fun a => pendBorrow s a) (fun a => pendBorrow { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } a) (fun a => a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index)) hPoint
  have hEq : ((s.accts.map fun a => a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index)).sum) = (s.accts.map Acct.borrow).sum * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) :=
      plan7_sum_mul_rightD s.accts _
  have hSumLe : sumPendBorrow { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤ sumPendBorrow s + (totalBorrows s) * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) := by
    unfold sumPendBorrow at hAdd ⊢
    rw [hAccts] at hAdd
    unfold totalBorrows at hAdd hEq ⊢
    rw [hEq] at hAdd
    exact hAdd
  have hMul : totalBorrows s * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) ≤ ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale :=
    plan7_accrueSide_index_mul_le s.borrowState s.blockNumber (totalBorrows s)
  have hPot : Pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } =
      s.credited * doubleScale + sumPendSupply s + sumPendBorrow { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } + unindexedSupply s * doubleScale := by
    have hCred : ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).credited = s.credited := rfl
    have hSupPend : sumPendSupply { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = sumPendSupply s := rfl
    have hUnSup : unindexedSupply { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = unindexedSupply s := rfl
    have hUnBor' : unindexedBorrow { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = 0 := by
      unfold unindexedBorrow
      rw [hBlkEq, hSpdEq, Nat.sub_self, Nat.zero_mul]
    unfold Pot
    rw [hCred, hSupPend, hUnSup, hUnBor']
    simp only [Nat.add_zero]
  have hPotS : Pot s = s.credited * doubleScale + sumPendSupply s + sumPendBorrow s + (unindexedSupply s * doubleScale + ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale) := by
    unfold Pot unindexedBorrow
    rw [Nat.add_mul]
  rw [hPot, hPotS]
  generalize s.credited * doubleScale = C at *
  generalize sumPendSupply s = S at *
  generalize sumPendBorrow { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = B' at *
  generalize sumPendBorrow s = B at *
  generalize unindexedSupply s * doubleScale = U at *
  generalize ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale = E at *
  generalize totalBorrows s * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) = T at *
  omega

theorem plan8_accrualStart_self (I : Nat) : accrualStart I I = I := aux_accrual_self6 I


theorem plan8_borrow_credit_scaled_le (units start idx : Nat) :
    doubleScale * creditFor units start idx ≤ units * (idx - start) := by
  exact plan7_creditFor_scaled_le units start idx


theorem plan8_borrow_term_le (a : Acct) (I : Nat) :
    (a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex I) I + a.wallet) * doubleScale +
      a.borrow * (I - accrualStart I I) ≤
      (a.accrued + a.wallet) * doubleScale +
        a.borrow * (I - accrualStart a.borrowerIndex I) := by
  have hself : accrualStart I I = I := aux_accrual_self6 I
  rw [hself, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  have hcred : doubleScale * creditFor a.borrow (accrualStart a.borrowerIndex I) I ≤
      a.borrow * (I - accrualStart a.borrowerIndex I) :=
    plan7_creditFor_scaled_le _ _ _
  have hperm : (a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex I) I + a.wallet) =
      (a.accrued + a.wallet) + creditFor a.borrow (accrualStart a.borrowerIndex I) I := by
    omega
  have hle : creditFor a.borrow (accrualStart a.borrowerIndex I) I * doubleScale ≤
      a.borrow * (I - accrualStart a.borrowerIndex I) := by
    rw [Nat.mul_comm]
    exact hcred
  rw [hperm, Nat.add_mul]
  exact Nat.add_le_add_left hle _




theorem plan8_pot_distribute_borrow_le (s : St) (who : Account) :
    Pot { s with accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } } ≤
      Pot s := by sorry

theorem plan8_pot_borrowDistributed_le_accrued (s : St) (who : Account) (s' : St)
    (h : BorrowDistributed s who s') :
    Pot s' ≤ Pot { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan8_accrualStart_self_fix (I : Nat) : accrualStart I I = I := aux_accrual_self6 I

theorem plan8_accrualStart_self2 (I : Nat) : accrualStart I I = I := aux_accrual_self6 I

theorem tmp_probe_modify_eq : True := by
  have h : ∀ (a b : Acct) (l : List Acct), (a :: l).modify 0 (fun _ => b) = b :: l := fun a b l => rfl
  trivial
#check @List.modify
#check List.modify_eq_set
#check List.getElem_modify

theorem plan8_supply_pend_eq_of_borrow_mod (s : St) (who : Account) (a : Acct) :
    pendSupply { s with accts := s.accts.modify who fun b =>
      ({ b with
        borrowerIndex := s.borrowState.index,
        accrued := b.accrued + creditFor b.borrow
          (accrualStart b.borrowerIndex s.borrowState.index)
          s.borrowState.index } : Acct) } a = pendSupply s a := by
  unfold pendSupply
  rfl

theorem plan8_supply_pend_pres (s : St) (a : Acct) :
    pendSupply s
      ({ a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } : Acct) = pendSupply s a := by
  unfold pendSupply
  rfl

theorem tmp_modify_unfold_test (hd : Acct) (tl : List Acct) (f : Acct → Acct) :
    (hd :: tl).modify 0 f = f hd :: tl := by rfl

theorem tmp_modify_unfold_test2 (hd : Acct) (tl : List Acct) (n : Nat) (f : Acct → Acct) :
    (hd :: tl).modify (n+1) f = hd :: tl.modify n f := by rfl

theorem tmp_nil_modify_test (n : Nat) (f : Acct → Acct) :
    (List.nil : List Acct).modify n f = [] := by cases n <;> rfl

theorem tmp_map_sum_congr_test (l : List Acct) (f g : Acct → Nat) (h : ∀ a, f a = g a) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, List.sum_cons, h hd, ih]

theorem plan8_sumPendSupply_modify_borrow (s : St) (who : Account) :
    sumPendSupply { s with accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } } =
      sumPendSupply s := by
  unfold sumPendSupply
  have hac : (({ s with accts := s.accts.modify who fun a =>
      ({ a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } : Acct) } : St).accts) =
      s.accts.modify who fun a =>
        ({ a with
          borrowerIndex := s.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex s.borrowState.index)
            s.borrowState.index } : Acct) := rfl
  have hf : ∀ (a : Acct), pendSupply s
      ({ a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } : Acct) = pendSupply s a :=
    fun a => plan8_supply_pend_pres s a
  have hgen : ∀ (l : List Acct) (n : Nat),
      ((l.modify n fun a =>
        ({ a with
          borrowerIndex := s.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex s.borrowState.index)
            s.borrowState.index } : Acct)).map fun a => pendSupply s a).sum =
      (l.map fun a => pendSupply s a).sum := by
    intro l
    induction l with
    | nil =>
      intro n
      rw [tmp_nil_modify_test]
    | cons hd tl ih =>
      intro n
      cases n with
      | zero =>
        rw [tmp_modify_unfold_test]
        simp only [List.map_cons, List.sum_cons]
        rw [hf hd]
      | succ n =>
        rw [tmp_modify_unfold_test2]
        simp only [List.map_cons, List.sum_cons]
        rw [ih n]
  have hsup_eq : ∀ (a : Acct),
      pendSupply { s with accts := s.accts.modify who fun b =>
        ({ b with
          borrowerIndex := s.borrowState.index,
          accrued := b.accrued + creditFor b.borrow
            (accrualStart b.borrowerIndex s.borrowState.index)
            s.borrowState.index } : Acct) } a = pendSupply s a := by
    intro a
    rfl
  have hcongr := tmp_map_sum_congr_test
    (s.accts.modify who fun a =>
      ({ a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } : Acct))
    (fun a => pendSupply { s with accts := s.accts.modify who fun b =>
        ({ b with
          borrowerIndex := s.borrowState.index,
          accrued := b.accrued + creditFor b.borrow
            (accrualStart b.borrowerIndex s.borrowState.index)
            s.borrowState.index } : Acct) } a)
    (fun a => pendSupply s a) hsup_eq
  rw [hac, hcongr]
  exact hgen s.accts who

theorem req_calls_succeed       : CallsSucceed comptroller := sorry

theorem req_supply_hook : SupplyHookEffects comptroller :=
  fun s who s' h => plan1_supplyHook_distributed s who s' h

theorem req_borrow_hook : BorrowHookEffects comptroller :=
  fun s who s' h => plan1_borrowHook_distributed s who s' h

theorem req_claim : ClaimEffects comptroller :=
  fun s who s' h => plan3_claim_claimed s who s' h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  exact plan4_setSpeeds_effects

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry

theorem req_account_bounded     : AccountBounded comptroller := sorry

theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
