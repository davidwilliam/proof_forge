import CompRewards.Spec
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.DeFi.Distributor
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
    if (s.acct supplier).supplierIndex = 0 ∧ supplyIndex ≥ compInitialIndex then compInitialIndex
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
    if (s.acct borrower).borrowerIndex = 0 ∧ borrowIndex ≥ compInitialIndex then compInitialIndex
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

theorem mytest : True := trivial

def fooTest : Nat := 5

theorem subChecked_isSome_test : (subChecked 3 2).isSome = true := by rfl

theorem subChecked_some_eq (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by unfold subChecked; simp [h]

theorem subChecked_none_eq (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by unfold subChecked; simp [h]

theorem subChecked_some_eq2 (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by unfold subChecked; simp [h]

theorem updateSupply_succeeds (s : St) (h : s.supplyState.block ≤ s.blockNumber) : (updateCompSupplyIndex s).isSome := by unfold updateCompSupplyIndex; rw [subChecked_some_eq s.blockNumber s.supplyState.block h]; by_cases h3 : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) <;> simp [h3]; by_cases h4 : s.blockNumber - s.supplyState.block > 0 <;> simp [h4]

theorem updateBorrow_succeeds (s : St) (h : s.borrowState.block ≤ s.blockNumber) : (updateCompBorrowIndex s).isSome := by unfold updateCompBorrowIndex; rw [subChecked_some_eq s.blockNumber s.borrowState.block h]; by_cases h3 : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) <;> simp [h3]; by_cases h4 : s.blockNumber - s.borrowState.block > 0 <;> simp [h4]

theorem side_block_same_tmp (sd : Side) (now : Nat) (h : sd.block = now) : ({ sd with block := now } : Side) = sd := by
  cases sd
  simp_all

theorem upd_none_of_lt_tmp (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  have h2 : subChecked s.blockNumber s.supplyState.block = none :=
    subChecked_none_eq s.blockNumber s.supplyState.block h
  simp [h2]

theorem upd_reduce_tmp (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (match (subChecked s.blockNumber s.supplyState.block) with | none => (none : Option St) | some d => if d > 0 then (some s : Option St) else (some s : Option St)) = (some s : Option St) := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    subChecked_some_eq s.blockNumber s.supplyState.block h
  simp [hsub]

theorem match_reduce_tmp2 (s : St) (d : Nat) :
    (match (some d : Option Nat) with | none => (none : Option St) | some e => some ({ s with blockNumber := e })) = some ({ s with blockNumber := d }) := by
  simp

theorem borrowUpdLem_test1 (sd : Side) (now : Nat) (h : sd.block = now) :
    ({ sd with block := now } : Side) = sd := by
  cases sd with
  | mk i b sp =>
    simp at h
    simp [h]

theorem accrueSide_block_eq (sd : Side) (now : Nat) (h : sd.block = now) :
    ({ sd with block := now } : Side) = sd := by
  cases sd with
  | mk i b sp =>
      simp_all

theorem updSupply_some_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
  subChecked_some_eq s.blockNumber s.supplyState.block h

theorem accrueSide_unfold_supply (s : St) :
    accrueSide s.supplyState s.blockNumber (totalSupply s) =
    (if 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s then
      ({ s.supplyState with index := s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s, block := s.blockNumber } : Side)
    else ({ s.supplyState with block := s.blockNumber } : Side)) := by
  unfold accrueSide
  by_cases h : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s)
  · simp [h]
  · simp [h]

theorem if_pos_test (P : Prop) [Decidable P] (h : P) (a b : Nat) : (if P then a else b) = a := if_pos h

theorem modify_nil_test (f : Acct → Acct) (n : Nat) : ([] : List Acct).modify n f = [] := by simp

theorem accrue_eq_of_le (sd : Side) (now total : Nat) :
    accrueSide sd now total =
      if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then
        ({ sd with index := sd.index + (now - sd.block) * sd.speed * doubleScale / total, block := now } : Side)
      else (({ sd with block := now } : Side)) := by
  unfold accrueSide
  by_cases h : (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)
  · simp [h]
  · simp [h]

theorem updSup_none (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex subChecked
  simp [h]

theorem updSup_some_form (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      (if s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 then
        let supplyTokens := totalSupply s
        let compAccrued := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
        let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
        some ({ s with supplyState :=
          { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } } : St)
      else if s.blockNumber - s.supplyState.block > 0 then
        some ({ s with supplyState := { s.supplyState with block := s.blockNumber } } : St)
      else (some s : Option St)) := by
  unfold updateCompSupplyIndex subChecked
  simp [h]

theorem tmp_test_thm : True := trivial

theorem my_helper_test2 : True := trivial

theorem probe_simp1 : ∀ (s : St), s.supplyState.block ≤ s.blockNumber → 0 < s.blockNumber - s.supplyState.block → 0 < s.supplyState.speed → 0 < (List.map Acct.supply s.accts).sum → updateCompSupplyIndex s = some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
  intro s h hd hs ht
  unfold updateCompSupplyIndex accrueSide totalSupply fraction
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := subChecked_some_eq s.blockNumber s.supplyState.block h
  rw [hsub]
  simp_all

theorem probe_simp2 : ∀ (s : St), s.supplyState.block ≤ s.blockNumber → 0 < s.blockNumber - s.supplyState.block → 0 < s.supplyState.speed → ¬ 0 < (List.map Acct.supply s.accts).sum → updateCompSupplyIndex s = some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
  intro s h hd hs ht
  unfold updateCompSupplyIndex accrueSide totalSupply fraction
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := subChecked_some_eq s.blockNumber s.supplyState.block h
  rw [hsub]
  simp_all

theorem probe_simp3 : ∀ (s : St), s.supplyState.block ≤ s.blockNumber → 0 < s.blockNumber - s.supplyState.block → ¬ 0 < s.supplyState.speed → updateCompSupplyIndex s = some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
  intro s h hd hs
  unfold updateCompSupplyIndex accrueSide totalSupply fraction
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := subChecked_some_eq s.blockNumber s.supplyState.block h
  rw [hsub]
  simp_all

def myfoo2 : Nat := 2

def supStart0 (s : St) (who : Account) : Nat :=
  if (s.acct who).supplierIndex = 0 then 0 else (s.acct who).supplierIndex

def borStart0 (s : St) (who : Account) : Nat :=
  if (s.acct who).borrowerIndex = 0 then 0 else (s.acct who).borrowerIndex

def borPend (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - borStart0 s who)

def supUnidx (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).supply then (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale else 0

def borUnidx (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).borrow then (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale else 0

def supPend2 (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - supStart0 s who)

def potW2 (s : St) (who : Account) : Nat :=
  (s.acct who).accrued * doubleScale + (s.acct who).wallet * doubleScale + supPend2 s who + borPend s who + supUnidx s who + borUnidx s who

theorem potW2_test : ∀ (s : St) (who : Account), (s.acct who).accrued * doubleScale ≤ potW2 s who := by
  intro s who
  unfold potW2 supPend2 borPend supUnidx borUnidx
  omega

theorem creditedTo_mul_le_potW2b (s : St) (who : Account) :
    (s.creditedTo who) * doubleScale ≤ potW2 s who := by
  unfold St.creditedTo potW2 supPend2 borPend supUnidx borUnidx
  have hmul : ((s.acct who).accrued + (s.acct who).wallet) * doubleScale
    = (s.acct who).accrued * doubleScale + (s.acct who).wallet * doubleScale := Nat.add_mul _ _ _
  omega

theorem accrualStart_le_index2 (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  split
  · next hr =>
    split
    · next hi => exact hi
    · exact Nat.zero_le index
  · next hr => exact h



theorem plan0_distributeSupplierComp_isSome_of_le (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  unfold distributeSupplierComp
  have hle : (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
    by_cases hc : ((s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex)
    · simp only [if_pos hc]
      exact (And.right hc)
    · simp only [if_neg hc]
      exact h
  have hsub := subChecked_some_eq s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).supplierIndex) hle
  simp only [hsub]
  rfl






theorem plan0_updateBorrow_shape (s s' : St)
    (hupd : updateCompBorrowIndex s = some s') :
    s'.accts = s.accts ∧
      s'.supplyState = s.supplyState ∧
      s'.blockNumber = s.blockNumber ∧
      s.borrowState.index ≤ s'.borrowState.index ∧
      s'.borrowState.block ≤ s'.blockNumber := by
  unfold updateCompBorrowIndex at hupd
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
      subChecked_some_eq s.blockNumber s.borrowState.block hle
    rw [hsub] at hupd
    by_cases hpos : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · simp only [if_pos hpos] at hupd
      have heq := Option.some_inj.mp hupd
      rw [← heq]
      exact ⟨rfl, rfl, rfl, Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [if_neg hpos] at hupd
      by_cases hpos2 : s.blockNumber - s.borrowState.block > 0
      · simp only [if_pos hpos2] at hupd
        have heq := Option.some_inj.mp hupd
        rw [← heq]
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
      · simp only [if_neg hpos2] at hupd
        have heq := Option.some_inj.mp hupd
        rw [← heq]
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, hle⟩
  · have hsub : subChecked s.blockNumber s.borrowState.block = none :=
      subChecked_none_eq s.blockNumber s.borrowState.block hle
    rw [hsub] at hupd
    simp at hupd




theorem plan0_acct_indices_le_of_consistent (s : St) (who : Account)
    (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
      (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨h1, h2, hall⟩ := h
  unfold St.acct
  have hbase_sup : noAcct.supplierIndex ≤ s.supplyState.index := by unfold noAcct; exact Nat.zero_le _
  have hbase_bor : noAcct.borrowerIndex ≤ s.borrowState.index := by unfold noAcct; exact Nat.zero_le _
  have hget : ∀ (l : List Acct) (n : Nat), (∀ a ∈ l, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index) → (l.getD n noAcct).supplierIndex ≤ s.supplyState.index ∧ (l.getD n noAcct).borrowerIndex ≤ s.borrowState.index := by
    intro l
    induction l with
    | nil => intro n _; simp; exact ⟨hbase_sup, hbase_bor⟩
    | cons hd tl ih =>
      intro n hall2
      cases n with
      | zero => simp; exact hall2 hd (by simp)
      | succ n => simp; exact ih n (fun a ha => hall2 a (by simp [ha]))
  exact hget s.accts who hall

theorem plan0_distributeSupplierComp_isSome_of_le_aux : True := trivial
#check @subChecked_some_eq

theorem probe_distr2 (s : St) (who : Account) (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ((if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index) := by
  by_cases hc : ((s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex)
  · simp only [if_pos hc]
    exact (And.right hc)
  · simp only [if_neg hc]
    exact h

theorem probe_distr3 (s : St) (who : Account) (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  unfold distributeSupplierComp
  have hle : (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
    by_cases hc : ((s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex)
    · simp only [if_pos hc]
      exact (And.right hc)
    · simp only [if_neg hc]
      exact h
  have hsub := subChecked_some_eq s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).supplierIndex) hle
  simp only [hsub]
  rfl

theorem plan0_distributeBorrowerComp_isSome_of_le_aux2 (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  unfold distributeBorrowerComp
  have hle : (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
    by_cases hc : ((s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex)
    · simp only [if_pos hc]
      exact (And.right hc)
    · simp only [if_neg hc]
      exact h
  have hsub := subChecked_some_eq s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).borrowerIndex) hle
  simp only [hsub]
  rfl

theorem plan0_distributeBorrowerComp_isSome_of_le2 : True := trivial

theorem plan0_distributeBorrowerComp_isSome_of_le (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  unfold distributeBorrowerComp
  have hle : (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
    by_cases hc : ((s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex)
    · simp only [if_pos hc]
      exact (And.right hc)
    · simp only [if_neg hc]
      exact h
  have hsub := subChecked_some_eq s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex else (s.acct who).borrowerIndex) hle
  simp only [hsub]
  rfl

theorem plan0_updateSupply_shape_aux : True := trivial
-- probe the structure of update
#check @updateCompSupplyIndex
#check @subChecked
#check @fraction

theorem plan0_updateSupply_shape (s s' : St)
    (hupd : updateCompSupplyIndex s = some s') :
    s'.accts = s.accts ∧
      s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber ∧
      s.supplyState.index ≤ s'.supplyState.index ∧
      s'.supplyState.block ≤ s'.blockNumber := by
  unfold updateCompSupplyIndex at hupd
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
      subChecked_some_eq s.blockNumber s.supplyState.block hle
    rw [hsub] at hupd
    by_cases hpos : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · simp only [if_pos hpos] at hupd
      have heq := Option.some_inj.mp hupd
      rw [← heq]
      exact ⟨rfl, rfl, rfl, Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [if_neg hpos] at hupd
      by_cases hpos2 : s.blockNumber - s.supplyState.block > 0
      · simp only [if_pos hpos2] at hupd
        have heq := Option.some_inj.mp hupd
        rw [← heq]
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
      · simp only [if_neg hpos2] at hupd
        have heq := Option.some_inj.mp hupd
        rw [← heq]
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, hle⟩
  · have hsub : subChecked s.blockNumber s.supplyState.block = none :=
      subChecked_none_eq s.blockNumber s.supplyState.block hle
    rw [hsub] at hupd
    simp at hupd

theorem plan0_updateBorrow_shape_aux2 (s s' : St)
    (hupd : updateCompBorrowIndex s = some s') :
    s'.accts = s.accts ∧
      s'.supplyState = s.supplyState ∧
      s'.blockNumber = s.blockNumber ∧
      s.borrowState.index ≤ s'.borrowState.index ∧
      s'.borrowState.block ≤ s'.blockNumber := by
  unfold updateCompBorrowIndex at hupd
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
      subChecked_some_eq s.blockNumber s.borrowState.block hle
    rw [hsub] at hupd
    by_cases hpos : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · simp only [if_pos hpos] at hupd
      have heq := Option.some_inj.mp hupd
      rw [← heq]
      exact ⟨rfl, rfl, rfl, Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [if_neg hpos] at hupd
      by_cases hpos2 : s.blockNumber - s.borrowState.block > 0
      · simp only [if_pos hpos2] at hupd
        have heq := Option.some_inj.mp hupd
        rw [← heq]
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
      · simp only [if_neg hpos2] at hupd
        have heq := Option.some_inj.mp hupd
        rw [← heq]
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, hle⟩
  · have hsub : subChecked s.blockNumber s.borrowState.block = none :=
      subChecked_none_eq s.blockNumber s.borrowState.block hle
    rw [hsub] at hupd
    simp at hupd

theorem plan0_withAcct_supplierIndex_probe (s : St) (who : Account)
    (f : Acct → Acct) :
    (s.withAcct who f).supplyState = s.supplyState := by
  rfl
#check @List.modify
#check @List.getD

theorem probe_modify_cons0 (hd : Acct) (tl : List Acct) (f : Acct → Acct) :
    (hd :: tl).modify 0 f = f hd :: tl := by rfl

theorem probe_modify_consS (hd : Acct) (tl : List Acct) (n : Nat) (f : Acct → Acct) :
    (hd :: tl).modify (n+1) f = hd :: tl.modify n f := by rfl

theorem probe_getD_cons0 (hd : Acct) (tl : List Acct) :
    (hd :: tl).getD 0 noAcct = hd := by rfl

theorem probe_getD_consS (hd : Acct) (tl : List Acct) (n : Nat) :
    (hd :: tl).getD (n+1) noAcct = tl.getD n noAcct := by rfl

theorem probe_modify_nil (f : Acct → Acct) (n : Nat) : ([] : List Acct).modify n f = [] := by
  cases n <;> rfl

theorem probe_modify_oob (l : List Acct) (n : Nat) (f : Acct → Acct) (h : l.length ≤ n) :
    l.modify n f = l := by
  induction l generalizing n with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero => simp at h
    | succ n => simp; exact ih n (by simpa using h)

theorem myModGetAux (l : List Acct) (n : Nat) (f : Acct → Acct) (h : n + 1 ≤ l.length) :
    (l.modify n f).getD n noAcct = f (l.getD n noAcct) := by
  induction l generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [probe_modify_consS, probe_getD_consS]
      exact ih n (by simpa using h)

theorem probeWithAcctProj (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).supplyState = s.supplyState := by
  unfold St.withAcct
  rfl

theorem probeWithAcctProj2 (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).blockNumber = s.blockNumber := by
  unfold St.withAcct
  rfl

theorem probeWithAcctAcct (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex)
    (hget : (s.accts.modify who f).getD who noAcct = f (s.accts.getD who noAcct)) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.withAcct St.acct
  simp only [hget, hf]

theorem tmpWithAcctPf (s : St) (who : Account)
    (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex =
        (s.acct who).supplierIndex ∧
      (s.withAcct who f).supplyState = s.supplyState ∧
      (s.withAcct who f).blockNumber = s.blockNumber := by
  have h1 : ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
    by_cases hlt : who < s.accts.length
    · have hle : who + 1 ≤ s.accts.length := hlt
      have hget : (s.accts.modify who f).getD who noAcct = f (s.accts.getD who noAcct) :=
        myModGetAux s.accts who f hle
      exact probeWithAcctAcct s who f hf hget
    · have hge : s.accts.length ≤ who := Nat.le_of_not_gt hlt
      have hmod : s.accts.modify who f = s.accts := probe_modify_oob s.accts who f hge
      unfold St.withAcct St.acct
      simp only [hmod]
    -- wait need hf? no, hmod case: acct same so rfl
  exact ⟨h1, rfl, rfl⟩

theorem plan1_modify_getD_self (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : n < l.length) :
    (l.modify n f).getD n noAcct = f (l.getD n noAcct) := myModGetAux l n f h








theorem plan1_modify_getD_self_new (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : n < l.length) :
    (l.modify n f).getD n noAcct = f (l.getD n noAcct) := myModGetAux l n f h

theorem plan1_modify_eq_self_of_le (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : l.length ≤ n) :
    l.modify n f = l := probe_modify_oob l n f h

theorem plan1_getD_modify_supplierIndex (l : List Acct) (n : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD n noAcct).supplierIndex =
      (l.getD n noAcct).supplierIndex := by
  by_cases hlt : n < l.length
  · have hget : (l.modify n f).getD n noAcct = f (l.getD n noAcct) :=
      myModGetAux l n f hlt
    rw [hget, hf]
  · have hge : l.length ≤ n := Nat.le_of_not_gt hlt
    have hmod : l.modify n f = l := probe_modify_oob l n f hge
    rw [hmod]

theorem plan1_withAcct_proj (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).supplyState = s.supplyState ∧
      (s.withAcct who f).blockNumber = s.blockNumber := ⟨rfl, rfl⟩

theorem plan0_withAcct_supplierIndex (s : St) (who : Account)
    (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex =
        (s.acct who).supplierIndex ∧
      (s.withAcct who f).supplyState = s.supplyState ∧
      (s.withAcct who f).blockNumber = s.blockNumber := by
  have h1 : ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
    unfold St.withAcct St.acct
    exact plan1_getD_modify_supplierIndex s.accts who f hf
  exact ⟨h1, rfl, rfl⟩

theorem cs_effSup_le (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
     else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
  by_cases hc : ((s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex)
  · simp only [if_pos hc]; exact And.right hc
  · simp only [if_neg hc]; exact h

theorem cs_distSup_state (s s' : St) (who : Account)
    (h : distributeSupplierComp s who = some s') :
    s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber ∧ s'.reserve = s.reserve := by
  have heq : distributeSupplierComp s who =
    match subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + mulDouble (s.acct who).supply d }) := by
    rfl
  rw [heq] at h
  cases hd : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem cs_distBor_state (s s' : St) (who : Account)
    (h : distributeBorrowerComp s who = some s') :
    s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber ∧ s'.reserve = s.reserve := by
  have heq : distributeBorrowerComp s who =
    match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + mulDouble (s.acct who).borrow d }) := by
    rfl
  rw [heq] at h
  cases hd : subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem cs_effBor_le (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
     else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
  by_cases hc : ((s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex)
  · simp only [if_pos hc]; exact And.right hc
  · simp only [if_neg hc]; exact h

theorem cs_distBor_some (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  have heq : distributeBorrowerComp s who =
    match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + mulDouble (s.acct who).borrow d }) := by
    rfl
  rw [heq]
  cases hd : subChecked s.borrowState.index _ with
  | none =>
    exfalso
    have hle := cs_effBor_le s who h
    have hs := subChecked_some_eq s.borrowState.index _ hle
    rw [hs] at hd
    simp at hd
  | some d => rfl

theorem cs_distSup_some (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  have heq : distributeSupplierComp s who =
    match subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + mulDouble (s.acct who).supply d }) := by
    rfl
  rw [heq]
  cases hd : subChecked s.supplyState.index _ with
  | none =>
    exfalso
    have hle := cs_effSup_le s who h
    have hs := subChecked_some_eq s.supplyState.index _ hle
    rw [hs] at hd
    simp at hd
  | some d => rfl

theorem cs_updSup_accts (s s' : St) (h : updateCompSupplyIndex s = some s') :
    s'.accts = s.accts ∧ s'.borrowState = s.borrowState ∧ s'.blockNumber = s.blockNumber ∧
    s.supplyState.index ≤ s'.supplyState.index ∧ s'.supplyState.block ≤ s'.blockNumber ∧
    s'.supplyState.speed = s.supplyState.speed := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := plan0_updateSupply_shape s s' h
  unfold updateCompSupplyIndex at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
      subChecked_some_eq s.blockNumber s.supplyState.block hle
    rw [hsub] at h
    by_cases hpos : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · simp only [if_pos hpos] at h
      have heq := Option.some_inj.mp h
      subst heq
      exact ⟨rfl, rfl, rfl, Nat.le_add_right _ _, Nat.le_refl _, rfl⟩
    · simp only [if_neg hpos] at h
      by_cases hpos2 : s.blockNumber - s.supplyState.block > 0
      · simp only [if_pos hpos2] at h
        have heq := Option.some_inj.mp h
        subst heq
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, rfl⟩
      · simp only [if_neg hpos2] at h
        have heq := Option.some_inj.mp h
        subst heq
        exact ⟨rfl, rfl, rfl, Nat.le_refl _, hle, rfl⟩
  · have hsub : subChecked s.blockNumber s.supplyState.block = none :=
      subChecked_none_eq s.blockNumber s.supplyState.block hle
    rw [hsub] at h
    simp at h

theorem updSup_bank3 (s s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
      subChecked_some_eq s.blockNumber s.supplyState.block hle
    rw [hsub] at h
    simp only at h
    by_cases hpos : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · rw [if_pos hpos] at h
      obtain ⟨rfl⟩ := Option.some_inj.mp h
      refine ⟨hle, ?_⟩
      unfold accrueSide totalSupply
      by_cases ht : 0 < (List.map Acct.supply s.accts).sum
      · have hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (List.map Acct.supply s.accts).sum := ⟨hpos.1, hpos.2, ht⟩
        simp only [hc, if_true]
        unfold fraction
        rfl
      · have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (List.map Acct.supply s.accts).sum) := fun hcon => ht hcon.2.2
        simp only [hc, if_false]
        have ht2 : ¬ (List.map Acct.supply s.accts).sum > 0 := by omega
        simp only [ht2, if_false, Nat.add_zero]
    · rw [if_neg hpos] at h
      by_cases hpos2 : s.blockNumber - s.supplyState.block > 0
      · rw [if_pos hpos2] at h
        obtain ⟨rfl⟩ := Option.some_inj.mp h
        refine ⟨hle, ?_⟩
        unfold accrueSide totalSupply
        have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (List.map Acct.supply s.accts).sum) := fun hcon => hpos ⟨hcon.1, hcon.2.1⟩
        simp only [hc, if_false]
      · rw [if_neg hpos2] at h
        obtain ⟨rfl⟩ := Option.some_inj.mp h
        refine ⟨hle, ?_⟩
        unfold accrueSide
        have hzero : s.blockNumber - s.supplyState.block = 0 :=
          Nat.le_zero.mp (Nat.le_of_not_gt hpos2)
        have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by simp [hzero]
        simp only [hc, if_false]
        have hbeq : s.supplyState.block = s.blockNumber := Nat.le_antisymm hle (by omega)
        have hside : ({ s.supplyState with block := s.blockNumber } : Side) = s.supplyState := by
          cases hsd : s.supplyState with
          | mk i b sp => simp_all
        rw [hside]
  · have hsub : subChecked s.blockNumber s.supplyState.block = none :=
      subChecked_none_eq s.blockNumber s.supplyState.block hle
    rw [hsub] at h
    simp at h











theorem plan2_accrualStart_eq_effective_test (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) := by
  unfold accrualStart
  by_cases h0 : recorded = 0
  · subst h0
    simp only [true_and]
    by_cases h1 : compInitialIndex ≤ index <;> simp [h1]
  · simp [h0]

theorem plan2_accrualStart_eq_effective (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) := by
  unfold accrualStart
  by_cases h0 : recorded = 0
  · subst h0
    simp only [true_and]
    by_cases h1 : compInitialIndex ≤ index <;> simp [h1]
  · simp [h0]

theorem plan2_modify_ext_getD (l : List Acct) (n : Nat) (f g : Acct → Acct)
    (h : f (l.getD n noAcct) = g (l.getD n noAcct)) :
    l.modify n f = l.modify n g := by
  induction l generalizing n with
  | nil =>
    cases n <;> rfl
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp only [probe_modify_cons0] at *
      simp only [probe_getD_cons0] at h
      rw [h]
    | succ n =>
      simp only [probe_modify_consS, probe_getD_consS] at *
      rw [ih n h]

theorem plan2_accrualStart_le_of_distributeSupplierComp_some
    (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index := by
  have heff := plan2_accrualStart_eq_effective (s.acct who).supplierIndex s.supplyState.index
  rw [heff]
  have heq : distributeSupplierComp s who =
    match subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + mulDouble (s.acct who).supply d }) := by
    rfl
  rw [heq] at h
  cases hd : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    unfold subChecked at hd
    by_cases hle : (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) ≤ s.supplyState.index
    · exact hle
    · simp [hle] at hd

theorem plan2_distributeSupplierComp_eq_aux_test : True := trivial

theorem plan2_distributeSupplierComp_eq_proofB (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with
        accts := s.accts.modify who fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex s.supplyState.index)
              s.supplyState.index } } := by
  have heff : (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    (plan2_accrualStart_eq_effective (s.acct who).supplierIndex s.supplyState.index).symm
  have hsub : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    rw [heff]
    exact subChecked_some_eq s.supplyState.index _ h
  have hval : mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = creditFor (s.accts.getD who noAcct).supply (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) s.supplyState.index := by
    unfold St.acct at *
    unfold mulDouble creditFor
    rfl
  have hfun : (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) ((s.accts.getD who noAcct))
    = (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) ((s.accts.getD who noAcct)) := by
    simp only [hval]
  have hmod : (s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct))
    = (s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) :=
    plan2_modify_ext_getD s.accts who _ _ hfun
  have hdist : distributeSupplierComp s who =
    (match subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + mulDouble (s.acct who).supply d }) ) := rfl
  rw [hdist, hsub]
  simp only [St.withAcct]
  rw [hmod]

theorem plan2_tmp_check : True := trivial

theorem plan2_distributeSupplierComp_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with
        accts := s.accts.modify who fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex s.supplyState.index)
              s.supplyState.index } } := by
  have heff : (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    (plan2_accrualStart_eq_effective (s.acct who).supplierIndex s.supplyState.index).symm
  have hsub : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    rw [heff]
    exact subChecked_some_eq s.supplyState.index _ h
  have hval : mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = creditFor (s.accts.getD who noAcct).supply (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) s.supplyState.index := by
    unfold St.acct at *
    unfold mulDouble creditFor
    rfl
  have hfun : (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) ((s.accts.getD who noAcct))
    = (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) ((s.accts.getD who noAcct)) := by
    simp only [hval]
  have hmod : (s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct))
    = (s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) :=
    plan2_modify_ext_getD s.accts who _ _ hfun
  have hdist : distributeSupplierComp s who =
    (match subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).supplierIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + mulDouble (s.acct who).supply d }) ) := rfl
  rw [hdist, hsub]
  simp only [St.withAcct]
  rw [hmod]

theorem plan2_bind_ex (s : St) (who : Account) (s' : St)
    (hbind : Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) = some s') :
    ∃ s1, updateCompSupplyIndex s = some s1 ∧ distributeSupplierComp s1 who = some s' := by
  generalize ho : updateCompSupplyIndex s = o at hbind ⊢
  cases o with
  | none =>
    simp at hbind
  | some t =>
    refine ⟨t, ?_, ?_⟩
    · simp [← ho]
    · simpa using hbind

theorem plan2_supplyHook_eq_aux999 (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) = some s' := h

theorem plan2_supplyHook_eq_final_check (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) = some s' := h

theorem plan2_supplyHook_eq (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    s.supplyState.block ≤ s.blockNumber ∧
    accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex :=
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  have hbind : Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) = some s' := h
  obtain ⟨s1, hs1, hs2⟩ := plan2_bind_ex s who s' hbind
  obtain ⟨hblock, hs1eq⟩ := updSup_bank3 s s1 hs1
  have haccts : s1.accts = s.accts := by rw [hs1eq]
  have hside : s1.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by rw [hs1eq]
  have hacct : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hidx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hside]
  have hle1 : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index :=
    plan2_accrualStart_le_of_distributeSupplierComp_some s1 who s' hs2
  have hle : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [← hacct, ← hidx]
    exact hle1
  have hdist := plan2_distributeSupplierComp_eq s1 who hle1
  rw [hs2] at hdist
  have hs_eq : s' = { s1 with accts := s1.accts.modify who fun a =>
      { a with supplierIndex := s1.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index) s1.supplyState.index } } :=
    Option.some_inj.mp hdist
  refine ⟨hblock, hle, ?_⟩
  rw [hs_eq, haccts, hside]
  rw [hs1eq]

theorem borUpd_bank3_new (s s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
      subChecked_some_eq s.blockNumber s.borrowState.block hle
    rw [hsub] at h
    simp only at h
    by_cases hpos : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · rw [if_pos hpos] at h
      obtain ⟨rfl⟩ := Option.some_inj.mp h
      refine ⟨hle, ?_⟩
      unfold accrueSide totalBorrows
      by_cases ht : 0 < (List.map Acct.borrow s.accts).sum
      · have hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (List.map Acct.borrow s.accts).sum := ⟨hpos.1, hpos.2, ht⟩
        simp only [hc, if_true]
        unfold fraction
        rfl
      · have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (List.map Acct.borrow s.accts).sum) := fun hcon => ht hcon.2.2
        simp only [hc, if_false]
        have ht2 : ¬ (List.map Acct.borrow s.accts).sum > 0 := by omega
        simp only [ht2, if_false, Nat.add_zero]
    · rw [if_neg hpos] at h
      by_cases hpos2 : s.blockNumber - s.borrowState.block > 0
      · rw [if_pos hpos2] at h
        obtain ⟨rfl⟩ := Option.some_inj.mp h
        refine ⟨hle, ?_⟩
        unfold accrueSide totalBorrows
        have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (List.map Acct.borrow s.accts).sum) := fun hcon => hpos ⟨hcon.1, hcon.2.1⟩
        simp only [hc, if_false]
      · rw [if_neg hpos2] at h
        obtain ⟨rfl⟩ := Option.some_inj.mp h
        refine ⟨hle, ?_⟩
        unfold accrueSide
        have hzero : s.blockNumber - s.borrowState.block = 0 :=
          Nat.le_zero.mp (Nat.le_of_not_gt hpos2)
        have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by simp [hzero]
        simp only [hc, if_false]
        have hbeq : s.borrowState.block = s.blockNumber := Nat.le_antisymm hle (by omega)
        have hside : ({ s.borrowState with block := s.blockNumber } : Side) = s.borrowState := by
          cases hsd : s.borrowState with
          | mk i b sp => simp_all
        rw [hside]
  · have hsub : subChecked s.blockNumber s.borrowState.block = none :=
      subChecked_none_eq s.blockNumber s.borrowState.block hle
    rw [hsub] at h
    simp at h

theorem borAccrual_le_of_some_new (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index := by
  have heff := plan2_accrualStart_eq_effective (s.acct who).borrowerIndex s.borrowState.index
  rw [heff]
  have heq : distributeBorrowerComp s who =
    match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + mulDouble (s.acct who).borrow d }) := rfl
  rw [heq] at h
  cases hd : subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    unfold subChecked at hd
    by_cases hle : (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) ≤ s.borrowState.index
    · exact hle
    · simp [hle] at hd

theorem borDist_eq_new (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with
        accts := s.accts.modify who fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index)
              s.borrowState.index } } := by
  have heff : (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    (plan2_accrualStart_eq_effective (s.acct who).borrowerIndex s.borrowState.index).symm
  have hsub : subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    rw [heff]
    exact subChecked_some_eq s.borrowState.index _ h
  have hval : mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      = creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index := by
    unfold St.acct at *
    unfold mulDouble creditFor
    rfl
  have hfun : (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)) ((s.accts.getD who noAcct))
    = (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) ((s.accts.getD who noAcct)) := by
    simp only [hval]
  have hmod : (s.accts.modify who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct))
    = (s.accts.modify who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) :=
    plan2_modify_ext_getD s.accts who _ _ hfun
  have hdist : distributeBorrowerComp s who =
    (match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
       else (s.acct who).borrowerIndex) with
    | none => (none : Option St)
    | some d => some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + mulDouble (s.acct who).borrow d }) ) := rfl
  rw [hdist, hsub]
  simp only [St.withAcct]
  rw [hmod]

theorem borBind_ex2 (s : St) (who : Account) (s' : St)
    (hbind : Option.bind (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who) = some s') :
    ∃ s1, updateCompBorrowIndex s = some s1 ∧ distributeBorrowerComp s1 who = some s' := by
  generalize ho : updateCompBorrowIndex s = o at hbind ⊢
  cases o with
  | none => simp at hbind
  | some t =>
    refine ⟨t, ?_, ?_⟩
    · simp [← ho]
    · simpa using hbind

theorem borHook_eq2 (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    s.borrowState.block ≤ s.blockNumber ∧
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ∧
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex :=
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  have hbind : Option.bind (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who) = some s' := h
  obtain ⟨s1, hs1, hs2⟩ := borBind_ex2 s who s' hbind
  obtain ⟨hblock, hs1eq⟩ := borUpd_bank3_new s s1 hs1
  have haccts : s1.accts = s.accts := by rw [hs1eq]
  have hside : s1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hs1eq]
  have hacct : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hidx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hside]
  have hle1 : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index :=
    borAccrual_le_of_some_new s1 who s' hs2
  have hle : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hidx]
    exact hle1
  have hdist := borDist_eq_new s1 who hle1
  rw [hs2] at hdist
  have hs_eq : s' = { s1 with accts := s1.accts.modify who fun a =>
      { a with borrowerIndex := s1.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } } :=
    Option.some_inj.mp hdist
  refine ⟨hblock, hle, ?_⟩
  rw [hs_eq, haccts, hside]
  rw [hs1eq]

theorem grant_probe1 (s : St) (who : Account)
    (h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) :
    grantCompInternal s who =
    { s with reserve := s.reserve - (s.acct who).accrued,
             accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } } := by
  unfold grantCompInternal
  simp [h]

theorem grant_probe2b (s : St) (who : Account)
    (h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) :
    grant s who =
    { s with reserve := s.reserve - (s.acct who).accrued,
             accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  unfold grant
  simp [h]

theorem grant_probe3b (s : St) (who : Account)
    (h : ¬ ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve)) :
    grantCompInternal s who = s := by
  unfold grantCompInternal
  simp [h]

theorem grant_probe4b (s : St) (who : Account)
    (h : ¬ ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve)) :
    grant s who = s := by
  unfold grant
  simp [h]

theorem grant_eq_full (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by
  by_cases h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve
  · have h1 := grant_probe1 s who h
    have h2 := grant_probe2b s who h
    rw [h1, h2]
    have hfun : (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) (s.accts.getD who noAcct)
      = (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) (s.accts.getD who noAcct) := by
      simp only [St.acct]
    have hmod := plan2_modify_ext_getD s.accts who
      (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct))
      (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) hfun
    -- the two structures differ only in accts field; rewrite
    rw [hmod]
  · have h1 := grant_probe3b s who h
    have h2 := grant_probe4b s who h
    rw [h1, h2]



theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := grant_eq_full s who


theorem plan3_borrowHook_distributed (s : St) (who : Account) (m1 : St)
    (h : comptroller s (.borrowHook who) = some m1) :
    BorrowDistributed s who m1 := by
  have h3 := borHook_eq2 s who m1 h
  obtain ⟨hb, hle, heq⟩ := h3
  exact ⟨hb, hle, heq⟩


theorem plan3_supplyHook_distributed (s : St) (who : Account) (m2 : St)
    (h : comptroller s (.supplyHook who) = some m2) :
    SupplyDistributed s who m2 := by
  have h3 := plan2_supplyHook_eq s who m2 h
  obtain ⟨hb, hle, heq⟩ := h3
  exact ⟨hb, hle, heq⟩


theorem plan3_claimed_of_steps (s : St) (who : Account) (m1 m2 s' : St)
    (hb : BorrowDistributed s who m1)
    (hs : SupplyDistributed m1 who m2)
    (hg : s' = grantCompInternal m2 who) :
    Claimed s who s' := by unfold Claimed; exact ⟨m1, m2, hb, hs, by rw [hg, grant_eq_full]⟩


theorem plan3_claim_decompose_aux_test2 : True := trivial

theorem plan3_bind_some_ex (o : Option St) (f : St → Option St) (s' : St)
    (h : Option.bind o f = some s') :
    ∃ t, o = some t ∧ f t = some s' := by
  cases o with
  | none => simp at h
  | some t =>
    simp at h
    exact ⟨t, rfl, h⟩

theorem plan3_bind_some_back2 (o : Option St) (f : St → Option St) (t s' : St)
    (ho : o = some t) (hf : f t = some s') :
    Option.bind o f = some s' := by
  rw [ho]
  simpa using hf

theorem plan3_claim_decompose_proof3 : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.claim who) = some s' →
    ∃ m1 m2, comptroller s (.borrowHook who) = some m1 ∧
      comptroller m1 (.supplyHook who) = some m2 ∧
      s' = grantCompInternal m2 who := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
  have h1 : Option.bind (updateCompBorrowIndex s) (fun s1 => Option.bind (distributeBorrowerComp s1 who) (fun s2 => Option.bind (updateCompSupplyIndex s2) (fun s3 => Option.bind (distributeSupplierComp s3 who) (fun s4 => some (grantCompInternal s4 who))))) = some s' := h
  obtain ⟨t1, ht1_eq, ht1_rest⟩ := plan3_bind_some_ex (updateCompBorrowIndex s) _ s' h1
  obtain ⟨t2, ht2_eq, ht2_rest⟩ := plan3_bind_some_ex (distributeBorrowerComp t1 who) _ s' ht1_rest
  obtain ⟨t3, ht3_eq, ht3_rest⟩ := plan3_bind_some_ex (updateCompSupplyIndex t2) _ s' ht2_rest
  obtain ⟨t4, ht4_eq, ht4_grant⟩ := plan3_bind_some_ex (distributeSupplierComp t3 who) _ s' ht3_rest
  have hgrant : grantCompInternal t4 who = s' := Option.some_inj.mp ht4_grant
  refine ⟨t2, t4, ?_, ?_, ?_⟩
  · unfold comptroller
    exact plan3_bind_some_back2 (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who) t1 t2 ht1_eq ht2_eq
  · unfold comptroller
    exact plan3_bind_some_back2 (updateCompSupplyIndex t2) (fun s1 => distributeSupplierComp s1 who) t3 t4 ht3_eq ht4_eq
  · exact hgrant.symm

theorem plan3_claim_decompose_new : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.claim who) = some s' →
    ∃ m1 m2, comptroller s (.borrowHook who) = some m1 ∧
      comptroller m1 (.supplyHook who) = some m2 ∧
      s' = grantCompInternal m2 who := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
  have h1 : Option.bind (updateCompBorrowIndex s) (fun s1 => Option.bind (distributeBorrowerComp s1 who) (fun s2 => Option.bind (updateCompSupplyIndex s2) (fun s3 => Option.bind (distributeSupplierComp s3 who) (fun s4 => some (grantCompInternal s4 who))))) = some s' := h
  obtain ⟨t1, ht1_eq, ht1_rest⟩ := plan3_bind_some_ex (updateCompBorrowIndex s) _ s' h1
  obtain ⟨t2, ht2_eq, ht2_rest⟩ := plan3_bind_some_ex (distributeBorrowerComp t1 who) _ s' ht1_rest
  obtain ⟨t3, ht3_eq, ht3_rest⟩ := plan3_bind_some_ex (updateCompSupplyIndex t2) _ s' ht2_rest
  obtain ⟨t4, ht4_eq, ht4_grant⟩ := plan3_bind_some_ex (distributeSupplierComp t3 who) _ s' ht3_rest
  have hgrant : grantCompInternal t4 who = s' := Option.some_inj.mp ht4_grant
  refine ⟨t2, t4, ?_, ?_, ?_⟩
  · unfold comptroller
    exact plan3_bind_some_back2 (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who) t1 t2 ht1_eq ht2_eq
  · unfold comptroller
    exact plan3_bind_some_back2 (updateCompSupplyIndex t2) (fun s1 => distributeSupplierComp s1 who) t3 t4 ht3_eq ht4_eq
  · exact hgrant.symm

theorem plan3_inline_test2 (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    ∃ m1 m2, comptroller s (.borrowHook who) = some m1 ∧
      comptroller m1 (.supplyHook who) = some m2 ∧
      s' = grantCompInternal m2 who := by
  unfold comptroller claimComp at h
  simp only at h
  cases h1 : updateCompBorrowIndex s with
  | none =>
    simp [h1] at h
  | some t1 =>
    simp [h1] at h
    cases h2 : distributeBorrowerComp t1 who with
    | none =>
      simp [h2] at h
    | some t2 =>
      simp [h2] at h
      cases h3 : updateCompSupplyIndex t2 with
      | none =>
        simp [h3] at h
      | some t3 =>
        simp [h3] at h
        cases h4 : distributeSupplierComp t3 who with
        | none =>
          simp [h4] at h
        | some t4 =>
          simp [h4] at h
          refine ⟨t2, t4, ?_, ?_, ?_⟩
          · unfold comptroller
            simp [h1, h2]
          · unfold comptroller
            simp [h3, h4]
          · exact h.symm



theorem plan4_borrowHook_eq_bind (s : St) (who : Account) :
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who) := by rfl




theorem plan4_claim_eq_hook_binds (s : St) (who : Account) :
    comptroller s (.claim who) =
      (comptroller s (.borrowHook who)).bind
        (fun m1 => (comptroller m1 (.supplyHook who)).bind
          (fun m2 => some (grantCompInternal m2 who))) := by sorry

theorem plan4_bind_some_elim (o : Option St) (f : St → Option St) (y : St)
    (h : o.bind f = some y) :
    ∃ t, o = some t ∧ f t = some y := by
  cases o with
  | none => simp at h
  | some t => exact ⟨t, rfl, h⟩

theorem plan4_borrowHook_eq_bind_proof : ∀ (s : St) (who : Account),
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who) := by
  intro s who
  rfl

theorem plan4_supplyHook_eq_bind (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind (fun s1 => distributeSupplierComp s1 who) := rfl

theorem plan4_probe_assoc_state : True := by
  have h1 : ∀ (a : Option St) (f : St → Option St) (g : St → Option St),
    Option.bind (Option.bind a f) g = Option.bind a (fun x => Option.bind (f x) g) := by
    intro a f g
    cases a <;> rfl
  trivial

theorem plan4_assoc_check : ∀ (a : Option St) (f : St → Option St) (g : St → Option St),
    (a.bind f).bind g = a.bind (fun x => (f x).bind g) := by
  intro a f g
  cases a <;> rfl

theorem plan4_reduce_probe (s : St) (who : Account) :
    comptroller s (.claim who) = claimComp s who := by
  unfold comptroller
  simp

theorem plan4_assoc_opt : ∀ (a : Option St) (f : St → Option St) (g : St → Option St),
    Option.bind (Option.bind a f) g = Option.bind a (fun x => Option.bind (f x) g) := by
  intro a f g
  cases a <;> rfl

theorem plan3_claim_decompose (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    ∃ m1 m2, comptroller s (.borrowHook who) = some m1 ∧
      comptroller m1 (.supplyHook who) = some m2 ∧
      s' = grantCompInternal m2 who :=
  plan3_claim_decompose_new s who s' h

theorem plan3_grantCompInternal_eq_grant2 (s : St) (who : Account) :
    grantCompInternal s who = grant s who := grant_eq_full s who

theorem plan3_borrowHook_distributed_pf2 : True := trivial

theorem plan3_supplyHook_distributed_aux_pf : True := trivial

theorem plan3_supplyHook_distributed_check (s : St) (who : Account) (m2 : St)
    (h : comptroller s (.supplyHook who) = some m2) :
    SupplyDistributed s who m2 := by
  have h3 := plan2_supplyHook_eq s who m2 h
  obtain ⟨hb, hle, heq⟩ := h3
  exact ⟨hb, hle, heq⟩

theorem plan3_supplyHook_distributed2 (s : St) (who : Account) (m2 : St)
    (h : comptroller s (.supplyHook who) = some m2) :
    SupplyDistributed s who m2 := by
  have h3 := plan2_supplyHook_eq s who m2 h
  obtain ⟨hb, hle, heq⟩ := h3
  exact ⟨hb, hle, heq⟩

theorem plan3_claimed_of_steps_proof : ∀ (s : St) (who : Account) (m1 m2 s' : St),
    BorrowDistributed s who m1 →
    SupplyDistributed m1 who m2 →
    (s' = grantCompInternal m2 who) →
    Claimed s who s' := by
  intro s who m1 m2 s' hb hs hg
  unfold Claimed
  exact ⟨m1, m2, hb, hs, by rw [hg, grant_eq_full]⟩

theorem setSupply_char2 (s : St) (a : Nat) (m : St)
    (h : setSupplySpeed s a = some m) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    m = { s with supplyState := if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    subst h
    simp [heq]
  · simp [heq] at h
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      subst h
      obtain ⟨hblock, hueq⟩ := updSup_bank3 s u hu
      rw [hueq]
      refine ⟨fun _ => hblock, ?_⟩
      simp [heq]

theorem setBorrow_char2 (s : St) (b : Nat) (m : St)
    (h : setBorrowSpeed s b = some m) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    m = { s with borrowState := if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    subst h
    simp [heq]
  · simp [heq] at h
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      subst h
      obtain ⟨hblock, hueq⟩ := borUpd_bank3_new s u hu
      rw [hueq]
      refine ⟨fun _ => hblock, ?_⟩
      simp [heq]

theorem probe_comp_set (s : St) (a b : Nat) :
    comptroller s (.setSpeeds a b) = (setSupplySpeed s a).bind (fun m => setBorrowSpeed m b) := by
  unfold comptroller setCompSpeedInternal
  rfl

theorem setSpeeds_decompB (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ m, setSupplySpeed s a = some m ∧ setBorrowSpeed m b = some s' := by
  have heq := probe_comp_set s a b
  rw [heq] at h
  exact plan3_bind_some_ex _ _ _ h

theorem m_bor_test (s : St) (a : Nat) (m : St)
    (hmeq : m = { s with supplyState := if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    m.borrowState = s.borrowState := by
  rw [hmeq]

theorem totBor_congr2 (m s : St) (h : m.accts = s.accts) :
    totalBorrows m = totalBorrows s := by
  unfold totalBorrows
  rw [h]

theorem totSup_congr2 (m s : St) (h : m.accts = s.accts) :
    totalSupply m = totalSupply s := by
  unfold totalSupply
  rw [h]

theorem supBlock_eq (s : St) (a : Nat) (m : St)
    (hmeq : m = { s with supplyState := if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    m.blockNumber = s.blockNumber := by
  rw [hmeq]

theorem supAccts_eq (s : St) (a : Nat) (m : St)
    (hmeq : m = { s with supplyState := if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    m.accts = s.accts := by
  rw [hmeq]

theorem plan5_setSpeeds_decomp (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ m, setSupplySpeed s a = some m ∧ setBorrowSpeed m b = some s' := by
  have heq := probe_comp_set s a b
  rw [heq] at h
  exact plan3_bind_some_ex _ _ _ h






theorem plan5_combine_updates (s : St) (a b : Nat) (m s' : St)
    (hm : m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hs' : s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) :
    s' = { s with
      supplyState :=
        if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState :=
        if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  subst hm
  subst hs'
  rfl




theorem plan5_setSpeeds_decomp_aux_proof : True := trivial

theorem plan5_setSpeeds_decomp_check (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ m, setSupplySpeed s a = some m ∧ setBorrowSpeed m b = some s' := by
  have heq := probe_comp_set s a b
  rw [heq] at h
  exact plan3_bind_some_ex _ _ _ h

theorem plan5_supply_form (s : St) (a : Nat) (m : St)
    (h : setSupplySpeed s a = some m) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } ∧
    m.borrowState = s.borrowState ∧
    m.accts = s.accts ∧
    m.blockNumber = s.blockNumber := by
  obtain ⟨hcond, hmeq⟩ := setSupply_char2 s a m h
  exact ⟨hcond, hmeq, by rw [hmeq], by rw [hmeq], by rw [hmeq]⟩

theorem plan5_borrow_form_translated (s : St) (b : Nat) (m s' : St)
    (hmBorrow : m.borrowState = s.borrowState)
    (hmAccts : m.accts = s.accts)
    (hmBlock : m.blockNumber = s.blockNumber)
    (h : setBorrowSpeed m b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  obtain ⟨hcondM, hmeq⟩ := setBorrow_char2 m b s' h
  have hspeed : m.borrowState.speed = s.borrowState.speed := by rw [hmBorrow]
  have hblock_eq : m.borrowState.block = s.borrowState.block := by rw [hmBorrow]
  have htot : totalBorrows m = totalBorrows s := totBor_congr2 m s hmAccts
  have hcond : (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) := by
    intro hne
    have hneM : m.borrowState.speed ≠ b := by rw [hspeed]; exact hne
    have hle := hcondM hneM
    rw [hblock_eq, hmBlock] at hle
    exact hle
  have hif : (if m.borrowState.speed = b then m.borrowState
      else { accrueSide m.borrowState m.blockNumber (totalBorrows m) with speed := b }) =
      (if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) := by
    rw [hspeed, hmBorrow, hmBlock, htot]
  refine ⟨hcond, ?_⟩
  rw [hmeq, hif]

theorem plan5_combine_updates_auxcheck (s : St) (a b : Nat) (m s' : St)
    (hm : m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hs' : s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) :
    s' = { s with
      supplyState :=
        if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState :=
        if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  subst hm
  subst hs'
  rfl

theorem plan5_combine_updates2 (s : St) (a b : Nat) (m s' : St)
    (hm : m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hs' : s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) :
    s' = { s with
      supplyState :=
        if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState :=
        if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } :=
  plan5_combine_updates_auxcheck s a b m s' hm hs'

theorem plan5_combine_updates_new (s : St) (a b : Nat) (m s' : St)
    (hm : m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hs' : s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) :
    s' = { s with
      supplyState :=
        if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState :=
        if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  exact plan5_combine_updates_auxcheck s a b m s' hm hs'

theorem plan5_combine_updates_selfcontained (s : St) (a b : Nat) (m s' : St)
    (hm : m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hs' : s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) :
    s' = { s with
      supplyState :=
        if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState :=
        if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  subst hm
  subst hs'
  rfl

theorem plan5_speedsSet_of_steps_proof : ∀ (s : St) (a b : Nat) (m s' : St),
    setSupplySpeed s a = some m →
    setBorrowSpeed m b = some s' →
    SpeedsSet s a b s' := by
  intro s a b m s' hSup hBor
  obtain ⟨hcondSup, hmeqSup, hmBor, hmAccts, hmBlock⟩ := plan5_supply_form s a m hSup
  obtain ⟨hcondBor, hs'eq⟩ := plan5_borrow_form_translated s b m s' hmBor hmAccts hmBlock hBor
  unfold SpeedsSet
  refine ⟨hcondSup, hcondBor, ?_⟩
  exact plan5_combine_updates_selfcontained s a b m s' hmeqSup hs'eq

theorem plan5_speedsSet_of_steps (s : St) (a b : Nat) (m s' : St)
    (hSup : setSupplySpeed s a = some m)
    (hBor : setBorrowSpeed m b = some s') :
    SpeedsSet s a b s' := by
  obtain ⟨hcondSup, hmeqSup, hmBor, hmAccts, hmBlock⟩ := plan5_supply_form s a m hSup
  obtain ⟨hcondBor, hs'eq⟩ := plan5_borrow_form_translated s b m s' hmBor hmAccts hmBlock hBor
  exact ⟨hcondSup, hcondBor, plan5_combine_updates_selfcontained s a b m s' hmeqSup hs'eq⟩

theorem req_set_speeds_aux : SetSpeedsEffects comptroller := by
  intro s a b s' h
  obtain ⟨m, hm1, hm2⟩ := plan5_setSpeeds_decomp s a b s' h
  exact plan5_speedsSet_of_steps s a b m s' hm1 hm2

def testLegacy : Legacy :=
  { blockNumber := 1000, compSpeed := 0, supplyIndex := 0, supplyBlock := 1000,
    borrowIndex := 0, borrowBlock := 1000, supplyStart := 0, borrowStart := 0,
    reserve := 100000000000000000000000,
    accts := [{ supply := 0, borrow := 18977306140567618322762,
                 supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def testSt : St := upgrade testLegacy
#check testSt

def testClaim : Option St := comptroller testSt (.claim 0)

def testCred : Nat := match testClaim with | some s => (s.acct 0).wallet + (s.acct 0).accrued | none => 999
#check testCred

theorem test_no_pay : testCred = 0 := by rfl









theorem plan6_exec_potential_step (s : St) (op : Op) (sp : Nat × Nat)
    (hcons : Consistent s)
    (hsp : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    (exec comptroller s op).credited * doubleScale +
          ((exec comptroller s op).accts.map fun a =>
            a.supply * ((exec comptroller s op).supplyState.index -
              accrualStart a.supplierIndex
                (exec comptroller s op).supplyState.index) +
            a.borrow * ((exec comptroller s op).borrowState.index -
              accrualStart a.borrowerIndex
                (exec comptroller s op).borrowState.index)).sum +
          (((exec comptroller s op).blockNumber -
              (exec comptroller s op).supplyState.block) *
              (exec comptroller s op).supplyState.speed +
            ((exec comptroller s op).blockNumber -
              (exec comptroller s op).borrowState.block) *
              (exec comptroller s op).borrowState.speed) * doubleScale ≤
        (s.credited * doubleScale +
          (s.accts.map fun a =>
            a.supply * (s.supplyState.index -
              accrualStart a.supplierIndex s.supplyState.index) +
            a.borrow * (s.borrowState.index -
              accrualStart a.borrowerIndex s.borrowState.index)).sum +
          ((s.blockNumber - s.supplyState.block) * s.supplyState.speed +
            (s.blockNumber - s.borrowState.block) * s.borrowState.speed) *
            doubleScale) +
          emittedBy sp op * doubleScale ∧
      Consistent (exec comptroller s op) ∧
      (exec comptroller s op).supplyState.speed = (nextSpeeds sp op).1 ∧
      (exec comptroller s op).borrowState.speed = (nextSpeeds sp op).2 := by
  sorry



theorem plan6_accrualStart_le_index (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  split
  · next hr =>
    split
    · next hi => exact hi
    · exact Nat.zero_le _
  · next hr => exact h

theorem plan6_sum_le_of_forall_le (l : List Acct) (f g : Acct → Nat)
    (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hhd : f hd ≤ g hd := h hd (by simp)
    have htl : ∀ a ∈ tl, f a ≤ g a := fun a ha => h a (by simp [ha])
    have ihtl := ih htl
    omega

theorem plan6_hacc_test (a : Acct) (idx : Nat) (h0 : a.supplierIndex = 0) (hinit : compInitialIndex ≤ idx) :
    accrualStart a.supplierIndex idx = compInitialIndex := by
  unfold accrualStart
  simp [h0, hinit]







theorem plan7_upgrade_borrow_diff_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    (upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by
  unfold Legacy.WellFormed at hL
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hall⟩ := hL
  have hrec : a.borrowerIndex ≤ L.borrowIndex := (hall a ha).2
  have hup : (upgrade L).borrowState.index =
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := by
    show (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).index = _
    unfold initSide
    by_cases h : L.borrowIndex = 0 <;> simp [h]
  rw [hup]
  by_cases hrec0 : a.borrowerIndex = 0
  · have hleg : legacyStart L.borrowStart 0 = L.borrowStart := by unfold legacyStart; simp
    have hacc : ∀ idx : Nat, accrualStart 0 idx = (if compInitialIndex ≤ idx then compInitialIndex else 0) := by
      intro idx; unfold accrualStart; simp
    rw [hrec0, hleg, hacc]
    by_cases horig : L.borrowIndex = 0
    · rw [horig]
      simp only [if_true]
      have hstart0 : L.borrowStart = 0 := Nat.le_zero.mp (horig ▸ hble)
      rw [hstart0]
      have hacc2 : (if compInitialIndex ≤ compInitialIndex then compInitialIndex else (0 : Nat)) = compInitialIndex := if_pos (Nat.le_refl _)
      rw [hacc2, Nat.sub_self]
      exact Nat.zero_le _
    · rw [if_neg horig]
      by_cases hinit : compInitialIndex ≤ L.borrowIndex
      · rw [if_pos hinit]
        rcases hb0 with h | h
        · rw [h]
          exact Nat.sub_le_sub_left (Nat.zero_le compInitialIndex) _
        · rw [h]; exact Nat.le_refl _
      · rw [if_neg hinit]
        have hstart0 : L.borrowStart = 0 := by
          rcases hb0 with h | h
          · exact h
          · exfalso; rw [h] at hble; exact hinit hble
        rw [hstart0]; exact Nat.le_refl _
  · have hacc : accrualStart a.borrowerIndex (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) = a.borrowerIndex := by
      unfold accrualStart
      simp [hrec0]
    have hleg : legacyStart L.borrowStart a.borrowerIndex = a.borrowerIndex := by
      unfold legacyStart
      simp [hrec0]
    rw [hacc, hleg]
    by_cases horig : L.borrowIndex = 0
    · rw [if_pos horig]
      omega
    · rw [if_neg horig]; exact Nat.le_refl _




theorem plan7_initSide_index (now : Nat) (sd : Side) :
    (initSide now sd).index =
      if sd.index = 0 then compInitialIndex else sd.index := by
  unfold initSide
  by_cases h : sd.index = 0 <;> simp [h]

theorem plan7_diff_le_of_start_aux_check : True := trivial

theorem plan7_diff_le_of_start (start recorded orig up : Nat)
    (hup : up = if orig = 0 then compInitialIndex else orig)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ orig)
    (hrec_le : recorded ≤ orig) :
    up - accrualStart recorded up ≤
      orig - legacyStart start recorded := by
  by_cases hrec : recorded = 0
  · subst hrec
    have hleg : legacyStart start 0 = start := by
      unfold legacyStart
      rw [if_pos rfl]
    by_cases horig : orig = 0
    · subst horig
      have hup2 : up = compInitialIndex := hup.trans (if_pos rfl)
      have hstart0 : start = 0 := Nat.le_zero.mp hstart_le
      rw [hleg, hstart0, hup2]
      have hacc : accrualStart 0 compInitialIndex = compInitialIndex := by
        unfold accrualStart
        rw [if_pos rfl, if_pos (Nat.le_refl _)]
      rw [hacc]
      simp
    · have hup2 : up = orig := hup.trans (if_neg horig)
      rw [hleg, hup2]
      have hacc : accrualStart 0 orig =
          (if compInitialIndex ≤ orig then compInitialIndex else 0) := by
        unfold accrualStart
        rw [if_pos rfl]
      rw [hacc]
      by_cases hinit : compInitialIndex ≤ orig
      · rw [if_pos hinit]
        rcases hstart with h | h
        · rw [h]
          exact Nat.sub_le_sub_left (Nat.zero_le compInitialIndex) orig
        · rw [h]
          exact Nat.le_refl _
      · rw [if_neg hinit]
        have hstart0 : start = 0 := by
          rcases hstart with h | h
          · exact h
          · exfalso
            rw [h] at hstart_le
            exact hinit hstart_le
        rw [hstart0]
        exact Nat.le_refl _
  · have hacc : accrualStart recorded up = recorded := by
      unfold accrualStart
      rw [if_neg hrec]
    have hleg : legacyStart start recorded = recorded := by
      unfold legacyStart
      rw [if_neg hrec]
    rw [hacc, hleg]
    have horig : orig ≠ 0 := by omega
    have hup2 : up = orig := hup.trans (if_neg horig)
    rw [hup2]
    exact Nat.le_refl _

theorem plan7_upgrade_supply_diff_le_aux (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    (upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index ≤
      L.supplyIndex - legacyStart L.supplyStart a.supplierIndex := by
  have hW := hL
  unfold Legacy.WellFormed at hW
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hall⟩ := hW
  have hrec := (hall a ha).1
  have hup : (upgrade L).supplyState.index =
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
    have hidx := plan7_initSide_index L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩
    have hup_eq : (upgrade L).supplyState = initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ := rfl
    rw [hup_eq, hidx]
  exact plan7_diff_le_of_start L.supplyStart a.supplierIndex L.supplyIndex (upgrade L).supplyState.index hup hs0 hsle hrec

theorem plan7_supply_self5 (L : Legacy) (a : Acct) (hL : L.WellFormed) (ha : a ∈ L.accts) :
    (upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index ≤
      L.supplyIndex - legacyStart L.supplyStart a.supplierIndex := by
  unfold Legacy.WellFormed at hL
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hall⟩ := hL
  have hrec : a.supplierIndex ≤ L.supplyIndex := (hall a ha).1
  have hup : (upgrade L).supplyState.index =
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
    show (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).index = _
    unfold initSide
    by_cases h : L.supplyIndex = 0 <;> simp [h]
  rw [hup]
  by_cases hrec0 : a.supplierIndex = 0
  · have hleg : legacyStart L.supplyStart 0 = L.supplyStart := by unfold legacyStart; simp
    have hacc : ∀ idx : Nat, accrualStart 0 idx = (if compInitialIndex ≤ idx then compInitialIndex else 0) := by
      intro idx; unfold accrualStart; simp
    rw [hrec0, hleg, hacc]
    by_cases horig : L.supplyIndex = 0
    · rw [horig]
      simp only [if_true]
      have hstart0 : L.supplyStart = 0 := Nat.le_zero.mp (horig ▸ hsle)
      rw [hstart0]
      have hacc2 : (if compInitialIndex ≤ compInitialIndex then compInitialIndex else (0 : Nat)) = compInitialIndex := if_pos (Nat.le_refl _)
      rw [hacc2, Nat.sub_self]
      exact Nat.zero_le _
    · rw [if_neg horig]
      by_cases hinit : compInitialIndex ≤ L.supplyIndex
      · rw [if_pos hinit]
        rcases hs0 with h | h
        · rw [h]
          exact Nat.sub_le_sub_left (Nat.zero_le compInitialIndex) _
        · rw [h]; exact Nat.le_refl _
      · rw [if_neg hinit]
        have hstart0 : L.supplyStart = 0 := by
          rcases hs0 with h | h
          · exact h
          · exfalso; rw [h] at hsle; exact hinit hsle
        rw [hstart0]; exact Nat.le_refl _
  · have hacc : accrualStart a.supplierIndex (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) = a.supplierIndex := by
      unfold accrualStart
      simp [hrec0]
    have hleg : legacyStart L.supplyStart a.supplierIndex = a.supplierIndex := by
      unfold legacyStart
      simp [hrec0]
    rw [hacc, hleg]
    by_cases horig : L.supplyIndex = 0
    · rw [if_pos horig]
      omega
    · rw [if_neg horig]; exact Nat.le_refl _

theorem plan7_upgrade_supply_diff_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    (upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index ≤
      L.supplyIndex - legacyStart L.supplyStart a.supplierIndex :=
  plan7_supply_self5 L a hL ha

theorem plan7_upgrade_borrow_diff_le_probe (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    (upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by
  unfold Legacy.WellFormed at hL
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, hall⟩ := hL
  have hrec : a.borrowerIndex ≤ L.borrowIndex := (hall a ha).2
  have hup : (upgrade L).borrowState.index =
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := by
    show (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).index = _
    unfold initSide
    by_cases h : L.borrowIndex = 0 <;> simp [h]
  rw [hup]
  by_cases hrec0 : a.borrowerIndex = 0
  · have hleg : legacyStart L.borrowStart 0 = L.borrowStart := by unfold legacyStart; simp
    have hacc : ∀ idx : Nat, accrualStart 0 idx = (if compInitialIndex ≤ idx then compInitialIndex else 0) := by
      intro idx; unfold accrualStart; simp
    rw [hrec0, hleg, hacc]
    by_cases horig : L.borrowIndex = 0
    · rw [horig]
      simp only [if_true]
      have hstart0 : L.borrowStart = 0 := Nat.le_zero.mp (horig ▸ hble)
      rw [hstart0]
      have hacc2 : (if compInitialIndex ≤ compInitialIndex then compInitialIndex else (0 : Nat)) = compInitialIndex := if_pos (Nat.le_refl _)
      rw [hacc2, Nat.sub_self]
      exact Nat.zero_le _
    · rw [if_neg horig]
      by_cases hinit : compInitialIndex ≤ L.borrowIndex
      · rw [if_pos hinit]
        rcases hb0 with h | h
        · rw [h]
          exact Nat.sub_le_sub_left (Nat.zero_le compInitialIndex) _
        · rw [h]; exact Nat.le_refl _
      · rw [if_neg hinit]
        have hstart0 : L.borrowStart = 0 := by
          rcases hb0 with h | h
          · exact h
          · exfalso; rw [h] at hble; exact hinit hble
        rw [hstart0]; exact Nat.le_refl _
  · have hacc : accrualStart a.borrowerIndex (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) = a.borrowerIndex := by
      unfold accrualStart
      simp [hrec0]
    have hleg : legacyStart L.borrowStart a.borrowerIndex = a.borrowerIndex := by
      unfold legacyStart
      simp [hrec0]
    rw [hacc, hleg]
    by_cases horig : L.borrowIndex = 0
    · rw [if_pos horig]
      omega
    · rw [if_neg horig]; exact Nat.le_refl _

theorem plan7_add_mul_le (x y xd yd xo yo : Nat)
    (hx : xd ≤ xo) (hy : yd ≤ yo) :
    x * xd + y * yd ≤ x * xo + y * yo := by
  have h1 : x * xd ≤ x * xo := Nat.mul_le_mul (Nat.le_refl x) hx
  have h2 : y * yd ≤ y * yo := Nat.mul_le_mul (Nat.le_refl y) hy
  exact Nat.add_le_add h1 h2

theorem plan6_upgrade_pending_le_aux_test (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      L.pendingScaled a := by
  have hsup := plan7_upgrade_supply_diff_le L a hL ha
  have hbor := plan7_upgrade_borrow_diff_le_probe L a hL ha
  unfold Legacy.pendingScaled
  exact plan7_add_mul_le _ _ _ _ _ _ hsup hbor

theorem plan6_hupS_check2 (L : Legacy) :
    (upgrade L).supplyState.index =
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
  by_cases h : L.supplyIndex = 0 <;> simp [upgrade, initSide, h]

theorem plan6_dspos_aux : 0 < doubleScale := by
  unfold doubleScale
  simp

theorem plan6_div_aux2 (S sc : Nat) (hpos : 0 < sc) :
    S ≤ S / sc * sc + (sc - 1) := by
  have hmod : S % sc < sc := Nat.mod_lt S hpos
  have hdiv : sc * (S / sc) + S % sc = S := Nat.div_add_mod S sc
  have hcomm : sc * (S / sc) = S / sc * sc := Nat.mul_comm _ _
  omega

theorem plan6_up_sup_spd2 (L : Legacy) : (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem plan6_up_bor_spd2 (L : Legacy) : (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem plan6_pending_sum_le (L : Legacy) (hL : L.WellFormed) :
    (((upgrade L).accts.map fun a =>
      a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum ≤
    (L.accts.map L.pendingScaled).sum) := by
  have haccts : (upgrade L).accts = L.accts := rfl
  rw [haccts]
  apply plan6_sum_le_of_forall_le
  intro a ha
  exact plan6_upgrade_pending_le_aux_test L a hL ha

theorem plan6_add_mul_dist (x y sc : Nat) : (x + y) * sc = x * sc + y * sc := Nat.add_mul x y sc

theorem plan6_generic_bound2 (C P U Pleg US UB sc : Nat)
    (hpos : 0 < sc)
    (hP : P ≤ Pleg)
    (hU : U ≤ US + UB) :
    C * sc + P + U * sc ≤ (C + (Pleg / sc + US + UB)) * sc + (sc - 1) := by
  have hdiv : Pleg ≤ Pleg / sc * sc + (sc - 1) := plan6_div_aux2 Pleg sc hpos
  have hUsc : U * sc ≤ (US + UB) * sc := Nat.mul_le_mul_right sc hU
  have hexpand : (C + (Pleg / sc + US + UB)) * sc
      = C * sc + (Pleg / sc * sc + (US + UB) * sc) := by
    have e1 : (C + (Pleg / sc + US + UB)) * sc = C * sc + (Pleg / sc + US + UB) * sc :=
      Nat.add_mul C (Pleg / sc + US + UB) sc
    have e2 : (Pleg / sc + US + UB) * sc = (Pleg / sc + (US + UB)) * sc := by
      have : Pleg / sc + US + UB = Pleg / sc + (US + UB) := Nat.add_assoc _ _ _
      rw [this]
    have e3 : (Pleg / sc + (US + UB)) * sc = Pleg / sc * sc + (US + UB) * sc :=
      Nat.add_mul _ _ _
    rw [e1, e2, e3]
  omega

theorem plan6_up_sup_blk2 (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem plan6_up_bor_blk2 (L : Legacy) :
    (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem plan6_up_bor_idx2 (L : Legacy) :
    (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem plan6_up_blk2 (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := rfl

theorem plan6_up_accts2 (L : Legacy) : (upgrade L).accts = L.accts := rfl









theorem plan8_upgrade_pending_le_acc_aux_unique123 : True := trivial

theorem plan8_upgrade_pending_le_acc (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      L.pendingScaled a := by
  have hsup := plan7_upgrade_supply_diff_le L a hL ha
  have hbor := plan7_upgrade_borrow_diff_le_probe L a hL ha
  unfold Legacy.pendingScaled
  exact plan7_add_mul_le _ _ _ _ _ _ hsup hbor

theorem plan8_pending_sum_le (L : Legacy) (hL : L.WellFormed) :
    ((upgrade L).accts.map fun a =>
      a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum ≤
      (L.accts.map L.pendingScaled).sum := by
  have haccts : (upgrade L).accts = L.accts := rfl
  rw [haccts]
  apply plan6_sum_le_of_forall_le
  intro a ha
  exact plan8_upgrade_pending_le_acc L a hL ha

def fooTest123 : Nat := 1

def testSt123 : St := { blockNumber := 100, supplyState := { index := 0, block := 0, speed := 0 }, borrowState := { index := 0, block := 0, speed := 0 }, reserve := 100000000000000000000000, accts := [{ supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def testClaim123 : Option St := comptroller testSt123 (.claim 0)

def upTest123 : St := upgrade { blockNumber := 10, compSpeed := 0, supplyIndex := 0, supplyBlock := 10, borrowIndex := 0, borrowBlock := 10, supplyStart := 0, borrowStart := 0, reserve := 1000000000000000000000000000000, accts := [{ supply := 0, borrow := 18977306140567618322762, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def afterAdv123 : St := { upTest123 with blockNumber := upTest123.blockNumber + 139 }

def claimRes123 : Option St := comptroller afterAdv123 (.claim 0)
#check upTest123
#check claimRes123

def checkClaimVal123 : Nat := match claimRes123 with | some s => (s.acct 0).accrued + (s.acct 0).wallet | none => 999999

theorem checkClaimVal123_is_zero : checkClaimVal123 = 0 := by rfl

def dummyOk123 : Nat := 0

def probeA123 : Bool := true
#check @List.getD
#check @List.modify
#check Consistent
#check St.acct
#check subChecked

def probeB123 : Nat := 1

theorem myHelper123 : 1 + 1 = 2 := rfl

theorem myTestHelperAux : True := trivial

theorem updSupplyEqAux2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (subChecked s.blockNumber s.supplyState.block) = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [h]

theorem borrow_update_eq_aux2 (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem borrow_delta_unfold (s : St) :
    (subChecked s.blockNumber s.borrowState.block) =
    if s.borrowState.block ≤ s.blockNumber then some (s.blockNumber - s.borrowState.block) else none := by
  unfold subChecked; rfl

theorem aux_updateSupply_eq (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem aux_probe_simp (s : St) : totalSupply s = (s.accts.map Acct.supply).sum := by
  simp only [totalSupply]

theorem simpTest (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧ True := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp [hb] at h
    exact ⟨hb, trivial⟩
  · simp [hb] at h

theorem pot_test_aux : doubleScale = 10 ^ 36 := rfl
#check ProofForgeFin.DeFi.Rewards.credit
#check ProofForgeFin.DeFi.Rewards.firstStart
#check ProofForgeFin.DeFi.Rewards.pending
#check @ProofForgeFin.DeFi.Distributor.State
#check ProofForgeFin.DeFi.Rewards.credit_anti_start

def pendingSupply (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)

def pendingBorrow (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)

def unindexedSupply (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def unindexedBorrow (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def potTo (s : St) (who : Account) : Nat :=
  (s.creditedTo who) * doubleScale + pendingSupply s who + pendingBorrow s who +
  (if 0 < (s.acct who).supply then unindexedSupply s * doubleScale else 0) +
  (if 0 < (s.acct who).borrow then unindexedBorrow s * doubleScale else 0)

theorem potTo_ge_credited (s : St) (who : Account) :
  (s.creditedTo who) * doubleScale ≤ potTo s who := by
  unfold potTo pendingSupply pendingBorrow
  omega

def checkListLemmasAux999 : Nat := 0
#check @List.getD
#check @List.modify
#check @List.length_modify
#check @List.getElem_mem
#check @Option.isSome

theorem updSupply_some_aux2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  unfold updateCompSupplyIndex subChecked
  simp only [h, ↓reduceIte]
  by_cases hd : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hd, and_self, ↓reduceIte]
    rfl
  · simp only [hd, ↓reduceIte]
    by_cases hd2 : 0 < s.blockNumber - s.supplyState.block
    · simp [hd2]
    · simp [hd2]

theorem updBorrow_some_aux2 (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  unfold updateCompBorrowIndex subChecked
  simp only [h, ↓reduceIte]
  by_cases hd : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hd, and_self, ↓reduceIte]
    rfl
  · simp only [hd, ↓reduceIte]
    by_cases hd2 : 0 < s.blockNumber - s.borrowState.block
    · simp [hd2]
    · simp [hd2]

theorem getD_default_of_le : ∀ (l : List Acct) (n : Nat), l.length ≤ n → l.getD n noAcct = noAcct := by
  intro l
  induction l with
  | nil => intro n h; simp [List.getD]
  | cons hd tl ih =>
    intro n h
    cases n with
    | zero => simp at h
    | succ n => simp [List.getD]; exact ih n (by simp at h ⊢; omega)

theorem plan0_consistent_acct_bounds_aux_mem : ∀ (l : List Acct) (n : Nat), n < l.length → l.getD n noAcct ∈ l := by
  intro l
  induction l with
  | nil => intro n h; simp at h
  | cons hd tl ih =>
    intro n h
    cases n with
    | zero => simp [List.getD]
    | succ n => simp [List.getD]; exact Or.inr (ih n (by simp at h ⊢; omega))

theorem plan0_consistent_acct_bounds (s : St) (who : Account) (h : Consistent s) :
    ((s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index) ∧
      ((s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index) := by
  unfold Consistent at h
  obtain ⟨_, _, hall⟩ := h
  by_cases hwho : who < s.accts.length
  · have hmem : s.acct who ∈ s.accts := by
      unfold St.acct
      exact plan0_consistent_acct_bounds_aux_mem s.accts who hwho
    have hb := hall (s.acct who) hmem
    exact ⟨Or.inr hb.1, Or.inr hb.2⟩
  · have hle : s.accts.length ≤ who := Nat.le_of_not_gt hwho
    have hget : s.accts.getD who noAcct = noAcct := getD_default_of_le s.accts who hle
    have hacct : s.acct who = noAcct := by unfold St.acct; exact hget
    rw [hacct]
    exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem plan0_updateSupply_exists (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' ∧
      s.supplyState.index ≤ s'.supplyState.index ∧
      s'.accts = s.accts ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompSupplyIndex
  rw [hsub]
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc, ↓reduceIte]
    exact ⟨_, rfl, Nat.le_add_right _ _, rfl, rfl, rfl⟩
  · simp only [hc, ↓reduceIte]
    by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩

theorem plan0_updateBorrow_exists (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' ∧
      s.borrowState.index ≤ s'.borrowState.index ∧
      s'.accts = s.accts ∧ s'.supplyState = s.supplyState ∧
      s'.blockNumber = s.blockNumber := by
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompBorrowIndex
  rw [hsub]
  by_cases hc : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hc, ↓reduceIte]
    exact ⟨_, rfl, Nat.le_add_right _ _, rfl, rfl, rfl⟩
  · simp only [hc, ↓reduceIte]
    by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩
    · simp only [hd, ↓reduceIte]
      exact ⟨_, rfl, Nat.le_refl _, rfl, rfl, rfl⟩

theorem plan0_distributeSupplier_exists (s : St) (who : Account)
    (h : (s.acct who).supplierIndex = 0 ∨
      (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' ∧
      s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  have hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
    by_cases hc : ((s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index)
    · simp only [hc, ↓reduceIte]
      exact hc.2
    · simp only [hc]
      rcases h with h0 | hle2
      · rw [h0]; exact Nat.zero_le _
      · exact hle2
  have hsub : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = some (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) := by
    unfold subChecked
    simp only [hle, ↓reduceIte]
  unfold distributeSupplierComp
  simp only at hsub ⊢
  rw [hsub]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem tmpProbeThm : True := trivial

theorem tmpExploreModify : List.modify [1,2] 0 (· + 1) = [2,2] := by rfl

theorem tmpProbeThm3 : True := trivial

theorem tmpProbeThm4 : True := trivial

theorem tmpP5 : True := trivial

theorem plan1_subChecked_of_le (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by unfold subChecked; simp [h]

theorem plan1_borrower_adjusted_le2 (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
  by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · rw [if_pos hc]
    exact hc.2
  · rw [if_neg hc]
    rcases h with h0 | hle
    · rw [h0]
      exact Nat.zero_le _
    · exact hle

theorem plan1_borrower_adjusted_le_aux_tmp : True := trivial

theorem plan1_modify_getD_supplierIndex (l : List Acct) (n : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD n noAcct).supplierIndex = (l.getD n noAcct).supplierIndex := by
  have h := ProofForgeFin.Ledger.getD_modify l n n f noAcct
  by_cases hn : n < l.length
  · have h2 : (l.modify n f).getD n noAcct = f (l.getD n noAcct) := by
      rw [h]
      simp [hn]
    rw [h2, hf]
  · have h2 : (l.modify n f).getD n noAcct = l.getD n noAcct := by
      rw [h]
      simp [hn]
    rw [h2]

theorem plan1_withAcct_supplierIndex (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.withAcct St.acct
  simp only
  exact plan1_modify_getD_supplierIndex s.accts who f hf

theorem plan1_distributeBorrower_supplierIndex (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by
  have hunfold : distributeBorrowerComp s who =
    match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
    | none => (none : Option St)
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex }) := rfl
  rw [hunfold] at h
  cases heq : subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
  | none => simp [heq] at h
  | some d =>
    simp [heq] at h
    rw [← h]
    apply plan1_withAcct_supplierIndex
    intro a
    rfl

theorem plan0_distributeBorrower_exists_PROBE (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' ∧
      (s'.acct who).supplierIndex = (s.acct who).supplierIndex ∧
      s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  have hle : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index :=
    plan1_borrower_adjusted_le2 s who h
  have hsub : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = some (s.borrowState.index - (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)) :=
    plan1_subChecked_of_le _ _ hle
  unfold distributeBorrowerComp
  simp only [hsub]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
  apply plan1_withAcct_supplierIndex
  intro a
  rfl

theorem borrowerPreserveClean (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts who who f noAcct
  have h1 : ((s.withAcct who f).acct who) = ((s.accts.modify who f).getD who noAcct) := rfl
  have h2 : (s.acct who) = (s.accts.getD who noAcct) := rfl
  rw [h1, h2]
  rw [hmod]
  by_cases hn : who < s.accts.length
  · simp [hn, hf]
  · simp [hn]

theorem testPreserveGeneric (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.withAcct St.acct
  simp only
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts who who f noAcct
  rw [hmod]
  by_cases hn : who < s.accts.length
  · simp [hn, hf]
  · simp [hn]

theorem probe_ledger_lemmas : True := trivial
#check ProofForgeFin.Ledger.getD_modify
#check ProofForgeFin.DeFi.Distributor.State

theorem supplyBound_transfer_aux (s s1 : St) (who : Account)
    (haccts : s1.accts = s.accts) (hle : s.supplyState.index ≤ s1.supplyState.index)
    (h : (s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (s1.acct who).supplierIndex = 0 ∨ (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
  have heq : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
  rw [heq]
  rcases h with h0 | hle2
  · exact Or.inl h0
  · exact Or.inr (Nat.le_trans hle2 hle)

theorem borrowBound_transfer_aux (s s1 : St) (who : Account)
    (haccts : s1.accts = s.accts) (hle : s.borrowState.index ≤ s1.borrowState.index)
    (h : (s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (s1.acct who).borrowerIndex = 0 ∨ (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
  have heq : s1.acct who = s.acct who := by unfold St.acct; rw [haccts]
  rw [heq]
  rcases h with h0 | hle2
  · exact Or.inl h0
  · exact Or.inr (Nat.le_trans hle2 hle)

theorem updSupply_isSome_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := updSupply_some_aux2 s h

theorem updBorrow_isSome_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := updBorrow_some_aux2 s h

theorem distSup_isSome_of_bound (s : St) (who : Account)
    (h : (s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome = true := by
  obtain ⟨s', hs', _, _, _⟩ := plan0_distributeSupplier_exists s who h
  rw [hs']
  rfl

theorem distBor_isSome_of_bound (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome = true := by
  obtain ⟨s', hs', _, _, _, _⟩ := plan0_distributeBorrower_exists_PROBE s who h
  rw [hs']
  rfl

theorem updSupply_char_aux (s : St) (mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem updSupply_inv (s : St) (mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid h
  unfold updateCompSupplyIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem supplyHook_decomp_ok (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ mid, updateCompSupplyIndex s = some mid ∧ distributeSupplierComp mid who = some s' := by
  unfold comptroller at h
  cases hup : updateCompSupplyIndex s with
  | none =>
    simp [hup] at h
  | some mid =>
    simp [hup] at h
    exact ⟨mid, rfl, h⟩

theorem plan2_accrualStart_adjusted (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp only [hr, true_and]
    by_cases hi : compInitialIndex ≤ index <;> simp [hi]
  · simp [hr]

theorem plan2_updateSupply_accrueSide (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid h
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompSupplyIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide at ⊢
  by_cases hdb : 0 < s.blockNumber - s.supplyState.block
  · by_cases hsp : 0 < s.supplyState.speed
    · by_cases htot : 0 < totalSupply s
      · simp only [hdb, hsp, htot, and_self, ↓reduceIte] at ⊢
        have hrw : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        unfold fraction at h
        cases h
        rfl
      · have hrw : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        have hfalse : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
          simp [htot]
        simp only [hfalse, ↓reduceIte] at ⊢
        cases h
        rfl
    · have hrw : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by
        simp [hsp]
      simp only [hrw, ↓reduceIte] at h
      have hfalse : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        simp [hsp]
      simp only [hfalse, ↓reduceIte] at ⊢
      simp only [hdb, ↓reduceIte] at h ⊢
      cases h
      rfl
  · have hrw : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := by
      simp [hdb]
    simp only [hrw, ↓reduceIte] at h
    have hfalse : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
      simp [hdb]
    simp only [hfalse, ↓reduceIte] at ⊢
    simp only [hdb, ↓reduceIte] at h ⊢
    cases h
    have heq : s.blockNumber = s.supplyState.block := by omega
    cases s with
    | mk bn sup bor res accts =>
      simp only at heq ⊢
      cases sup with
      | mk idx blk spd =>
        simp only at heq ⊢
        subst heq
        rfl

theorem snippet_probe_modify_eq : True := trivial
#check @List.modify
#check @List.getD

theorem snippet_modify_congr_test (l : List Acct) (n : Nat) (f1 f2 : Acct → Acct)
    (h : f1 (l.getD n noAcct) = f2 (l.getD n noAcct)) :
    l.modify n f1 = l.modify n f2 := by
  induction l generalizing n with
  | nil =>
    cases n with
    | zero => simp
    | succ n => simp
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp [List.getD] at h
      simp [h]
    | succ n =>
      simp [List.getD] at h
      simp [ih n h]

theorem plan2_distributeSupplier_char_aux_tmp2 : True := trivial
#check @snippet_modify_congr_test
#check distributeSupplierComp
#check subChecked
#check mulDouble
#check creditFor
#check accrualStart

theorem plan3_subChecked_some_inv_fix : ∀ (a b d : Nat), subChecked a b = some d → b ≤ a ∧ d = a - b := by
  intro a b d h
  unfold subChecked at h
  by_cases hb : b ≤ a
  · simp only [hb, ↓reduceIte] at h
    cases h
    exact ⟨hb, rfl⟩
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem plan3_subChecked_some_inv (a b d : Nat) (h : subChecked a b = some d) :
    b ≤ a ∧ d = a - b := by
  unfold subChecked at h
  by_cases hb : b ≤ a
  · simp only [hb, ↓reduceIte] at h
    cases h
    exact ⟨hb, rfl⟩
  · simp only [hb, ↓reduceIte, reduceCtorEq] at h

theorem plan3_supplier_adjusted_eq_accrualStart_check (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hr : recorded = 0 <;> simp [hr]

theorem plan3_supplier_adjusted_eq_accrualStart (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hr : recorded = 0 <;> simp [hr]

theorem plan3_mulDouble_eq_creditFor (units start index : Nat) :
    mulDouble units (index - start) = creditFor units start index := by
  unfold mulDouble creditFor
  rfl

theorem beta_probe1 (l : List Acct) (n idx : Nat) :
    (fun a : Acct => ({ a with supplierIndex := idx } : Acct)) (l.getD n noAcct) =
    ({ (l.getD n noAcct) with supplierIndex := idx } : Acct) := by rfl

theorem plan3_withAcct_eq_modify (s : St) (who : Account) (f : Acct → Acct) :
    s.withAcct who f = { s with accts := s.accts.modify who f } := by rfl

theorem plan2_distributeSupplier_char_test_tmp : True := trivial

theorem probe_congr_goal2 (mid : St) (who : Account) (d : Nat)
    (hmul : mulDouble (mid.acct who).supply d =
          creditFor (mid.acct who).supply (accrualStart (mid.acct who).supplierIndex mid.supplyState.index) mid.supplyState.index) :
    (fun a : Acct => ({ a with supplierIndex := mid.supplyState.index, accrued := a.accrued + mulDouble (mid.acct who).supply d } : Acct)) (mid.accts.getD who noAcct) =
    (fun a : Acct => ({ a with supplierIndex := mid.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex mid.supplyState.index) mid.supplyState.index } : Acct)) (mid.accts.getD who noAcct) := by
  have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
  simp only [← hacct, hmul]

theorem plan2_dist_char_PROOFTEST4 (mid : St) (who : Account) (s' : St)
    (h : distributeSupplierComp mid who = some s') :
    accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤
        mid.supplyState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            supplierIndex := mid.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex mid.supplyState.index)
              mid.supplyState.index } } := by
  have hadj : (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) =
      accrualStart (mid.acct who).supplierIndex mid.supplyState.index := by
    rw [plan3_supplier_adjusted_eq_accrualStart]
  unfold distributeSupplierComp at h
  simp only at h
  cases hc : subChecked mid.supplyState.index
      (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).supply d =
          creditFor (mid.acct who).supply (accrualStart (mid.acct who).supplierIndex mid.supplyState.index) mid.supplyState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with supplierIndex := mid.supplyState.index, accrued := a.accrued + mulDouble (mid.acct who).supply d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            supplierIndex := mid.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex mid.supplyState.index)
              mid.supplyState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan4_acct_eq_check_tmp : ∀ (s mid : St) (who : Account),
    updateCompSupplyIndex s = some mid → mid.acct who = s.acct who := by
  intro s mid who h
  have haccts : mid.accts = s.accts := updSupply_inv s mid h
  unfold St.acct
  rw [haccts]

theorem plan4_updateSupply_acct_eq (s mid : St) (who : Account)
    (h : updateCompSupplyIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updSupply_inv s mid h
  unfold St.acct
  rw [haccts]

theorem plan4_updateSupply_supplyState_eq (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by
  have hmid := plan2_updateSupply_accrueSide s mid h
  rw [hmid]

theorem plan4_supply_bound_transfer (s mid : St) (who : Account)
    (hacct : mid.acct who = s.acct who)
    (hstate : mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s))
    (hle : accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤
        mid.supplyState.index) :
    accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  rw [hacct, hstate] at hle
  exact hle

theorem tmp_snippet_ok : True := trivial

theorem tmpA1 : True := trivial

theorem plan4_aux_test1 (s mid : St) (hmid : mid = { s with supplyState := s.supplyState }) : mid.accts = s.accts := by rw [hmid]

theorem tmpRwTest (a b : Nat) (h : a = b) : a = b := by rw [h]

theorem tmpShort : 1 = 1 := rfl

theorem tmpLineTest : True := trivial

theorem tmpC1 : True := trivial

theorem tmpC2 : True := trivial

theorem plan4_supply_eq_transfer3 (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          supplierIndex := mid.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex mid.supplyState.index)
            mid.supplyState.index } }) :
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  subst hmid
  exact heq

theorem plan4_supply_eq_transfer (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          supplierIndex := mid.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex mid.supplyState.index)
            mid.supplyState.index } }) :
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  subst hmid
  exact heq

theorem plan2_supplyDistributed_of_steps2 (s : St) (who : Account) (mid s' : St)
    (hup : updateCompSupplyIndex s = some mid)
    (hdist : distributeSupplierComp mid who = some s') :
    SupplyDistributed s who s' := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid hup
  have hmid : mid = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    plan2_updateSupply_accrueSide s mid hup
  have hchar := plan2_dist_char_PROOFTEST4 mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have hacct : mid.acct who = s.acct who := plan4_updateSupply_acct_eq s mid who hup
  have hstate : mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) :=
    plan4_updateSupply_supplyState_eq s mid hup
  have hle : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    plan4_supply_bound_transfer s mid who hacct hstate hle_mid
  have heq : s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } :=
    plan4_supply_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan2_supplyDistributed_of_steps (s : St) (who : Account) (mid s' : St)
    (hup : updateCompSupplyIndex s = some mid)
    (hdist : distributeSupplierComp mid who = some s') :
    SupplyDistributed s who s' :=
  plan2_supplyDistributed_of_steps2 s who mid s' hup hdist

theorem bh_parse_test (mid : St) (who : Account) :
    True := by
  have h : ∀ (s' : St), BorrowDistributed mid who s' → True := fun _ _ => trivial
  trivial

theorem bh_struct_test (mid : St) (who : Account) :
    mid.accts.modify who (fun a => ({ a with borrowerIndex := mid.borrowState.index } : Acct)) =
    mid.accts.modify who (fun a => ({ a with borrowerIndex := mid.borrowState.index } : Acct)) := by
  rfl

theorem plan5_borrower_adjusted_eq_accrualStart (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hr : recorded = 0 <;> simp [hr]

theorem plan5_distributeBorrower_char_PROBE (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    rw [plan5_borrower_adjusted_eq_accrualStart]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan5_distributeBorrower_char_fix (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    rw [plan5_borrower_adjusted_eq_accrualStart]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan5_char_selfcontained (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    unfold accrualStart
    by_cases hr : (mid.acct who).borrowerIndex = 0 <;> simp [hr]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan5_distributeBorrower_char (mid : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp mid who = some s') :
    accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
  have hadj : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) =
      accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := by
    unfold accrualStart
    by_cases hr : (mid.acct who).borrowerIndex = 0 <;> simp [hr]
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked mid.borrowState.index
      (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) with
  | none =>
    simp [hc] at h
  | some d =>
    simp [hc] at h
    obtain ⟨hle, hdelt⟩ := plan3_subChecked_some_inv _ _ d hc
    subst h
    constructor
    · rw [← hadj]; exact hle
    · have hmul : mulDouble (mid.acct who).borrow d =
          creditFor (mid.acct who).borrow (accrualStart (mid.acct who).borrowerIndex mid.borrowState.index) mid.borrowState.index := by
        rw [hadj] at hdelt
        rw [hdelt]
        rw [plan3_mulDouble_eq_creditFor]
      have hwith : mid.withAcct who (fun a => ({ a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow d } : Acct)) =
          { mid with accts := mid.accts.modify who fun a =>
          { a with
            borrowerIndex := mid.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex mid.borrowState.index)
              mid.borrowState.index } } := by
        unfold St.withAcct
        congr 1
        apply snippet_modify_congr_test
        have hacct : mid.acct who = mid.accts.getD who noAcct := rfl
        simp only [← hacct, hmul]
      exact hwith

theorem plan5_updateBorrow_accrueSide_tmpProbe : True := trivial

theorem plan5_updateBorrow_accrueSide_test (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide at ⊢
  by_cases hdb : 0 < s.blockNumber - s.borrowState.block
  · by_cases hsp : 0 < s.borrowState.speed
    · by_cases htot : 0 < totalBorrows s
      · simp only [hdb, hsp, htot, and_self, ↓reduceIte] at ⊢
        have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        unfold fraction at h
        cases h
        rfl
      · have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          simp [htot]
        simp only [hfalse, ↓reduceIte] at ⊢
        cases h
        rfl
    · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
        simp [hsp]
      simp only [hrw, ↓reduceIte] at h
      have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [hsp]
      simp only [hfalse, ↓reduceIte] at ⊢
      simp only [hdb, ↓reduceIte] at h ⊢
      cases h
      rfl
  · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
      simp [hdb]
    simp only [hrw, ↓reduceIte] at h
    have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
      simp [hdb]
    simp only [hfalse, ↓reduceIte] at ⊢
    simp only [hdb, ↓reduceIte] at h ⊢
    cases h
    have heq : s.blockNumber = s.borrowState.block := by omega
    cases s with
    | mk bn sup bor res accts =>
      simp only at heq ⊢
      cases bor with
      | mk idx blk spd =>
        simp only at heq ⊢
        subst heq
        rfl

theorem plan5_updateBorrow_accrueSide_proof2 : True := trivial

theorem plan5_updateBorrow_accrueSide (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide at ⊢
  by_cases hdb : 0 < s.blockNumber - s.borrowState.block
  · by_cases hsp : 0 < s.borrowState.speed
    · by_cases htot : 0 < totalBorrows s
      · simp only [hdb, hsp, htot, and_self, ↓reduceIte] at ⊢
        have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        unfold fraction at h
        cases h
        rfl
      · have hrw : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := ⟨hdb, hsp⟩
        simp only [hrw, htot, ↓reduceIte] at h
        have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          simp [htot]
        simp only [hfalse, ↓reduceIte] at ⊢
        cases h
        rfl
    · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
        simp [hsp]
      simp only [hrw, ↓reduceIte] at h
      have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [hsp]
      simp only [hfalse, ↓reduceIte] at ⊢
      simp only [hdb, ↓reduceIte] at h ⊢
      cases h
      rfl
  · have hrw : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := by
      simp [hdb]
    simp only [hrw, ↓reduceIte] at h
    have hfalse : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
      simp [hdb]
    simp only [hfalse, ↓reduceIte] at ⊢
    simp only [hdb, ↓reduceIte] at h ⊢
    cases h
    have heq : s.blockNumber = s.borrowState.block := by omega
    cases s with
    | mk bn sup bor res accts =>
      simp only at heq ⊢
      cases bor with
      | mk idx blk spd =>
        simp only at heq ⊢
        subst heq
        rfl

theorem plan5_borrow_eq_transfer_fix_tmp (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          borrowerIndex := mid.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex mid.borrowState.index)
            mid.borrowState.index } }) :
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  subst hmid
  exact heq

theorem plan5_borrow_eq_transfer (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          borrowerIndex := mid.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex mid.borrowState.index)
            mid.borrowState.index } }) :
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  subst hmid
  exact heq

theorem updBorrow_inv_test (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan5_updateBorrow_acct_eq_aux (s mid : St) (who : Account)
    (h : updateCompBorrowIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid h
  unfold St.acct
  rw [haccts]

theorem plan5_updateBorrow_state_eq_aux (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
  have hmid := plan5_updateBorrow_accrueSide s mid h
  rw [hmid]

theorem plan5_borrow_bound_transfer_aux (s mid : St) (who : Account)
    (hacct : mid.acct who = s.acct who)
    (hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s))
    (hle : accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤
        mid.borrowState.index) :
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  rw [hacct, hstate] at hle
  exact hle

theorem plan5_borrowDistributed_aux_final (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid hup
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer_fix_tmp s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan5_borrowDistributed_of_steps_aux_check (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid hup
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer_fix_tmp s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem check_aux_present : True := by
  have h := plan5_borrowDistributed_of_steps_aux_check
  trivial

theorem plan5_borrowDistributed_of_steps_direct (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' :=
  plan5_borrowDistributed_of_steps_aux_check s who mid s' hup hdist

theorem plan5_inline_accts_check (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan6_borrow_update_accts_check_tmp (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan6_borrow_update_accts_fixed (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan6_borrow_update_accts2 (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts :=
  plan6_borrow_update_accts_check_tmp s mid h

theorem plan6_borrow_update_accts (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  unfold updateCompBorrowIndex subChecked at h
  simp only [hb, ↓reduceIte] at h
  split at h
  next hc =>
    split at h
    next ht =>
      cases h
      rfl
    next ht =>
      cases h
      rfl
  next hc =>
    split at h
    next hd =>
      cases h
      rfl
    next hd =>
      cases h
      rfl

theorem plan6_borrow_mid_acct_proof : True := trivial
#check @updBorrow_inv_test
#check @plan6_borrow_update_accts_fixed

theorem plan6_borrow_mid_acct_inline (s mid : St) (who : Account)
    (h : updateCompBorrowIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid h
  unfold St.acct
  rw [haccts]

theorem plan6_borrow_mid_acct (s mid : St) (who : Account)
    (h : updateCompBorrowIndex s = some mid) :
    mid.acct who = s.acct who := by
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid h
  unfold St.acct
  rw [haccts]

theorem plan6_borrow_mid_state (s mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
  have hmid := plan5_updateBorrow_accrueSide s mid h
  rw [hmid]

theorem plan6_borrow_start_le (s mid s' : St) (who : Account)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨hle_mid, _⟩ := hchar
  have haccts : mid.accts = s.accts := updBorrow_inv_test s mid hup
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hmid := plan5_updateBorrow_accrueSide s mid hup
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  rw [hacct, hstate] at hle_mid
  exact hle_mid

theorem plan6_borrow_eq_proof_tmp : True := trivial

theorem plan6_borrow_eq_via_subst3 (s mid s' : St) (who : Account)
    (hmid2 : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (heq2 : s' = { mid with accts := mid.accts.modify who fun a => { a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + 1 } }) :
    s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + 1 } } := by
  subst hmid2
  exact heq2

theorem plan6_borrow_eq (s mid s' : St) (who : Account) (hup : updateCompBorrowIndex s = some mid) (hdist : distributeBorrowerComp mid who = some s') : s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_char_selfcontained mid who s' hdist
  obtain ⟨_, heq_mid⟩ := hchar
  have heq2 : s' = { mid with accts := mid.accts.modify who fun a => { a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex mid.borrowState.index) mid.borrowState.index } } := heq_mid
  subst hmid
  exact heq2

theorem plan5_borrowDistributed_of_steps_check_tmp (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' :=
  plan5_borrowDistributed_aux_final s who mid s' hup hdist

theorem plan5_borrowDistributed_of_steps_proof_tmp2 (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' :=
  plan5_borrowDistributed_aux_final s who mid s' hup hdist

theorem plan5_borrowDistributed_of_steps_dup_test (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_distributeBorrower_char mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := by
    unfold updateCompBorrowIndex subChecked at hup
    simp only [hb, ↓reduceIte] at hup
    split at hup
    next hc =>
      split at hup
      next ht => cases hup; rfl
      next ht => cases hup; rfl
    next hc =>
      split at hup
      next hd => cases hup; rfl
      next hd => cases hup; rfl
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan5_borrowDistributed_of_steps_NEWNAME (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_distributeBorrower_char mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := by
    unfold updateCompBorrowIndex subChecked at hup
    simp only [hb, ↓reduceIte] at hup
    split at hup
    next hc =>
      split at hup
      next ht => cases hup; rfl
      next ht => cases hup; rfl
    next hc =>
      split at hup
      next hd => cases hup; rfl
      next hd => cases hup; rfl
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem plan5_borrowDistributed_of_steps_finalcheck (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  exact plan5_borrowDistributed_of_steps_dup_test s who mid s' hup hdist

theorem plan5_borrowDistributed_inline_early (s : St) (who : Account) (mid s' : St)
    (hup : updateCompBorrowIndex s = some mid)
    (hdist : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid hup
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan5_updateBorrow_accrueSide s mid hup
  have hchar := plan5_distributeBorrower_char mid who s' hdist
  obtain ⟨hle_mid, heq_mid⟩ := hchar
  have haccts : mid.accts = s.accts := by
    unfold updateCompBorrowIndex subChecked at hup
    simp only [hb, ↓reduceIte] at hup
    split at hup
    next hc =>
      split at hup
      next ht => cases hup; rfl
      next ht => cases hup; rfl
    next hc =>
      split at hup
      next hd => cases hup; rfl
      next hd => cases hup; rfl
  have hacct : mid.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hstate : mid.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by rw [hmid]
  have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacct, ← hstate]; exact hle_mid
  have heq : s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } :=
    plan5_borrow_eq_transfer s mid s' who hmid heq_mid
  exact ⟨hb, hle, heq⟩

theorem borrow_accts_nosplit (s : St) (mid : St)
    (h : updateCompBorrowIndex s = some mid) :
    mid.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := borrow_update_eq_aux2 s mid h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    plan1_subChecked_of_le _ _ hb
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  by_cases hc : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hc, ↓reduceIte] at h
    by_cases ht : 0 < totalBorrows s
    · simp only [ht, ↓reduceIte] at h
      cases h
      rfl
    · simp only [ht, ↓reduceIte] at h
      cases h
      rfl
  · simp only [hc, ↓reduceIte] at h
    by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · simp only [hd, ↓reduceIte] at h
      cases h
      rfl
    · simp only [hd, ↓reduceIte] at h
      cases h
      rfl

theorem plan5_borrowHook_decomp (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ mid, updateCompBorrowIndex s = some mid ∧ distributeBorrowerComp mid who = some s' := by
  unfold comptroller at h
  cases hup : updateCompBorrowIndex s with
  | none =>
    simp [hup] at h
  | some mid =>
    simp [hup] at h
    exact ⟨mid, rfl, h⟩

theorem req_borrow_hook_PROBE : BorrowHookEffects comptroller := by
  intro s who s' h
  obtain ⟨mid, hup, hdist⟩ := plan5_borrowHook_decomp s who s' h
  exact plan5_borrowDistributed_aux_final s who mid s' hup hdist

theorem grant_shape (s : St) (who : Account) :
    grantCompInternal s who =
    (let amount := (s.accts.getD who noAcct).accrued;
     if amount > 0 ∧ amount ≤ s.reserve then
      { s with reserve := s.reserve - amount,
               accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + amount } }
     else s) := by rfl

theorem grantUnfold_test (s : St) (who : Account) :
    grantCompInternal s who =
    (if (s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve then
      { s with reserve := s.reserve - (s.accts.getD who noAcct).accrued,
               accts := s.accts.modify who fun a => ({ a with accrued := 0, wallet := a.wallet + (s.accts.getD who noAcct).accrued } : Acct) }
     else s) := by
  unfold grantCompInternal St.acct
  rfl

theorem tmp_bind_probe6 (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') : True := by
  have hc2 : Option.bind (updateCompBorrowIndex s) (fun b1 =>
      Option.bind (distributeBorrowerComp b1 who) (fun b2 =>
        Option.bind (updateCompSupplyIndex b2) (fun u2 =>
          Option.bind (distributeSupplierComp u2 who) (fun fin =>
            some (grantCompInternal fin who))))) = some s' := h
  rw [Option.bind_eq_some_iff] at hc2
  obtain ⟨b1, hb1, hrest⟩ := hc2
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨b2, hb2, hrest2⟩ := hrest
  rw [Option.bind_eq_some_iff] at hrest2
  obtain ⟨u2, hu2, hrest3⟩ := hrest2
  rw [Option.bind_eq_some_iff] at hrest3
  obtain ⟨fin, hfin, hlast⟩ := hrest3
  simp only [Option.some.injEq] at hlast
  trivial

theorem plan7_claim_decomp (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    ∃ b1 b2 u2 fin,
      updateCompBorrowIndex s = some b1 ∧
      distributeBorrowerComp b1 who = some b2 ∧
      updateCompSupplyIndex b2 = some u2 ∧
      distributeSupplierComp u2 who = some fin ∧
      s' = grantCompInternal fin who := by
  have hc2 : Option.bind (updateCompBorrowIndex s) (fun b1 =>
      Option.bind (distributeBorrowerComp b1 who) (fun b2 =>
        Option.bind (updateCompSupplyIndex b2) (fun u2 =>
          Option.bind (distributeSupplierComp u2 who) (fun fin =>
            some (grantCompInternal fin who))))) = some s' := h
  rw [Option.bind_eq_some_iff] at hc2
  obtain ⟨b1, hb1, hrest⟩ := hc2
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨b2, hb2, hrest2⟩ := hrest
  rw [Option.bind_eq_some_iff] at hrest2
  obtain ⟨u2, hu2, hrest3⟩ := hrest2
  rw [Option.bind_eq_some_iff] at hrest3
  obtain ⟨fin, hfin, hlast⟩ := hrest3
  simp only [Option.some.injEq] at hlast
  subst hlast
  exact ⟨b1, b2, u2, fin, hb1, hb2, hu2, hfin, rfl⟩

theorem plan7_probe_gt (n m : Nat) : (n > m) = (m < n) := rfl

theorem plan7_probe_cond (s : St) (who : Account) :
    (((s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve) =
     (0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve)) := rfl

theorem plan8_modify_grant_wallet_eq_new (s : St) (who : Account) :
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) =
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply snippet_modify_congr_test
  rfl

theorem plan8_modify_grant_wallet_eq (s : St) (who : Account) :
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) =
    s.accts.modify who
        (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply snippet_modify_congr_test
  rfl

theorem plan8_grant_branch_eq_try (s : St) (who : Account) :
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } } =
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  rw [plan8_modify_grant_wallet_eq]

theorem plan8_grant_branch_eq (s : St) (who : Account) :
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } } =
    { s with
      reserve := s.reserve - (s.acct who).accrued,
      accts := s.accts.modify who
        fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  rw [plan8_modify_grant_wallet_eq]

theorem plan8_grantCompInternal_eq_if (s : St) (who : Account) :
    grantCompInternal s who =
      if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
        { s with
          reserve := s.reserve - (s.acct who).accrued,
          accts := s.accts.modify who
            fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } }
      else s := by
  unfold grantCompInternal
  rfl

theorem plan8_grant_eq_if (s : St) (who : Account) :
    grant s who =
      if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
        { s with
          reserve := s.reserve - (s.acct who).accrued,
          accts := s.accts.modify who
            fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
      else s := by
  rfl

theorem plan7_claim_steps_distributed
    (s b1 b2 u2 fin : St) (who : Account)
    (hbUp : updateCompBorrowIndex s = some b1)
    (hbDist : distributeBorrowerComp b1 who = some b2)
    (hsUp : updateCompSupplyIndex b2 = some u2)
    (hsDist : distributeSupplierComp u2 who = some fin) :
    BorrowDistributed s who b2 ∧ SupplyDistributed b2 who fin := by
  exact ⟨plan5_borrowDistributed_aux_final s who b1 b2 hbUp hbDist,
    plan2_supplyDistributed_of_steps b2 who u2 fin hsUp hsDist⟩

theorem plan7_claim_of_raw_steps
    (s b1 b2 u2 fin s' : St) (who : Account)
    (hbUp : updateCompBorrowIndex s = some b1)
    (hbDist : distributeBorrowerComp b1 who = some b2)
    (hsUp : updateCompSupplyIndex b2 = some u2)
    (hsDist : distributeSupplierComp u2 who = some fin)
    (hfin : s' = grantCompInternal fin who) :
    Claimed s who s' := by
  have hB : BorrowDistributed s who b2 :=
    plan5_borrowDistributed_aux_final s who b1 b2 hbUp hbDist
  have hS : SupplyDistributed b2 who fin :=
    plan2_supplyDistributed_of_steps b2 who u2 fin hsUp hsDist
  have hgr : grantCompInternal fin who = grant fin who := by
    rw [plan8_grantCompInternal_eq_if, plan8_grant_eq_if, plan8_grant_branch_eq]
  exact ⟨b2, fin, hB, hS, by rw [hfin, hgr]⟩

theorem updSupply_preserve_borrow (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid.borrowState = s.borrowState := by
  have hb : s.supplyState.block ≤ s.blockNumber := updSupply_char_aux s mid h
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := plan1_subChecked_of_le _ _ hb
  unfold updateCompSupplyIndex at h
  rw [hsub] at h
  simp only at h
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc, ↓reduceIte] at h
    by_cases ht : 0 < totalSupply s
    · simp only [ht, ↓reduceIte] at h
      cases h; rfl
    · simp only [ht, ↓reduceIte] at h
      cases h; rfl
  · simp only [hc, ↓reduceIte] at h
    by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · simp only [hd, ↓reduceIte] at h
      cases h; rfl
    · simp only [hd, ↓reduceIte] at h
      cases h; rfl

theorem plan3_borrowHook_distributed_pf (s : St) (who : Account) (m1 : St)
    (h : comptroller s (.borrowHook who) = some m1) :
    BorrowDistributed s who m1 := by
  have h3 := borHook_eq2 s who m1 h
  obtain ⟨hb, hle, heq⟩ := h3
  exact ⟨hb, hle, heq⟩

def td0_Inv (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

def td0_pendingScaled (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def td0_unindexedBorrow (s : St) : Nat :=
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def td0_unindexedSupply (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def td0_owedTo (s : St) (who : Account) : Nat :=
  td0_pendingScaled s (s.acct who) / doubleScale +
    (if 0 < (s.acct who).supply then td0_unindexedSupply s else 0) +
    (if 0 < (s.acct who).borrow then td0_unindexedBorrow s else 0)

def td0_owed (s : St) : Nat :=
  (s.accts.map (td0_pendingScaled s)).sum / doubleScale +
    td0_unindexedSupply s + td0_unindexedBorrow s

theorem td0_inv_upgrade (L : Legacy) (hWF : L.WellFormed) :
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  unfold td0_Inv Consistent upgrade at *
  obtain ⟨hs0, hs_le, hb0, hb_le, hsblk, hbblk, haccts⟩ := hWF
  simp only [initSide]
  refine ⟨⟨?h1, ?h2, ?h3⟩, ?s1, ?s2⟩
  · by_cases h : L.supplyIndex = 0
    · simp [h]
    · simp [h]; exact hsblk
  · by_cases h : L.borrowIndex = 0
    · simp [h]
    · simp [h]; exact hbblk
  · intro a ha
    have ha0 := haccts a ha
    obtain ⟨hsa, hba⟩ := ha0
    by_cases hs : L.supplyIndex = 0 <;> by_cases hb : L.borrowIndex = 0
    · simp [hs, hb]
      have hs0a : a.supplierIndex = 0 := Nat.le_zero.mp (by simpa [hs] using hsa)
      have hb0a : a.borrowerIndex = 0 := Nat.le_zero.mp (by simpa [hb] using hba)
      constructor
      · rw [hs0a]; exact Nat.zero_le _
      · rw [hb0a]; exact Nat.zero_le _
    · simp [hs, hb]
      have hs0a : a.supplierIndex = 0 := Nat.le_zero.mp (by simpa [hs] using hsa)
      constructor
      · rw [hs0a]; exact Nat.zero_le _
      · exact hba
    · simp [hs, hb]
      have hb0a : a.borrowerIndex = 0 := Nat.le_zero.mp (by simpa [hb] using hba)
      constructor
      · exact hsa
      · rw [hb0a]; exact Nat.zero_le _
    · simp [hs, hb]
      exact ⟨hsa, hba⟩
  · by_cases h : L.supplyIndex = 0 <;> simp [h]
  · by_cases h : L.borrowIndex = 0 <;> simp [h]

open CompRewards in def foo : Nat := 1

def bar : Nat := 2

theorem tmp_check_modify (s : St) (who : Account) :
    (s.withAcct who id).accts = s.accts := by simp [St.withAcct]

theorem tmp_ledger_check (l : List Acct) (i j : Nat) (f : Acct → Acct) :
    (l.modify i f).getD j noAcct = if i = j ∧ j < l.length then f (l.getD j noAcct) else l.getD j noAcct :=
  ProofForgeFin.Ledger.getD_modify l i j f noAcct

def auxTestFoo2 : Nat := 1

def auxTestFoo3 : Nat := 2

def auxBorrowArith1 : Nat := 3

def auxBorrowTestA : Nat := 4

def auxBorrowTestB : Nat := 5

def auxArithA : Nat := 6

def auxScalePos : Nat := doubleScale

theorem myTestThm1 : 1 + 1 = 2 := by rfl

def myTestLem : Nat := 1

theorem auxTotalNil : (([] : List Acct).map Acct.supply).sum = 0 := by simp

theorem auxGetDZero : ([].getD (0 : Nat) noAcct) = noAcct := by simp

theorem aux_creditedTo_other (s : St) (actor who : Account) (f : Acct → Acct)
    (hne : actor ≠ who) :
    (s.withAcct actor f).creditedTo who = s.creditedTo who := by
  unfold St.creditedTo St.acct St.withAcct
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts actor who f noAcct
  rw [hmod]
  simp [hne]

theorem aux_creditedTo_pres4 (s : St) (actor who : Account) (f : Acct → Acct)
    (hacc : ∀ a, (f a).accrued = a.accrued ∧ (f a).wallet = a.wallet) :
    (s.withAcct actor f).creditedTo who = s.creditedTo who := by
  unfold St.creditedTo St.acct St.withAcct
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts actor who f noAcct
  rw [hmod]
  by_cases h : actor = who ∧ who < s.accts.length
  · simp only [if_pos h]
    have h2 := hacc (List.getD s.accts who noAcct)
    have e1 : (f (List.getD s.accts who noAcct)).accrued = (List.getD s.accts who noAcct).accrued := h2.1
    have e2 : (f (List.getD s.accts who noAcct)).wallet = (List.getD s.accts who noAcct).wallet := h2.2
    rw [e1, e2]
  · simp only [if_neg h]

theorem aux_acct_withAcct_same (s : St) (actor who : Account) (f : Acct → Acct)
    (hne : actor ≠ who) :
    (s.withAcct actor f).acct who = s.acct who := by
  unfold St.acct St.withAcct
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts actor who f noAcct
  rw [hmod]
  simp [hne]

theorem aux_accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

open CompRewards in theorem tmp_scale_pos : 0 < doubleScale := by unfold doubleScale; decide
#check ProofForgeFin.DeFi.Rewards.settle_le
#check ProofForgeFin.DeFi.Rewards.pending_le_add
#check ProofForgeFin.DeFi.Rewards.sum_pending_le_add
#check ProofForgeFin.DeFi.Rewards.credit_mul_le

theorem tmp_rewards_sig : True := trivial

open ProofForgeFin.DeFi.Rewards in theorem probe_pending_def (u s i : Nat) : pending u s i = u * (i - s) := by rfl

open ProofForgeFin.DeFi.Rewards in theorem probe2 (o u s i : Nat) : credit o u s i = u * (i - s) / o := by rfl

open ProofForgeFin.DeFi.Rewards in theorem probe_first2 (i r x : Nat) : firstStart i r x = if r = 0 then (if i ≤ x then i else 0) else r := by rfl

theorem aux_grant_credited_ok (s : St) (who : Account) :
    (grant s who).credited = s.credited := by
  unfold grant St.credited
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [if_pos h]
    exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who
      (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct))
      (fun a => a.accrued + a.wallet) noAcct (by intro _; simp only; omega)
  · simp only [if_neg h]

theorem plan1_setSpeeds_global_potential_aux1 (s : St) :
    totalSupply s = totalSupply { s with supplyState := { s.supplyState with block := s.blockNumber } } := by
  simp [totalSupply]

theorem aux_pending_mono_helper {idx0 idx1 st0 st1 : Nat}
    (hle : idx0 ≤ idx1) (hst : st0 ≤ st1) :
    idx1 - st1 ≤ (idx0 - st0) + (idx1 - idx0) := by
  omega

theorem aux_DS_pos : 0 < doubleScale := by unfold doubleScale; decide

theorem aux_credited_withAcct_supply2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with supply := a.supply + x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_credited_withAcct_borrow_sub2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with borrow := a.borrow - x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_credited_withAcct_borrow_add2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with borrow := a.borrow + x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_credited_withAcct_supply_sub2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with supply := a.supply - x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_unindexedB_withAcct2 (s : St) (who : Account) (f : Acct → Acct) :
    td0_unindexedBorrow (s.withAcct who f) = td0_unindexedBorrow s := by
  simp [td0_unindexedBorrow, St.withAcct]

theorem aux_unindexed_withAcct2 (s : St) (who : Account) (f : Acct → Acct) :
    td0_unindexedSupply (s.withAcct who f) = td0_unindexedSupply s := by
  simp [td0_unindexedSupply, St.withAcct]

theorem aux_compInit_le_double : compInitialIndex ≤ doubleScale := by
  unfold compInitialIndex doubleScale
  simp

theorem aux_compInit_pos : 0 < compInitialIndex := by
  unfold compInitialIndex
  decide

theorem aux_probe_acc1 (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem aux_accrue_index_ge5 (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
    exact Nat.le_add_right sd.index _
  · simp only [if_neg h]
    exact Nat.le_refl _

theorem aux_probe_subst (s : St) (who : Account) (s' : St)
    (h : SupplyDistributed s who s') : s'.blockNumber = s.blockNumber := by
  obtain ⟨hblk, hle, heq⟩ := h
  subst heq
  rfl

theorem auxAccStartSelf (idx : Nat) : accrualStart idx idx = idx := by
  unfold accrualStart
  by_cases h : idx = 0
  · subst h
    simp only
    have hci : ¬ compInitialIndex ≤ 0 := by unfold compInitialIndex; omega
    simp [hci]
  · simp [h]

theorem auxPendingSettledSupply (s : St) (a : Acct) (x : Nat)
    (hset : accrualStart a.supplierIndex s.supplyState.index = s.supplyState.index) :
    td0_pendingScaled s ({ a with supply := a.supply + x }) = td0_pendingScaled s a := by
  unfold td0_pendingScaled
  rw [hset]
  simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]

theorem auxPendWithAcctEq (s : St) (who : Account) (f : Acct → Acct) (a : Acct) :
    td0_pendingScaled (s.withAcct who f) a = td0_pendingScaled s a := by
  unfold td0_pendingScaled St.withAcct
  simp only

theorem aux_CI_pos : 0 < compInitialIndex := by
  unfold compInitialIndex
  decide

theorem aux_CI_ne_zero : compInitialIndex ≠ 0 := by
  unfold compInitialIndex
  omega

theorem aux_up_blockNum (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade; simp only

theorem aux_up_accts (L : Legacy) : (upgrade L).accts = L.accts := by
  unfold upgrade; simp only

theorem aux_up_speeds (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed ∧ (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h1 : L.supplyIndex = 0 <;> by_cases h2 : L.borrowIndex = 0 <;> simp [h1, h2]

theorem aux_up_borrow_block (L : Legacy) :
    (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem aux_up_borrow_index (L : Legacy) :
    (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem aux_up_supply_block (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_supply_index (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_legStart_nz (S r : Nat) (h : r ≠ 0) :
    legacyStart S r = r := by
  unfold legacyStart
  simp [h]

theorem aux_legStart_zero (S : Nat) :
    legacyStart S 0 = S := by
  unfold legacyStart
  simp

theorem aux_accStart_nz (r idx : Nat) (h : r ≠ 0) :
    accrualStart r idx = r := by
  unfold accrualStart
  simp [h]

theorem aux_accStart_zero (idx : Nat) :
    accrualStart 0 idx = (if compInitialIndex ≤ idx then compInitialIndex else 0) := by
  unfold accrualStart
  simp

theorem aux_start_diff_le4 (S r I : Nat)
    (hS : S = 0 ∨ S = compInitialIndex) (hSI : S ≤ I) (hr : r ≤ I) :
    (if I = 0 then compInitialIndex else I) -
      accrualStart r (if I = 0 then compInitialIndex else I) ≤
    I - legacyStart S r := by
  by_cases hI : I = 0
  · subst hI
    have hr0 : r = 0 := Nat.le_zero.mp hr
    have hS0 : S = 0 := by
      rcases hS with h | h
      · exact h
      · subst h
        have hpos : 0 < compInitialIndex := aux_CI_pos
        omega
    subst hr0; subst hS0
    have hJ : (if (0 : Nat) = 0 then compInitialIndex else 0) = compInitialIndex := by simp
    rw [hJ, aux_legStart_zero, aux_accStart_zero]
    have h1 : compInitialIndex ≤ compInitialIndex := Nat.le_refl _
    have h2 : (if compInitialIndex ≤ compInitialIndex then compInitialIndex else 0) = compInitialIndex := if_pos h1
    rw [h2]
    simp
  · have hIf : (if I = 0 then compInitialIndex else I) = I := if_neg hI
    rw [hIf]
    by_cases hr0 : r = 0
    · subst hr0
      rw [aux_legStart_zero, aux_accStart_zero]
      by_cases hle : compInitialIndex ≤ I
      · rw [if_pos hle]
        rcases hS with h | h
        · subst h; simp
        · subst h; simp
      · rw [if_neg hle]
        have hS0 : S = 0 := by
          rcases hS with h | h
          · exact h
          · exfalso; subst h; omega
        subst hS0; simp
    · rw [aux_accStart_nz _ _ hr0, aux_legStart_nz _ _ hr0]
      exact Nat.le_refl _

theorem aux_pend_up_le (L : Legacy) (hWF : L.WellFormed) (a : Acct) (ha : a ∈ L.accts) :
    td0_pendingScaled (upgrade L) a ≤ Legacy.pendingScaled L a := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs0, hs_le, hb0, hb_le, hsblk, hbblk, haccts⟩ := hWF
  have hacct := haccts a ha
  obtain ⟨hsa, hba⟩ := hacct
  have hsup := aux_up_supply_index L
  have hbor := aux_up_borrow_index L
  unfold td0_pendingScaled Legacy.pendingScaled
  rw [hsup, hbor]
  have h1 : a.supply * ((if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) -
      accrualStart a.supplierIndex (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex)) ≤
    a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
    apply Nat.mul_le_mul_left
    exact aux_start_diff_le4 L.supplyStart a.supplierIndex L.supplyIndex hs0 hs_le hsa
  have h2 : a.borrow * ((if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) -
      accrualStart a.borrowerIndex (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex)) ≤
    a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
    apply Nat.mul_le_mul_left
    exact aux_start_diff_le4 L.borrowStart a.borrowerIndex L.borrowIndex hb0 hb_le hba
  omega

theorem aux_sum_map_mono (l : List Acct) (f g : Acct → Nat)
    (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hhd : f hd ≤ g hd := h hd (by simp)
    have htl : ∀ a ∈ tl, f a ≤ g a := fun a ha => h a (List.mem_cons_of_mem hd ha)
    have iht := ih htl
    omega

theorem plan2_start_diff_le (S r I : Nat)
    (hS : S = 0 ∨ S = compInitialIndex) (hSI : S ≤ I) (hrI : r ≤ I) :
    (if I = 0 then compInitialIndex else I) -
        accrualStart r (if I = 0 then compInitialIndex else I) ≤
      I - legacyStart S r :=
  aux_start_diff_le4 S r I hS hSI hrI

theorem plan2_pending_upgrade_le (L : Legacy) (hWF : L.WellFormed)
    (a : Acct) (ha : a ∈ L.accts) :
    td0_pendingScaled (upgrade L) a ≤ Legacy.pendingScaled L a :=
  aux_pend_up_le L hWF a ha

theorem plan2_unindexedSupply_upgrade_le (L : Legacy) :
    td0_unindexedSupply (upgrade L) ≤ L.unindexedSupply := by
  unfold td0_unindexedSupply upgrade initSide Legacy.unindexedSupply
  simp only
  by_cases h : L.supplyIndex = 0
  · simp [h]
  · simp [h]

theorem plan2_unindexedBorrow_upgrade_le_aux_tmp : True := trivial

theorem plan2_unindexedBorrow_upgrade_le_check (L : Legacy) :
    td0_unindexedBorrow (upgrade L) ≤ L.unindexedBorrow := by
  unfold td0_unindexedBorrow upgrade initSide Legacy.unindexedBorrow
  simp only
  by_cases h : L.borrowIndex = 0
  · simp [h]
  · simp [h]

theorem plan2_unindexedBorrow_upgrade_le (L : Legacy) :
    td0_unindexedBorrow (upgrade L) ≤ L.unindexedBorrow := by
  unfold td0_unindexedBorrow upgrade initSide Legacy.unindexedBorrow
  simp only
  by_cases h : L.borrowIndex = 0
  · simp [h]
  · simp [h]

theorem plan2_sum_pending_upgrade_le_aux (L : Legacy) (hWF : L.WellFormed) :
    ((upgrade L).accts.map (td0_pendingScaled (upgrade L))).sum ≤
      (L.accts.map L.pendingScaled).sum := by
  have hAccts : (upgrade L).accts = L.accts := aux_up_accts L
  rw [hAccts]
  apply aux_sum_map_mono _ _ _
  intro a ha
  exact plan2_pending_upgrade_le L hWF a ha

theorem plan2_sum_pending_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    ((upgrade L).accts.map (td0_pendingScaled (upgrade L))).sum ≤
      (L.accts.map L.pendingScaled).sum := by
  have hAccts : (upgrade L).accts = L.accts := aux_up_accts L
  rw [hAccts]
  apply aux_sum_map_mono _ _ _
  intro a ha
  exact plan2_pending_upgrade_le L hWF a ha

theorem plan2_owed_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed := by
  unfold td0_owed Legacy.owed
  have hSum := plan2_sum_pending_upgrade_le L hWF
  have hS := plan2_unindexedSupply_upgrade_le L
  have hB := plan2_unindexedBorrow_upgrade_le L
  have hDiv : ((upgrade L).accts.map (td0_pendingScaled (upgrade L))).sum / doubleScale ≤
      (L.accts.map L.pendingScaled).sum / doubleScale :=
    Nat.div_le_div_right hSum
  omega

theorem td0_owed_upgrade_le_fix (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed :=
  plan2_owed_upgrade_le L hWF

theorem td0_owed_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed :=
  plan2_owed_upgrade_le L hWF

theorem aux_ping : 1 = 1 := rfl

theorem td0_owedTo_upgrade_le (L : Legacy) (hWF : L.WellFormed) (who : Account) :
    td0_owedTo (upgrade L) who ≤ L.owedTo who := by
  have hAccts : (upgrade L).accts = L.accts := aux_up_accts L
  have hAcctEq : (upgrade L).acct who = L.accts.getD who noAcct := by
    unfold St.acct
    rw [hAccts]
  have hMemOr := ProofForgeFin.Ledger.getD_mem_or L.accts who noAcct
  have hPend : td0_pendingScaled (upgrade L) (L.accts.getD who noAcct) ≤
      Legacy.pendingScaled L (L.accts.getD who noAcct) := by
    cases hMemOr with
    | inl hmem =>
      exact aux_pend_up_le L hWF _ hmem
    | inr heq =>
      rw [heq]
      unfold td0_pendingScaled Legacy.pendingScaled noAcct
      simp
  have hSupUn : td0_unindexedSupply (upgrade L) ≤ L.unindexedSupply :=
    plan2_unindexedSupply_upgrade_le L
  have hBorUn : td0_unindexedBorrow (upgrade L) ≤ L.unindexedBorrow :=
    plan2_unindexedBorrow_upgrade_le L
  have hDiv : td0_pendingScaled (upgrade L) (L.accts.getD who noAcct) / doubleScale ≤
      Legacy.pendingScaled L (L.accts.getD who noAcct) / doubleScale :=
    Nat.div_le_div_right hPend
  have hS : (if 0 < (L.accts.getD who noAcct).supply then td0_unindexedSupply (upgrade L) else 0) ≤
      (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) := by
    by_cases h0 : 0 < (L.accts.getD who noAcct).supply
    · simp only [if_pos h0]
      exact hSupUn
    · simp only [if_neg h0, Nat.le_refl]
  have hB : (if 0 < (L.accts.getD who noAcct).borrow then td0_unindexedBorrow (upgrade L) else 0) ≤
      (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0) := by
    by_cases h0 : 0 < (L.accts.getD who noAcct).borrow
    · simp only [if_pos h0]
      exact hBorUn
    · simp only [if_neg h0, Nat.le_refl]
  unfold td0_owedTo Legacy.owedTo
  rw [hAcctEq]
  omega

theorem aux_subChecked_eq (a b : Nat) :
    subChecked a b = if b ≤ a then some (a - b) else none := by rfl

theorem aux_updS1 (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    (if s.supplyState.block ≤ s.blockNumber then (1:Nat) else 2) = 1 := by simp [hle]

theorem aux_sub_nle (s : St) (hle : ¬ s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = none := by
  unfold subChecked
  simp [hle]

theorem aux_sub_le (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [hle]

theorem aux_updSupply_rw (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      (let deltaBlocks := s.blockNumber - s.supplyState.block;
      if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
        let supplyTokens := totalSupply s
        let compAccrued := deltaBlocks * s.supplyState.speed
        let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
        some ({ s with supplyState := { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } } : St)
      else if deltaBlocks > 0 then
        some ({ s with supplyState := { s.supplyState with block := s.blockNumber } } : St)
      else (some s : Option St)) := by
  unfold updateCompSupplyIndex
  rw [aux_sub_le s hle]

theorem aux_updSupply_some2 (s t : St) (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · exact hle
  · rw [aux_sub_nle s hle] at h
    simp at h

theorem aux_opt_some_eq {α : Type} (x y : α) (h : (some x : Option α) = some y) : x = y := by cases h; rfl

theorem tmp_side_eta (sd : Side) (n : Nat) (h : sd.block = n) :
    ({ sd with block := n } : Side) = sd := by
  cases sd with
  | mk idx blk spd =>
    simp only at h ⊢
    rw [h]

theorem plan3_updateSupplyIndex_accrue (s : St) (t : St)
    (h : updateCompSupplyIndex s = some t) :
    t = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hle : s.supplyState.block ≤ s.blockNumber := aux_updSupply_some2 s t h
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := aux_sub_le s hle
  unfold updateCompSupplyIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [if_pos hd] at h
    by_cases hpos : 0 < totalSupply s
    · simp only [if_pos hpos] at h
      have hTT : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s := ⟨hd.1, hd.2, hpos⟩
      rw [if_pos hTT]
      cases h
      rfl
    · have hnpos : ¬ 0 < totalSupply s := by omega
      simp only [if_neg hnpos] at h
      have hFF : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      rw [if_neg hFF]
      cases h
      rfl
  · simp only [if_neg hd] at h
    by_cases hd2 : s.blockNumber - s.supplyState.block > 0
    · simp only [if_pos hd2] at h
      have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      rw [if_neg hneg]
      cases h
      rfl
    · have hnd : ¬ s.blockNumber - s.supplyState.block > 0 := by omega
      simp only [if_neg hnd] at h
      have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      rw [if_neg hneg]
      cases h
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      have hS : ({ s.supplyState with block := s.blockNumber } : Side) = s.supplyState :=
        tmp_side_eta s.supplyState s.blockNumber hbeq
      cases s with
      | mk bn sup bor res ac =>
        simp only at hS hbeq ⊢
        simp only [hS]

theorem aux_borrow_eta (sd : Side) (n : Nat) (h : sd.block = n) :
    ({ sd with block := n } : Side) = sd := by
  cases sd with
  | mk idx blk spd => simp only at h ⊢; rw [h]

theorem aux_borrow_block_le (s t : St) (h : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex at h
  unfold subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem plan3_updateBorrowIndex_accrue_aux : True := trivial

theorem plan3_updateBorrowIndex_accrue (s : St) (t : St)
    (h : updateCompBorrowIndex s = some t) :
    t = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hle : s.borrowState.block ≤ s.blockNumber := aux_borrow_block_le s t h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [hle]
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [if_pos hd] at h
    by_cases hpos : 0 < totalBorrows s
    · simp only [if_pos hpos] at h
      have hTT : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s := ⟨hd.1, hd.2, hpos⟩
      rw [if_pos hTT]
      cases h
      rfl
    · have hnpos : ¬ 0 < totalBorrows s := by omega
      simp only [if_neg hnpos] at h
      have hFF : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      rw [if_neg hFF]
      cases h
      rfl
  · simp only [if_neg hd] at h
    by_cases hd2 : s.blockNumber - s.borrowState.block > 0
    · simp only [if_pos hd2] at h
      have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      rw [if_neg hneg]
      cases h
      rfl
    · have hnd : ¬ s.blockNumber - s.borrowState.block > 0 := by omega
      simp only [if_neg hnd] at h
      have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      rw [if_neg hneg]
      cases h
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      have hS : ({ s.borrowState with block := s.blockNumber } : Side) = s.borrowState :=
        aux_borrow_eta s.borrowState s.blockNumber hbeq
      cases s with
      | mk bn sup bor res ac =>
        simp only at hS hbeq ⊢
        simp only [hS]

theorem plan3_setSupplySpeed_spec (s : St) (sup : Nat) (t : St)
    (h : setSupplySpeed s sup = some t) :
    (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = sup
  · have hcond : ¬ s.supplyState.speed ≠ sup := by simp [heq]
    rw [if_neg hcond] at h
    have ht : s = t := by cases h; rfl
    subst ht
    constructor
    · intro hne; exact absurd hne hcond
    · simp [heq]
  · have hcond : s.supplyState.speed ≠ sup := heq
    rw [if_pos hcond] at h
    cases hU : updateCompSupplyIndex s with
    | none =>
      rw [hU] at h
      simp at h
    | some s1 =>
      rw [hU] at h
      simp only [Option.map_some] at h
      have hle : s.supplyState.block ≤ s.blockNumber :=
        aux_updSupply_some2 s s1 hU
      have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
        plan3_updateSupplyIndex_accrue s s1 hU
      cases h
      rw [hs1]
      constructor
      · intro _; exact hle
      · simp only [if_neg heq]

theorem plan3_setBorrowSpeed_spec_proof (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = bor
  · have hcond : ¬ s.borrowState.speed ≠ bor := by simp [heq]
    rw [if_neg hcond] at h
    have ht : s = t := by cases h; rfl
    subst ht
    constructor
    · intro hne; exact absurd hne hcond
    · simp [heq]
  · have hcond : s.borrowState.speed ≠ bor := heq
    rw [if_pos hcond] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      rw [hU] at h
      simp at h
    | some s1 =>
      rw [hU] at h
      simp only [Option.map_some] at h
      have hle : s.borrowState.block ≤ s.blockNumber :=
        aux_borrow_block_le s s1 hU
      have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        plan3_updateBorrowIndex_accrue s s1 hU
      cases h
      rw [hs1]
      constructor
      · intro _; exact hle
      · simp only [if_neg heq]

theorem plan3_setBorrowSpeed_spec_aux_use (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } :=
  plan3_setBorrowSpeed_spec_proof s bor t h

theorem plan3_setBorrowSpeed_spec_alt (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } :=
  plan3_setBorrowSpeed_spec_proof s bor t h

theorem plan3_setBorrowSpeed_spec (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = bor
  · have hcond : ¬ s.borrowState.speed ≠ bor := by simp [heq]
    rw [if_neg hcond] at h
    have ht : s = t := by cases h; rfl
    subst ht
    constructor
    · intro hne; exact absurd hne hcond
    · simp [heq]
  · have hcond : s.borrowState.speed ≠ bor := heq
    rw [if_pos hcond] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      rw [hU] at h
      simp at h
    | some s1 =>
      rw [hU] at h
      simp only [Option.map_some] at h
      have hle : s.borrowState.block ≤ s.blockNumber :=
        aux_borrow_block_le s s1 hU
      have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        plan3_updateBorrowIndex_accrue s s1 hU
      cases h
      rw [hs1]
      constructor
      · intro _; exact hle
      · simp only [if_neg heq]

theorem plan3_compose_with_test (s : St) (X : Side) (Y : Side) :
    ({ ({ s with supplyState := X } : St) with borrowState := Y } : St) =
    ({ s with supplyState := X, borrowState := Y } : St) := by
  cases s <;> rfl

theorem plan3_mid_projs (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    mid.borrowState = s.borrowState := by
  rw [hmidEq]

theorem plan3_compose_gen3 (s : St) (X Y : Side) :
    ({ ({ s with supplyState := X } : St) with borrowState := Y } : St) =
    ({ s with supplyState := X, borrowState := Y } : St) := by
  cases s with
  | mk bn sup bor res ac => rfl

theorem plan3_mid_block (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    mid.blockNumber = s.blockNumber := by
  rw [hmidEq]

theorem plan3_mid_accts (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    mid.accts = s.accts := by
  rw [hmidEq]

theorem plan3_mid_borrows (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    totalBorrows mid = totalBorrows s := by
  have hac : mid.accts = s.accts := plan3_mid_accts s mid a hmidEq
  unfold totalBorrows
  rw [hac]

theorem td0_setSpeeds_effect_aux_tmp : True := trivial

theorem req_set_speeds_check_tmp : SpeedsSet (St.mk 0 ⟨0,0,0⟩ ⟨0,0,0⟩ 0 []) 0 0 (St.mk 0 ⟨0,0,0⟩ ⟨0,0,0⟩ 0 []) := by
  unfold SpeedsSet
  simp

theorem tmp_comp_eq (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) := by
  unfold comptroller
  rfl

theorem tmp_do_bind (s : St) (who : Account) :
    (do let s1 ← updateCompSupplyIndex s
        distributeSupplierComp s1 who) =
      Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) := by
  rfl

theorem tmp_list_modify_succ (hd : Acct) (tl : List Acct) (n : Nat) (f : Acct → Acct) :
    (hd :: tl).modify (n+1) f = hd :: tl.modify n f := by
  rfl

#check List.modify

theorem tmp_list_modify_unfold (l : List Acct) (f : Acct → Acct) :
    l.modify 0 f = match l with | [] => [] | hd :: tl => f hd :: tl := by
  cases l <;> rfl

theorem aux_modify_congr2 (l : List Acct) (i : Nat) (f g : Acct → Acct)
    (hfg : f (l.getD i noAcct) = g (l.getD i noAcct)) :
    l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hfg
      show (f hd :: tl) = (g hd :: tl)
      rw [hfg]
    | succ n =>
      simp only [List.getD_cons_succ] at hfg
      show hd :: tl.modify n f = hd :: tl.modify n g
      rw [ih n hfg]

theorem tmp_bind_none_contra (s : St) (who : Account) (s' : St)
    (hU : updateCompSupplyIndex s = none)
    (h : comptroller s (.supplyHook who) = some s') : False := by
  have hComp := tmp_comp_eq s who
  rw [hComp, hU] at h
  simp at h

theorem tmp_bind_reduce2 (s : St) (who : Account) (s' s1 : St)
    (hU : updateCompSupplyIndex s = some s1)
    (h : comptroller s (.supplyHook who) = some s') :
    distributeSupplierComp s1 who = some s' := by
  have hComp := tmp_comp_eq s who
  rw [hComp, hU] at h
  simpa using h

theorem plan4_test_ge (index : Nat) :
    (index ≥ compInitialIndex) = (compInitialIndex ≤ index) := by rfl

theorem plan4_accrualStart_eq2 (recorded index : Nat) :
    (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hrec : recorded = 0
  · simp [hrec]
  · simp [hrec]

theorem plan4_accrualStart_eq (recorded index : Nat) :
    (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) =
      accrualStart recorded index := plan4_accrualStart_eq2 recorded index

theorem plan4_updateCompSupplyIndex_spec_check (s s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ∧
    s1.accts = s.accts := by
  have hle : s.supplyState.block ≤ s.blockNumber := aux_updSupply_some2 s s1 h
  have heq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    plan3_updateSupplyIndex_accrue s s1 h
  refine ⟨hle, heq, ?_⟩
  rw [heq]

theorem plan4_updateCompSupplyIndex_spec (s s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ∧
    s1.accts = s.accts := by
  have hle : s.supplyState.block ≤ s.blockNumber := aux_updSupply_some2 s s1 h
  have heq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    plan3_updateSupplyIndex_accrue s s1 h
  refine ⟨hle, heq, ?_⟩
  rw [heq]

theorem plan4_distributeSupplierComp_spec_aux1 (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  rw [plan4_accrualStart_eq2]

theorem tmp_parse_test (s : St) (who : Account) :
    s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index } : Acct)) = s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index } : Acct)) := by
  rfl

theorem tmp_FG_eq2 (s : St) (a : Acct) :
    ({ a with supplierIndex := s.supplyState.index } : Acct) = ({ a with supplierIndex := s.supplyState.index } : Acct) := by
  rfl

theorem tmp_twofield (s : St) (a : Acct) (x : Nat) :
    ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + x } : Acct) =
    ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + x } : Acct) := by
  rfl

theorem tmp_FG_eq3 (s : St) (who : Account) :
    (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + 1 } : Acct)) (List.getD s.accts who noAcct) = (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + 1 } : Acct)) (List.getD s.accts who noAcct) := by
  rfl

theorem plan4_impl_eq_spec_at (s : St) (who : Account) : (({ List.getD s.accts who noAcct with supplierIndex := s.supplyState.index, accrued := (List.getD s.accts who noAcct).accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) = (({ List.getD s.accts who noAcct with supplierIndex := s.supplyState.index, accrued := (List.getD s.accts who noAcct).accrued + creditFor (List.getD s.accts who noAcct).supply (accrualStart (List.getD s.accts who noAcct).supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) := by
  have e1 : (List.getD s.accts who noAcct).supply = (s.acct who).supply := rfl
  have e2 : (List.getD s.accts who noAcct).supplierIndex = (s.acct who).supplierIndex := rfl
  rw [e1, e2]
  rfl

theorem plan4_supplyDistributed_of_steps_aux_tmp2 : True := trivial

theorem aux_withAcct_after_supply (s : St) (X : Side) (who : Account) (f : Acct → Acct) :
    (({ s with supplyState := X } : St).withAcct who f) =
    ({ s with supplyState := X, accts := s.accts.modify who f } : St) := by
  cases s with
  | mk bn sup bor res ac =>
    rfl

theorem myDist_supply (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
        s.supplyState.index ∧
    s' = s.withAcct who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s.supplyState.index)
          s.supplyState.index } := by
  unfold distributeSupplierComp at h
  simp only at h
  have hAcc : (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    rw [plan4_accrualStart_eq2]
  rw [hAcc] at h
  cases hSub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none =>
    rw [hSub] at h
    simp at h
  | some delta =>
    rw [hSub] at h
    have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
      unfold subChecked at hSub
      by_cases hc : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
      · exact hc
      · simp [hc] at hSub
    have hdelta : delta = s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index := by
      unfold subChecked at hSub
      simp [hle] at hSub
      exact hSub.symm
    simp only [Option.some_inj] at h
    subst h
    rw [hdelta]
    constructor
    · exact hle
    · unfold St.withAcct
      congr 1
      apply aux_modify_congr2
      show ({ List.getD s.accts who noAcct with supplierIndex := s.supplyState.index, accrued := (List.getD s.accts who noAcct).accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct) = _
      have e1 : (List.getD s.accts who noAcct).supply = (s.acct who).supply := rfl
      have e2 : (List.getD s.accts who noAcct).supplierIndex = (s.acct who).supplierIndex := rfl
      rw [e1, e2]
      unfold mulDouble creditFor
      rfl

theorem td0_supplyHook_effect_proof (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' := by
  have hComp := tmp_comp_eq s who
  rw [hComp] at h
  unfold Option.bind at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    rw [hU] at h
    simp at h
  | some s1 =>
    rw [hU] at h
    simp only at h
    have hD : distributeSupplierComp s1 who = some s' := h
    have hUspec := plan4_updateCompSupplyIndex_spec s s1 hU
    obtain ⟨hblk, hs1eq, haccts⟩ := hUspec
    have hDspec := myDist_supply s1 who s' hD
    obtain ⟨hle1, heq1⟩ := hDspec
    have hIdx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hs1eq]
    have hAcctEq : s1.acct who = s.acct who := by
      unfold St.acct
      rw [haccts]
    have hle2 : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [← hIdx, ← hAcctEq]
      exact hle1
    refine ⟨hblk, hle2, ?_⟩
    subst hs1eq
    rw [heq1]
    simp only [St.withAcct]

theorem td0_supplyHook_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' :=
  td0_supplyHook_effect_proof s who s' h

theorem myDist_borrow (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
        s.borrowState.index ∧
    s' = s.withAcct who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } := by
  unfold distributeBorrowerComp at h
  simp only at h
  have hAcc : (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
      else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
    rw [plan4_accrualStart_eq2]
  rw [hAcc] at h
  cases hSub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none =>
    rw [hSub] at h
    simp at h
  | some delta =>
    rw [hSub] at h
    have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
      unfold subChecked at hSub
      by_cases hc : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
      · exact hc
      · simp [hc] at hSub
    have hdelta : delta = s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
      unfold subChecked at hSub
      simp [hle] at hSub
      exact hSub.symm
    simp only [Option.some_inj] at h
    subst h
    rw [hdelta]
    constructor
    · exact hle
    · unfold St.withAcct
      congr 1
      apply aux_modify_congr2
      show ({ List.getD s.accts who noAcct with borrowerIndex := s.borrowState.index, accrued := (List.getD s.accts who noAcct).accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct) = _
      have e1 : (List.getD s.accts who noAcct).borrow = (s.acct who).borrow := rfl
      have e2 : (List.getD s.accts who noAcct).borrowerIndex = (s.acct who).borrowerIndex := rfl
      rw [e1, e2]
      unfold mulDouble creditFor
      rfl

theorem plan4_updateCompBorrowIndex_spec (s s1 : St)
    (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1 = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ∧
    s1.accts = s.accts := by
  have hle : s.borrowState.block ≤ s.blockNumber := aux_borrow_block_le s s1 h
  have heq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan3_updateBorrowIndex_accrue s s1 h
  refine ⟨hle, heq, ?_⟩
  rw [heq]

theorem td0_borrowHook_effect_proved (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    BorrowDistributed s who s' := by
  have hComp : comptroller s (.borrowHook who) =
      Option.bind (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who) := rfl
  rw [hComp] at h
  unfold Option.bind at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    rw [hU] at h
    simp at h
  | some s1 =>
    rw [hU] at h
    simp only at h
    have hD : distributeBorrowerComp s1 who = some s' := h
    have hUspec := plan4_updateCompBorrowIndex_spec s s1 hU
    obtain ⟨hblk, hs1eq, haccts⟩ := hUspec
    have hDspec := myDist_borrow s1 who s' hD
    obtain ⟨hle1, heq1⟩ := hDspec
    have hIdx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hs1eq]
    have hAcctEq : s1.acct who = s.acct who := by
      unfold St.acct
      rw [haccts]
    have hle2 : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [← hIdx, ← hAcctEq]
      exact hle1
    refine ⟨hblk, hle2, ?_⟩
    subst hs1eq
    rw [heq1]
    simp only [St.withAcct]

theorem td0_borrowHook_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    BorrowDistributed s who s' :=
  td0_borrowHook_effect_proved s who s' h

theorem td0_setSpeeds_some_auxB (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [hle]
  unfold updateCompBorrowIndex
  rw [hsub]
  by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [if_pos h1, Option.isSome_some]
  · simp only [if_neg h1]
    by_cases h2 : s.blockNumber - s.borrowState.block > 0
    · simp only [if_pos h2, Option.isSome_some]
    · simp only [if_neg h2, Option.isSome_some]

theorem td0_setSpeeds_some_auxA (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := aux_sub_le s hle
  unfold updateCompSupplyIndex
  rw [hsub]
  by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [if_pos h1, Option.isSome_some]
  · simp only [if_neg h1]
    by_cases h2 : s.blockNumber - s.supplyState.block > 0
    · simp only [if_pos h2, Option.isSome_some]
    · simp only [if_neg h2, Option.isSome_some]

theorem td0_setSpeeds_some_clean2 (s : St) (a b : Nat) (hs : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome = true := by
  have hsSup : s.supplyState.block ≤ s.blockNumber := hs.1
  have hsBor : s.borrowState.block ≤ s.blockNumber := hs.2.1
  have hSup : (setSupplySpeed s a).isSome = true := by
    unfold setSupplySpeed
    by_cases heq : s.supplyState.speed ≠ a
    · rw [if_pos heq]
      have hU := td0_setSpeeds_some_auxA s hsSup
      cases hU' : updateCompSupplyIndex s
      · rw [hU'] at hU
        contradiction
      · rfl
    · rw [if_neg heq]
      rfl
  obtain ⟨mid, hMid⟩ : ∃ mid, setSupplySpeed s a = some mid := Option.isSome_iff_exists.mp hSup
  have hspec := plan3_setSupplySpeed_spec s a mid hMid
  obtain ⟨_, hmidEq⟩ := hspec
  have hMidBlock : mid.blockNumber = s.blockNumber := plan3_mid_block s mid a hmidEq
  have hMidBorSt : mid.borrowState = s.borrowState := plan3_mid_projs s mid a hmidEq
  have hMidBor : mid.borrowState.block ≤ mid.blockNumber := by
    rw [hMidBorSt, hMidBlock]
    exact hsBor
  have hBorSome : (setBorrowSpeed mid b).isSome = true := by
    unfold setBorrowSpeed
    by_cases heq2 : mid.borrowState.speed ≠ b
    · rw [if_pos heq2]
      have hU2 := td0_setSpeeds_some_auxB mid hMidBor
      cases hU2' : updateCompBorrowIndex mid
      · rw [hU2'] at hU2
        contradiction
      · rfl
    · rw [if_neg heq2]
      rfl
  have hComp : comptroller s (.setSpeeds a b) =
      Option.bind (setSupplySpeed s a) (fun m => setBorrowSpeed m b) := rfl
  rw [hComp, hMid]
  exact hBorSome

theorem plan5_updateSupply_some (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  exact td0_setSpeeds_some_auxA s h

theorem plan5_updateBorrow_some (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := td0_setSpeeds_some_auxB s h

theorem plan5_updateSupply_preserve_proof3 (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState := by
  have heq := plan3_updateSupplyIndex_accrue s t h
  rw [heq]
  exact ⟨rfl, rfl⟩

theorem plan5_preserve_inline_test (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState := by
  have heq := plan3_updateSupplyIndex_accrue s t h
  rw [heq]
  exact ⟨rfl, rfl⟩

theorem plan5_updateSupply_preserve (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState := by
  have heq := plan3_updateSupplyIndex_accrue s t h
  rw [heq]
  exact ⟨rfl, rfl⟩

theorem plan5_setSupply_some_proof (s : St) (a : Nat)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (setSupplySpeed s a).isSome = true := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed ≠ a
  · rw [if_pos heq]
    have hU := plan5_updateSupply_some s h
    cases hE : updateCompSupplyIndex s with
    | none =>
      have hF : (updateCompSupplyIndex s).isSome = false := by rw [hE]; rfl
      rw [hF] at hU
      contradiction
    | some s1 =>
      rfl
  · rw [if_neg heq]; rfl

theorem plan5_setSupply_some (s : St) (a : Nat)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (setSupplySpeed s a).isSome = true := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed ≠ a
  · rw [if_pos heq]
    have hU := plan5_updateSupply_some s h
    cases hE : updateCompSupplyIndex s with
    | none =>
      have hF : (updateCompSupplyIndex s).isSome = false := by rw [hE]; rfl
      rw [hF] at hU
      contradiction
    | some s1 =>
      rfl
  · rw [if_neg heq]; rfl

theorem plan5_setSupply_preserve2 (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    mid.blockNumber = s.blockNumber ∧ mid.borrowState = s.borrowState := by
  have hspec := plan3_setSupplySpeed_spec s a mid h
  obtain ⟨_, hmidEq⟩ := hspec
  rw [hmidEq]
  exact ⟨rfl, rfl⟩

theorem plan5_setSupply_preserve_inline (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    mid.blockNumber = s.blockNumber ∧ mid.borrowState = s.borrowState := by
  have hspec := plan3_setSupplySpeed_spec s a mid h
  obtain ⟨_, hmidEq⟩ := hspec
  rw [hmidEq]
  exact ⟨rfl, rfl⟩

theorem plan5_setSupply_preserve (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    mid.blockNumber = s.blockNumber ∧ mid.borrowState = s.borrowState := by
  have hspec := plan3_setSupplySpeed_spec s a mid h
  obtain ⟨_, hmidEq⟩ := hspec
  rw [hmidEq]
  exact ⟨rfl, rfl⟩

theorem plan5_setBorrow_some (s : St) (b : Nat)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (setBorrowSpeed s b).isSome = true := by
  unfold setBorrowSpeed
  by_cases heq : s.borrowState.speed ≠ b
  · rw [if_pos heq]
    have hU := plan5_updateBorrow_some s h
    cases hE : updateCompBorrowIndex s with
    | none =>
      have hF : (updateCompBorrowIndex s).isSome = false := by rw [hE]; rfl
      rw [hF] at hU
      contradiction
    | some s1 =>
      rfl
  · rw [if_neg heq]; rfl

theorem td0_setSpeeds_some_proof (s : St) (a b : Nat) (hs : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome := by
  exact td0_setSpeeds_some_clean2 s a b hs

def td0_pendingAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def td0_pendingTo (s : St) (who : Account) : Nat := td0_pendingAcct s (s.acct who)

def td0_unindexedTo (s : St) (who : Account) : Nat :=
  (if 0 < (s.acct who).supply then
     (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0) +
  (if 0 < (s.acct who).borrow then
     (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0)

def td0_potentialTo (s : St) (who : Account) : Nat :=
  doubleScale * s.creditedTo who + td0_pendingTo s who + doubleScale * td0_unindexedTo s who

def td0_pending (s : St) : Nat := (s.accts.map (td0_pendingAcct s)).sum

def td0_unindexed (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def td0_potential (s : St) : Nat :=
  doubleScale * s.credited + td0_pending s + doubleScale * td0_unindexed s

theorem td0_upgrade_inv_aux : ∀ (L : Legacy), L.WellFormed →
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  intro L hW
  unfold td0_Inv upgrade Consistent initSide Legacy.WellFormed at *
  obtain ⟨hs0, hs_le, hb0, hb_le, hsblk, hbblk, haccts⟩ := hW
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · by_cases h : L.supplyIndex = 0 <;> simp [h] <;> omega
  · by_cases h : L.borrowIndex = 0 <;> simp [h] <;> omega
  · intro a ha
    have ha' := haccts a ha
    by_cases hs : L.supplyIndex = 0 <;> by_cases hb : L.borrowIndex = 0 <;> simp [hs, hb] <;> omega
  · by_cases h : L.supplyIndex = 0 <;> simp [h]
  · by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem td0_upgrade_inv : ∀ (L : Legacy), L.WellFormed →
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  intro L h
  exact td0_upgrade_inv_aux L h

def td0_check1 : 0 < doubleScale := by unfold doubleScale; omega
#check @Nat.le_of_mul_le_mul_left
#check @Nat.mul_left_cancel

theorem td0_no_backdated_conclude : ∀ (s : St) (sp : Nat × Nat) (ops : List Op)
    (who : Account),
    td0_potentialTo (run comptroller s ops) who ≤
        td0_potentialTo s who + doubleScale * emitted sp ops →
    td0_potentialTo s who = doubleScale * s.creditedTo who →
    (run comptroller s ops).creditedTo who ≤ s.creditedTo who + emitted sp ops := by
  intro s sp ops who hRun hInit
  have hLow : doubleScale * (run comptroller s ops).creditedTo who ≤
      td0_potentialTo (run comptroller s ops) who := by
    unfold td0_potentialTo
    omega
  rw [hInit] at hRun
  have hDS : 0 < doubleScale := by unfold doubleScale; omega
  have hComb : doubleScale * (run comptroller s ops).creditedTo who ≤
      doubleScale * (s.creditedTo who + emitted sp ops) := by
    calc doubleScale * (run comptroller s ops).creditedTo who
        ≤ td0_potentialTo (run comptroller s ops) who := hLow
      _ ≤ doubleScale * s.creditedTo who + doubleScale * emitted sp ops := hRun
      _ = doubleScale * (s.creditedTo who + emitted sp ops) := by rw [Nat.mul_add]
  exact Nat.le_of_mul_le_mul_left hComb hDS

def foo_test : Nat := 1

theorem aux_sum_le_sum2 (f g : Acct → Nat) (l : List Acct) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp
    have hhd : f hd ≤ g hd := h hd (by simp)
    have htl : ∀ a ∈ tl, f a ≤ g a := fun a ha => h a (by simp [ha])
    have iht := ih htl
    omega

theorem aux_up_accts2 (L : Legacy) : (upgrade L).accts = L.accts := by
  unfold upgrade; simp

theorem aux_up_spd_supply2 (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_blk_supply (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_idx_supply (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem my_test_thm : 1 + 1 = 2 := by rfl

theorem my_test2 : ∀ (s : St), s = s := by intro s; rfl

theorem td0_updSup_some2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex subChecked
  simp only [h, ite_true]
  split
  · simp
  · split
    · simp
    · simp

theorem td0_potentialTo_of_noPosition : ∀ (s : St) (who : Account), NoPosition s who →
    td0_potentialTo s who = doubleScale * s.creditedTo who := by
  intro s who h
  unfold NoPosition at h
  unfold td0_potentialTo td0_pendingTo td0_unindexedTo td0_pendingAcct St.creditedTo
  obtain ⟨hsup, hbor⟩ := h
  have hsup' : (s.acct who).supply = 0 := hsup
  have hbor' : (s.acct who).borrow = 0 := hbor
  rw [hsup', hbor']
  simp

theorem td0_updSup_eq (s : St) :
    updateCompSupplyIndex s =
      match subChecked s.blockNumber s.supplyState.block with
      | none => none
      | some d =>
        if d > 0 ∧ s.supplyState.speed > 0 then
          let tot := totalSupply s
          let r := if tot > 0 then (d * s.supplyState.speed) * doubleScale / tot else 0
          some { s with supplyState :=
            { s.supplyState with index := s.supplyState.index + r, block := s.blockNumber } }
        else if d > 0 then
          some { s with supplyState := { s.supplyState with block := s.blockNumber } }
        else some s := by
  unfold updateCompSupplyIndex totalSupply fraction
  rfl

theorem td0_subChecked_eq (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]

def check_modify : Nat := 1
#check @List.modify
#check @List.getD

def dummyY : Nat := 2

theorem chkLen (l : List Acct) (n : Nat) (f : Acct → Acct) : (l.modify n f).length = l.length := by simp

theorem plan0_env_inv (sp : Nat × Nat) (s : St) (k x : Nat) :
    td0_Inv sp s →
    td0_Inv sp { s with blockNumber := s.blockNumber + k } ∧
    td0_Inv sp { s with reserve := s.reserve + x } := by
  intro h
  unfold td0_Inv Consistent at *
  obtain ⟨⟨hsup, hbor, haccts⟩, hsp1, hsp2⟩ := h
  constructor
  · refine ⟨⟨?_, ?_, ?_⟩, hsp1, hsp2⟩ <;> simp_all <;> omega
  · refine ⟨⟨?_, ?_, ?_⟩, hsp1, hsp2⟩ <;> simp_all

theorem plan2_potentialTo_claim_aux_test (sp : Nat × Nat) (s : St) (a who : Account) (hInv : td0_Inv sp s) :
    emittedBy sp (.claim a) = 0 := by simp [emittedBy]

theorem plan2_potentialTo_advance (sp : Nat × Nat) (s : St) (k : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.advance k)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.advance k) := by
  intro hInv
  obtain ⟨hCons, hSup, hBor⟩ := hInv
  have hSB : s.supplyState.block ≤ s.blockNumber := hCons.1
  have hBB : s.borrowState.block ≤ s.blockNumber := hCons.2.1
  have hexec : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := by
    simp [exec]
  have hemit : emittedBy sp (.advance k) = k * (sp.1 + sp.2) := by simp [emittedBy]
  rw [hexec, hemit]
  have hsup_eq : s.supplyState.speed = sp.1 := hSup
  have hbor_eq : s.borrowState.speed = sp.2 := hBor
  have hSB' : s.blockNumber + k - s.supplyState.block = (s.blockNumber - s.supplyState.block) + k := by
    omega
  have hBB' : s.blockNumber + k - s.borrowState.block = (s.blockNumber - s.borrowState.block) + k := by
    omega
  have h1 : ((s.blockNumber - s.supplyState.block) + k) * sp.1 =
      (s.blockNumber - s.supplyState.block) * sp.1 + k * sp.1 := Nat.add_mul _ _ _
  have h2 : ((s.blockNumber - s.borrowState.block) + k) * sp.2 =
      (s.blockNumber - s.borrowState.block) * sp.2 + k * sp.2 := Nat.add_mul _ _ _
  have hdist : k * (sp.1 + sp.2) = k * sp.1 + k * sp.2 := Nat.mul_add k sp.1 sp.2
  unfold td0_potentialTo td0_pendingTo td0_unindexedTo St.creditedTo td0_pendingAcct St.acct
  simp only []
  rw [hSB', hBB', hsup_eq, hbor_eq, h1, h2]
  by_cases hs : 0 < (s.accts.getD who noAcct).supply
  · by_cases hb : 0 < (s.accts.getD who noAcct).borrow
    · simp only [hs, hb, ↓reduceIte]
      have e1 : doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 + k * sp.1 +
          ((s.blockNumber - s.borrowState.block) * sp.2 + k * sp.2)) =
        doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 +
          (s.blockNumber - s.borrowState.block) * sp.2) +
        (doubleScale * (k * sp.1) + doubleScale * (k * sp.2)) := by
        simp only [Nat.mul_add]
        ac_rfl
      have e2 : doubleScale * (k * (sp.1 + sp.2)) =
        doubleScale * (k * sp.1) + doubleScale * (k * sp.2) := by
        rw [hdist, Nat.mul_add]
      rw [e1, e2]
      omega
    · simp only [hs, show ¬ (0 < (s.accts.getD who noAcct).borrow) from hb, ↓reduceIte]
      have e1 : doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 + k * sp.1 + 0) =
        doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 + 0) +
        doubleScale * (k * sp.1) := by
        simp only [Nat.mul_add]
        ac_rfl
      have e2 : doubleScale * (k * (sp.1 + sp.2)) =
        doubleScale * (k * sp.1) + doubleScale * (k * sp.2) := by
        rw [hdist, Nat.mul_add]
      rw [e1, e2]
      omega
  · by_cases hb : 0 < (s.accts.getD who noAcct).borrow
    · simp only [show ¬ (0 < (s.accts.getD who noAcct).supply) from hs, hb, ↓reduceIte]
      have e1 : doubleScale * (0 + ((s.blockNumber - s.borrowState.block) * sp.2 + k * sp.2)) =
        doubleScale * (0 + (s.blockNumber - s.borrowState.block) * sp.2) +
        doubleScale * (k * sp.2) := by
        simp only [Nat.mul_add]
        ac_rfl
      have e2 : doubleScale * (k * (sp.1 + sp.2)) =
        doubleScale * (k * sp.1) + doubleScale * (k * sp.2) := by
        rw [hdist, Nat.mul_add]
      rw [e1, e2]
      omega
    · simp only [show ¬ (0 < (s.accts.getD who noAcct).supply) from hs,
        show ¬ (0 < (s.accts.getD who noAcct).borrow) from hb, ↓reduceIte]
      omega

theorem plan2_potentialTo_drip (sp : Nat × Nat) (s : St) (x : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.drip x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.drip x) := by
  intro _
  have h1 : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := by
    simp [exec]
  have h2 : emittedBy sp (.drip x) = 0 := by simp [emittedBy]
  rw [h1, h2, Nat.mul_zero, Nat.add_zero]
  unfold td0_potentialTo td0_pendingTo td0_unindexedTo St.creditedTo td0_pendingAcct St.acct
  simp

theorem plan4_owed_eq (L : Legacy) :
    L.owed = (L.accts.map L.pendingScaled).sum / doubleScale +
      (L.unindexedSupply + L.unindexedBorrow) := by
  unfold Legacy.owed
  rw [Nat.add_assoc]

theorem plan4_credited_le_potential (s : St) :
    doubleScale * s.credited ≤ td0_potential s := by
  unfold td0_potential
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem chk_omega_test (a b : Nat) (h : ¬ a ≤ b) : b < a := by
  omega
#check @Nat.mul_le_mul_left
#check @Nat.le_of_mul_le_mul_left
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.succ_le_of_lt
#check @Classical.byContradiction

theorem plan5_lt_div_mul_add (s : Nat) :
    s < doubleScale * (s / doubleScale) + doubleScale := by
  have hpos : 0 < doubleScale := by unfold doubleScale; exact Nat.pow_pos (by decide)
  have hmod : s % doubleScale < doubleScale := Nat.mod_lt _ hpos
  have hdiv : doubleScale * (s / doubleScale) + s % doubleScale = s := Nat.div_add_mod s doubleScale
  omega

theorem plan5_mul_target_succ (c0 s u e : Nat) :
    doubleScale * (c0 + (s / doubleScale + u) + e + 1) =
      doubleScale * c0 + doubleScale * (s / doubleScale) +
        doubleScale * u + doubleScale * e + doubleScale := by
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem plan5_mul_mono (d a b : Nat) (h : a ≤ b) :
    d * a ≤ d * b := by
  exact Nat.mul_le_mul_left d h

theorem plan5_test_aux (s : Nat) : s < doubleScale * (s / doubleScale) + doubleScale := by
  have hpos : 0 < doubleScale := by unfold doubleScale; exact Nat.pow_pos (by decide)
  have hmod : s % doubleScale < doubleScale := Nat.mod_lt _ hpos
  have hdiv : doubleScale * (s / doubleScale) + s % doubleScale = s := Nat.div_add_mod s doubleScale
  omega

theorem plan4_bound_of_scaled_le (c c0 s u e : Nat) :
    doubleScale * c ≤
        doubleScale * c0 + s + doubleScale * u + doubleScale * e →
    c ≤ c0 + (s / doubleScale + u) + e := by
  intro h
  have hlt := plan5_lt_div_mul_add s
  have hexp := plan5_mul_target_succ c0 s u e
  by_cases hc : c ≤ c0 + (s / doubleScale + u) + e
  · exact hc
  · exfalso
    have hsucc : c0 + (s / doubleScale + u) + e + 1 ≤ c := by omega
    have hmono := plan5_mul_mono doubleScale _ _ hsucc
    omega

theorem td0_rewards_conclude : ∀ (L : Legacy) (ops : List Op),
    td0_potential (run comptroller (upgrade L) ops) ≤
        td0_potential (upgrade L) + doubleScale * emitted (L.compSpeed, L.compSpeed) ops →
    td0_potential (upgrade L) ≤
        doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
          doubleScale * (L.unindexedSupply + L.unindexedBorrow) →
    (run comptroller (upgrade L) ops).credited ≤
      (upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops := by
  intro L ops h1 h2
  have hlow := plan4_credited_le_potential (run comptroller (upgrade L) ops)
  have htrans :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        td0_potential (upgrade L) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.le_trans hlow h1
  have hstep :
      td0_potential (upgrade L) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops ≤
        (doubleScale * (upgrade L).credited +
            (L.accts.map L.pendingScaled).sum +
            doubleScale * (L.unindexedSupply + L.unindexedBorrow)) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.add_le_add_right h2 _
  have hcomb :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        doubleScale * (upgrade L).credited +
          (L.accts.map L.pendingScaled).sum +
          doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.le_trans htrans hstep
  have hbound := plan4_bound_of_scaled_le _ _ _ _ _ hcomb
  rw [plan4_owed_eq L]
  exact hbound

theorem tmp_getD_unfold_test (l : List Acct) (n : Nat) : l.getD n noAcct = (l[n]?).getD noAcct := by rfl

theorem tmp_hUp_test (L : Legacy) :
    (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
  unfold upgrade initSide
  simp only
  split
  · rfl
  · rfl

theorem tmp_pos_test : 0 < compInitialIndex := by
  unfold compInitialIndex
  omega

theorem plan6_supply_unindexed_le (L : Legacy) (a : Acct) :
    (if 0 < a.supply then
       ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
         (upgrade L).supplyState.speed
     else 0) ≤
      (if 0 < a.supply then L.unindexedSupply else 0) := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hsup : (upgrade L).supplyState = initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ := rfl
  by_cases hpos : 0 < a.supply
  · have hifL : (if 0 < a.supply then ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed else 0)
      = ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed := by
      simp [hpos]
    have hifR : (if 0 < a.supply then L.unindexedSupply else 0) = L.unindexedSupply := by
      simp [hpos]
    rw [hifL, hifR, hbn, hsup]
    by_cases hidx : L.supplyIndex = 0
    · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.blockNumber := by
        unfold initSide
        simp only [hidx, if_true]
      rw [hblock, Nat.sub_self, Nat.zero_mul]
      exact Nat.zero_le _
    · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.supplyBlock := by
        unfold initSide
        simp only [hidx, if_false]
      have hspeed : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).speed = L.compSpeed := by
        unfold initSide
        simp only [hidx, if_false]
      rw [hblock, hspeed]
      exact Nat.le_refl _
  · have hifL : (if 0 < a.supply then ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed else 0) = 0 := by
      simp [hpos]
    have hifR : (if 0 < a.supply then L.unindexedSupply else 0) = 0 := by
      simp [hpos]
    rw [hifL, hifR]
    exact Nat.le_refl _

theorem plan6_borrow_unindexed_le (L : Legacy) (a : Acct) :
    (if 0 < a.borrow then
       ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
         (upgrade L).borrowState.speed
     else 0) ≤
      (if 0 < a.borrow then L.unindexedBorrow else 0) := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hbor : (upgrade L).borrowState = initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ := rfl
  by_cases hpos : 0 < a.borrow
  · have hifL : (if 0 < a.borrow then ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed else 0)
      = ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed := by
      simp [hpos]
    have hifR : (if 0 < a.borrow then L.unindexedBorrow else 0) = L.unindexedBorrow := by
      simp [hpos]
    rw [hifL, hifR, hbn, hbor]
    by_cases hidx : L.borrowIndex = 0
    · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.blockNumber := by
        unfold initSide
        simp only [hidx, if_true]
      rw [hblock, Nat.sub_self, Nat.zero_mul]
      exact Nat.zero_le _
    · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.borrowBlock := by
        unfold initSide
        simp only [hidx, if_false]
      have hspeed : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).speed = L.compSpeed := by
        unfold initSide
        simp only [hidx, if_false]
      rw [hblock, hspeed]
      exact Nat.le_refl _
  · have hifL : (if 0 < a.borrow then ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed else 0) = 0 := by
      simp [hpos]
    have hifR : (if 0 < a.borrow then L.unindexedBorrow else 0) = 0 := by
      simp [hpos]
    rw [hifL, hifR]
    exact Nat.le_refl _

theorem plan7_noAcct_borrowerIndex : noAcct.borrowerIndex = 0 := rfl

theorem plan7_noAcct_supplierIndex : noAcct.supplierIndex = 0 := rfl

theorem plan7_tmp_proof (l : List Acct) (who : Nat) :
    l.getD who noAcct ∈ l ∨ l.getD who noAcct = noAcct := by
  induction l generalizing who with
  | nil =>
    simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      exact Or.inl (List.Mem.head _)
    | succ n =>
      simp only [List.getD_cons_succ]
      rcases ih n with h | h
      · exact Or.inl (List.Mem.tail _ h)
      · exact Or.inr h

theorem plan7_getD_mem_or_default (l : List Acct) (who : Nat) :
    l.getD who noAcct ∈ l ∨ l.getD who noAcct = noAcct := by
  induction l generalizing who with
  | nil =>
    simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      exact Or.inl (List.Mem.head _)
    | succ n =>
      simp only [List.getD_cons_succ]
      rcases ih n with h | h
      · exact Or.inl (List.Mem.tail _ h)
      · exact Or.inr h

theorem plan7_wellformed_apply (L : Legacy) (a : Acct)
    (hWF : L.WellFormed) (ha : a ∈ L.accts) :
    a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex := by
  unfold Legacy.WellFormed at hWF
  exact hWF.2.2.2.2.2.2 _ ha

theorem plan6_acct_bounds (L : Legacy) (who : Account) (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  cases plan7_getD_mem_or_default L.accts who with
  | inl hmem =>
    exact plan7_wellformed_apply L (L.accts.getD who noAcct) hWF hmem
  | inr heq =>
    rw [heq]
    exact ⟨by rw [plan7_noAcct_supplierIndex]; exact Nat.zero_le _,
           by rw [plan7_noAcct_borrowerIndex]; exact Nat.zero_le _⟩

theorem plan9_combine (L : Legacy)
    (hp : td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum)
    (hu : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow) :
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  show doubleScale * (upgrade L).credited + td0_pending (upgrade L) +
      doubleScale * td0_unindexed (upgrade L) ≤ _
  exact Nat.add_le_add (Nat.add_le_add_left hp _) (Nat.mul_le_mul_left _ hu)

theorem plan9_pending_sum_le (L : Legacy)
    (h : ∀ a ∈ L.accts, td0_pendingAcct (upgrade L) a ≤ L.pendingScaled a) :
    td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
  unfold td0_pending
  rw [aux_up_accts2]
  exact aux_sum_le_sum2 _ _ _ h

theorem plan9_supply_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed ≤
      L.unindexedSupply := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hsup : (upgrade L).supplyState = initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ := rfl
  rw [hbn, hsup]
  by_cases hidx : L.supplyIndex = 0
  · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.blockNumber := by
      unfold initSide
      simp only [hidx, if_true]
    rw [hblock, Nat.sub_self, Nat.zero_mul]
    exact Nat.zero_le _
  · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.supplyBlock := by
      unfold initSide
      simp only [hidx, if_false]
    have hspeed : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).speed = L.compSpeed := by
      unfold initSide
      simp only [hidx, if_false]
    rw [hblock, hspeed]
    unfold Legacy.unindexedSupply
    exact Nat.le_refl _

theorem plan9_borrow_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed ≤
      L.unindexedBorrow := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hbor : (upgrade L).borrowState = initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ := rfl
  rw [hbn, hbor]
  by_cases hidx : L.borrowIndex = 0
  · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.blockNumber := by
      unfold initSide
      simp only [hidx, if_true]
    rw [hblock, Nat.sub_self, Nat.zero_mul]
    exact Nat.zero_le _
  · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.borrowBlock := by
      unfold initSide
      simp only [hidx, if_false]
    have hspeed : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).speed = L.compSpeed := by
      unfold initSide
      simp only [hidx, if_false]
    rw [hblock, hspeed]
    unfold Legacy.unindexedBorrow
    exact Nat.le_refl _

theorem plan10_upgrade_supply_index (L : Legacy) :
    (upgrade L).supplyState.index =
      if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem plan10_accrualStart_zero (st idx : Nat) :
    accrualStart 0 idx =
        (if compInitialIndex ≤ idx then compInitialIndex else 0) ∧
      legacyStart st 0 = st := by
  constructor
  · unfold accrualStart; simp
  · unfold legacyStart; simp

theorem plan10_accrualStart_pos {r : Nat} (hr : r ≠ 0) (st idx : Nat) :
    accrualStart r idx = r ∧ legacyStart st r = r := by
  unfold accrualStart legacyStart
  simp [hr]

theorem plan10_mul_le_mono (n x y : Nat) (h : x ≤ y) :
    n * x ≤ n * y := by exact Nat.mul_le_mul_left n h

theorem plan9_supply_pending_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  have hU := plan10_upgrade_supply_index L
  apply plan10_mul_le_mono
  by_cases hr : a.supplierIndex = 0
  · have hz :=
      plan10_accrualStart_zero L.supplyStart (upgrade L).supplyState.index
    rw [hr, hz.1, hz.2, hU]
    by_cases hi : L.supplyIndex = 0
    · rw [if_pos hi, if_pos (Nat.le_refl compInitialIndex)]
      cases hstart with
      | inl hst => rw [hst]; omega
      | inr hst => rw [hst]; omega
    · rw [if_neg hi]
      by_cases hc : compInitialIndex ≤ L.supplyIndex
      · rw [if_pos hc]
        cases hstart with
        | inl hst => rw [hst]; omega
        | inr hst => rw [hst]; omega
      · rw [if_neg hc]
        cases hstart with
        | inl hst => rw [hst]; omega
        | inr hst => rw [hst]; omega
  · have hp :=
      plan10_accrualStart_pos hr L.supplyStart (upgrade L).supplyState.index
    rw [hp.1, hp.2, hU]
    by_cases hi : L.supplyIndex = 0
    · rw [if_pos hi]; omega
    · rw [if_neg hi]; omega

theorem plan12_bind_some {α β : Type} (m : Option α) (f : α → Option β) (y : β) :
    m.bind f = some y → ∃ x, m = some x ∧ f x = some y := by
  intro h
  cases m with
  | none => simp at h
  | some x => exact ⟨x, rfl, h⟩

theorem snippet_test_by_cases (s : St) : s.supplyState.block ≤ s.blockNumber ∨ ¬ s.supplyState.block ≤ s.blockNumber := by
  by_cases h : s.supplyState.block ≤ s.blockNumber
  · exact Or.inl h
  · exact Or.inr h

theorem plan12_combine_supply (s t s' : St) (who : Account) :
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } →
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        supplierIndex := t.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex t.supplyState.index) t.supplyState.index } } →
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  intro ht hs'
  subst ht
  subst hs'
  rfl

theorem plan13_update_borrow_spec_aux1 (s : St) :
    accrueSide s.borrowState s.blockNumber (totalBorrows s) =
    if 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s then
      { s.borrowState with index := s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s, block := s.blockNumber }
    else { s.borrowState with block := s.blockNumber } := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem plan13_distribute_borrow_spec_aux_check :
    ∀ (t : St) (who : Account),
    (if (t.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t.borrowState.index
      then compInitialIndex else (t.acct who).borrowerIndex) =
    accrualStart (t.acct who).borrowerIndex t.borrowState.index := by
  intro t who
  unfold accrualStart St.acct
  by_cases h : (t.accts.getD who noAcct).borrowerIndex = 0
  · simp only [h, ↓reduceIte]
    by_cases h2 : compInitialIndex ≤ t.borrowState.index <;> simp [h2, h]
  · simp only [h, ↓reduceIte]
    have : ¬ ((t.accts.getD who noAcct).borrowerIndex = 0 ∧
      compInitialIndex ≤ t.borrowState.index) := fun hh => h hh.1
    simp [this]

theorem plan13_start_le_of_update (s t : St) (who : Account) :
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
    accrualStart (t.acct who).borrowerIndex t.borrowState.index ≤ t.borrowState.index →
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  intro ht hle
  subst ht
  exact hle

theorem plan13_combine_borrow (s t s' : St) (who : Account) :
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        borrowerIndex := t.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex t.borrowState.index) t.borrowState.index } } →
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  intro ht hs'
  subst ht
  subst hs'
  rfl

theorem plan14_block_le_of_update_aux_tmp : ∀ (s : St) (t : St),
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber := by
  intro s t h
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem plan15_updateSupply_pres_aux_tmp2 (s : St) :
    Consistent s →
    ∃ t, updateCompSupplyIndex s = some t ∧ Consistent t := by
  intro hC
  obtain ⟨hSup, hBor, hIdx⟩ := hC
  have hsub : subChecked s.blockNumber s.supplyState.block =
    some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [hSup]
  unfold updateCompSupplyIndex
  rw [hsub]
  by_cases h1 : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · simp only [h1, ↓reduceIte]
    refine ⟨_, rfl, ?_, hBor, ?_⟩
    · simp
    · intro a ha
      obtain ⟨hs, hb⟩ := hIdx a ha
      simp only
      constructor
      · apply Nat.le_trans hs
        apply Nat.le_add_right
      · exact hb
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (s.blockNumber - s.supplyState.block) > 0
    · simp only [h2, ↓reduceIte]
      refine ⟨_, rfl, ?_, hBor, ?_⟩
      · simp
      · intro a ha
        obtain ⟨hs, hb⟩ := hIdx a ha
        simp only
        constructor
        · exact hs
        · exact hb
    · have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have heq : s.blockNumber = s.supplyState.block := by omega
      simp only [h2, ↓reduceIte]
      refine ⟨s, rfl, ?_, ?_, ?_⟩
      · omega
      · exact hBor
      · exact hIdx

theorem plan15_updateSupply_pres (s : St) :
    Consistent s →
    ∃ t, updateCompSupplyIndex s = some t ∧ Consistent t :=
  fun h => plan15_updateSupply_pres_aux_tmp2 s h

theorem plan15_updateBorrow_pres (s : St) :
    Consistent s →
    ∃ t, updateCompBorrowIndex s = some t ∧ Consistent t := by
  intro hC
  obtain ⟨hSup, hBor, hIdx⟩ := hC
  have hsub : subChecked s.blockNumber s.borrowState.block =
    some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hBor]
  unfold updateCompBorrowIndex
  rw [hsub]
  by_cases h1 : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · simp only [h1, ↓reduceIte]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · exact hSup
    · simp
    · intro a ha
      obtain ⟨hs, hb⟩ := hIdx a ha
      simp only
      constructor
      · exact hs
      · apply Nat.le_trans hb
        apply Nat.le_add_right
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (s.blockNumber - s.borrowState.block) > 0
    · simp only [h2, ↓reduceIte]
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · exact hSup
      · simp
      · intro a ha
        obtain ⟨hs, hb⟩ := hIdx a ha
        simp only
        constructor
        · exact hs
        · exact hb
    · have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have heq : s.blockNumber = s.borrowState.block := by omega
      simp only [h2, ↓reduceIte]
      refine ⟨s, rfl, ?_, ?_, ?_⟩
      · exact hSup
      · omega
      · exact hIdx

theorem plan16_claimed_intro (s : St) (who : Account) (m1 m2 s' : St) :
    BorrowDistributed s who m1 → SupplyDistributed m1 who m2 →
    s' = grant m2 who → Claimed s who s' := by
  intro hb hs hg
  unfold Claimed
  exact ⟨m1, m2, hb, hs, hg⟩

theorem plan16_claim_decomp_auxcheck3 : ∀ (s : St) (who : Account),
    comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) := by
  intro s who; rfl

theorem plan16_claim_decomp_auxcheck2 : ∀ (s : St) (who : Account),
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) := by
  intro s who; rfl

theorem plan16_claim_decomp_auxcheck : ∀ (s : St) (who : Account),
    comptroller s (.claim who) = claimComp s who := by
  intro s who; rfl

def td0_unindexedOf (L : Legacy) (who : Account) : Nat :=
  (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
  (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)

def td0_pendingOf (L : Legacy) (who : Account) : Nat :=
  L.pendingScaled (L.accts.getD who noAcct)

def td0_pendingScaledAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

theorem td0_initSide_index_ge2 (now : Nat) (sd : Side) :
    sd.index ≤ (initSide now sd).index := by
  unfold initSide
  split
  · next h =>
    have h0 : sd.index = 0 := h
    omega
  · exact Nat.le_refl _

theorem td0_initSide_block_le2 (now : Nat) (sd : Side) (hblk : sd.block ≤ now) :
    (initSide now sd).block ≤ now := by
  unfold initSide
  split
  · simp
  · exact hblk

theorem td0_initSide_speed2 (now : Nat) (sd : Side) :
    (initSide now sd).speed = sd.speed := by
  unfold initSide
  split
  · rfl
  · rfl

theorem td0_probe_len2 (l : List Acct) (n : Nat) (f : Acct → Acct) :
    (l.modify n f).length = l.length := by simp
#check @List.modify

theorem td0_probe_print : True := by trivial
#print List.modify
#print St.withAcct
#print Consistent
#print SupplyDistributed

theorem plan0_accrueSide_props (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index ∧
      (accrueSide sd now total).block = now ∧
      (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem my_len_thm (l : List Acct) (n : Nat) (f : Acct → Acct) : (l.modify n f).length = l.length := by simp

theorem my_check_modify_eq : (List.modify ([] : List Acct) 0 id = []) := by rfl

theorem my_probe1 : True := trivial

theorem plan0_withAcct_inv (sp : Nat × Nat) (s : St) (who : Account) (f : Acct → Acct) (hsi : ∀ a, (f a).supplierIndex = a.supplierIndex) (hbi : ∀ a, (f a).borrowerIndex = a.borrowerIndex) : td0_Inv sp s → td0_Inv sp (s.withAcct who f) := by
  intro h
  unfold td0_Inv at h ⊢
  unfold St.withAcct
  simp only at ⊢
  obtain ⟨hc, hsp1, hsp2⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hb1, hb2, hmem⟩ := hc
  refine ⟨⟨?_, ?_, ?_⟩, hsp1, hsp2⟩
  · exact hb1
  · exact hb2
  · intro a ha
    apply ProofForgeFin.DeFi.Rewards.forall_mem_modify (l := s.accts) (i := who) (f := f) _ _ a ha
    · intro b hb
      exact hmem b hb
    · intro b hb
      have h1 : (f b).supplierIndex = b.supplierIndex := hsi b
      have h2 : (f b).borrowerIndex = b.borrowerIndex := hbi b
      obtain ⟨hs, hbo⟩ := hmem b hb
      rw [h1, h2]
      exact ⟨hs, hbo⟩

theorem tmp_struct_proj (s : St) (X : Side) :
    ({ s with supplyState := X } : St).supplyState.speed = X.speed := by
  simp

theorem plan0_borrowDistributed_inv (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → BorrowDistributed s who s' → td0_Inv sp s' := by
  intro hInv hDist
  unfold td0_Inv at hInv ⊢
  unfold BorrowDistributed at hDist
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hblk, hle, heq⟩ := hDist
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hprops := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hIdxLe, hBlkEq, hSpdEq⟩ := hprops
  subst heq
  simp only at ⊢
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hsb
  · omega
  · intro a ha
    apply ProofForgeFin.DeFi.Rewards.forall_mem_modify (l := s.accts) (i := who) _ _ a ha
    · intro b hb
      obtain ⟨hs, hbo⟩ := hmem b hb
      exact ⟨hs, Nat.le_trans hbo hIdxLe⟩
    · intro b hb
      obtain ⟨hs, hbo⟩ := hmem b hb
      refine ⟨?_, ?_⟩
      · exact hs
      · exact Nat.le_refl _
  · exact hsp1
  · omega

theorem plan0_speedsSet_inv_aux1 (sp : Nat × Nat) (s : St) (a b : Nat)
    (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' → td0_Inv (a, b) s' := by
  intro hInv hSS
  unfold td0_Inv at hInv ⊢
  unfold SpeedsSet at hSS
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hsupNe, hborNe, heq⟩ := hSS
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hsupProps := plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  obtain ⟨hsupIdxLe, hsupBlkEq, hsupSpdEq⟩ := hsupProps
  have hborProps := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hborIdxLe, hborBlkEq, hborSpdEq⟩ := hborProps
  subst heq
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsb]
    · simp [h, hsupBlkEq]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hbb]
    · simp [h, hborBlkEq]
  · intro a0 ha0
    simp only at ha0
    obtain ⟨hs0, hb0⟩ := hmem a0 ha0
    have hsupLe : s.supplyState.index ≤ (if s.supplyState.speed = a then s.supplyState else {accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a}).index := by
      by_cases h : s.supplyState.speed = a
      · simp [h]
      · simp [h, hsupIdxLe]
    have hborLe : s.borrowState.index ≤ (if s.borrowState.speed = b then s.borrowState else {accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b}).index := by
      by_cases h : s.borrowState.speed = b
      · simp [h]
      · simp [h, hborIdxLe]
    simp only
    exact ⟨Nat.le_trans hs0 hsupLe, Nat.le_trans hb0 hborLe⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsp1]
    · simp [h]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hsp2]
    · simp [h]

theorem plan0_speedsSet_inv_direct (sp : Nat × Nat) (s : St) (a b : Nat)
    (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' → td0_Inv (a, b) s' := by
  intro hInv hSS
  unfold td0_Inv at hInv ⊢
  unfold SpeedsSet at hSS
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hsupNe, hborNe, heq⟩ := hSS
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hsupProps := plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  obtain ⟨hsupIdxLe, hsupBlkEq, hsupSpdEq⟩ := hsupProps
  have hborProps := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hborIdxLe, hborBlkEq, hborSpdEq⟩ := hborProps
  subst heq
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsb]
    · simp [h, hsupBlkEq]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hbb]
    · simp [h, hborBlkEq]
  · intro a0 ha0
    simp only at ha0
    obtain ⟨hs0, hb0⟩ := hmem a0 ha0
    have hsupLe : s.supplyState.index ≤ (if s.supplyState.speed = a then s.supplyState else {accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a}).index := by
      by_cases h : s.supplyState.speed = a
      · simp [h]
      · simp [h, hsupIdxLe]
    have hborLe : s.borrowState.index ≤ (if s.borrowState.speed = b then s.borrowState else {accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b}).index := by
      by_cases h : s.borrowState.speed = b
      · simp [h]
      · simp [h, hborIdxLe]
    simp only
    exact ⟨Nat.le_trans hs0 hsupLe, Nat.le_trans hb0 hborLe⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsp1]
    · simp [h]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hsp2]
    · simp [h]

theorem plan0_speedsSet_inv (sp : Nat × Nat) (s : St) (a b : Nat)
    (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' → td0_Inv (a, b) s' := by
  intro hInv hSS
  unfold td0_Inv at hInv ⊢
  unfold SpeedsSet at hSS
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hsupNe, hborNe, heq⟩ := hSS
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hsupProps := plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  obtain ⟨hsupIdxLe, hsupBlkEq, hsupSpdEq⟩ := hsupProps
  have hborProps := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hborIdxLe, hborBlkEq, hborSpdEq⟩ := hborProps
  subst heq
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsb]
    · simp [h, hsupBlkEq]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hbb]
    · simp [h, hborBlkEq]
  · intro a0 ha0
    simp only at ha0
    obtain ⟨hs0, hb0⟩ := hmem a0 ha0
    have hsupLe : s.supplyState.index ≤ (if s.supplyState.speed = a then s.supplyState else {accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a}).index := by
      by_cases h : s.supplyState.speed = a
      · simp [h]
      · simp [h, hsupIdxLe]
    have hborLe : s.borrowState.index ≤ (if s.borrowState.speed = b then s.borrowState else {accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b}).index := by
      by_cases h : s.borrowState.speed = b
      · simp [h]
      · simp [h, hborIdxLe]
    simp only
    exact ⟨Nat.le_trans hs0 hsupLe, Nat.le_trans hb0 hborLe⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsp1]
    · simp [h]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hsp2]
    · simp [h]

theorem td0_exec_inv_aux_check : True := trivial

theorem td0_drip_inv_aux (sp : Nat × Nat) (s : St) (x : Nat) :
    td0_Inv sp s → td0_Inv sp ({ s with reserve := s.reserve + x }) := by
  intro h
  unfold td0_Inv at h ⊢
  obtain ⟨hc, h1, h2⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hb1, hb2, hmem⟩ := hc
  simp only at ⊢
  exact ⟨⟨hb1, hb2, hmem⟩, h1, h2⟩

theorem td0_advance_inv_aux (sp : Nat × Nat) (s : St) (k : Nat) :
    td0_Inv sp s → td0_Inv sp ({ s with blockNumber := s.blockNumber + k }) := by
  intro h
  unfold td0_Inv at h ⊢
  obtain ⟨hc, h1, h2⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hb1, hb2, hmem⟩ := hc
  simp only at ⊢
  refine ⟨⟨by omega, by omega, hmem⟩, h1, h2⟩

theorem td0_mint_some_eq (s : St) (who x : Nat) (s' : St) (hwho : who < s.accts.length)
    (hhook : comptroller s (.supplyHook who) = some s') :
    exec comptroller s (Op.mint who x) = s'.withAcct who fun a => { a with supply := a.supply + x } := by
  unfold exec
  simp [hwho, hhook]

theorem td0_mint_none_eq (s : St) (who x : Nat) (hwho : who < s.accts.length)
    (hhook : comptroller s (.supplyHook who) = none) :
    exec comptroller s (Op.mint who x) = s := by
  unfold exec
  simp [hwho, hhook]

theorem td0_probe_exec2 (s : St) (who x : Nat) (s' : St)
    (hwho : who < s.accts.length)
    (hhook : comptroller s (.supplyHook who) = some s') :
    exec comptroller s (Op.mint who x) = s'.withAcct who fun a => { a with supply := a.supply + x } := by
  unfold exec
  simp [hwho, hhook]

theorem td0_probe_repay (s : St) (who x : Nat) (s' : St)
    (hhook : comptroller s (.borrowHook who) = some s')
    (hle : ¬ x ≤ (s'.acct who).borrow) :
    (match comptroller s (.borrowHook who) with
      | some s'' => if x ≤ (s''.acct who).borrow then s''.withAcct who fun a => { a with borrow := a.borrow - x } else s
      | none => s) = s := by
  simp [hhook, hle]

theorem td0_probe_repay_exec (s : St) (who x : Nat) (s' : St)
    (hwho : who < s.accts.length)
    (hhook : comptroller s (.borrowHook who) = some s')
    (hle : ¬ x ≤ (s'.acct who).borrow) :
    exec comptroller s (Op.repay who x) = s := by
  unfold exec
  simp [hwho, hhook, hle]

theorem td0_creditedTo_le_potential (s : St) (who : Account) :
    doubleScale * s.creditedTo who ≤ td0_potentialTo s who := by
  unfold td0_potentialTo
  omega

theorem snippet_probe_rewards_defs : True := trivial
#check @ProofForgeFin.DeFi.Rewards.settle_le
#check @ProofForgeFin.DeFi.Rewards.ite_accrue_le

def probe_defs_eq : Bool := true
#check @ProofForgeFin.DeFi.Rewards.pending
#check @ProofForgeFin.DeFi.Rewards.credit
#check @ProofForgeFin.DeFi.Rewards.firstStart
#check @ProofForgeFin.DeFi.Rewards.p62Start
#check @ProofForgeFin.DeFi.Rewards.effStart

theorem probe_pending_defs2 : True := by
  have h1 := ProofForgeFin.DeFi.Rewards.credit_mul_le (one := 5) (units := 3) (start := 1) (index := 10)
  have h2 := ProofForgeFin.DeFi.Rewards.settle_le (one := 5) (units := 3) (p := 1) (q := 2) (p' := 10) (index := 10) (r := 0) (r' := 1)
  trivial
#check @ProofForgeFin.DeFi.Rewards.pending
#check @ProofForgeFin.DeFi.Rewards.credit
#check @List.modify
#check @List.getD

theorem probe_defs_bridge2a : ProofForgeFin.DeFi.Rewards.credit 100 5 2 10 = 5 * (10 - 2) / 100 := by rfl

theorem probe_defs_bridge1a : ProofForgeFin.DeFi.Rewards.pending 5 2 10 = 5 * (10 - 2) := by rfl

theorem tmp_check_modify_def : True := by
  trivial
#check @List.modify
#check @List.getD

theorem tmp_print_modify : True := trivial
#check @List.modify
#check @List.getD
#print axioms List.modify

theorem aux_unfold_modify : True := trivial
#check List.modify
#reduce List.modify [1,2,3] 1 id

theorem tmp_explore_modify_eq2 (a : Nat) (as : List Nat) (n : Nat) (f : Nat → Nat) :
    List.modify (a :: as) (n+1) f = a :: List.modify as n f := by rfl

theorem tmp_explore_modify_eq : List.modify (a :: as : List Nat) 0 f = f a :: as := by rfl

theorem tmp_supply_change_probe2 (s : St) (tgt : Account) (f : Acct → Acct) :
    (s.withAcct tgt f).blockNumber = s.blockNumber := by rfl
#check @List.modify
#check @List.getD

theorem tmp_supply_change_probe1 (s : St) (tgt : Account) (f : Acct → Acct) :
    (s.withAcct tgt f).supplyState = s.supplyState := by rfl

theorem tmp_list_probe2 : True := trivial
#check @List.modify
#check @List.getElem_modify
#check @List.getD
#check @List.length_modify

theorem tmp_ne_lemma3 (l : List Acct) (tgt who : Nat) (f : Acct → Acct) (h : tgt ≠ who) :
    (l.modify tgt f).getD who noAcct = l.getD who noAcct := by
  induction l generalizing tgt who with
  | nil => simp
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact absurd rfl h
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w (by intro heq; apply h; rw [heq])

theorem tmp_withAcct_side (s : St) (tgt : Nat) (f : Acct → Acct) :
    (s.withAcct tgt f).supplyState = s.supplyState ∧
    (s.withAcct tgt f).borrowState = s.borrowState ∧
    (s.withAcct tgt f).blockNumber = s.blockNumber := by
  refine ⟨rfl, rfl, rfl⟩

theorem tmp_acct_ne (s : St) (tgt who : Nat) (f : Acct → Acct) (h : tgt ≠ who) :
    (s.withAcct tgt f).acct who = s.acct who := by
  unfold St.withAcct St.acct
  simp only
  exact tmp_ne_lemma3 s.accts tgt who f h

theorem tmp_check_mod3 : True := by trivial
#check @List.modify
#check @List.modifyTailIdx
#check @List.length_modify
#check @List.getElem_modify
#check @List.modifyHead

theorem bc_supply_pres (l : List Acct) (tgt who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supply = a.supply) :
    ((l.modify tgt f).getD who noAcct).supply = (l.getD who noAcct).supply := by
  induction l generalizing tgt who with
  | nil =>
    cases tgt with
    | zero => rfl
    | succ t => rfl
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact hf a
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w

theorem bc_accrued_pres (l : List Acct) (tgt who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).accrued = a.accrued) :
    ((l.modify tgt f).getD who noAcct).accrued = (l.getD who noAcct).accrued := by
  induction l generalizing tgt who with
  | nil =>
    cases tgt with
    | zero => rfl
    | succ t => rfl
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact hf a
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w

theorem bc_wallet_pres (l : List Acct) (tgt who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).wallet = a.wallet) :
    ((l.modify tgt f).getD who noAcct).wallet = (l.getD who noAcct).wallet := by
  induction l generalizing tgt who with
  | nil =>
    cases tgt with
    | zero => rfl
    | succ t => rfl
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact hf a
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w

theorem bc_explore6 (n : Nat) : List.getD ([] : List Acct) (n+1) noAcct = noAcct := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem bc_explore5 : List.getD ([] : List Acct) 0 noAcct = noAcct := by rfl

theorem bc_explore4 (a : Acct) (as : List Acct) (n : Nat) :
    List.getD (a :: as) (n+1) noAcct = List.getD as n noAcct := by rfl

theorem bc_explore3 (a : Acct) (as : List Acct) :
    List.getD (a :: as) 0 noAcct = a := by rfl

theorem bc_explore2 (a : Acct) (as : List Acct) (n : Nat) (f : Acct → Acct) :
    List.modify (a :: as) (n+1) f = a :: List.modify as n f := by rfl

theorem bc_explore1 (a : Acct) (as : List Acct) (f : Acct → Acct) :
    List.modify (a :: as) 0 f = f a :: as := by rfl

theorem tmp_adv_unindexed_eq2 (s : St) (k : Nat) (h1 : s.supplyState.block ≤ s.blockNumber) (h2 : s.borrowState.block ≤ s.blockNumber) :
    (s.blockNumber + k - s.borrowState.block) = (s.blockNumber - s.borrowState.block) + k := by omega

theorem tmp_adv_unindexed_eq (s : St) (k : Nat) (h1 : s.supplyState.block ≤ s.blockNumber) (h2 : s.borrowState.block ≤ s.blockNumber) :
    (s.blockNumber + k - s.supplyState.block) = (s.blockNumber - s.supplyState.block) + k := by omega

theorem tmp_if_neg_test (x : Nat) (hx : ¬ x = 0) : (if x = 0 then 1 else x) = x := by simp [hx]

theorem tmp_pow_pos : 0 < compInitialIndex := by unfold compInitialIndex; exact Nat.pow_pos (by decide)

theorem tmp_supDist_block2 (s : St) (tgt : Account) (s' : St) :
    SupplyDistributed s tgt s' → s'.supplyState.block = s.blockNumber := by
  intro h
  unfold SupplyDistributed at h
  obtain ⟨_, _, heq⟩ := h
  subst heq
  simp only
  unfold accrueSide
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [hc]
  · simp [hc]

theorem td0_ds_pos_aux : 0 < doubleScale := by
  unfold doubleScale
  apply Nat.pow_pos
  decide

theorem td0_owedTo_unfold (L : Legacy) (who : Account) :
    L.owedTo who = td0_pendingOf L who / doubleScale + td0_unindexedOf L who := by
  unfold Legacy.owedTo td0_pendingOf td0_unindexedOf
  rw [Nat.add_assoc]

theorem td0_account_bound_of_scaled (s : St) (L : Legacy) (who : Account) (e : Nat) :
    doubleScale * s.creditedTo who ≤
        doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who +
        doubleScale * e →
      s.creditedTo who ≤ (upgrade L).creditedTo who + L.owedTo who + e := by
  intro h
  have hD : 0 < doubleScale := td0_ds_pos_aux
  have howed := td0_owedTo_unfold L who
  rw [howed]
  have eq1 : s.creditedTo who * doubleScale = doubleScale * s.creditedTo who := Nat.mul_comm _ _
  have eq2 : ((upgrade L).creditedTo who + td0_unindexedOf L who + e) * doubleScale =
      doubleScale * (upgrade L).creditedTo who + doubleScale * td0_unindexedOf L who + doubleScale * e := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm ((upgrade L).creditedTo who) doubleScale, Nat.mul_comm (td0_unindexedOf L who) doubleScale, Nat.mul_comm e doubleScale]
  have h' : s.creditedTo who * doubleScale ≤ ((upgrade L).creditedTo who + td0_unindexedOf L who + e) * doubleScale + td0_pendingOf L who := by
    rw [eq1, eq2]
    omega
  have hle := ProofForgeFin.le_add_div_of_mul_le (X := s.creditedTo who) (Y := (upgrade L).creditedTo who + td0_unindexedOf L who + e) (P := td0_pendingOf L who) (D := doubleScale) hD h'
  omega

theorem tmp_init_char (now : Nat) (sd : Side) :
    (initSide now sd).index = (if sd.index = 0 then compInitialIndex else sd.index) ∧
    (initSide now sd).block = (if sd.index = 0 then now else sd.block) ∧
    (initSide now sd).speed = sd.speed := by
  unfold initSide
  by_cases h : sd.index = 0 <;> simp [h]

theorem tmp_upg_supply_accts (L : Legacy) : (upgrade L).accts = L.accts := by
  unfold upgrade; simp

theorem tmp_upg_block_eq (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade; simp

theorem tmp_upg_acct_eq (L : Legacy) (who : Account) :
    (upgrade L).acct who = L.accts.getD who noAcct := by
  unfold upgrade St.acct
  simp

theorem tmp_upg_cred_eq (L : Legacy) (who : Account) :
    (upgrade L).creditedTo who = (L.accts.getD who noAcct).accrued + (L.accts.getD who noAcct).wallet := by
  unfold St.creditedTo
  rw [tmp_upg_acct_eq]

theorem tmp_list_api_probe2 : True := trivial
#check List.getD
#check List.getElem_mem

theorem tmp_getD_unfold_probe (l : List Acct) (n : Nat) :
    l.getD n noAcct = (l[n]?.getD noAcct) := by rfl
#check List.getD

theorem plan2_legacyStart_le_accrualStart (start recorded index : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hle : start ≤ index) (hrec : recorded ≤ index) :
    legacyStart start recorded ≤ accrualStart recorded index := by
  unfold legacyStart accrualStart
  by_cases hrec0 : recorded = 0
  · subst hrec0
    simp only [beq_self_eq_true, ↓reduceIte]
    rcases hstart with rfl | rfl
    · exact Nat.zero_le _
    · simp [hle]
  · simp only [hrec0, ↓reduceIte]
    exact Nat.le_refl _

theorem plan2_supply_gap_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    (initSide L.blockNumber
      (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.supplierIndex
          (initSide L.blockNumber
            (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index ≤
      L.supplyIndex - legacyStart L.supplyStart a.supplierIndex := by
  by_cases hI : L.supplyIndex = 0
  · have hS0 : L.supplyStart = 0 := by omega
    have ha0 : a.supplierIndex = 0 := by omega
    have hinit : (initSide L.blockNumber
      (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index = compInitialIndex := by
      unfold initSide
      simp [hI]
    rw [hinit, ha0, hS0, hI]
    unfold accrualStart legacyStart
    simp
  · have hinit : (initSide L.blockNumber
      (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index = L.supplyIndex := by
      unfold initSide
      simp [hI]
    rw [hinit]
    have hle2 : legacyStart L.supplyStart a.supplierIndex ≤
      accrualStart a.supplierIndex L.supplyIndex :=
      plan2_legacyStart_le_accrualStart L.supplyStart a.supplierIndex L.supplyIndex hstart hle ha
    have hacc_le : accrualStart a.supplierIndex L.supplyIndex ≤ L.supplyIndex := by
      unfold accrualStart
      split
      · split
        · assumption
        · omega
      · omega
    have hleg_le : legacyStart L.supplyStart a.supplierIndex ≤ L.supplyIndex := by
      unfold legacyStart
      split
      · exact hle
      · omega
    omega

theorem plan2_borrow_gap_le_aux (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.borrowerIndex
          (initSide L.blockNumber
            (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by
  by_cases hI : L.borrowIndex = 0
  · have hS0 : L.borrowStart = 0 := by omega
    have ha0 : a.borrowerIndex = 0 := by omega
    have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = compInitialIndex := by
      unfold initSide
      simp [hI]
    rw [hinit, ha0, hS0, hI]
    unfold accrualStart legacyStart
    simp
  · have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = L.borrowIndex := by
      unfold initSide
      simp [hI]
    rw [hinit]
    have hle2 : legacyStart L.borrowStart a.borrowerIndex ≤
      accrualStart a.borrowerIndex L.borrowIndex :=
      plan2_legacyStart_le_accrualStart L.borrowStart a.borrowerIndex L.borrowIndex hstart hle ha
    have hacc_le : accrualStart a.borrowerIndex L.borrowIndex ≤ L.borrowIndex := by
      unfold accrualStart
      split
      · split
        · assumption
        · omega
      · omega
    have hleg_le : legacyStart L.borrowStart a.borrowerIndex ≤ L.borrowIndex := by
      unfold legacyStart
      split
      · exact hle
      · omega
    omega

theorem plan2_borrow_gap_le (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.borrowerIndex
          (initSide L.blockNumber
            (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by
  by_cases hI : L.borrowIndex = 0
  · have hS0 : L.borrowStart = 0 := by omega
    have ha0 : a.borrowerIndex = 0 := by omega
    have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = compInitialIndex := by
      unfold initSide
      simp [hI]
    rw [hinit, ha0, hS0, hI]
    unfold accrualStart legacyStart
    simp
  · have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = L.borrowIndex := by
      unfold initSide
      simp [hI]
    rw [hinit]
    have hle2 : legacyStart L.borrowStart a.borrowerIndex ≤
      accrualStart a.borrowerIndex L.borrowIndex :=
      plan2_legacyStart_le_accrualStart L.borrowStart a.borrowerIndex L.borrowIndex hstart hle ha
    have hacc_le : accrualStart a.borrowerIndex L.borrowIndex ≤ L.borrowIndex := by
      unfold accrualStart
      split
      · split
        · assumption
        · omega
      · omega
    have hleg_le : legacyStart L.borrowStart a.borrowerIndex ≤ L.borrowIndex := by
      unfold legacyStart
      split
      · exact hle
      · omega
    omega

theorem plan2_tmp_mem2 (hd : Acct) (tl : List Acct) (a : Acct) (ha : a ∈ tl) : a ∈ hd :: tl := by simp [ha]

theorem plan2_tmp_mem (hd : Acct) (tl : List Acct) : hd ∈ hd :: tl := by simp

theorem plan2_dbg1 (tl : List Acct) (hd : Acct) : hd ∈ hd :: tl := by exact List.Mem.head _

theorem plan2_dbg2 : True := trivial

theorem plan2_probe_getD (l : List Acct) (who : Nat) : True := by
  cases l with
  | nil =>
    cases who with
    | zero => trivial
    | succ n => trivial
  | cons hd tl => trivial

theorem plan2_rfl4 (n : Nat) : List.getD ([] : List Acct) (n+1) noAcct = noAcct := by
  cases n with
  | zero => rfl
  | succ m => rfl

theorem plan2_rfl3 : List.getD ([] : List Acct) 0 noAcct = noAcct := by rfl

theorem plan2_rfl2 (a : Acct) (as : List Acct) (n : Nat) : List.getD (a :: as) (n+1) noAcct = List.getD as n noAcct := by rfl

theorem plan2_rfl1 (a : Acct) (as : List Acct) : List.getD (a :: as) 0 noAcct = a := by rfl

theorem plan2_aux_getD_le (l : List Acct) (S B : Nat) (who : Nat)
    (hmem : ∀ a ∈ l, a.supplierIndex ≤ S ∧ a.borrowerIndex ≤ B) :
    (l.getD who noAcct).supplierIndex ≤ S ∧ (l.getD who noAcct).borrowerIndex ≤ B := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero =>
      have h : List.getD ([] : List Acct) 0 noAcct = noAcct := rfl
      rw [h]
      constructor <;> (unfold noAcct; simp)
    | succ n =>
      have h : List.getD ([] : List Acct) (n+1) noAcct = noAcct := rfl
      rw [h]
      constructor <;> (unfold noAcct; simp)
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h : List.getD (hd :: tl) 0 noAcct = hd := rfl
      rw [h]
      exact hmem hd (List.Mem.head _)
    | succ n =>
      have h : List.getD (hd :: tl) (n+1) noAcct = List.getD tl n noAcct := rfl
      rw [h]
      apply ih
      intro a ha
      exact hmem a (List.Mem.tail _ ha)

theorem plan2_getD_index_le2 (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  obtain ⟨_, _, _, _, _, _, hmem⟩ := hWF
  exact plan2_aux_getD_le L.accts L.supplyIndex L.borrowIndex who hmem

theorem plan2_getD_index_le (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  obtain ⟨_, _, _, _, _, _, hmem⟩ := hWF
  exact plan2_aux_getD_le L.accts L.supplyIndex L.borrowIndex who hmem

theorem plan2_upgrade_pending_le (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    td0_pendingScaledAcct (upgrade L) ((upgrade L).acct who) ≤
      td0_pendingOf L who := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, haccts⟩ := hWF
  have hWF2 : L.WellFormed := ⟨hs0, hsle, hb0, hble, hsb, hbb, haccts⟩
  have hidx := plan2_getD_index_le L who hWF2
  have hsup_mem : (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex := hidx.1
  have hbor_mem : (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := hidx.2
  have hgapS := plan2_supply_gap_le L (L.accts.getD who noAcct) hs0 hsle hsup_mem
  have hgapB := plan2_borrow_gap_le L (L.accts.getD who noAcct) hb0 hble hbor_mem
  unfold td0_pendingScaledAcct td0_pendingOf Legacy.pendingScaled
  have hacct_eq : (upgrade L).acct who = L.accts.getD who noAcct := tmp_upg_acct_eq L who
  have hsup_idx : (upgrade L).supplyState.index =
      (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  have hbor_idx : (upgrade L).borrowState.index =
      (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  rw [hacct_eq, hsup_idx, hbor_idx]
  have hmulS : (L.accts.getD who noAcct).supply *
      ((initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index -
        accrualStart (L.accts.getD who noAcct).supplierIndex
          (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index) ≤
      (L.accts.getD who noAcct).supply * (L.supplyIndex - legacyStart L.supplyStart (L.accts.getD who noAcct).supplierIndex) :=
    Nat.mul_le_mul_left _ hgapS
  have hmulB : (L.accts.getD who noAcct).borrow *
      ((initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart (L.accts.getD who noAcct).borrowerIndex
          (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index) ≤
      (L.accts.getD who noAcct).borrow * (L.borrowIndex - legacyStart L.borrowStart (L.accts.getD who noAcct).borrowerIndex) :=
    Nat.mul_le_mul_left _ hgapB
  exact Nat.add_le_add hmulS hmulB

theorem plan2_upgrade_unindexedTo_le_aux5 (L : Legacy) :
    (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade
  simp only

theorem plan2_upgrade_unindexedTo_le_aux4 (L : Legacy) :
    (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le_aux3 (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le_aux2 (L : Legacy) :
    (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le_aux1 (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le (L : Legacy) (who : Account) :
    td0_unindexedTo (upgrade L) who ≤ td0_unindexedOf L who := by
  have hsup_blk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hbor_blk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hsup_spd : (upgrade L).supplyState.speed = L.compSpeed := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hbor_spd : (upgrade L).borrowState.speed = L.compSpeed := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hblk : (upgrade L).blockNumber = L.blockNumber := by
    unfold upgrade
    simp
  have hacct : (upgrade L).acct who = L.accts.getD who noAcct := by
    unfold upgrade St.acct
    simp
  have hS : (L.blockNumber - (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock)) * L.compSpeed ≤ (L.blockNumber - L.supplyBlock) * L.compSpeed := by
    by_cases hS0 : L.supplyIndex = 0
    · simp [hS0]
    · simp [hS0]
  have hB : (L.blockNumber - (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock)) * L.compSpeed ≤ (L.blockNumber - L.borrowBlock) * L.compSpeed := by
    by_cases hB0 : L.borrowIndex = 0
    · simp [hB0]
    · simp [hB0]
  unfold td0_unindexedTo td0_unindexedOf Legacy.unindexedSupply Legacy.unindexedBorrow
  rw [hsup_blk, hbor_blk, hsup_spd, hbor_spd, hblk, hacct]
  by_cases hs : 0 < (L.accts.getD who noAcct).supply <;> by_cases hb : 0 < (L.accts.getD who noAcct).borrow <;> simp only [hs, hb, if_true, if_false, Nat.zero_add, Nat.add_zero, Nat.zero_le]
  · exact Nat.add_le_add hS hB
  · exact hS
  · exact hB

theorem plan2_tmp_inline1 (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  split
  · rfl
  · rfl

theorem plan2_inline_check4 (L : Legacy) (who : Account) :
    (upgrade L).acct who = L.accts.getD who noAcct := by
  unfold upgrade St.acct
  simp

theorem plan2_inline_check3 (L : Legacy) :
    (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade
  simp

theorem plan2_inline_check2 (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  split
  · rfl
  · rfl

theorem plan2_upgrade_unindexedTo_le_newproof (L : Legacy) (who : Account) :
    td0_unindexedTo (upgrade L) who ≤ td0_unindexedOf L who := by
  have hsup_blk := plan2_tmp_inline1 L
  have hbor_blk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hsup_spd := plan2_inline_check2 L
  have hbor_spd : (upgrade L).borrowState.speed = L.compSpeed := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hblk := plan2_inline_check3 L
  have hacct := plan2_inline_check4 L who
  have hS : (L.blockNumber - (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock)) * L.compSpeed ≤ (L.blockNumber - L.supplyBlock) * L.compSpeed := by
    by_cases hS0 : L.supplyIndex = 0
    · simp [hS0]
    · simp [hS0]
  have hB : (L.blockNumber - (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock)) * L.compSpeed ≤ (L.blockNumber - L.borrowBlock) * L.compSpeed := by
    by_cases hB0 : L.borrowIndex = 0
    · simp [hB0]
    · simp [hB0]
  unfold td0_unindexedTo td0_unindexedOf Legacy.unindexedSupply Legacy.unindexedBorrow
  rw [hsup_blk, hbor_blk, hsup_spd, hbor_spd, hblk, hacct]
  by_cases hs : 0 < (L.accts.getD who noAcct).supply <;> by_cases hb : 0 < (L.accts.getD who noAcct).borrow <;> simp only [hs, hb, if_true, if_false, Nat.zero_add, Nat.add_zero, Nat.zero_le]
  · exact Nat.add_le_add hS hB
  · exact hS
  · exact hB

theorem td0_rewards_bound_of_scaled (s : St) (L : Legacy) (e : Nat) :
    doubleScale * s.credited ≤
        doubleScale * (upgrade L).credited +
        (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * e →
      s.credited ≤ (upgrade L).credited + L.owed + e := by
  intro h
  have hD : 0 < doubleScale := td0_ds_pos_aux
  have howed : L.owed = (L.accts.map L.pendingScaled).sum / doubleScale + L.unindexedSupply + L.unindexedBorrow := rfl
  rw [howed]
  have eq1 : s.credited * doubleScale = doubleScale * s.credited := Nat.mul_comm _ _
  have eq2 : ((upgrade L).credited + (L.unindexedSupply + L.unindexedBorrow) + e) * doubleScale =
      doubleScale * (upgrade L).credited + doubleScale * (L.unindexedSupply + L.unindexedBorrow) + doubleScale * e := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm ((upgrade L).credited) doubleScale, Nat.mul_comm (L.unindexedSupply + L.unindexedBorrow) doubleScale, Nat.mul_comm e doubleScale]
  have h' : s.credited * doubleScale ≤ ((upgrade L).credited + (L.unindexedSupply + L.unindexedBorrow) + e) * doubleScale + (L.accts.map L.pendingScaled).sum := by
    rw [eq1, eq2]
    omega
  have hle := ProofForgeFin.le_add_div_of_mul_le (X := s.credited) (Y := (upgrade L).credited + (L.unindexedSupply + L.unindexedBorrow) + e) (P := (L.accts.map L.pendingScaled).sum) (D := doubleScale) hD h'
  omega

theorem tmp_upg_sum_aux (L : Legacy) (l : List Acct)
    (h : ∀ a ∈ l, td0_pendingScaledAcct (upgrade L) a ≤ L.pendingScaled a) :
    ((l.map (td0_pendingScaledAcct (upgrade L))).sum ≤ (l.map L.pendingScaled).sum) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hhd : td0_pendingScaledAcct (upgrade L) hd ≤ L.pendingScaled hd := h hd (List.Mem.head _)
    have htl : ∀ a ∈ tl, td0_pendingScaledAcct (upgrade L) a ≤ L.pendingScaled a := fun a ha =>
      h a (List.Mem.tail _ ha)
    have iht := ih htl
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add hhd iht

theorem tmp_upg_mem_pend_le (L : Legacy) (a : Acct) (hWF : L.WellFormed) (hmem : a ∈ L.accts) :
    td0_pendingScaledAcct (upgrade L) a ≤ L.pendingScaled a := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, haccts⟩ := hWF
  have ha := haccts a hmem
  have hsup_mem : a.supplierIndex ≤ L.supplyIndex := ha.1
  have hbor_mem : a.borrowerIndex ≤ L.borrowIndex := ha.2
  have hgapS := plan2_supply_gap_le L a hs0 hsle hsup_mem
  have hgapB := plan2_borrow_gap_le L a hb0 hble hbor_mem
  have hsup_idx : (upgrade L).supplyState.index =
      (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  have hbor_idx : (upgrade L).borrowState.index =
      (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  unfold td0_pendingScaledAcct Legacy.pendingScaled
  rw [hsup_idx, hbor_idx]
  have hmulS : a.supply *
      ((initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.supplierIndex
          (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) :=
    Nat.mul_le_mul_left _ hgapS
  have hmulB : a.borrow *
      ((initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.borrowerIndex
          (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index) ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) :=
    Nat.mul_le_mul_left _ hgapB
  exact Nat.add_le_add hmulS hmulB

theorem tmp_upg_unidx_le (L : Legacy) :
    td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by
  have hsup_blk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock :=
    plan2_upgrade_unindexedTo_le_aux1 L
  have hbor_blk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock :=
    plan2_upgrade_unindexedTo_le_aux2 L
  have hsup_spd : (upgrade L).supplyState.speed = L.compSpeed :=
    plan2_upgrade_unindexedTo_le_aux3 L
  have hbor_spd : (upgrade L).borrowState.speed = L.compSpeed :=
    plan2_upgrade_unindexedTo_le_aux4 L
  have hblk : (upgrade L).blockNumber = L.blockNumber :=
    plan2_upgrade_unindexedTo_le_aux5 L
  have hS : ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed ≤
      L.unindexedSupply := by
    rw [hsup_blk, hsup_spd, hblk]
    unfold Legacy.unindexedSupply
    by_cases hS0 : L.supplyIndex = 0
    · simp [hS0]
    · simp [hS0]
  have hB : ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed ≤
      L.unindexedBorrow := by
    rw [hbor_blk, hbor_spd, hblk]
    unfold Legacy.unindexedBorrow
    by_cases hB0 : L.borrowIndex = 0
    · simp [hB0]
    · simp [hB0]
  unfold td0_unindexed
  exact Nat.add_le_add hS hB

theorem upd_supply_eq2 (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [hle]

theorem probe_upd_simp (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    (match (if s.supplyState.block ≤ s.blockNumber then some (s.blockNumber - s.supplyState.block) else none : Option Nat) with
    | none => (none : Option St)
    | some deltaBlocks => some s) = some s := by
  simp [hle]

theorem plan3_updateSupply_accrue_aux1 (s : St) :
    accrueSide s.supplyState s.blockNumber (totalSupply s) =
    (if 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s then
      ({ s.supplyState with index := s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s, block := s.blockNumber } : Side)
    else ({ s.supplyState with block := s.blockNumber } : Side)) := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem plan3_updateSupply_accrue_try1 (s : St) (t : St) (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem plan3_supply_fraq_eq (d spd tot : Nat) :
    fraction (d * spd) tot = d * spd * doubleScale / tot := by
  unfold fraction
  rw [Nat.mul_assoc]

theorem plan3_supply_eta1d (bn : Nat) (sup : Side) (hbeq : sup.block = bn) :
    ({ sup with block := bn } : Side) = sup := by
  cases sup with | mk idx blk spd =>
    simp at hbeq ⊢
    subst hbeq
    rfl

theorem plan3_supply_eta2d (s : St) (hbeq : s.supplyState.block = s.blockNumber) :
    ({ s with supplyState := ({ s.supplyState with block := s.blockNumber } : Side) } : St) = s := by
  have h1 : (({ s.supplyState with block := s.blockNumber } : Side)) = s.supplyState :=
    plan3_supply_eta1d s.blockNumber s.supplyState hbeq
  cases s with | mk bn sup bor res accts =>
    simp at h1 hbeq ⊢
    rw [h1]

theorem plan3_updateBorrow_accrue (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber ∧
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  intro h
  have hle : s.borrowState.block ≤ s.blockNumber := by
    by_cases hc : s.borrowState.block ≤ s.blockNumber
    · exact hc
    · have hnone : subChecked s.blockNumber s.borrowState.block = none := by
        unfold subChecked
        rw [if_neg hc]
      unfold updateCompBorrowIndex at h
      rw [hnone] at h
      simp at h
  refine ⟨hle, ?_⟩
  unfold updateCompBorrowIndex subChecked at h
  rw [if_pos hle] at h
  simp only at h
  by_cases hpos : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hpos] at h
    cases h
    congr 1
    have h0 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed := hpos
    by_cases htot : 0 < totalBorrows s
    · have hacc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s := ⟨h0.1, h0.2, htot⟩
      have htot' : totalBorrows s > 0 := htot
      have e1 : (if totalBorrows s > 0 then fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s) else 0) = (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s := by
        rw [if_pos htot']; rfl
      rw [e1]
      unfold accrueSide
      rw [if_pos hacc]
    · have htot' : ¬ totalBorrows s > 0 := by omega
      have e1 : (if totalBorrows s > 0 then fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s) else 0) = 0 := if_neg htot'
      rw [e1]
      have hacc_neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      rfl
  · rw [if_neg hpos] at h
    by_cases hdelta : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos hdelta] at h
      cases h
      congr 1
      have hacc_neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        intro hc
        exact hpos ⟨hc.1, hc.2.1⟩
      unfold accrueSide
      rw [if_neg hacc_neg]
    · rw [if_neg hdelta] at h
      cases h
      have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have hacc_neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res accts =>
        simp only at hbeq ⊢
        cases bor with
        | mk idx blk spd =>
          simp only at hbeq ⊢
          rw [hbeq]

theorem tmp_supply_if2 (s : St) (a : Nat) (t : St) (hne : s.supplyState.speed ≠ a)
    (u : St) (hU : updateCompSupplyIndex s = some u)
    (h : ((updateCompSupplyIndex s).map fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) = some t) : True := by
  rw [hU] at h
  simp at h
  trivial

theorem tmp_supply_if1 (s : St) (a : Nat) (t : St) (heq : s.supplyState.speed = a)
    (h : setSupplySpeed s a = some t) : t = s := by
  unfold setSupplySpeed at h
  simp [heq] at h
  exact h.symm

theorem tmp_supply_rw2 (s : St) (u : St) (hU : u = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)) (a : Nat) (t : St)
    (h : t = ({ u with supplyState := ({ u.supplyState with speed := a } : Side) } : St)) :
    t = ({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St) := by
  rw [hU] at h
  rw [h]

theorem tmp_supply_rw (s : St) (Y X : Side) :
    ({ ({ s with supplyState := Y } : St) with supplyState := X } : St) = ({ s with supplyState := X } : St) := by
  rfl

theorem tmp_supply_branch_ne (s : St) (a : Nat) (t : St) (hNe : s.supplyState.speed ≠ a)
    (h : setSupplySpeed s a = some t) :
    ((updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) = some t) := by
  unfold setSupplySpeed at h
  have hSimp : (if s.supplyState.speed ≠ a then (updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) else some s) = (updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) := by
    simp [hNe]
  rw [hSimp] at h
  exact h

theorem tmp_supply_branch_eq (s : St) (a : Nat) (t : St) (hEq : s.supplyState.speed = a)
    (h : setSupplySpeed s a = some t) : s = t := by
  unfold setSupplySpeed at h
  have hSimp : (if s.supplyState.speed ≠ a then (updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) else some s) = some s := by
    simp [hEq]
  rw [hSimp] at h
  simpa using h

theorem tmp_if_same2 (s : St) (a : Nat) (hEq : s.supplyState.speed = a) :
    ({ s with supplyState := (if s.supplyState.speed = a then s.supplyState else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) } : St) = s := by
  have hIf : (if s.supplyState.speed = a then s.supplyState else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) = s.supplyState := by
    simp [hEq]
  rw [hIf]

theorem tmp_eta_same2 (s : St) : ({ s with supplyState := s.supplyState } : St) = s := by
  cases s
  rfl

theorem tmp_goal_eq (s u : St) (a : Nat) (hU : u = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)) :
    ({ u with supplyState := ({ u.supplyState with speed := a } : Side) } : St) =
    ({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St) := by
  rw [hU]

theorem tmp_map_extract2 (u t : St) (a : Nat) (h : (Option.some u).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) = some t) :
    t = ({ u with supplyState := ({ u.supplyState with speed := a } : Side) } : St) := by
  simp at h
  exact h.symm

theorem tmp_inj_probe (u t : St) (f : St → St)
    (h : Option.map f (some u) = some t) : f u = t := by
  simpa using h

theorem tmp_borrow_rw (s u : St) (b : Nat)
    (hu : u = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)) :
    (({ u with borrowState := ({ u.borrowState with speed := b } : Side) } : St)) =
    (({ s with borrowState := ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side) } : St)) := by
  rw [hu]

theorem tmp_mid_exists5 (s : St) (a b : Nat) (s' : St)
    (h : setCompSpeedInternal s a b = some s') :
    ∃ mid, setSupplySpeed s a = some mid ∧ setBorrowSpeed mid b = some s' := by
  unfold setCompSpeedInternal at h
  cases heq : setSupplySpeed s a
  · simp [heq] at h
  · simp [heq] at h
    exact ⟨_, rfl, h⟩

theorem tmp_mid_preserve (s mid : St) (a : Nat)
    (h : mid = ({ s with supplyState := (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) } : St)) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧ mid.accts = s.accts ∧ mid.borrowState.speed = s.borrowState.speed := by
  constructor
  · rw [h]
  constructor
  · rw [h]
  constructor
  · rw [h]
  · rw [h]

theorem tmp_merge_eq (s : St) (SA : Side) (BA : Side) :
    (({ ({ s with supplyState := SA } : St) with borrowState := BA } : St)) =
    ({ s with supplyState := SA, borrowState := BA } : St) := by
  rfl

theorem tmp_supply_unfold (t : St) (who : Account) (s' : St)
    (hd : distributeSupplierComp t who = some s') : True := by
  unfold distributeSupplierComp at hd
  trivial

theorem tmp_supply_step1b (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ t, updateCompSupplyIndex s = some t ∧
      distributeSupplierComp t who = some s' := by
  unfold comptroller at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    simp [hU] at h
  | some t =>
    simp [hU] at h
    exact ⟨t, rfl, h⟩

theorem tmp_if_parse (t : St) (who : Account) (h : (t.acct who).supplierIndex = 0) : True := by
  trivial

theorem tmp_try_modify_congr (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil =>
    cases who <;> rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h0 : f hd = g hd := h
      show List.modify (hd :: tl) 0 f = List.modify (hd :: tl) 0 g
      simp [h0]
    | succ n =>
      have h0 : f (tl.getD n noAcct) = g (tl.getD n noAcct) := h
      show List.modify (hd :: tl) (n+1) f = List.modify (hd :: tl) (n+1) g
      simp [ih n h0]

theorem plan4_modify_congr_at_proof (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g :=
  tmp_try_modify_congr l who f g h

theorem tmp_try_modify_congr2 (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  exact tmp_try_modify_congr l who f g h

theorem tmp_inline_proof_check (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h0 : f hd = g hd := h
      simp [h0]
    | succ n =>
      have h0 : f (tl.getD n noAcct) = g (tl.getD n noAcct) := h
      simp [ih n h0]

theorem plan4_modify_congr_at (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h0 : f hd = g hd := h
      simp [h0]
    | succ n =>
      have h0 : f (tl.getD n noAcct) = g (tl.getD n noAcct) := h
      simp [ih n h0]

theorem plan4_supplier_start_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · subst h
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [h, show ¬ (recorded = 0 ∧ compInitialIndex ≤ index) from fun ⟨heq, _⟩ => h heq]

theorem tmp_distrib_unfold (s : St) (who : Account) :
    distributeSupplierComp s who =
    match subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply deltaIndex }) := by
  unfold distributeSupplierComp subChecked
  simp only

theorem tmp_step_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := plan4_supplier_start_eq _ _
#check @plan4_modify_congr_at
#check @plan4_supplier_start_eq

theorem tmp_distrib_spec_aux2 (s : St) (who : Account) (s2 : St)
    (h : distributeSupplierComp s who = some s2) : True := by
  trivial

theorem tmp_final_auxB (s : St) (who : Account) :
    (s.accts.getD who noAcct).supplierIndex = (s.acct who).supplierIndex := rfl

theorem tmp_final_auxA (s : St) (who : Account) :
    (s.accts.getD who noAcct).supply = (s.acct who).supply := rfl

theorem tmp_pos_branch (s : St) (who : Account) (tgt : St)
    (hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index)
    (h : (some (s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) } : Acct))) : Option St) = some tgt) :
    tgt = s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) := by
  have hsup : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := plan4_supplier_start_eq _ _
  have hY : s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) } : Acct)) = tgt := Option.some_inj.mp h
  rw [hsup] at hY
  exact hY.symm

theorem tmp_parse_checkA (s : St) (who : Account) (t : St) (h : t = s.withAcct who fun a => { a with supplierIndex := s.supplyState.index }) : True := by trivial

theorem plan4_supplyHook_decomp (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' →
      ∃ t, updateCompSupplyIndex s = some t ∧
        distributeSupplierComp t who = some s' :=
  fun h => tmp_supply_step1b s who s' h

theorem ztest_merge2 (s : St) (A : Side) (who : Nat) (f : Acct → Acct) :
    ({ s with supplyState := A } : St).withAcct who f =
    { s with supplyState := A, accts := s.accts.modify who f } := by
  unfold St.withAcct
  cases s with
  | mk bn sup bor res ac =>
    rfl

theorem plan3_updateSupply_accrue (s : St) (t : St) :
    updateCompSupplyIndex s = some t →
    s.supplyState.block ≤ s.blockNumber ∧
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  intro h
  have hle : s.supplyState.block ≤ s.blockNumber := by
    by_cases hc : s.supplyState.block ≤ s.blockNumber
    · exact hc
    · have hnone : subChecked s.blockNumber s.supplyState.block = none := by
        unfold subChecked
        rw [if_neg hc]
      unfold updateCompSupplyIndex at h
      rw [hnone] at h
      simp at h
  refine ⟨hle, ?_⟩
  unfold updateCompSupplyIndex subChecked at h
  rw [if_pos hle] at h
  simp only at h
  by_cases hpos : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hpos] at h
    cases h
    congr 1
    have h0 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed := hpos
    by_cases htot : 0 < totalSupply s
    · have hacc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s := ⟨h0.1, h0.2, htot⟩
      have htot' : totalSupply s > 0 := htot
      have e1 : (if totalSupply s > 0 then fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s) else 0) = (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s := by
        rw [if_pos htot']; rfl
      rw [e1]
      unfold accrueSide
      rw [if_pos hacc]
    · have htot' : ¬ totalSupply s > 0 := by omega
      have e1 : (if totalSupply s > 0 then fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s) else 0) = 0 := if_neg htot'
      rw [e1]
      have hacc_neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      rfl
  · rw [if_neg hpos] at h
    by_cases hdelta : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos hdelta] at h
      cases h
      congr 1
      have hacc_neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        intro hc
        exact hpos ⟨hc.1, hc.2.1⟩
      unfold accrueSide
      rw [if_neg hacc_neg]
    · rw [if_neg hdelta] at h
      cases h
      have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have hacc_neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res accts =>
        simp only at hbeq ⊢
        cases sup with
        | mk idx blk spd =>
          simp only at hbeq ⊢
          rw [hbeq]

theorem tmp_borrow_step1b_aux (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ t, updateCompBorrowIndex s = some t ∧
      distributeBorrowerComp t who = some s' := by
  unfold comptroller at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    simp [hU] at h
  | some t =>
    simp [hU] at h
    exact ⟨t, rfl, h⟩

theorem tmp_bdistr_explore (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    True := by
  unfold distributeBorrowerComp at h
  simp only at h
  guard_hyp h : _ = some s'
  trivial

theorem tmp_bdistr_explore2 (s : St) (who : Account) :
    distributeBorrowerComp s who =
    let borrowIndex := s.borrowState.index
    let borrowerIndex :=
      if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ borrowIndex then compInitialIndex
      else (s.acct who).borrowerIndex
    match subChecked borrowIndex borrowerIndex with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := borrowIndex, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex }) := by
  rfl

theorem plan5_borrower_start_eq_proof (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · subst h
    simp only
    by_cases h2 : compInitialIndex ≤ index <;> simp [h2]
  · have hne : ¬ (recorded = 0 ∧ compInitialIndex ≤ index) := fun hh => h hh.1
    simp [hne, h]

theorem plan5_borrower_start_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · subst h
    simp only
    by_cases h2 : compInitialIndex ≤ index <;> simp [h2]
  · have hne : ¬ (recorded = 0 ∧ compInitialIndex ≤ index) := fun hh => h hh.1
    simp [hne, h]

theorem plan5_accrue_borrow_acct_eq (s : St) (who : Account) :
    ({ s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who =
      s.acct who := by
  rfl

theorem plan5_accrue_borrow_withAcct_eq (s : St) (who : Account) (f : Acct → Acct) :
    ({ s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who f =
    { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who f } := by
  unfold St.withAcct
  cases s with | mk blockNumber supplyState borrowState reserve accts =>
    rfl

theorem plan5_mulDouble_eq_creditFor (u d idx st : Nat) (h : st ≤ idx) (hd : d = idx - st) :
    mulDouble u d = creditFor u st idx := by unfold mulDouble creditFor; rw [hd]

theorem plan5_distributeBorrowerComp_spec_aux_check (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index := plan5_borrower_start_eq _ _

theorem tmp_bspec_explore (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') : True := by
  unfold distributeBorrowerComp subChecked at h
  trivial

theorem tmp_borrow_unfold_match (s : St) (who : Account) :
    distributeBorrowerComp s who =
    match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex }) := by
  unfold distributeBorrowerComp subChecked
  simp only

theorem plan5_borrowHook_decomp_proof : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.borrowHook who) = some s' →
      ∃ t, updateCompBorrowIndex s = some t ∧ distributeBorrowerComp t who = some s' :=
  fun s who s' h => tmp_borrow_step1b_aux s who s' h

theorem plan5_inj_probe (s : St) (who : Account) (s' : St)
    (h : some (s.withAcct who id) = some s') :
    s.withAcct who id = s' := by
  cases h
  rfl

theorem plan5_try_proof5 (s : St) (who : Account) (s' : St) :
    distributeBorrowerComp s who = some s' →
      accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
          s.borrowState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index)
              s.borrowState.index } := by
  intro h
  have hunfold := tmp_borrow_unfold_match s who
  rw [hunfold] at h
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    plan5_borrower_start_eq _ _
  rw [hstart] at h
  unfold subChecked at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    cases h
    unfold St.withAcct
    have hpt : (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)) (s.accts.getD who noAcct) =
      (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) (s.accts.getD who noAcct) := by
      show ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct) =
        ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)
      have ha1 : (s.accts.getD who noAcct).borrowerIndex = (s.acct who).borrowerIndex := rfl
      have ha2 : (s.accts.getD who noAcct).borrow = (s.acct who).borrow := rfl
      rw [ha1, ha2]
      unfold mulDouble creditFor
      rfl
    have hmod := plan4_modify_congr_at (l := s.accts) (who := who)
      (f := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)))
      (g := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct))) hpt
    rw [hmod]
  · simp only [hle, ↓reduceIte] at h
    simp at h

theorem plan5_try_proof6 (s : St) (who : Account) (s' : St) :
    distributeBorrowerComp s who = some s' →
      accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
          s.borrowState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index)
              s.borrowState.index } := by
  intro h
  unfold distributeBorrowerComp at h
  simp only at h
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    plan5_borrower_start_eq _ _
  -- need to rewrite inside h's match scrutinee; generalize
  have h2 : (match subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
    | none => (none : Option St)
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex })) = some s' := by
    have := h
    rw [hstart] at this
    -- the let borrowerDelta etc may need unfolding; simp the lets
    simp only [subChecked, mulDouble] at this ⊢
    exact this
  unfold subChecked at h2
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h2
    refine ⟨hle, ?_⟩
    cases h2
    unfold St.withAcct
    have hpt : (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)) (s.accts.getD who noAcct) =
      (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) (s.accts.getD who noAcct) := by
      show ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct) =
        ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)
      have ha1 : (s.accts.getD who noAcct).borrowerIndex = (s.acct who).borrowerIndex := rfl
      have ha2 : (s.accts.getD who noAcct).borrow = (s.acct who).borrow := rfl
      rw [ha1, ha2]
      unfold mulDouble creditFor
      rfl
    have hmod := plan4_modify_congr_at (l := s.accts) (who := who)
      (f := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)))
      (g := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct))) hpt
    rw [hmod]
  · simp only [hle, ↓reduceIte] at h2
    simp at h2

theorem td0_call_some_aux_test (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := upd_supply_eq2 s h
  rw [hsub]
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc]
    simp
  · simp only [hc]
    by_cases hc2 : s.blockNumber - s.supplyState.block > 0
    · simp [hc2]
    · simp [hc2]

theorem td0_accrual_le (r idx : Nat) (h : r ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi, hi]
    · simp [hi]
  · simp [hr, h]

theorem td0_getD_bor_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  have hboth := plan2_aux_getD_le s.accts s.supplyState.index s.borrowState.index who hmem
  exact hboth.2

theorem td0_getD_sup_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  unfold St.acct
  have h2 : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index := hmem
  have hS : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (h2 a ha).1
  -- use plan2_aux_getD_le with B := borrow index
  have hboth := plan2_aux_getD_le s.accts s.supplyState.index s.borrowState.index who h2
  exact hboth.1

theorem td0_borrow_sub_eq (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
  unfold subChecked
  simp [hle]

theorem td0_updateBorrow_some2 (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome := by
  unfold updateCompBorrowIndex
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [h]
  rw [hsub]
  by_cases hc : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hc]; simp
  · simp only [hc]
    by_cases hc2 : s.blockNumber - s.borrowState.block > 0
    · simp [hc2]
    · simp [hc2]

theorem td0_updateSupply_some2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked; simp [h]
  rw [hsub]
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc]; simp
  · simp only [hc]
    by_cases hc2 : s.blockNumber - s.supplyState.block > 0
    · simp [hc2]
    · simp [hc2]

theorem td0_distBorrow_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  unfold distributeBorrowerComp
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := plan5_borrower_start_eq _ _
  have hle : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by rw [hstart]; exact h
  have hsub : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = some (s.borrowState.index - (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)) := by
    unfold subChecked; simp [hle]
  simp only []
  rw [hsub]
  simp

theorem td0_distSupply_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  unfold distributeSupplierComp
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := plan4_supplier_start_eq _ _
  have hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by rw [hstart]; exact h
  have hsub : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = some (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) := by
    unfold subChecked; simp [hle]
  simp only []
  rw [hsub]
  simp

theorem td0_updBor_pres (s t : St)
    (h : updateCompBorrowIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.supplyState = s.supplyState ∧ t.borrowState.block = s.blockNumber := by
  have hacc := plan3_updateBorrow_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  refine ⟨rfl, rfl, ?_⟩
  exact (plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)).2.1

theorem td0_updBor_idx_ge (s t : St)
    (h : updateCompBorrowIndex s = some t) :
    s.borrowState.index ≤ t.borrowState.index := by
  have hacc := plan3_updateBorrow_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  show s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
  exact (plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)).1

theorem td0_updBor_acct (s t : St) (who : Account)
    (h : updateCompBorrowIndex s = some t) :
    t.acct who = s.acct who := by
  have hacc := plan3_updateBorrow_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  rfl

theorem td0_updSup_blk (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState ∧ t.supplyState.block = s.blockNumber := by
  have hacc := plan3_updateSupply_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  refine ⟨rfl, rfl, ?_⟩
  exact (plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)).2.1

theorem td0_updSup_idx_ge (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    s.supplyState.index ≤ t.supplyState.index := by
  have hacc := plan3_updateSupply_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  show s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
  exact (plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)).1

theorem td0_updSup_acct (s t : St) (who : Account)
    (h : updateCompSupplyIndex s = some t) :
    t.acct who = s.acct who := by
  have hacc := plan3_updateSupply_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  rfl

theorem td0_setSup_pres2 (s mid : St) (a : Nat)
    (h : setSupplySpeed s a = some mid) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧ mid.accts = s.accts := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    rw [← h]
    exact ⟨rfl, rfl, rfl⟩
  · simp [heq] at h
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      rw [← h]
      have hacc := plan3_updateSupply_accrue s u hu
      obtain ⟨_, ht⟩ := hacc
      rw [ht]
      exact ⟨rfl, rfl, rfl⟩

theorem td0_setComp_exists (s : St) (a b : Nat) (s' : St)
    (h : setCompSpeedInternal s a b = some s') :
    ∃ mid, setSupplySpeed s a = some mid ∧ setBorrowSpeed mid b = some s' :=
  tmp_mid_exists5 s a b s' h

theorem td0_setBor_pres2 (s mid : St) (b : Nat)
    (h : setBorrowSpeed s b = some mid) :
    mid.supplyState = s.supplyState ∧ mid.blockNumber = s.blockNumber ∧ mid.accts = s.accts := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    rw [← h]
    exact ⟨rfl, rfl, rfl⟩
  · simp [heq] at h
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      rw [← h]
      have hacc := plan3_updateBorrow_accrue s u hu
      obtain ⟨_, ht⟩ := hacc
      rw [ht]
      exact ⟨rfl, rfl, rfl⟩

theorem plan8_upgrade_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed +
      ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed ≤
      L.unindexedSupply + L.unindexedBorrow := by
  have hsup_blk := plan6_up_sup_blk2 L
  have hbor_blk := plan6_up_bor_blk2 L
  have hsup_spd := plan6_up_sup_spd2 L
  have hbor_spd := plan6_up_bor_spd2 L
  have hblk := plan6_up_blk2 L
  have hrw : ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed +
      ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed =
      ((L.blockNumber - (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock)) * L.compSpeed +
       ((L.blockNumber - (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock)) * L.compSpeed)) := by
    rw [hsup_blk, hsup_spd, hblk, hbor_blk, hbor_spd]
  rw [hrw]
  unfold Legacy.unindexedSupply Legacy.unindexedBorrow
  have h1 : (L.blockNumber - (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock)) * L.compSpeed ≤
      (L.blockNumber - L.supplyBlock) * L.compSpeed := by
    by_cases hsup : L.supplyIndex = 0
    · simp [hsup]
    · simp [hsup]
  have h2 : (L.blockNumber - (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock)) * L.compSpeed ≤
      (L.blockNumber - L.borrowBlock) * L.compSpeed := by
    by_cases hbor : L.borrowIndex = 0
    · simp [hbor]
    · simp [hbor]
  exact Nat.add_le_add h1 h2

theorem plan8_arith_initial (C P Pleg U US UB : Nat)
    (hP : P ≤ Pleg) (hU : U ≤ US + UB) :
    C * doubleScale + P + U * doubleScale ≤
      (C + (Pleg / doubleScale + US + UB)) * doubleScale +
        (doubleScale - 1) :=
  plan6_generic_bound2 C P U Pleg US UB doubleScale plan6_dspos_aux hP hU

theorem plan6_initial_potential_le (L : Legacy) (hL : L.WellFormed) :
    (upgrade L).credited * doubleScale +
        ((upgrade L).accts.map fun a =>
          a.supply * ((upgrade L).supplyState.index -
            accrualStart a.supplierIndex (upgrade L).supplyState.index) +
          a.borrow * ((upgrade L).borrowState.index -
            accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum +
        (((upgrade L).blockNumber - (upgrade L).supplyState.block) *
            (upgrade L).supplyState.speed +
          ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
            (upgrade L).borrowState.speed) * doubleScale ≤
      ((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1) := by
  have hP : ((upgrade L).accts.map fun a =>
          a.supply * ((upgrade L).supplyState.index -
            accrualStart a.supplierIndex (upgrade L).supplyState.index) +
          a.borrow * ((upgrade L).borrowState.index -
            accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum ≤
      (L.accts.map L.pendingScaled).sum :=
    plan8_pending_sum_le L hL
  have hU : ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed +
      ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed ≤
      L.unindexedSupply + L.unindexedBorrow :=
    plan8_upgrade_unindexed_le L
  have h := plan8_arith_initial ((upgrade L).credited)
    (((upgrade L).accts.map fun a =>
          a.supply * ((upgrade L).supplyState.index -
            accrualStart a.supplierIndex (upgrade L).supplyState.index) +
          a.borrow * ((upgrade L).borrowState.index -
            accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum)
    ((L.accts.map L.pendingScaled).sum)
    (((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed +
      ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed)
    L.unindexedSupply L.unindexedBorrow hP hU
  have howed : L.owed = (L.accts.map L.pendingScaled).sum / doubleScale + L.unindexedSupply + L.unindexedBorrow := rfl
  rw [howed]
  exact h

def Pot (s : St) : Nat :=
  s.credited * doubleScale +
    (s.accts.map fun a =>
      a.supply * (s.supplyState.index -
        accrualStart a.supplierIndex s.supplyState.index) +
      a.borrow * (s.borrowState.index -
        accrualStart a.borrowerIndex s.borrowState.index)).sum +
    ((s.blockNumber - s.supplyState.block) * s.supplyState.speed +
      (s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale

theorem pot_eq_test (s : St) : Pot s = Pot s := rfl
#check ProofForgeFin.DeFi.Rewards.pending
#check ProofForgeFin.DeFi.Rewards.credit
#check ProofForgeFin.DeFi.Rewards.indexDelta
#check ProofForgeFin.DeFi.Rewards.firstStart

theorem firstStart_probe (init recorded index : Nat) :
    ProofForgeFin.DeFi.Rewards.firstStart init recorded index =
    ProofForgeFin.DeFi.Rewards.firstStart init recorded index := rfl

theorem plan6_upgrade_pending_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      L.pendingScaled a := by
  exact plan6_upgrade_pending_le_aux_test L a hL ha

theorem plan4_claim_eq_hook_binds_aux (s : St) (who : Account) :
    claimComp s who =
      ((updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who)).bind
        (fun m1 => ((updateCompSupplyIndex m1).bind (fun s3 => distributeSupplierComp s3 who)).bind
          (fun m2 => some (grantCompInternal m2 who))) := by
  unfold claimComp
  simp only [Option.bind_assoc]
  rfl

theorem plan4_claim_eq_hook_binds_step (s : St) (who : Account) :
    (comptroller s (.borrowHook who)).bind
        (fun m1 => (comptroller m1 (.supplyHook who)).bind
          (fun m2 => some (grantCompInternal m2 who)))
    = ((updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who)).bind
        (fun m1 => ((updateCompSupplyIndex m1).bind (fun s3 => distributeSupplierComp s3 who)).bind
          (fun m2 => some (grantCompInternal m2 who))) := by
  rfl

theorem plan4_claim_eq_hook_binds_final (s : St) (who : Account) :
    comptroller s (.claim who) =
      (comptroller s (.borrowHook who)).bind
        (fun m1 => (comptroller m1 (.supplyHook who)).bind
          (fun m2 => some (grantCompInternal m2 who))) := by
  calc comptroller s (.claim who) = claimComp s who := rfl
    _ = ((updateCompBorrowIndex s).bind (fun s1 => distributeBorrowerComp s1 who)).bind
        (fun m1 => ((updateCompSupplyIndex m1).bind (fun s3 => distributeSupplierComp s3 who)).bind
          (fun m2 => some (grantCompInternal m2 who))) := plan4_claim_eq_hook_binds_aux s who
    _ = (comptroller s (.borrowHook who)).bind
        (fun m1 => (comptroller m1 (.supplyHook who)).bind
          (fun m2 => some (grantCompInternal m2 who))) := (plan4_claim_eq_hook_binds_step s who).symm

theorem plan4_claim_unfold_probe (s : St) (who : Account) :
    claimComp s who =
      Option.bind (updateCompBorrowIndex s) (fun s1 => Option.bind (distributeBorrowerComp s1 who) (fun s2 => Option.bind (updateCompSupplyIndex s2) (fun s3 => Option.bind (distributeSupplierComp s3 who) (fun s4 => some (grantCompInternal s4 who))))) := by rfl

theorem plan6_run_potential_le_auxkey2 (sp : Nat × Nat) (s : St) (ops : List Op) :
    td0_Inv sp s → Pot (run comptroller s ops) ≤ Pot s + emitted sp ops * doubleScale := by
  intro hInv
  induction ops generalizing sp s with
  | nil => simp [run, Pot]
  | cons op rest ih =>
    have hcons : Consistent s := hInv.1
    have hsp : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2 := ⟨hInv.2.1, hInv.2.2⟩
    have hstep := plan6_exec_potential_step s op sp hcons hsp
    obtain ⟨hle, hcons1, hsp1⟩ := hstep
    have hPot1 : Pot (exec comptroller s op) ≤ Pot s + emittedBy sp op * doubleScale := hle
    have hInv1 : td0_Inv (nextSpeeds sp op) (exec comptroller s op) := ⟨hcons1, hsp1.1, hsp1.2⟩
    have hIH := ih (nextSpeeds sp op) (exec comptroller s op) hInv1
    have hrun : run comptroller s (op :: rest) = run comptroller (exec comptroller s op) rest := rfl
    have hem : emitted sp (op :: rest) = emittedBy sp op + emitted (nextSpeeds sp op) rest := rfl
    calc Pot (run comptroller s (op :: rest))
        = Pot (run comptroller (exec comptroller s op) rest) := by rw [hrun]
      _ ≤ Pot (exec comptroller s op) + emitted (nextSpeeds sp op) rest * doubleScale := hIH
      _ ≤ (Pot s + emittedBy sp op * doubleScale) + emitted (nextSpeeds sp op) rest * doubleScale := by
          exact Nat.add_le_add_right hPot1 _
      _ = Pot s + emitted sp (op :: rest) * doubleScale := by
          rw [hem, Nat.add_mul, Nat.add_assoc]

theorem plan6_run_potential_le (L : Legacy) (ops : List Op)
    (hL : L.WellFormed) :
    (run comptroller (upgrade L) ops).credited * doubleScale +
          ((run comptroller (upgrade L) ops).accts.map fun a =>
            a.supply * ((run comptroller (upgrade L) ops).supplyState.index -
              accrualStart a.supplierIndex
                (run comptroller (upgrade L) ops).supplyState.index) +
            a.borrow * ((run comptroller (upgrade L) ops).borrowState.index -
              accrualStart a.borrowerIndex
                (run comptroller (upgrade L) ops).borrowState.index)).sum +
          (((run comptroller (upgrade L) ops).blockNumber -
              (run comptroller (upgrade L) ops).supplyState.block) *
              (run comptroller (upgrade L) ops).supplyState.speed +
            ((run comptroller (upgrade L) ops).blockNumber -
              (run comptroller (upgrade L) ops).borrowState.block) *
              (run comptroller (upgrade L) ops).borrowState.speed) *
            doubleScale ≤
        ((upgrade L).credited + L.owed +
          emitted (L.compSpeed, L.compSpeed) ops) * doubleScale +
          (doubleScale - 1) := by
  have hInv : td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := td0_inv_upgrade L hL
  have hkey := plan6_run_potential_le_auxkey2 (L.compSpeed, L.compSpeed) (upgrade L) ops hInv
  have hinit := plan6_initial_potential_le L hL
  have hmid : Pot (run comptroller (upgrade L) ops)
      ≤ (((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1)) +
        emitted (L.compSpeed, L.compSpeed) ops * doubleScale :=
    Nat.le_trans hkey (Nat.add_le_add_right hinit _)
  have heq : (((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1)) +
        emitted (L.compSpeed, L.compSpeed) ops * doubleScale =
      ((upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops) * doubleScale +
        (doubleScale - 1) := by
    have hmul : ((upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops) * doubleScale =
      ((upgrade L).credited + L.owed) * doubleScale + emitted (L.compSpeed, L.compSpeed) ops * doubleScale := by
      rw [Nat.add_mul]
    omega
  have hcomb : Pot (run comptroller (upgrade L) ops) ≤
      ((upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops) * doubleScale +
        (doubleScale - 1) := heq ▸ hmid
  exact hcomb

theorem dummy_chk : True := trivial

theorem supplyHook_isSome (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.supplyHook who)).isSome = true := by
  have hsupBlk : s.supplyState.block ≤ s.blockNumber := hs.1
  have hsupLe : (s.acct who).supplierIndex ≤ s.supplyState.index :=
    td0_getD_sup_le s who hs
  obtain ⟨u, hu, hleU, hacU, hborU, hblkU⟩ := plan0_updateSupply_exists s hsupBlk
  have hacctU : u.acct who = s.acct who := td0_updSup_acct s u who hu
  have hleU' : (u.acct who).supplierIndex ≤ u.supplyState.index := by
    rw [hacctU]
    exact Nat.le_trans hsupLe hleU
  have hboundU : (u.acct who).supplierIndex = 0 ∨ (u.acct who).supplierIndex ≤ u.supplyState.index :=
    Or.inr hleU'
  obtain ⟨s', hs', _, _, _⟩ := plan0_distributeSupplier_exists u who hboundU
  have hcomp : comptroller s (.supplyHook who) = (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) := rfl
  rw [hcomp, hu]
  simp only [Option.bind_some]
  rw [hs']
  rfl

theorem borrowHook_isSome (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.borrowHook who)).isSome = true := by
  have hborBlk : s.borrowState.block ≤ s.blockNumber := hs.2.1
  have hborLe : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
    td0_getD_bor_le s who hs
  obtain ⟨u, hu, hleU, hacU, hsupU, hblkU⟩ := plan0_updateBorrow_exists s hborBlk
  have hacctU : u.acct who = s.acct who := by
    have h := td0_updBor_acct s u who hu
    exact h
  have hleU' : (u.acct who).borrowerIndex ≤ u.borrowState.index := by
    rw [hacctU]
    exact Nat.le_trans hborLe hleU
  have hboundU : (u.acct who).borrowerIndex = 0 ∨ (u.acct who).borrowerIndex ≤ u.borrowState.index :=
    Or.inr hleU'
  obtain ⟨s', hs', _, _, _⟩ := plan0_distributeBorrower_exists_PROBE u who hboundU
  have hcomp : comptroller s (.borrowHook who) = (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) := rfl
  rw [hcomp, hu]
  simp only [Option.bind_some]
  rw [hs']
  rfl

theorem probe_accr (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := aux_probe_acc1 sd now total

theorem claim_simp_probe (s u1 : St) (who : Account)
    (hu1 : updateCompBorrowIndex s = some u1) :
    (Option.bind (updateCompBorrowIndex s) fun s1 => Option.bind (distributeBorrowerComp s1 who) fun s2 => some s2) =
    Option.bind (distributeBorrowerComp u1 who) fun s2 => some s2 := by
  simp [hu1]

theorem tmp_chk2 : True := trivial

theorem tmp_lib1 : True := trivial

theorem nb_ds_pos : 0 < doubleScale := by unfold doubleScale; decide
#check @td0_potentialTo
#check @td0_Inv
#check @td0_pendingTo
#check @td0_unindexedTo
#check @emittedBy
#check @nextSpeeds
#check @exec
#check @run

theorem nb_div_mul_le (a b : Nat) : a / b * b ≤ a := by
  have h : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have h2 : a / b * b = b * (a / b) := Nat.mul_comm _ _
  omega

theorem nb_sup_le_total (s : St) (who : Account) : (s.acct who).supply ≤ totalSupply s := by
  unfold St.acct totalSupply
  induction s.accts generalizing who with
  | nil => simp [noAcct]
  | cons hd tl ih =>
    cases who with
    | zero => simp
    | succ n => simp; exact Nat.le_trans (ih n) (Nat.le_add_left _ _)

theorem nb_bor_le_total (s : St) (who : Account) : (s.acct who).borrow ≤ totalBorrows s := by
  unfold St.acct totalBorrows
  induction s.accts generalizing who with
  | nil => simp [noAcct]
  | cons hd tl ih =>
    cases who with
    | zero => simp
    | succ n => simp; exact Nat.le_trans (ih n) (Nat.le_add_left _ _)

theorem nb_ds_mul_credit_le (u st idx : Nat) : doubleScale * creditFor u st idx ≤ u * (idx - st) := by
  unfold creditFor
  have h : (u * (idx - st) / doubleScale) * doubleScale ≤ u * (idx - st) := nb_div_mul_le _ _
  have hc : doubleScale * (u * (idx - st) / doubleScale) = (u * (idx - st) / doubleScale) * doubleScale := Nat.mul_comm _ _
  rw [hc]; exact h

theorem nb_acc_gap (rec idx0 idx1 : Nat) (hle : idx0 ≤ idx1) :
    (idx1 - accrualStart rec idx1) ≤ (idx0 - accrualStart rec idx0) + (idx1 - idx0) := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    simp only [↓reduceIte]
    by_cases h0 : compInitialIndex ≤ idx0
    · have h1 : compInitialIndex ≤ idx1 := Nat.le_trans h0 hle
      simp [h0, h1]
      omega
    · by_cases h1 : compInitialIndex ≤ idx1
      · simp [h0, h1]
        omega
      · simp [h0, h1]
        omega
  · simp [hr]
    omega

theorem tst_getmod (l : List Acct) (n : Nat) (f : Acct → Acct) :
    (l.modify n f).getD n noAcct = f (l.getD n noAcct) ∨ (l.modify n f).getD n noAcct = l.getD n noAcct := by
  have h := ProofForgeFin.Ledger.getD_modify l n n f noAcct
  by_cases hn : n < l.length
  · have h2 : (l.modify n f).getD n noAcct = f (l.getD n noAcct) := by
      rw [h]
      simp [hn]
    exact Or.inl h2
  · have h2 : (l.modify n f).getD n noAcct = l.getD n noAcct := by
      rw [h]
      simp [hn]
    exact Or.inr h2

theorem recorded_le_of_accrual_le_aux (r idx : Nat)
    (h : accrualStart r idx ≤ idx) : r ≤ idx := by
  by_cases hr : r = 0
  · subst hr; exact Nat.zero_le _
  · have heq : accrualStart r idx = r := by unfold accrualStart; simp [hr]
    rw [heq] at h; exact h

theorem tmp_claim_isSome3 (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.claim who)).isSome = true := by
  have hsupBlk : s.supplyState.block ≤ s.blockNumber := hs.1
  have hborBlk : s.borrowState.block ≤ s.blockNumber := hs.2.1
  have hsupLe : (s.acct who).supplierIndex ≤ s.supplyState.index :=
    td0_getD_sup_le s who hs
  have hborLe : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
    td0_getD_bor_le s who hs
  obtain ⟨u1, hu1, hleU1, hacU1, hsupU1, hblkU1⟩ := plan0_updateBorrow_exists s hborBlk
  have hacctU1 : u1.acct who = s.acct who := by unfold St.acct; rw [hacU1]
  have hborLeU1 : (u1.acct who).borrowerIndex ≤ u1.borrowState.index := by
    rw [hacctU1]; exact Nat.le_trans hborLe hleU1
  obtain ⟨s1, hs1, hpresS1, hsupS1, hborS1, hblkS1⟩ := plan0_distributeBorrower_exists_PROBE u1 who (Or.inr hborLeU1)
  have hsupBlkS1 : s1.supplyState.block ≤ s1.blockNumber := by
    rw [hsupS1, hsupU1, hblkS1, hblkU1]; exact hsupBlk
  have hsupLeS1 : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
    rw [hpresS1, hacctU1, hsupS1, hsupU1]; exact hsupLe
  obtain ⟨u2, hu2, hleU2, hacU2, hborU2, hblkU2⟩ := plan0_updateSupply_exists s1 hsupBlkS1
  have hacctU2 : u2.acct who = s1.acct who := by unfold St.acct; rw [hacU2]
  have hsupLeU2 : (u2.acct who).supplierIndex ≤ u2.supplyState.index := by
    rw [hacctU2]; exact Nat.le_trans hsupLeS1 hleU2
  obtain ⟨s2, hs2, _, _, _⟩ := plan0_distributeSupplier_exists u2 who (Or.inr hsupLeU2)
  have hclaim : claimComp s who =
      ((updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who)).bind
        (fun m1 => ((updateCompSupplyIndex m1).bind (fun t => distributeSupplierComp t who)).bind
          (fun m2 => some (grantCompInternal m2 who))) :=
    plan4_claim_eq_hook_binds_aux s who
  have hcomp : comptroller s (.claim who) = claimComp s who := rfl
  rw [hcomp, hclaim, hu1]
  simp only [Option.bind_some]
  rw [hs1]
  simp only [Option.bind_some]
  rw [hu2]
  simp only [Option.bind_some]
  rw [hs2]
  rfl

theorem req_calls_succeed_proof : CallsSucceed comptroller := by
  intro s c hs
  cases c with
  | supplyHook who =>
    have h := supplyHook_isSome s who hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩
  | borrowHook who =>
    have h := borrowHook_isSome s who hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩
  | claim who =>
    have h := tmp_claim_isSome3 s who hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩
  | setSpeeds a b =>
    have h := td0_setSpeeds_some_clean2 s a b hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩

def snippetProbeB : Nat := 1

def snippetProbeC : Nat := 2

def snippetProbeD : Nat := 3

theorem libPendingEq (u s i : Nat) : ProofForgeFin.DeFi.Rewards.pending u s i = u * (i - s) := by rfl

theorem libCreditEq (o u s i : Nat) : ProofForgeFin.DeFi.Rewards.credit o u s i = u * (i - s) / o := by rfl

def snippetProbeE : Nat := 4

def snippetProbeF : Nat := 5

def snippetProbeG : Nat := 6

theorem tmp_pot_eq_td0 (s : St) : Pot s = td0_potential s := by
  unfold Pot td0_potential td0_pending td0_pendingAcct td0_unindexed
  have h1 : s.credited * doubleScale = doubleScale * s.credited := Nat.mul_comm _ _
  have h2 : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed +
      (s.blockNumber - s.borrowState.block) * s.borrowState.speed) * doubleScale =
    doubleScale * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed +
      (s.blockNumber - s.borrowState.block) * s.borrowState.speed) := Nat.mul_comm _ _
  rw [h1, h2]

theorem plan18_run_potential_le (L : Legacy) (ops : List Op) (hL : L.WellFormed) :
    td0_potential (run comptroller (upgrade L) ops) ≤
      td0_potential (upgrade L) + doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by
  have hInv : td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := td0_upgrade_inv L hL
  have hPot := plan6_run_potential_le_auxkey2 (L.compSpeed, L.compSpeed) (upgrade L) ops hInv
  rw [tmp_pot_eq_td0, tmp_pot_eq_td0] at hPot
  calc td0_potential (run comptroller (upgrade L) ops)
      ≤ td0_potential (upgrade L) + emitted (L.compSpeed, L.compSpeed) ops * doubleScale := hPot
    _ = td0_potential (upgrade L) + doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by rw [Nat.mul_comm]


theorem plan18_upgrade_potential_le (L : Legacy) (hL : L.WellFormed) :
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  have hP : td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
    apply plan9_pending_sum_le
    intro a ha
    exact aux_pend_up_le L hL a ha
  have hU : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow :=
    tmp_upg_unidx_le L
  unfold td0_potential
  have h1 : doubleScale * td0_unindexed (upgrade L) ≤ doubleScale * (L.unindexedSupply + L.unindexedBorrow) :=
    Nat.mul_le_mul_left doubleScale hU
  omega


theorem plan18_scaled_credited_le (L : Legacy) (ops : List Op) (hL : L.WellFormed) :
    doubleScale * (run comptroller (upgrade L) ops).credited ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by
  have h2 := plan18_run_potential_le L ops hL
  have h3 := plan18_upgrade_potential_le L hL
  have h1 : doubleScale * (run comptroller (upgrade L) ops).credited ≤
      td0_potential (run comptroller (upgrade L) ops) := by
    unfold td0_potential
    omega
  omega




theorem plan18_upgrade_potential_le_aux_try (L : Legacy) (hL : L.WellFormed) :
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  have hP : td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
    apply plan9_pending_sum_le
    intro a ha
    exact aux_pend_up_le L hL a ha
  have hU : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow :=
    tmp_upg_unidx_le L
  unfold td0_potential
  have h1 : doubleScale * td0_unindexed (upgrade L) ≤ doubleScale * (L.unindexedSupply + L.unindexedBorrow) :=
    Nat.mul_le_mul_left doubleScale hU
  omega

theorem plan18_upgrade_potential_le_newname (L : Legacy) (hL : L.WellFormed) :
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) :=
  plan18_upgrade_potential_le_aux_try L hL

theorem plan18_scaled_credited_le_proof_tmp (L : Legacy) (ops : List Op) (hL : L.WellFormed) :
    doubleScale * (run comptroller (upgrade L) ops).credited ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by
  have h2 := plan18_run_potential_le L ops hL
  have h3 := plan18_upgrade_potential_le L hL
  have h1 : doubleScale * (run comptroller (upgrade L) ops).credited ≤
      td0_potential (run comptroller (upgrade L) ops) := by
    unfold td0_potential
    omega
  omega

theorem plan18_rewards_bounded_auxcheck : RewardsBounded comptroller := by
  intro L ops hL
  exact td0_rewards_bound_of_scaled (run comptroller (upgrade L) ops) L (emitted (L.compSpeed, L.compSpeed) ops) (plan18_scaled_credited_le_proof_tmp L ops hL)

theorem plan18_rewards_bounded : RewardsBounded comptroller := by
  intro L ops hL
  exact td0_rewards_bound_of_scaled (run comptroller (upgrade L) ops) L (emitted (L.compSpeed, L.compSpeed) ops) (plan18_scaled_credited_le_proof_tmp L ops hL)

theorem req_rewards_bounded_aux_tmp : RewardsBounded comptroller := plan18_rewards_bounded

theorem supplyDeltaBound3 (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤ (now - sd.block) * sd.speed * doubleScale := by
  have hpr : (accrueSide sd now total).index = sd.index + (if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
      then (now - sd.block) * sd.speed * doubleScale / total else 0) := by
    unfold accrueSide
    by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [hc]
  rw [hpr, Nat.add_sub_cancel_left]
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · have h2 : (total * if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then (now - sd.block) * sd.speed * doubleScale / total else 0)
        = total * ((now - sd.block) * sd.speed * doubleScale / total) := by simp [hc]
    rw [h2]
    have hdiv : ((now - sd.block) * sd.speed * doubleScale / total) * total
        ≤ (now - sd.block) * sd.speed * doubleScale := nb_div_mul_le _ _
    have hcomm : total * ((now - sd.block) * sd.speed * doubleScale / total)
        = ((now - sd.block) * sd.speed * doubleScale / total) * total := Nat.mul_comm _ _
    rw [hcomm]
    exact hdiv
  · have h2 : (total * if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then (now - sd.block) * sd.speed * doubleScale / total else 0) = 0 := by simp [hc]
    rw [h2]
    exact Nat.zero_le _

theorem plan19_exec_potentialTo_step (sp : Nat × Nat) (s : St) (op : Op) (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s op) who ≤
        td0_potentialTo s who + doubleScale * emittedBy sp op ∧
      td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by sorry

theorem plan19_run_potentialTo_le (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (run comptroller s ops) who ≤
        td0_potentialTo s who + doubleScale * emitted sp ops ∧
      td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by sorry

theorem plan19_potentialTo_upgrade_le (L : Legacy) (who : Account) :
    L.WellFormed →
    td0_potentialTo (upgrade L) who ≤
      doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who := by sorry

theorem plan19_scaled_creditedTo_run_le (L : Legacy) (ops : List Op) (who : Account) :
    L.WellFormed →
    doubleScale * (run comptroller (upgrade L) ops).creditedTo who ≤
      doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by sorry

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hs
  cases c with
  | supplyHook who =>
    have h := supplyHook_isSome s who hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩
  | borrowHook who =>
    have h := borrowHook_isSome s who hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩
  | claim who =>
    have h := tmp_claim_isSome3 s who hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩
  | setSpeeds a b =>
    have h := td0_setSpeeds_some_clean2 s a b hs
    simp [Option.isSome_iff_exists] at h ⊢
    obtain ⟨s', hs'⟩ := h
    exact ⟨s', hs'⟩

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  have h3 := plan2_supplyHook_eq s who s' h
  obtain ⟨hb, hle, heq⟩ := h3
  unfold SupplyDistributed
  exact ⟨hb, hle, heq⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  have h3 := borHook_eq2 s who s' h
  obtain ⟨hb, hle, heq⟩ := h3
  unfold BorrowDistributed
  exact ⟨hb, hle, heq⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  obtain ⟨m1, m2, hb_hook, hs_hook, hgrant⟩ := plan3_claim_decompose_new s who s' h
  have hb : BorrowDistributed s who m1 := req_borrow_hook s who m1 hb_hook
  have hs : SupplyDistributed m1 who m2 := req_supply_hook m1 who m2 hs_hook
  exact ⟨m1, m2, hb, hs, by rw [hgrant, grant_eq_full]⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  obtain ⟨m, hm1, hm2⟩ := plan5_setSpeeds_decomp s a b s' h
  exact plan5_speedsSet_of_steps s a b m s' hm1 hm2

theorem req_rewards_bounded : RewardsBounded comptroller := plan18_rewards_bounded

theorem req_account_bounded     : AccountBounded comptroller := sorry

theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
