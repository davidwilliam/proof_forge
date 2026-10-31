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





theorem plan6_upgrade_pending_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      L.pendingScaled a := by
  sorry



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

theorem req_calls_succeed       : CallsSucceed comptroller := sorry

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

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry

theorem req_account_bounded     : AccountBounded comptroller := sorry

theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
