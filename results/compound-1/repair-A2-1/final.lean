import CompRewards.Spec
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

theorem t1b (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [h]

theorem t2b (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  unfold updateCompSupplyIndex
  have h2 := t1b s h
  simp only [h2]
  split
  · simp
  · split
    · simp
    · simp

theorem updSup_red (s : St) (d : Nat)
    (hsub : subChecked s.blockNumber s.supplyState.block = some d) :
    updateCompSupplyIndex s =
      (if d > 0 ∧ s.supplyState.speed > 0 then
        let supplyTokens := totalSupply s
        let compAccrued := d * s.supplyState.speed
        let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
        some { s with supplyState :=
          { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
      else if d > 0 then
        some { s with supplyState := { s.supplyState with block := s.blockNumber } }
      else some s) := by
  unfold updateCompSupplyIndex
  rw [hsub]

theorem side_block_idem (sd : Side) (n : Nat) (h : sd.block = n) : ({ sd with block := n } : Side) = sd := by
  cases sd with | mk i b sp =>
    simp_all

theorem st_supply_block_idem (s : St) (h : s.supplyState.block = s.blockNumber) :
    ({ s with supplyState := ({ s.supplyState with block := s.blockNumber } : Side) } : St) = s := by
  cases s with | mk b sup bor res accs =>
    simp_all
    exact side_block_idem sup b h

theorem cSUSHI_test : True := by
  trivial

#check comptroller
#check upgrade
#check run
#check exec

theorem borrow_bind_lemma (o : Option St) (f : St → Option St) (s' : St)
    (h : (o.bind f) = some s') : ∃ m, o = some m ∧ f m = some s' := by
  cases ho : o with
  | none => simp [ho] at h
  | some m => exact ⟨m, rfl, by simp [ho] at h; exact h⟩

theorem updBor_block_le2 (s : St) (m : St)
    (h : updateCompBorrowIndex s = some m) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem accrue_if_true (sd : Side) (now total : Nat)
    (h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total) :
    accrueSide sd now total =
      { sd with index := sd.index + (now - sd.block) * sd.speed * doubleScale / total, block := now } := by
  unfold accrueSide
  simp [h]

theorem accrue_if_false (sd : Side) (now total : Nat)
    (h : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)) :
    accrueSide sd now total = { sd with block := now } := by
  unfold accrueSide
  simp [h]

theorem helper_frac_eq (a b : Nat) : fraction a b = a * doubleScale / b := by rfl

theorem helper_subChecked_eq (a b : Nat) : subChecked a b = if b ≤ a then some (a - b) else none := by rfl

theorem helper_updSup_some (s : St) (u : St) (h : updateCompSupplyIndex s = some u) : s.supplyState.block ≤ s.blockNumber := by unfold updateCompSupplyIndex subChecked at h; by_cases hle : s.supplyState.block ≤ s.blockNumber <;> simp [hle] at h ⊢ <;> exact hle

theorem foo_test : True := by trivial

theorem tactic_probe1 (a b : Nat) (h : a ≤ b) : a - b = 0 := by simp [Nat.sub_eq_zero_of_le h]

theorem omega_probe (a : Nat) (h : a < 5) : a < 6 := by omega

theorem ring_probe (a : Nat) : a + 0 = a := by simp

theorem updSup_eq_accrue (s : St) (u : St) (h : updateCompSupplyIndex s = some u) : s.supplyState.block ≤ s.blockNumber := by exact helper_updSup_some s u h

def testLegacy : Legacy :=
  { blockNumber := 100, compSpeed := 0,
    supplyIndex := 0, supplyBlock := 100,
    borrowIndex := 0, borrowBlock := 100,
    supplyStart := 0, borrowStart := 0,
    reserve := 100000000000000000000000,
    accts := [{ supply := 0, borrow := 18977306140567618322762,
                supplierIndex := 0, borrowerIndex := 0,
                accrued := 0, wallet := 0 }] }

def testUpgrade : St := upgrade testLegacy

#check testUpgrade

def testAfterAdvance : St := { testUpgrade with blockNumber := testUpgrade.blockNumber + 139 }

def testClaim : Option St := comptroller testAfterAdvance (.claim 0)

def testCred : Option Nat := testClaim.map (fun s => (s.acct 0).accrued + (s.acct 0).wallet)

-- evaluate via decide
example : testUpgrade.supplyState.index = 1000000000000000000000000000000000000 := by rfl
example : testUpgrade.borrowState.index = 1000000000000000000000000000000000000 := by rfl
example : (testClaim.map (fun s => (s.acct 0).accrued)).getD 999 = 0 := by rfl

theorem probe_lemmas : True := by trivial
#check CompRewards.doubleScale
#check CompRewards.compInitialIndex

theorem check_wallet_phantom : (testClaim.map (fun s => (s.acct 0).wallet)).getD 999 = 0 := by rfl

theorem check_credited_phantom : (testClaim.map (fun s => (s.acct 0).accrued + (s.acct 0).wallet)).getD 999 = 0 := by rfl

theorem check_claim_isSome : testClaim.isSome = true := by rfl

theorem probe_defs : True := by trivial
#check St.credited
#check Legacy.owed
#check emitted
#check run
#check exec

theorem probe_defs2 : True := by trivial
#check St.credited
#check Legacy.owed
#check List.sum

def supplyPend (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)

def borrowPend (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def pendSum (s : St) : Nat :=
  (s.accts.map fun a => supplyPend s a + borrowPend s a).sum

def unidx (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def measure (s : St) : Nat :=
  s.credited * doubleScale + pendSum s + unidx s * doubleScale

theorem measure_unfold (s : St) :
    measure s = s.credited * doubleScale + pendSum s + unidx s * doubleScale := by rfl

theorem probe_sum1 : True := by trivial
#check List.sum
#check List.map
#check List.getD
#check List.modify
#check Nat.div_add_mod
#check Nat.div_le_div_right
#check Nat.mul_div_cancel

theorem probe_list_api : True := by trivial
#check List.modify
#check List.getD
#check List.sum
#check List.map
#check List.length

theorem probe_account_bounded_shape : True := by trivial
#check AccountBounded
#check RewardsBounded
#check run
#check exec
#check Consistent
#check upgrade
#check Legacy.WellFormed
#check Legacy.owedTo
#check emitted
#check speedsAfter
#check comptroller
#check accrueSide
#check accrualStart

theorem lem_probe : True := by trivial
#check List.sum_append

theorem t_getD_modify (xs : List Acct) (i : Nat) (f : Acct → Acct) :
    (xs.modify i f).length = xs.length := by simp
#check List.modify
#check List.length_modify

theorem dummy_probe : True := by trivial

theorem dummy3 : True := by trivial
#check Lean.versionString

theorem bank_test1 : doubleScale > 0 := by unfold doubleScale; omega
#check List.modify
#check List.getD
#check Nat.div_mul_le_self
#check Nat.mul_le_mul
#check Nat.le_of_mul_le_mul_right

theorem bank_probe2 : True := by trivial
#check List.modify
#check List.get
#check List.getD

theorem aux_updBor_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  unfold updateCompBorrowIndex subChecked
  simp only [h, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem aux_updSup_idx_ge (s u : St) (h : updateCompSupplyIndex s = some u) :
    s.supplyState.index ≤ u.supplyState.index := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · cases h; simp
  · simp [hle] at h

theorem aux_updBor_idx_ge (s u : St) (h : updateCompBorrowIndex s = some u) :
    s.borrowState.index ≤ u.borrowState.index := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · cases h; simp
  · simp [hle] at h

theorem probe_modify_sig : True := by trivial
#check @List.modify
#check @List.getD
#check @St.acct
#check @Consistent
#check @updateCompSupplyIndex
#check @distributeSupplierComp

theorem aux_updSup_accts (s u : St) (h : updateCompSupplyIndex s = some u) :
    u.accts = s.accts := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h; rfl
  · simp [hle] at h

theorem aux_updSup_borrow (s u : St) (h : updateCompSupplyIndex s = some u) :
    u.borrowState = s.borrowState := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h; rfl
  · simp [hle] at h

theorem aux_updSup_blk (s u : St) (h : updateCompSupplyIndex s = some u) :
    u.blockNumber = s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h; rfl
  · simp [hle] at h

theorem aux_updBor_accts (s u : St) (h : updateCompBorrowIndex s = some u) :
    u.accts = s.accts := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h; rfl
  · simp [hle] at h

theorem aux_updBor_supply (s u : St) (h : updateCompBorrowIndex s = some u) :
    u.supplyState = s.supplyState := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h; rfl
  · simp [hle] at h

theorem aux_updBor_blk (s u : St) (h : updateCompBorrowIndex s = some u) :
    u.blockNumber = s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h; rfl
  · simp [hle] at h

theorem probe_list2 : True := by trivial
#check @List.getD
#check @List.modify_eq_nil_iff
#check @List.length_modify
#check @List.getElem_modify

theorem plan0_updateSupply_spec (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ m, updateCompSupplyIndex s = some m ∧ m.accts = s.accts ∧
      m.blockNumber = s.blockNumber ∧ m.borrowState = s.borrowState ∧
      s.supplyState.index ≤ m.supplyState.index := by
  have hSome : (updateCompSupplyIndex s).isSome = true := t2b s h
  cases hu : updateCompSupplyIndex s with
  | none => simp [hu] at hSome
  | some m =>
    exact ⟨m, rfl, aux_updSup_accts s m hu, aux_updSup_blk s m hu,
      aux_updSup_borrow s m hu, aux_updSup_idx_ge s m hu⟩












theorem plan0_updateSupply_spec_proof (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ m, updateCompSupplyIndex s = some m ∧ m.accts = s.accts ∧
      m.blockNumber = s.blockNumber ∧ m.borrowState = s.borrowState ∧
      s.supplyState.index ≤ m.supplyState.index := by
  have hSome : (updateCompSupplyIndex s).isSome = true := t2b s h
  cases hu : updateCompSupplyIndex s with
  | none => simp [hu] at hSome
  | some m =>
    exact ⟨m, rfl, aux_updSup_accts s m hu, aux_updSup_blk s m hu,
      aux_updSup_borrow s m hu, aux_updSup_idx_ge s m hu⟩

theorem plan0_updateBorrow_spec (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ m, updateCompBorrowIndex s = some m ∧ m.accts = s.accts ∧
      m.blockNumber = s.blockNumber ∧ m.supplyState = s.supplyState ∧
      s.borrowState.index ≤ m.borrowState.index := by
  have hSome : (updateCompBorrowIndex s).isSome = true := aux_updBor_some s h
  cases hu : updateCompBorrowIndex s with
  | none => simp [hu] at hSome
  | some m =>
    exact ⟨m, rfl, aux_updBor_accts s m hu, aux_updBor_blk s m hu,
      aux_updBor_supply s m hu, aux_updBor_idx_ge s m hu⟩

theorem aux_probe2 (s : St) (who : Account) :
    distributeSupplierComp s who =
    match subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
    | none => none
    | some d => some (s.withAcct who fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply d }) := by
  unfold distributeSupplierComp subChecked
  rfl

theorem aux_probe5 (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by
  by_cases hc : (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
  · simp only [if_pos hc]
    exact hc.2
  · simp only [if_neg hc]
    exact h

theorem aux_probe6 (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome = true := by
  unfold distributeSupplierComp subChecked
  have hle := aux_probe5 s who h
  simp only [hle, ↓reduceIte]
  rfl

theorem plan0_distributeSupplier_isSome (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome = true := by
  unfold distributeSupplierComp subChecked
  have hle := aux_probe5 s who h
  simp only [hle, ↓reduceIte]
  rfl

theorem aux_borrower_start_le_test (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by
  by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · simp only [if_pos hc]
    exact hc.2
  · simp only [if_neg hc]
    exact h

theorem plan0_distributeBorrower_isSome_test (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome = true := by
  unfold distributeBorrowerComp subChecked
  have hle := aux_borrower_start_le_test s who h
  simp only [hle, ↓reduceIte]
  rfl

theorem plan0_distributeBorrower_isSome (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome = true := by
  unfold distributeBorrowerComp subChecked
  have hle := aux_borrower_start_le_test s who h
  simp only [hle, ↓reduceIte]
  rfl

def foo : List Nat := [1,2,3]
example : ([1,2,3].modify 5 (·+1)) = [1,2,3] := by rfl
example : ([1,2,3].modify 1 (·+10)) = [1,12,3] := by rfl
example : ([1,2,3].getD 5 99) = 99 := by rfl





theorem plan1_borrow_half_consistent (s : St) (who : Account) (m : St)
    (h : Consistent s)
    (hm : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some m) :
    Consistent m := by
  obtain ⟨t, ht_eq, ht_dist⟩ := borrow_bind_lemma (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) m hm
  have haccts_t : t.accts = s.accts := aux_updBor_accts s t ht_eq
  have hsupEq_t : t.supplyState = s.supplyState := aux_updBor_supply s t ht_eq
  have hblkEq_t : t.blockNumber = s.blockNumber := aux_updBor_blk s t ht_eq
  have hidxGe_t : s.borrowState.index ≤ t.borrowState.index := aux_updBor_idx_ge s t ht_eq
  have hCon_t : Consistent t := by
    obtain ⟨hsupB, hborB, hall⟩ := h
    have hblkLe : t.borrowState.block ≤ s.blockNumber := by
      unfold updateCompBorrowIndex subChecked at ht_eq
      by_cases hle : s.borrowState.block ≤ s.blockNumber
      · simp only [hle, ↓reduceIte] at ht_eq
        by_cases hc1 : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
        · simp only [hc1, ↓reduceIte] at ht_eq
          cases ht_eq
          simp
        · simp only [hc1, ↓reduceIte] at ht_eq
          by_cases hc2 : (s.blockNumber - s.borrowState.block > 0)
          · simp only [hc2, ↓reduceIte] at ht_eq
            cases ht_eq
            simp
          · simp only [hc2, ↓reduceIte] at ht_eq
            cases ht_eq
            exact hle
      · simp [hle] at ht_eq
    refine ⟨?_, ?_, ?_⟩
    · calc t.supplyState.block = s.supplyState.block := by rw [hsupEq_t]
        _ ≤ s.blockNumber := hsupB
        _ = t.blockNumber := by rw [hblkEq_t]
    · calc t.borrowState.block ≤ s.blockNumber := hblkLe
        _ = t.blockNumber := by rw [hblkEq_t]
    · intro a ha
      rw [haccts_t] at ha
      rw [hsupEq_t]
      have hpair := hall a ha
      constructor
      · exact hpair.1
      · exact Nat.le_trans hpair.2 hidxGe_t
  obtain ⟨hsupT, hborT, hallT⟩ := hCon_t
  unfold distributeBorrowerComp at ht_dist
  simp only at ht_dist
  cases hsc : subChecked t.borrowState.index
      (if (t.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t.borrowState.index then compInitialIndex else (t.acct who).borrowerIndex) with
  | none =>
    simp [hsc] at ht_dist
  | some d =>
    simp [hsc] at ht_dist
    subst ht_dist
    refine ⟨hsupT, hborT, ?_⟩
    have key : ∀ (xs : List Acct) (n C Isup Ibor : Nat),
      (∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor) →
      ∀ a ∈ xs.modify n (fun x => ({ x with borrowerIndex := Ibor, accrued := x.accrued + C } : Acct)),
        a.supplierIndex ≤ Isup ∧ a.borrowerIndex ≤ Ibor := by
      intro xs
      induction xs with
      | nil =>
        intro n C Isup Ibor _h a ha
        simp at ha
      | cons x xs ih =>
        intro n C Isup Ibor hall a ha
        cases n with
        | zero =>
          simp at ha
          cases ha with
          | inl heq =>
            rw [heq]
            simp
            exact (hall x (by simp)).1
          | inr hmem =>
            exact hall a (by simp [hmem])
        | succ n =>
          simp at ha
          cases ha with
          | inl heq =>
            rw [heq]
            exact hall x (by simp)
          | inr hmem =>
            have htail : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor := by
              intro b hb
              exact hall b (by simp [hb])
            exact ih n C Isup Ibor htail a hmem
    exact key t.accts who (mulDouble (t.acct who).borrow d) t.supplyState.index t.borrowState.index hallT








theorem plan1_borrower_acct_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨hsup, hbor, hall⟩ := h
  unfold St.acct
  have aux : ∀ (xs : List Acct) (who : Nat) (idx : Nat),
      (∀ a ∈ xs, a.borrowerIndex ≤ idx) → ((xs.getD who noAcct).borrowerIndex ≤ idx) := by
    intro xs
    induction xs with
    | nil =>
      intro who idx _h
      unfold noAcct
      simp
    | cons x xs ih =>
      intro who idx hall
      cases who with
      | zero =>
        simp
        have hxmem : x ∈ x :: xs := by simp
        have hx := hall x hxmem
        exact hx
      | succ n =>
        simp
        apply ih n idx
        intro a ha
        apply hall a
        simp [ha]
  exact aux s.accts who s.borrowState.index (fun a ha => (hall a ha).2)

theorem plan1_supplier_acct_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at h
  obtain ⟨hsup, hbor, hall⟩ := h
  unfold St.acct
  have aux : ∀ (xs : List Acct) (who : Nat) (idx : Nat),
      (∀ a ∈ xs, a.supplierIndex ≤ idx) → ((xs.getD who noAcct).supplierIndex ≤ idx) := by
    intro xs
    induction xs with
    | nil =>
      intro who idx _h
      unfold noAcct
      simp
    | cons x xs ih =>
      intro who idx hall
      cases who with
      | zero =>
        simp
        have hxmem : x ∈ x :: xs := by simp
        have hx := hall x hxmem
        exact hx
      | succ n =>
        simp
        apply ih n idx
        intro a ha
        apply hall a
        simp [ha]
  exact aux s.accts who s.supplyState.index (fun a ha => (hall a ha).1)

theorem mem_modify_bound (xs : List Acct) (who : Nat) (f : Acct → Acct) (Isup Ibor : Nat)
    (hAll : ∀ a ∈ xs, a.supplierIndex ≤ Isup ∧ a.borrowerIndex ≤ Ibor)
    (hF : ∀ a, a.supplierIndex ≤ Isup → (f a).supplierIndex ≤ Isup ∧ (f a).borrowerIndex ≤ Ibor) :
    ∀ a ∈ xs.modify who f, a.supplierIndex ≤ Isup ∧ a.borrowerIndex ≤ Ibor := by
  induction xs generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons x xs ih =>
    intro a ha
    cases who with
    | zero =>
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        apply hF x
        have hxmem : x ∈ x :: xs := by simp
        exact (hAll x hxmem).1
      | inr hmem =>
        have hxmem : x ∈ x :: xs := by simp
        -- need that tail elements satisfy; f not applied
        have htail : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor := by
          intro b hb
          apply hAll b
          simp [hb]
        -- a ∈ xs
        exact hAll a (by simp [hmem])
    | succ n =>
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        have hxmem : x ∈ x :: xs := by simp
        exact hAll x hxmem
      | inr hmem =>
        -- a ∈ xs.modify n f
        have htailAll : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor := by
          intro b hb
          apply hAll b
          simp [hb]
        exact ih n htailAll a hmem

theorem updBor_blk_le_aux (s t : St) (h : updateCompBorrowIndex s = some t) :
    t.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp only [hle, ↓reduceIte] at h
    by_cases hc1 : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
    · simp only [hc1, ↓reduceIte] at h
      cases h
      simp
    · simp only [hc1, ↓reduceIte] at h
      by_cases hc2 : (s.blockNumber - s.borrowState.block > 0)
      · simp only [hc2, ↓reduceIte] at h
        cases h
        simp
      · simp only [hc2, ↓reduceIte] at h
        cases h
        exact hle
  · simp [hle] at h

theorem updBor_pres_consistent2 (s t : St) (hC : Consistent s)
    (h : updateCompBorrowIndex s = some t) : Consistent t := by
  obtain ⟨hsupB, hborB, hall⟩ := hC
  have haccts : t.accts = s.accts := aux_updBor_accts s t h
  have hsupEq : t.supplyState = s.supplyState := aux_updBor_supply s t h
  have hblkEq : t.blockNumber = s.blockNumber := aux_updBor_blk s t h
  have hidxGe : s.borrowState.index ≤ t.borrowState.index := aux_updBor_idx_ge s t h
  have hblkLe : t.borrowState.block ≤ s.blockNumber := updBor_blk_le_aux s t h
  have h1 : t.supplyState.block ≤ t.blockNumber := by
    calc t.supplyState.block = s.supplyState.block := by rw [hsupEq]
      _ ≤ s.blockNumber := hsupB
      _ = t.blockNumber := by rw [hblkEq]
  have h2 : t.borrowState.block ≤ t.blockNumber := by
    calc t.borrowState.block ≤ s.blockNumber := hblkLe
      _ = t.blockNumber := by rw [hblkEq]
  have h3 : ∀ a ∈ t.accts, a.supplierIndex ≤ t.supplyState.index ∧ a.borrowerIndex ≤ t.borrowState.index := by
    intro a ha
    rw [haccts] at ha
    rw [hsupEq]
    have hpair := hall a ha
    constructor
    · exact hpair.1
    · exact Nat.le_trans hpair.2 hidxGe
  exact ⟨h1, h2, h3⟩

theorem plan1_supply_modify_aux (xs : List Acct) (n C Isup Ibor : Nat)
    (hall : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor) :
    ∀ a ∈ xs.modify n (fun x => ({ x with supplierIndex := Isup, accrued := x.accrued + C } : Acct)),
      a.supplierIndex ≤ Isup ∧ a.borrowerIndex ≤ Ibor := by
  induction xs generalizing n with
  | nil =>
    intro a ha
    simp at ha
  | cons x xs ih =>
    intro a ha
    cases n with
    | zero =>
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        simp
        exact (hall x (by simp)).2
      | inr hmem =>
        exact hall a (by simp [hmem])
    | succ n =>
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        exact hall x (by simp)
      | inr hmem =>
        have htail : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor := by
          intro b hb
          exact hall b (by simp [hb])
        exact ih n htail a hmem

theorem plan1_supply_half_consistent (s : St) (who : Account) (m : St)
    (h : Consistent s)
    (hm : (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) = some m) :
    Consistent m := by
  obtain ⟨t, ht_eq, ht_dist⟩ := borrow_bind_lemma (updateCompSupplyIndex s) (fun t => distributeSupplierComp t who) m hm
  have hCon_t : Consistent t := by
    obtain ⟨hsupB, hborB, hall⟩ := h
    have haccts : t.accts = s.accts := aux_updSup_accts s t ht_eq
    have hborEq : t.borrowState = s.borrowState := aux_updSup_borrow s t ht_eq
    have hblkEq : t.blockNumber = s.blockNumber := aux_updSup_blk s t ht_eq
    have hidxGe : s.supplyState.index ≤ t.supplyState.index := aux_updSup_idx_ge s t ht_eq
    have hblkLe : t.supplyState.block ≤ s.blockNumber := by
      unfold updateCompSupplyIndex subChecked at ht_eq
      by_cases hle : s.supplyState.block ≤ s.blockNumber
      · simp only [hle, ↓reduceIte] at ht_eq
        by_cases hc1 : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
        · simp only [hc1, ↓reduceIte] at ht_eq
          cases ht_eq
          simp
        · simp only [hc1, ↓reduceIte] at ht_eq
          by_cases hc2 : (s.blockNumber - s.supplyState.block > 0)
          · simp only [hc2, ↓reduceIte] at ht_eq
            cases ht_eq
            simp
          · simp only [hc2, ↓reduceIte] at ht_eq
            cases ht_eq
            exact hle
      · simp [hle] at ht_eq
    have h1 : t.supplyState.block ≤ t.blockNumber := by
      calc t.supplyState.block ≤ s.blockNumber := hblkLe
        _ = t.blockNumber := by rw [hblkEq]
    have h2 : t.borrowState.block ≤ t.blockNumber := by
      calc t.borrowState.block = s.borrowState.block := by rw [hborEq]
        _ ≤ s.blockNumber := hborB
        _ = t.blockNumber := by rw [hblkEq]
    have h3 : ∀ a ∈ t.accts, a.supplierIndex ≤ t.supplyState.index ∧ a.borrowerIndex ≤ t.borrowState.index := by
      intro a ha
      rw [haccts] at ha
      rw [hborEq]
      have hpair := hall a ha
      constructor
      · exact Nat.le_trans hpair.1 hidxGe
      · exact hpair.2
    exact ⟨h1, h2, h3⟩
  obtain ⟨hsupT, hborT, hallT⟩ := hCon_t
  unfold distributeSupplierComp at ht_dist
  simp only at ht_dist
  cases hsc : subChecked t.supplyState.index
      (if (t.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ t.supplyState.index then compInitialIndex else (t.acct who).supplierIndex) with
  | none =>
    simp [hsc] at ht_dist
  | some d =>
    simp [hsc] at ht_dist
    subst ht_dist
    exact ⟨hsupT, hborT, fun a ha => plan1_supply_modify_aux t.accts who (mulDouble (t.acct who).supply d) t.supplyState.index t.borrowState.index hallT a ha⟩

theorem plan1_bind_pure_isSome (o : Option St) (f : St → St)
    (h : o.isSome = true) :
    (o.bind (fun t => some (f t))).isSome = true := by
  cases o with
  | none => simp at h
  | some x => simp

theorem plan1_claim_steps_isSome (s : St) (who : Account) (h : Consistent s) :
    (((updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who)).bind
      (fun t => (updateCompSupplyIndex t).bind
        (fun u => distributeSupplierComp u who))).isSome = true := by
  obtain ⟨hsupBlk, hborBlk, hall⟩ := h
  have hBorUpdSome : (updateCompBorrowIndex s).isSome = true := aux_updBor_some s hborBlk
  cases huBor : updateCompBorrowIndex s with
  | none => simp [huBor] at hBorUpdSome
  | some t =>
    have haccts_t : t.accts = s.accts := aux_updBor_accts s t huBor
    have hidxGe_bor : s.borrowState.index ≤ t.borrowState.index := aux_updBor_idx_ge s t huBor
    have hBorLe_s : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
      plan1_borrower_acct_le s who ⟨hsupBlk, hborBlk, hall⟩
    have hBorLe_t : (t.acct who).borrowerIndex ≤ t.borrowState.index := by
      unfold St.acct
      rw [haccts_t]
      exact Nat.le_trans hBorLe_s hidxGe_bor
    have hDistBorSome : (distributeBorrowerComp t who).isSome = true :=
      plan0_distributeBorrower_isSome t who hBorLe_t
    cases hdBor : distributeBorrowerComp t who with
    | none => simp [hdBor] at hDistBorSome
    | some m =>
      have hm_eq : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some m := by
        simp [huBor, hdBor]
      have hConsM : Consistent m := plan1_borrow_half_consistent s who m ⟨hsupBlk, hborBlk, hall⟩ hm_eq
      have hsupBlkM : m.supplyState.block ≤ m.blockNumber := hConsM.1
      have hSupUpdSome : (updateCompSupplyIndex m).isSome = true := t2b m hsupBlkM
      cases huSup : updateCompSupplyIndex m with
      | none => simp [huSup] at hSupUpdSome
      | some u =>
        have haccts_u : u.accts = m.accts := aux_updSup_accts m u huSup
        have hidxGe_sup : m.supplyState.index ≤ u.supplyState.index := aux_updSup_idx_ge m u huSup
        have hSupLeM : (m.acct who).supplierIndex ≤ m.supplyState.index :=
          plan1_supplier_acct_le m who hConsM
        have hSupLeU : (u.acct who).supplierIndex ≤ u.supplyState.index := by
          unfold St.acct
          rw [haccts_u]
          exact Nat.le_trans hSupLeM hidxGe_sup
        have hDistSupSome : (distributeSupplierComp u who).isSome = true :=
          plan0_distributeSupplier_isSome u who hSupLeU
        cases hdSup : distributeSupplierComp u who with
        | none => simp [hdSup] at hDistSupSome
        | some k =>
          simp [hdBor, huSup, hdSup]

theorem plan1_borrow_modify_aux (xs : List Acct) (n C Isup Ibor : Nat)
    (hall : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor) :
    ∀ a ∈ xs.modify n (fun x => ({ x with borrowerIndex := Ibor, accrued := x.accrued + C } : Acct)),
      a.supplierIndex ≤ Isup ∧ a.borrowerIndex ≤ Ibor := by
  induction xs generalizing n with
  | nil =>
    intro a ha
    simp at ha
  | cons x xs ih =>
    intro a ha
    cases n with
    | zero =>
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        simp
        exact (hall x (by simp)).1
      | inr hmem =>
        exact hall a (by simp [hmem])
    | succ n =>
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        exact hall x (by simp)
      | inr hmem =>
        have htail : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor := by
          intro b hb
          exact hall b (by simp [hb])
        exact ih n htail a hmem

theorem plan1_borrow_half_consistent_pf (s : St) (who : Account) (m : St)
    (h : Consistent s)
    (hm : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some m) :
    Consistent m := by
  obtain ⟨t, ht_eq, ht_dist⟩ := borrow_bind_lemma (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) m hm
  have hCon_t : Consistent t := updBor_pres_consistent2 s t h ht_eq
  obtain ⟨hsupT, hborT, hallT⟩ := hCon_t
  unfold distributeBorrowerComp at ht_dist
  simp only at ht_dist
  cases hsc : subChecked t.borrowState.index
      (if (t.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t.borrowState.index then compInitialIndex else (t.acct who).borrowerIndex) with
  | none =>
    simp [hsc] at ht_dist
  | some d =>
    simp [hsc] at ht_dist
    subst ht_dist
    exact ⟨hsupT, hborT, fun a ha => plan1_borrow_modify_aux t.accts who (mulDouble (t.acct who).borrow d) t.supplyState.index t.borrowState.index hallT a ha⟩

theorem self_contained_borrow_half (s : St) (who : Account) (m : St)
    (h : Consistent s)
    (hm : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some m) :
    Consistent m := by
  obtain ⟨t, ht_eq, ht_dist⟩ := borrow_bind_lemma (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) m hm
  have haccts_t : t.accts = s.accts := aux_updBor_accts s t ht_eq
  have hsupEq_t : t.supplyState = s.supplyState := aux_updBor_supply s t ht_eq
  have hblkEq_t : t.blockNumber = s.blockNumber := aux_updBor_blk s t ht_eq
  have hidxGe_t : s.borrowState.index ≤ t.borrowState.index := aux_updBor_idx_ge s t ht_eq
  have hCon_t : Consistent t := by
    obtain ⟨hsupB, hborB, hall⟩ := h
    have hblkLe : t.borrowState.block ≤ s.blockNumber := by
      unfold updateCompBorrowIndex subChecked at ht_eq
      by_cases hle : s.borrowState.block ≤ s.blockNumber
      · simp only [hle, ↓reduceIte] at ht_eq
        by_cases hc1 : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
        · simp only [hc1, ↓reduceIte] at ht_eq
          cases ht_eq
          simp
        · simp only [hc1, ↓reduceIte] at ht_eq
          by_cases hc2 : (s.blockNumber - s.borrowState.block > 0)
          · simp only [hc2, ↓reduceIte] at ht_eq
            cases ht_eq
            simp
          · simp only [hc2, ↓reduceIte] at ht_eq
            cases ht_eq
            exact hle
      · simp [hle] at ht_eq
    refine ⟨?_, ?_, ?_⟩
    · calc t.supplyState.block = s.supplyState.block := by rw [hsupEq_t]
        _ ≤ s.blockNumber := hsupB
        _ = t.blockNumber := by rw [hblkEq_t]
    · calc t.borrowState.block ≤ s.blockNumber := hblkLe
        _ = t.blockNumber := by rw [hblkEq_t]
    · intro a ha
      rw [haccts_t] at ha
      rw [hsupEq_t]
      have hpair := hall a ha
      constructor
      · exact hpair.1
      · exact Nat.le_trans hpair.2 hidxGe_t
  obtain ⟨hsupT, hborT, hallT⟩ := hCon_t
  unfold distributeBorrowerComp at ht_dist
  simp only at ht_dist
  cases hsc : subChecked t.borrowState.index
      (if (t.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t.borrowState.index then compInitialIndex else (t.acct who).borrowerIndex) with
  | none =>
    simp [hsc] at ht_dist
  | some d =>
    simp [hsc] at ht_dist
    subst ht_dist
    refine ⟨hsupT, hborT, ?_⟩
    have key : ∀ (xs : List Acct) (n C Isup Ibor : Nat),
      (∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor) →
      ∀ a ∈ xs.modify n (fun x => ({ x with borrowerIndex := Ibor, accrued := x.accrued + C } : Acct)),
        a.supplierIndex ≤ Isup ∧ a.borrowerIndex ≤ Ibor := by
      intro xs
      induction xs with
      | nil =>
        intro n C Isup Ibor _h a ha
        simp at ha
      | cons x xs ih =>
        intro n C Isup Ibor hall a ha
        cases n with
        | zero =>
          simp at ha
          cases ha with
          | inl heq =>
            rw [heq]
            simp
            exact (hall x (by simp)).1
          | inr hmem =>
            exact hall a (by simp [hmem])
        | succ n =>
          simp at ha
          cases ha with
          | inl heq =>
            rw [heq]
            exact hall x (by simp)
          | inr hmem =>
            have htail : ∀ b ∈ xs, b.supplierIndex ≤ Isup ∧ b.borrowerIndex ≤ Ibor := by
              intro b hb
              exact hall b (by simp [hb])
            exact ih n C Isup Ibor htail a hmem
    exact key t.accts who (mulDouble (t.acct who).borrow d) t.supplyState.index t.borrowState.index hallT

theorem plan1_borrow_half_consistent_aux_use (s : St) (who : Account) (m : St)
    (h : Consistent s)
    (hm : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some m) :
    Consistent m :=
  self_contained_borrow_half s who m h hm

theorem plan0_claimComp_isSome (s : St) (who : Account)
    (h : Consistent s) :
    (claimComp s who).isSome = true := by
  obtain ⟨hsupBlk, hborBlk, hall⟩ := h
  have hBorUpdSome : (updateCompBorrowIndex s).isSome = true := aux_updBor_some s hborBlk
  cases huBor : updateCompBorrowIndex s with
  | none => simp [huBor] at hBorUpdSome
  | some t =>
    have haccts_t : t.accts = s.accts := aux_updBor_accts s t huBor
    have hCon_t : Consistent t := updBor_pres_consistent2 s t ⟨hsupBlk, hborBlk, hall⟩ huBor
    have hBorLe_t : (t.acct who).borrowerIndex ≤ t.borrowState.index :=
      plan1_borrower_acct_le t who hCon_t
    have hDistBorSome : (distributeBorrowerComp t who).isSome = true :=
      plan0_distributeBorrower_isSome t who hBorLe_t
    cases hdBor : distributeBorrowerComp t who with
    | none => simp [hdBor] at hDistBorSome
    | some m =>
      have hm_eq : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some m := by
        simp [huBor, hdBor]
      have hConsM : Consistent m := plan1_borrow_half_consistent s who m ⟨hsupBlk, hborBlk, hall⟩ hm_eq
      have hsupBlkM : m.supplyState.block ≤ m.blockNumber := hConsM.1
      have hSupUpdSome : (updateCompSupplyIndex m).isSome = true := t2b m hsupBlkM
      cases huSup : updateCompSupplyIndex m with
      | none => simp [huSup] at hSupUpdSome
      | some u =>
        have haccts_u : u.accts = m.accts := aux_updSup_accts m u huSup
        have hidxGe_sup : m.supplyState.index ≤ u.supplyState.index := aux_updSup_idx_ge m u huSup
        have hSupLeM : (m.acct who).supplierIndex ≤ m.supplyState.index :=
          plan1_supplier_acct_le m who hConsM
        have hSupLeU : (u.acct who).supplierIndex ≤ u.supplyState.index := by
          unfold St.acct
          rw [haccts_u]
          exact Nat.le_trans hSupLeM hidxGe_sup
        have hDistSupSome : (distributeSupplierComp u who).isSome = true :=
          plan0_distributeSupplier_isSome u who hSupLeU
        cases hdSup : distributeSupplierComp u who with
        | none => simp [hdSup] at hDistSupSome
        | some k =>
          unfold claimComp
          simp [huBor, hdBor, huSup, hdSup]

theorem plan0_setCompSpeedInternal_isSome (s : St) (a b : Nat)
    (hs : s.supplyState.block ≤ s.blockNumber)
    (hb : s.borrowState.block ≤ s.blockNumber) :
    (setCompSpeedInternal s a b).isSome = true := by
  unfold setCompSpeedInternal
  have hUpdS : (updateCompSupplyIndex s).isSome = true := t2b s hs
  have hSupSome : (setSupplySpeed s a).isSome = true := by
    unfold setSupplySpeed
    by_cases heq : s.supplyState.speed ≠ a
    · simp only [if_pos heq]
      have : ((updateCompSupplyIndex s).map fun t =>
            ({ t with supplyState := ({ t.supplyState with speed := a } : Side) } : St)).isSome
          = (updateCompSupplyIndex s).isSome := by
        cases updateCompSupplyIndex s <;> rfl
      simp [this, hUpdS]
    · simp [if_neg heq]
  cases h1 : setSupplySpeed s a with
  | none => simp [h1] at hSupSome
  | some s1 =>
    have hS1blk : s1.borrowState.block ≤ s1.blockNumber := by
      unfold setSupplySpeed at h1
      by_cases heq : s.supplyState.speed ≠ a
      · rw [if_pos heq] at h1
        cases ht : updateCompSupplyIndex s with
        | none =>
          simp [ht] at h1
        | some t =>
          simp [ht] at h1
          cases h1
          show ({ t with supplyState := ({ t.supplyState with speed := a } : Side) } : St).borrowState.block ≤ _
          have hbor : t.borrowState = s.borrowState := aux_updSup_borrow s t ht
          have hblk : t.blockNumber = s.blockNumber := aux_updSup_blk s t ht
          simp only [hbor, hblk]
          exact hb
      · rw [if_neg heq] at h1
        simp at h1
        rw [← h1]
        exact hb
    have hUpdB : (updateCompBorrowIndex s1).isSome = true := aux_updBor_some s1 hS1blk
    have hBorSome : (setBorrowSpeed s1 b).isSome = true := by
      unfold setBorrowSpeed
      by_cases heq2 : s1.borrowState.speed ≠ b
      · simp only [if_pos heq2]
        have : ((updateCompBorrowIndex s1).map fun t =>
              ({ t with borrowState := ({ t.borrowState with speed := b } : Side) } : St)).isSome
            = (updateCompBorrowIndex s1).isSome := by
          cases updateCompBorrowIndex s1 <;> rfl
        simp [this, hUpdB]
      · simp [if_neg heq2]
    simpa using hBorSome

theorem updSup_pres_consistent_aux (s t : St) (hC : Consistent s)
    (h : updateCompSupplyIndex s = some t) : Consistent t := by
  obtain ⟨hsupB, hborB, hall⟩ := hC
  have haccts : t.accts = s.accts := aux_updSup_accts s t h
  have hborEq : t.borrowState = s.borrowState := aux_updSup_borrow s t h
  have hblkEq : t.blockNumber = s.blockNumber := aux_updSup_blk s t h
  have hidxGe : s.supplyState.index ≤ t.supplyState.index := aux_updSup_idx_ge s t h
  have hblkLe : t.supplyState.block ≤ s.blockNumber := by
    unfold updateCompSupplyIndex subChecked at h
    by_cases hle : s.supplyState.block ≤ s.blockNumber
    · simp only [hle, ↓reduceIte] at h
      by_cases hc1 : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
      · simp only [hc1, ↓reduceIte] at h
        cases h
        simp
      · simp only [hc1, ↓reduceIte] at h
        by_cases hc2 : (s.blockNumber - s.supplyState.block > 0)
        · simp only [hc2, ↓reduceIte] at h
          cases h
          simp
        · simp only [hc2, ↓reduceIte] at h
          cases h
          exact hle
    · simp [hle] at h
  refine ⟨?_, ?_, ?_⟩
  · calc t.supplyState.block ≤ s.blockNumber := hblkLe
      _ = t.blockNumber := by rw [hblkEq]
  · calc t.borrowState.block = s.borrowState.block := by rw [hborEq]
      _ ≤ s.blockNumber := hborB
      _ = t.blockNumber := by rw [hblkEq]
  · intro a ha
    rw [haccts] at ha
    rw [hborEq]
    exact ⟨Nat.le_trans (hall a ha).1 hidxGe, (hall a ha).2⟩

theorem distSup_start_eqX (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)
    = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0 <;> simp [h0]

theorem updSup_is_accrue (s t : St) (h : updateCompSupplyIndex s = some t) :
    t.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by
  have hle : s.supplyState.block ≤ s.blockNumber := helper_updSup_some s t h
  have hd : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [hle]
  have hEq := updSup_red s (s.blockNumber - s.supplyState.block) hd
  have hIf : (if s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 then
        let supplyTokens := totalSupply s
        let compAccrued := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
        let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
        some { s with supplyState :=
          { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
      else if s.blockNumber - s.supplyState.block > 0 then
        some { s with supplyState := { s.supplyState with block := s.blockNumber } }
      else some s) = some t := by
    rw [← hEq]
    exact h
  unfold accrueSide
  by_cases hc1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp only [hc1]
    obtain ⟨hdp, hsp, htot⟩ := hc1
    simp only [hdp, hsp] at hIf
    simp only [htot] at hIf
    cases hIf
    rfl
  · simp only [hc1]
    by_cases hdpos : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · simp only [hdpos] at hIf
      obtain ⟨hdp, hsp⟩ := hdpos
      by_cases hpos : totalSupply s > 0
      · simp only [hpos] at hIf
        cases hIf
        exfalso
        exact hc1 ⟨hdp, hsp, hpos⟩
      · simp only [hpos] at hIf
        cases hIf
        rfl
    · simp only [hdpos] at hIf
      by_cases hdpos2 : s.blockNumber - s.supplyState.block > 0
      · simp only [hdpos2] at hIf
        cases hIf
        rfl
      · simp only [hdpos2] at hIf
        cases hIf
        have hBeq : s.supplyState.block = s.blockNumber := by omega
        exact (side_block_idem s.supplyState s.blockNumber hBeq).symm

theorem distSup_pres_supply (s u : St) (who : Account)
    (h : distributeSupplierComp s who = some u) : u.supplyState = s.supplyState := by
  unfold distributeSupplierComp at h
  simp only at h
  cases hsc : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
  | none => simp [hsc] at h
  | some d => simp [hsc] at h; subst h; rfl

theorem distSup_pres_borrow (s u : St) (who : Account)
    (h : distributeSupplierComp s who = some u) : u.borrowState = s.borrowState := by
  unfold distributeSupplierComp at h
  simp only at h
  cases hsc : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
  | none => simp [hsc] at h
  | some d => simp [hsc] at h; subst h; rfl

theorem distSup_pres_blk (s u : St) (who : Account)
    (h : distributeSupplierComp s who = some u) : u.blockNumber = s.blockNumber := by
  unfold distributeSupplierComp at h
  simp only at h
  cases hsc : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
  | none => simp [hsc] at h
  | some d => simp [hsc] at h; subst h; rfl

theorem distSup_pres_reserve (s u : St) (who : Account)
    (h : distributeSupplierComp s who = some u) : u.reserve = s.reserve := by
  unfold distributeSupplierComp at h
  simp only at h
  cases hsc : subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
  | none => simp [hsc] at h
  | some d => simp [hsc] at h; subst h; rfl



theorem plan2_accrualStart_eq (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by
  unfold accrualStart
  by_cases h0 : recorded = 0 <;> by_cases hle : compInitialIndex ≤ index <;> simp [h0, hle]










theorem plan2_creditFor_eq (units start index : Nat) :
    creditFor units start index = mulDouble units (index - start) := by rfl

theorem plan2_accrualStart_eq2 (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by
  unfold accrualStart
  by_cases h0 : recorded = 0 <;> by_cases hle : compInitialIndex ≤ index <;> simp [h0, hle]

theorem probe_modify_simp (x : Acct) (xs : List Acct) (f : Acct → Acct) :
    (x :: xs).modify 0 f = f x :: xs := by simp

theorem probe_modify_succ (x : Acct) (xs : List Acct) (n : Nat) (f : Acct → Acct) :
    (x :: xs).modify (n+1) f = x :: xs.modify n f := by simp

theorem probe_getD_succ (x : Acct) (xs : List Acct) (n : Nat) :
    (x :: xs).getD (n+1) noAcct = xs.getD n noAcct := by simp

theorem plan2_modify_congr_getD_proof (xs : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (xs.getD who noAcct) = g (xs.getD who noAcct)) :
    xs.modify who f = xs.modify who g := by
  induction xs generalizing who with
  | nil =>
    cases who with
    | zero => simp
    | succ n => simp
  | cons x xs ih =>
    cases who with
    | zero =>
      have h0 : f x = g x := by simpa using h
      simp only [probe_modify_simp, h0]
    | succ n =>
      have h1 : f (xs.getD n noAcct) = g (xs.getD n noAcct) := by simpa using h
      have ihr := ih (n) h1
      simp only [probe_modify_succ, ihr]

theorem plan2_modify_congr_getD (xs : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (xs.getD who noAcct) = g (xs.getD who noAcct)) :
    xs.modify who f = xs.modify who g := plan2_modify_congr_getD_proof xs who f g h

theorem plan2_updateSupply_eq (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber ∧
      t = { s with
            supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hle : s.supplyState.block ≤ s.blockNumber := helper_updSup_some s t h
  have hsup : t.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) :=
    updSup_is_accrue s t h
  have haccts : t.accts = s.accts := aux_updSup_accts s t h
  have hbor : t.borrowState = s.borrowState := aux_updSup_borrow s t h
  have hblk : t.blockNumber = s.blockNumber := aux_updSup_blk s t h
  have hres : t.reserve = s.reserve := by
    unfold updateCompSupplyIndex subChecked at h
    simp only [hle, ↓reduceIte] at h
    by_cases hc1 : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
    · simp only [hc1, ↓reduceIte] at h
      by_cases hpos : totalSupply s > 0
      · simp only [hpos, ↓reduceIte] at h
        cases h
        rfl
      · simp only [hpos, ↓reduceIte] at h
        cases h
        rfl
    · simp only [hc1, ↓reduceIte] at h
      by_cases hc2 : (s.blockNumber - s.supplyState.block > 0)
      · simp only [hc2, ↓reduceIte] at h
        cases h
        rfl
      · simp only [hc2, ↓reduceIte] at h
        cases h
        rfl
  constructor
  · exact hle
  · cases s with | mk b sup bor res accs =>
    cases t with | mk b2 sup2 bor2 res2 accs2 =>
      simp_all

theorem plan2_distributeSupplier_eq (s : St) (who : Account) (u : St)
    (h : distributeSupplierComp s who = some u) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
      u = { s with
            accts := s.accts.modify who fun a =>
              { a with
                supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply
                  (accrualStart a.supplierIndex s.supplyState.index)
                  s.supplyState.index } } := by
  have hStart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)
      = accrualStart (s.acct who).supplierIndex s.supplyState.index := distSup_start_eqX s who
  have hEq : distributeSupplierComp s who =
    match subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
    | none => none
    | some d => some (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply d }) := by
    unfold distributeSupplierComp
    simp only [hStart]
  rw [hEq] at h
  cases hsc : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none =>
    simp [hsc] at h
  | some d =>
    simp [hsc] at h
    subst h
    have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
      unfold subChecked at hsc
      by_cases hle2 : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
      · exact hle2
      · simp [hle2] at hsc
    constructor
    · exact hle
    · have hd : d = s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index := by
        unfold subChecked at hsc
        simp [hle] at hsc
        exact hsc.symm
      subst hd
      unfold St.withAcct
      congr 1
      apply plan2_modify_congr_getD
      show { (s.accts.getD who noAcct) with supplierIndex := s.supplyState.index, accrued := (s.accts.getD who noAcct).accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) }
        = { (s.accts.getD who noAcct) with supplierIndex := s.supplyState.index, accrued := (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).supply (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) s.supplyState.index }
      rfl

theorem dbg1 (s : St) (who : Account) (t u : St)
    (ht : updateCompSupplyIndex s = some t)
    (hu : distributeSupplierComp t who = some u) :
    True := by
  obtain ⟨hle, htEq⟩ := plan2_updateSupply_eq s t ht
  obtain ⟨hle2, huEq⟩ := plan2_distributeSupplier_eq t who u hu
  have haccts : t.accts = s.accts := by rw [htEq]
  have hsupIdx : t.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [htEq]
  trivial

theorem dbg2 (s : St) (who : Account) (t u : St)
    (ht : updateCompSupplyIndex s = some t)
    (hu : distributeSupplierComp t who = some u) :
    SupplyDistributed s who u := by
  obtain ⟨hle, htEq⟩ := plan2_updateSupply_eq s t ht
  obtain ⟨hle2, huEq⟩ := plan2_distributeSupplier_eq t who u hu
  have haccts : t.accts = s.accts := by rw [htEq]
  have hsupIdx : t.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [htEq]
  have hacctEq : t.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hle2' : accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [← hacctEq, ← hsupIdx]; exact hle2
  refine ⟨hle, hle2', ?_⟩
  rw [huEq, htEq]

theorem plan2_supply_hook_effect (s : St) (who : Account) (t u : St)
    (ht : updateCompSupplyIndex s = some t)
    (hu : distributeSupplierComp t who = some u) :
    SupplyDistributed s who u := by
  obtain ⟨hle, htEq⟩ := plan2_updateSupply_eq s t ht
  obtain ⟨hle2, huEq⟩ := plan2_distributeSupplier_eq t who u hu
  have haccts : t.accts = s.accts := by rw [htEq]
  have hsupIdx : t.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [htEq]
  have hacctEq : t.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hle2' : accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [← hacctEq, ← hsupIdx]; exact hle2
  refine ⟨hle, hle2', ?_⟩
  rw [huEq, htEq]

theorem req_supply_hook_proof_attempt : SupplyHookEffects comptroller := by
  unfold SupplyHookEffects
  intro s who s' h
  unfold comptroller at h
  simp only at h
  obtain ⟨t, ht, hu⟩ := borrow_bind_lemma (updateCompSupplyIndex s) (fun t => distributeSupplierComp t who) s' h
  exact plan2_supply_hook_effect s who t s' ht hu

theorem updBor_red_bh2 (s : St) (d : Nat)
    (hsub : subChecked s.blockNumber s.borrowState.block = some d) :
    updateCompBorrowIndex s =
      (if d > 0 ∧ s.borrowState.speed > 0 then
        let borrowAmount := totalBorrows s
        let compAccrued := d * s.borrowState.speed
        let ratio := if borrowAmount > 0 then fraction compAccrued borrowAmount else 0
        some { s with borrowState :=
          { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
      else if d > 0 then
        some { s with borrowState := { s.borrowState with block := s.blockNumber } }
      else some s) := by
  unfold updateCompBorrowIndex
  rw [hsub]

theorem updBor_is_accrue_bh2 (s t : St) (h : updateCompBorrowIndex s = some t) :
    t.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
  have hle : s.borrowState.block ≤ s.blockNumber := updBor_block_le2 s t h
  have hd : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hle]
  have hEq := updBor_red_bh2 s (s.blockNumber - s.borrowState.block) hd
  have hIf : (if s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 then
        let borrowAmount := totalBorrows s
        let compAccrued := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
        let ratio := if borrowAmount > 0 then fraction compAccrued borrowAmount else 0
        some { s with borrowState :=
          { s.borrowState with index := s.borrowState.index + ratio, block := s.blockNumber } }
      else if s.blockNumber - s.borrowState.block > 0 then
        some { s with borrowState := { s.borrowState with block := s.blockNumber } }
      else some s) = some t := by
    rw [← hEq]
    exact h
  have hAcc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
    (if 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s then
      ({ s.borrowState with index := s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s, block := s.blockNumber } : Side)
    else ({ s.borrowState with block := s.blockNumber } : Side)) := by
    unfold accrueSide
    split
    · rfl
    · rfl
  by_cases hc1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · rw [hAcc, if_pos hc1]
    obtain ⟨hdp, hsp, htot⟩ := hc1
    simp only [hdp, hsp, ↓reduceIte] at hIf
    simp only [htot, ↓reduceIte] at hIf
    cases hIf
    rfl
  · rw [hAcc, if_neg hc1]
    by_cases hdpos : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · simp only [hdpos, ↓reduceIte] at hIf
      obtain ⟨hdp, hsp⟩ := hdpos
      by_cases hpos : totalBorrows s > 0
      · simp only [hpos, ↓reduceIte] at hIf
        cases hIf
        exfalso
        exact hc1 ⟨hdp, hsp, hpos⟩
      · simp only [hpos, ↓reduceIte] at hIf
        cases hIf
        rfl
    · simp only [hdpos, ↓reduceIte] at hIf
      by_cases hdpos2 : s.blockNumber - s.borrowState.block > 0
      · simp only [hdpos2, ↓reduceIte] at hIf
        cases hIf
        rfl
      · simp only [hdpos2, ↓reduceIte] at hIf
        cases hIf
        have hBeq : s.borrowState.block = s.blockNumber := by omega
        exact (side_block_idem s.borrowState s.blockNumber hBeq).symm

theorem plan2_updateBorrow_eq_bh2 (s t : St)
    (h : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber ∧
      t = { s with
            borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hle : s.borrowState.block ≤ s.blockNumber := updBor_block_le2 s t h
  have hbor : t.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) :=
    updBor_is_accrue_bh2 s t h
  have haccts : t.accts = s.accts := aux_updBor_accts s t h
  have hsup : t.supplyState = s.supplyState := aux_updBor_supply s t h
  have hblk : t.blockNumber = s.blockNumber := aux_updBor_blk s t h
  have hres : t.reserve = s.reserve := by
    unfold updateCompBorrowIndex subChecked at h
    simp only [hle, ↓reduceIte] at h
    by_cases hc1 : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
    · simp only [hc1, ↓reduceIte] at h
      by_cases hpos : totalBorrows s > 0
      · simp only [hpos, ↓reduceIte] at h
        cases h
        rfl
      · simp only [hpos, ↓reduceIte] at h
        cases h
        rfl
    · simp only [hc1, ↓reduceIte] at h
      by_cases hc2 : (s.blockNumber - s.borrowState.block > 0)
      · simp only [hc2, ↓reduceIte] at h
        cases h
        rfl
      · simp only [hc2, ↓reduceIte] at h
        cases h
        rfl
  constructor
  · exact hle
  · cases s with | mk b sup bor res accs =>
    cases t with | mk b2 sup2 bor2 res2 accs2 =>
      simp_all

theorem distBor_start_eq_bh2 (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)
    = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0 <;> simp [h0]

theorem plan2_distributeBorrower_eq_bh2 (s : St) (who : Account) (u : St)
    (h : distributeBorrowerComp s who = some u) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
      u = { s with
            accts := s.accts.modify who fun a =>
              { a with
                borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow
                  (accrualStart a.borrowerIndex s.borrowState.index)
                  s.borrowState.index } } := by
  have hStart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)
      = accrualStart (s.acct who).borrowerIndex s.borrowState.index := distBor_start_eq_bh2 s who
  have hEq : distributeBorrowerComp s who =
    match subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
    | none => none
    | some d => some (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow d }) := by
    unfold distributeBorrowerComp
    simp only [hStart]
  rw [hEq] at h
  cases hsc : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none =>
    simp [hsc] at h
  | some d =>
    simp [hsc] at h
    subst h
    have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
      unfold subChecked at hsc
      by_cases hle2 : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
      · exact hle2
      · simp [hle2] at hsc
    constructor
    · exact hle
    · have hd : d = s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
        unfold subChecked at hsc
        simp [hle] at hsc
        exact hsc.symm
      subst hd
      unfold St.withAcct
      congr 1
      apply plan2_modify_congr_getD
      rfl

theorem plan2_borrow_hook_effect_bh2 (s : St) (who : Account) (t u : St)
    (ht : updateCompBorrowIndex s = some t)
    (hu : distributeBorrowerComp t who = some u) :
    BorrowDistributed s who u := by
  obtain ⟨hle, htEq⟩ := plan2_updateBorrow_eq_bh2 s t ht
  obtain ⟨hle2, huEq⟩ := plan2_distributeBorrower_eq_bh2 t who u hu
  have haccts : t.accts = s.accts := by rw [htEq]
  have hborIdx : t.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [htEq]
  have hacctEq : t.acct who = s.acct who := by unfold St.acct; rw [haccts]
  have hle2' : accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← hacctEq, ← hborIdx]; exact hle2
  refine ⟨hle, hle2', ?_⟩
  rw [huEq, htEq]

theorem grant_mod_eq_aux (xs : List Acct) (who amount : Nat)
    (ham : amount = (xs.getD who noAcct).accrued) :
    xs.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + amount } : Acct))
    = xs.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) := by
  induction xs generalizing who with
  | nil =>
    cases who with
    | zero => simp [ham]
    | succ n => simp
  | cons x xs ih =>
    cases who with
    | zero =>
      simp at ham ⊢
      rw [ham]
    | succ n =>
      simp
      exact ih n ham

theorem grant_unfold_probe (s : St) (who : Account) : True := by
  have h1 : grantCompInternal s who =
    (let amount := (s.acct who).accrued
    ; if amount > 0 ∧ amount ≤ s.reserve then
      { s with reserve := s.reserve - amount,
               accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + amount } }
    else s) := rfl
  trivial



theorem plan3_claimComp_decomp (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ m1 m2,
      (∃ t, updateCompBorrowIndex s = some t ∧
            distributeBorrowerComp t who = some m1) ∧
      (∃ u, updateCompSupplyIndex m1 = some u ∧
            distributeSupplierComp u who = some m2) ∧
      s' = grantCompInternal m2 who := by
  have hU : claimComp s who = ((updateCompBorrowIndex s).bind fun t => (distributeBorrowerComp t who).bind fun m1 => (updateCompSupplyIndex m1).bind fun u => (distributeSupplierComp u who).bind fun m2 => some (grantCompInternal m2 who)) := by
    unfold claimComp
    simp only [bind, Option.bind]
    rfl
  rw [hU] at h
  obtain ⟨t, ht, hrest⟩ := borrow_bind_lemma (updateCompBorrowIndex s) _ s' h
  obtain ⟨m1, hm1, hrest2⟩ := borrow_bind_lemma (distributeBorrowerComp t who) _ s' hrest
  obtain ⟨u, hu, hrest3⟩ := borrow_bind_lemma (updateCompSupplyIndex m1) _ s' hrest2
  obtain ⟨m2, hm2, hfinal⟩ := borrow_bind_lemma (distributeSupplierComp u who) _ s' hrest3
  simp at hfinal
  subst hfinal
  refine ⟨m1, m2, ?_, ?_, rfl⟩
  · exact Exists.intro t ⟨ht, hm1⟩
  · exact Exists.intro u ⟨hu, hm2⟩






theorem plan3_grant_show (s : St) (who : Account) :
    True := by
  have h1 : grantCompInternal s who =
    (let amount := (s.acct who).accrued
    ; if amount > 0 ∧ amount ≤ s.reserve then
      { s with reserve := s.reserve - amount,
               accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + amount } }
    else s) := rfl
  have h2 : grant s who =
    (if 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve then
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
    else s) := rfl
  trivial

theorem plan3_grant_step1 (s : St) (who : Account) (h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) :
    grantCompInternal s who =
      { s with reserve := s.reserve - (s.acct who).accrued,
               accts := s.accts.modify who fun a => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct) } := by
  unfold grantCompInternal
  simp [h]

theorem plan3_grant_step2 (s : St) (who : Account) (h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) :
    grant s who =
      ({ s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct) } : St) := by
  unfold grant
  simp [h]

theorem plan3_grant_step3 (s : St) (who : Account) (h : ¬ ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve)) :
    grantCompInternal s who = s := by
  unfold grantCompInternal
  simp [h]

theorem plan3_grant_step4 (s : St) (who : Account) (h : ¬ ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve)) :
    grant s who = s := by
  unfold grant
  have h2 : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) := by omega
  simp [h2]

theorem plan4_modify_wallet_amount (xs : List Acct) (who amount : Nat)
    (h : amount = (xs.getD who noAcct).accrued) :
    xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + amount }) =
      xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply plan2_modify_congr_getD
  simp only [h]


theorem plan4_grantCompInternal_pos (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grantCompInternal s who =
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a =>
          { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  unfold grantCompInternal
  simp only [h, and_self, ↓reduceIte]
  congr 1
  apply plan2_modify_congr_getD
  rfl




theorem plan4_grantCompInternal_neg_and_grant_neg (s : St) (who : Account)
    (h : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve)) :
    grantCompInternal s who = s ∧ grant s who = s := by
  constructor
  · unfold grantCompInternal
    simp [h]
  · unfold grant
    simp [h]


theorem plan4_modify_wallet_amount_aux (xs : List Acct) (who amount : Nat)
    (h : amount = (xs.getD who noAcct).accrued) :
    xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + amount }) =
      xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply plan2_modify_congr_getD
  simp only [h]

theorem plan4_modify_wallet_amount_check (xs : List Acct) (who amount : Nat)
    (h : amount = (xs.getD who noAcct).accrued) :
    xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + amount }) =
      xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply plan2_modify_congr_getD
  simp only [h]

theorem plan4_inline_test (xs : List Acct) (who amount : Nat)
    (h : amount = (xs.getD who noAcct).accrued) :
    xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + amount }) =
      xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  exact plan4_modify_wallet_amount_check xs who amount h

theorem plan4_probe_direct (xs : List Acct) (who amount : Nat)
    (h : amount = (xs.getD who noAcct).accrued) :
    xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + amount }) =
      xs.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  apply plan2_modify_congr_getD
  simp only [h]

theorem plan4_grantCompInternal_pos4 (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grantCompInternal s who =
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a =>
          { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  unfold grantCompInternal
  simp only [h, and_self, ↓reduceIte]
  congr 1
  apply plan2_modify_congr_getD
  rfl

theorem plan4_grantCompInternal_pos_auxcheck (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grantCompInternal s who =
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a =>
          { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  unfold grantCompInternal
  simp only [h, and_self, ↓reduceIte]
  congr 1
  apply plan2_modify_congr_getD
  rfl

theorem plan4_grant_pos_proof (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grant s who =
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a =>
          { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  unfold grant
  simp [h]

theorem plan4_grant_pos (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grant s who =
      { s with
        reserve := s.reserve - (s.acct who).accrued,
        accts := s.accts.modify who fun a =>
          { a with accrued := 0, wallet := a.wallet + a.accrued } } := by
  unfold grant
  simp [h]

theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · have hg1 := plan4_grantCompInternal_pos_auxcheck s who h
    have hg2 := plan4_grant_pos s who h
    rw [hg1, hg2]
  · have hpair := plan4_grantCompInternal_neg_and_grant_neg s who h
    rw [hpair.1, hpair.2]

theorem plan3_claimComp_decomp_proof3 (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ m1 m2,
      (∃ t, updateCompBorrowIndex s = some t ∧
            distributeBorrowerComp t who = some m1) ∧
      (∃ u, updateCompSupplyIndex m1 = some u ∧
            distributeSupplierComp u who = some m2) ∧
      s' = grantCompInternal m2 who := by
  have hU : claimComp s who = ((updateCompBorrowIndex s).bind fun t => (distributeBorrowerComp t who).bind fun m1 => (updateCompSupplyIndex m1).bind fun u => (distributeSupplierComp u who).bind fun m2 => some (grantCompInternal m2 who)) := by
    unfold claimComp
    simp only [bind, Option.bind]
    rfl
  rw [hU] at h
  obtain ⟨t, ht, hrest⟩ := borrow_bind_lemma (updateCompBorrowIndex s) _ s' h
  obtain ⟨m1, hm1, hrest2⟩ := borrow_bind_lemma (distributeBorrowerComp t who) _ s' hrest
  obtain ⟨u, hu, hrest3⟩ := borrow_bind_lemma (updateCompSupplyIndex m1) _ s' hrest2
  obtain ⟨m2, hm2, hfinal⟩ := borrow_bind_lemma (distributeSupplierComp u who) _ s' hrest3
  simp at hfinal
  subst hfinal
  refine ⟨m1, m2, ?_, ?_, rfl⟩
  · exact Exists.intro t ⟨ht, hm1⟩
  · exact Exists.intro u ⟨hu, hm2⟩

theorem plan3_claimed_of_distributed (s : St) (who : Account) (m1 m2 : St)
    (hB : BorrowDistributed s who m1) (hS : SupplyDistributed m1 who m2) :
    Claimed s who (grant m2 who) := by
  unfold Claimed
  exact ⟨m1, m2, hB, hS, rfl⟩

theorem plan3_claimComp_claimed_proof2 (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    Claimed s who s' := by
  obtain ⟨m1, m2, ⟨t, ht, hm1⟩, ⟨u, hu, hm2⟩, heq⟩ :=
    plan3_claimComp_decomp_proof3 s who s' h
  have hB : BorrowDistributed s who m1 :=
    plan2_borrow_hook_effect_bh2 s who t m1 ht hm1
  have hS : SupplyDistributed m1 who m2 :=
    plan2_supply_hook_effect m1 who u m2 hu hm2
  have hg : grantCompInternal m2 who = grant m2 who :=
    plan3_grantCompInternal_eq_grant m2 who
  have hCl : Claimed s who (grant m2 who) :=
    plan3_claimed_of_distributed s who m1 m2 hB hS
  rw [heq, hg]
  exact hCl

theorem plan3_claimComp_claimed (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    Claimed s who s' := by
  obtain ⟨m1, m2, ⟨t, ht, hm1⟩, ⟨u, hu, hm2⟩, heq⟩ :=
    plan3_claimComp_decomp_proof3 s who s' h
  have hB : BorrowDistributed s who m1 :=
    plan2_borrow_hook_effect_bh2 s who t m1 ht hm1
  have hS : SupplyDistributed m1 who m2 :=
    plan2_supply_hook_effect m1 who u m2 hu hm2
  have hg : grantCompInternal m2 who = grant m2 who :=
    plan3_grantCompInternal_eq_grant m2 who
  have hCl : Claimed s who (grant m2 who) :=
    plan3_claimed_of_distributed s who m1 m2 hB hS
  rw [heq, hg]
  exact hCl

theorem req_claim_test_tmp : ClaimEffects comptroller := by
  intro s who s' h
  exact plan3_claimComp_claimed s who s' h

theorem setSup_cases (s s1 : St) (a : Nat)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed = a ∧ s1 = s) ∨
    (s.supplyState.speed ≠ a ∧ s.supplyState.block ≤ s.blockNumber ∧
      s1 = { (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)) with supplyState := ({ (accrueSide s.supplyState s.blockNumber (totalSupply s)) with speed := a } : Side) }) := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed ≠ a
  · simp only [if_pos heq] at h
    have hUpdSome : (updateCompSupplyIndex s).isSome = true := by
      cases hu : updateCompSupplyIndex s with
      | none =>
        have : ((updateCompSupplyIndex s).map fun t => ({ t with supplyState := ({ t.supplyState with speed := a } : Side) } : St)) = none := by
          rw [hu]; rfl
        rw [this] at h
        simp at h
      | some v => rfl
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at hUpdSome
    | some t =>
      simp [hu] at h
      have hle : s.supplyState.block ≤ s.blockNumber := helper_updSup_some s t hu
      have htEq : t = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by
        have hpair := plan2_updateSupply_eq s t hu
        exact hpair.2
      right
      refine ⟨heq, hle, ?_⟩
      rw [← h, htEq]
  · simp only [if_neg heq] at h
    cases h
    left
    constructor
    · omega
    · rfl

theorem setBor_cases (s s1 : St) (b : Nat)
    (h : setBorrowSpeed s b = some s1) :
    (s.borrowState.speed = b ∧ s1 = s) ∨
    (s.borrowState.speed ≠ b ∧ s.borrowState.block ≤ s.blockNumber ∧
      s1 = { (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)) with borrowState := ({ (accrueSide s.borrowState s.blockNumber (totalBorrows s)) with speed := b } : Side) }) := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed ≠ b
  · simp only [if_pos heq] at h
    have hUpdSome : (updateCompBorrowIndex s).isSome = true := by
      cases hu : updateCompBorrowIndex s with
      | none =>
        have : ((updateCompBorrowIndex s).map fun t => ({ t with borrowState := ({ t.borrowState with speed := b } : Side) } : St)) = none := by
          rw [hu]; rfl
        rw [this] at h
        simp at h
      | some v => rfl
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at hUpdSome
    | some t =>
      simp [hu] at h
      have hle : s.borrowState.block ≤ s.blockNumber := updBor_block_le2 s t hu
      have htEq : t = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by
        have hpair := plan2_updateBorrow_eq_bh2 s t hu
        exact hpair.2
      right
      refine ⟨heq, hle, ?_⟩
      rw [← h, htEq]
  · simp only [if_neg heq] at h
    cases h
    left
    constructor
    · omega
    · rfl

theorem setSup_pres (s s1 : St) (a : Nat) (h : setSupplySpeed s a = some s1) :
    s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧ s1.reserve = s.reserve := by
  rcases setSup_cases s s1 a h with ⟨heq, rfl⟩ | ⟨hne, _, heq2⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [heq2]
    simp

theorem setBor_pres (s s1 : St) (b : Nat) (h : setBorrowSpeed s b = some s1) :
    s1.supplyState = s.supplyState ∧ s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧ s1.reserve = s.reserve := by
  rcases setBor_cases s s1 b h with ⟨heq, rfl⟩ | ⟨hne, _, heq2⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [heq2]
    simp

theorem speedsSet_mk (s s' : St) (a b : Nat)
    (h1 : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber)
    (h2 : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)
    (h3 : s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) :
    SpeedsSet s a b s' := by
  unfold SpeedsSet
  exact ⟨h1, h2, h3⟩

theorem supplyDoubleOverwrite (s : St) (Y Z : Side) :
    ({ (({ s with supplyState := Y } : St)) with supplyState := Z } : St)
    = ({ s with supplyState := Z } : St) := by
  cases s with | mk b sup bor res accs =>
    simp

theorem borrowDoubleOverwrite (s : St) (Y Z : Side) :
    ({ (({ s with borrowState := Y } : St)) with borrowState := Z } : St)
    = ({ s with borrowState := Z } : St) := by
  cases s with | mk b sup bor res accs =>
    simp

theorem supplyBorrowCombine (s : St) (Za Zb : Side) :
    ({ (({ s with supplyState := Za } : St)) with borrowState := Zb } : St)
    = ({ s with supplyState := Za, borrowState := Zb } : St) := by
  cases s with | mk b sup bor res accs =>
    simp

theorem borrowOfSupPres (s s1 : St) (a : Nat) (h : setSupplySpeed s a = some s1) :
    s1.borrowState = s.borrowState := (setSup_pres s s1 a h).1

theorem borSpeed_congr_setSup (s s1 : St) (a : Nat) (h : setSupplySpeed s a = some s1) :
    s1.borrowState.speed = s.borrowState.speed := by
  have hp := setSup_pres s s1 a h
  rw [hp.1]

theorem totSup_pres_setSup (s s1 : St) (a : Nat) (h : setSupplySpeed s a = some s1) :
    totalSupply s1 = totalSupply s := by
  have hp := setSup_pres s s1 a h
  unfold totalSupply
  rw [hp.2.2.1]

theorem totBor_pres_setSup (s s1 : St) (a : Nat) (h : setSupplySpeed s a = some s1) :
    totalBorrows s1 = totalBorrows s := by
  have hp := setSup_pres s s1 a h
  unfold totalBorrows
  rw [hp.2.2.1]

theorem accBor_congr_setSup (s s1 : St) (a : Nat) (h : setSupplySpeed s a = some s1) :
    accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) =
    accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
  have hp := setSup_pres s s1 a h
  rw [hp.1, hp.2.1, totBor_pres_setSup s s1 a h]

theorem plan5_setSupplySpeed_spec (s s1 : St) (a : Nat)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1.supplyState = (if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) ∧
    s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧ s1.reserve = s.reserve := by
  rcases setSup_cases s s1 a h with ⟨heq, rfl⟩ | ⟨hne, hle, heq2⟩
  · exact ⟨fun hne2 => absurd heq hne2, by simp [heq], rfl, rfl, rfl, rfl⟩
  · exact ⟨fun _ => hle, by rw [heq2]; simp [hne], by rw [heq2], by rw [heq2], by rw [heq2], by rw [heq2]⟩






theorem plan5_setSpeeds_state_eq (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1) (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  have hSupPres : s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber ∧
      s1.accts = s.accts ∧ s1.reserve = s.reserve := setSup_pres s s1 a h1
  have hAccEq : accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) =
      accrueSide s.borrowState s.blockNumber (totalBorrows s) :=
    accBor_congr_setSup s s1 a h1
  have hSupEq : s1.supplyState = (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
    rcases setSup_cases s s1 a h1 with ⟨heq, heqS1⟩ | ⟨hne, _, heq2⟩
    · rw [heqS1]
      simp [heq]
    · have h1s : s1.supplyState =
          ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) := by
        rw [heq2]
      rw [h1s]
      simp [hne]
  have hBorEq : s'.borrowState = (if s.borrowState.speed = b then s.borrowState
      else ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side)) := by
    have hBorSpeed : s1.borrowState.speed = s.borrowState.speed := by rw [hSupPres.1]
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · have hEq : s.borrowState.speed = b := by rw [← hBorSpeed, heqB]
      have hBeq : s'.borrowState = s.borrowState := by rw [heqS, hSupPres.1]
      rw [hBeq]
      simp [hEq]
    · have hneB' : s.borrowState.speed ≠ b := by rw [← hBorSpeed]; exact hneB
      have h2s : s'.borrowState =
          ({ accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) with speed := b } : Side) := by
        rw [heq2B]
      rw [h2s, hAccEq]
      simp [hneB']
  have hSupEq' : s'.supplyState = (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS]
      exact hSupEq
    · have hss : s'.supplyState = s1.supplyState := by rw [heq2B]
      rw [hss, hSupEq]
  have hBlk' : s'.blockNumber = s.blockNumber := by
    have h1b := hSupPres.2.1
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS, h1b]
    · rw [heq2B, h1b]
  have hAccts' : s'.accts = s.accts := by
    have h1a := hSupPres.2.2.1
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS, h1a]
    · rw [heq2B, h1a]
  have hRes' : s'.reserve = s.reserve := by
    have h1r := hSupPres.2.2.2
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS, h1r]
    · rw [heq2B, h1r]
  cases s with | mk b0 sup0 bor0 res0 accs0 =>
    cases s' with | mk b2 sup2 bor2 res2 accs2 =>
      simp only at hSupEq' hBorEq hBlk' hAccts' hRes' ⊢
      simp [hSupEq', hBorEq, hBlk', hAccts', hRes']




theorem plan5_setSupplySpeed_spec_auxcheck (s : St) (a : Nat) (hne : s.supplyState.speed ≠ a) :
    (if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a })
    = ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) := by
  simp [hne]

theorem plan5_supply_eq_single (s : St) (a : Nat) :
    ({ (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)) with supplyState := ({ (accrueSide s.supplyState s.blockNumber (totalSupply s)) with speed := a } : Side) } : St)
    = ({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St) := by
  exact supplyDoubleOverwrite s _ _

theorem plan5_supply_target_sup (s : St) (a : Nat) :
    (({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St).supplyState
    = ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
  rfl

theorem plan5_supply_target_bor (s : St) (a : Nat) :
    (({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St).borrowState
    = s.borrowState) := by
  rfl

theorem plan5_setSupplySpeed_spec_try3 (s s1 : St) (a : Nat)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1.supplyState = (if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) ∧
    s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧ s1.reserve = s.reserve := by
  rcases setSup_cases s s1 a h with ⟨heq, rfl⟩ | ⟨hne, hle, heq2⟩
  · exact ⟨fun hne2 => absurd heq hne2, by simp [heq], rfl, rfl, rfl, rfl⟩
  · exact ⟨fun _ => hle, by rw [heq2]; simp [hne], by rw [heq2], by rw [heq2], by rw [heq2], by rw [heq2]⟩

theorem plan5_setBorrowSpeed_spec (s s' : St) (b : Nat)
    (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s'.borrowState = (if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) ∧
    s'.supplyState = s.supplyState ∧ s'.blockNumber = s.blockNumber ∧
    s'.accts = s.accts ∧ s'.reserve = s.reserve := by
  rcases setBor_cases s s' b h with ⟨heq, rfl⟩ | ⟨hne, hle, heq2⟩
  · exact ⟨fun hne2 => absurd heq hne2, by simp [heq], rfl, rfl, rfl, rfl⟩
  · exact ⟨fun _ => hle, by rw [heq2]; simp [hne], by rw [heq2], by rw [heq2], by rw [heq2], by rw [heq2]⟩

theorem plan5_setSpeeds_decomp (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ s1, setSupplySpeed s a = some s1 ∧ setBorrowSpeed s1 b = some s' := by
  have h2 : setCompSpeedInternal s a b = some s' := by
    have : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := by rfl
    rw [this] at h
    exact h
  unfold setCompSpeedInternal at h2
  exact borrow_bind_lemma (setSupplySpeed s a) (fun s => setBorrowSpeed s b) s' h2

theorem plan5_setSpeeds_state_eq_try (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1) (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  obtain ⟨_, hSupEq, hBorEq1, hBlk1, hAccts1, hRes1⟩ := plan5_setSupplySpeed_spec s s1 a h1
  obtain ⟨_, hBorEq, hSupEq2, hBlk2, hAccts2, hRes2⟩ := plan5_setBorrowSpeed_spec s1 s' b h2
  have hBorSpeed : s1.borrowState.speed = s.borrowState.speed := by rw [hBorEq1]
  have hAccEq : accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) =
      accrueSide s.borrowState s.blockNumber (totalBorrows s) :=
    accBor_congr_setSup s s1 a h1
  have hBorEq' : s'.borrowState = (if s.borrowState.speed = b then s.borrowState
      else ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side)) := by
    rw [hBorEq, hBorSpeed, hAccEq, hBorEq1]
  have hSupEq' : s'.supplyState = (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
    rw [hSupEq2, hSupEq]
  have hBlk' : s'.blockNumber = s.blockNumber := by rw [hBlk2, hBlk1]
  have hAccts' : s'.accts = s.accts := by rw [hAccts2, hAccts1]
  have hRes' : s'.reserve = s.reserve := by rw [hRes2, hRes1]
  cases s with | mk b0 sup0 bor0 res0 accs0 =>
    cases s' with | mk b2 sup2 bor2 res2 accs2 =>
      simp only at hSupEq' hBorEq' hBlk' hAccts' hRes' ⊢
      rw [hSupEq', hBorEq', hBlk', hAccts', hRes']

theorem plan5_state_eq_robust2 (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1) (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  have hSupPres : s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber ∧
      s1.accts = s.accts ∧ s1.reserve = s.reserve := setSup_pres s s1 a h1
  have hAccEq : accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) =
      accrueSide s.borrowState s.blockNumber (totalBorrows s) :=
    accBor_congr_setSup s s1 a h1
  have hSupEq : s1.supplyState = (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
    rcases setSup_cases s s1 a h1 with ⟨heq, heqS1⟩ | ⟨hne, _, heq2⟩
    · rw [heqS1]
      simp [heq]
    · have h1s : s1.supplyState =
          ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) := by
        rw [heq2]
      rw [h1s]
      simp [hne]
  have hBorEq : s'.borrowState = (if s.borrowState.speed = b then s.borrowState
      else ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side)) := by
    have hBorSpeed : s1.borrowState.speed = s.borrowState.speed := by rw [hSupPres.1]
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · have hEq : s.borrowState.speed = b := by rw [← hBorSpeed, heqB]
      have hBeq : s'.borrowState = s.borrowState := by rw [heqS, hSupPres.1]
      rw [hBeq]
      simp [hEq]
    · have hneB' : s.borrowState.speed ≠ b := by rw [← hBorSpeed]; exact hneB
      have h2s : s'.borrowState =
          ({ accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) with speed := b } : Side) := by
        rw [heq2B]
      rw [h2s, hAccEq]
      simp [hneB']
  have hSupEq' : s'.supplyState = (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS]
      exact hSupEq
    · have hss : s'.supplyState = s1.supplyState := by rw [heq2B]
      rw [hss, hSupEq]
  have hBlk' : s'.blockNumber = s.blockNumber := by
    have h1b := hSupPres.2.1
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS, h1b]
    · rw [heq2B, h1b]
  have hAccts' : s'.accts = s.accts := by
    have h1a := hSupPres.2.2.1
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS, h1a]
    · rw [heq2B, h1a]
  have hRes' : s'.reserve = s.reserve := by
    have h1r := hSupPres.2.2.2
    rcases setBor_cases s1 s' b h2 with ⟨heqB, heqS⟩ | ⟨hneB, _, heq2B⟩
    · rw [heqS, h1r]
    · rw [heq2B, h1r]
  cases s with | mk b0 sup0 bor0 res0 accs0 =>
    cases s' with | mk b2 sup2 bor2 res2 accs2 =>
      simp only at hSupEq' hBorEq hBlk' hAccts' hRes' ⊢
      simp [hSupEq', hBorEq, hBlk', hAccts', hRes']

theorem plan5_setSpeeds_effect_test (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    SpeedsSet s a b s' := by
  obtain ⟨s1, h1, h2'⟩ := plan5_setSpeeds_decomp s a b s' h
  obtain ⟨hSupNe, hSupEq, hBorEq1, hBlk1, hAccts1, hRes1⟩ := plan5_setSupplySpeed_spec s s1 a h1
  obtain ⟨hBorNe1, hBorEq, hSupEq2, hBlk2, hAccts2, hRes2⟩ := plan5_setBorrowSpeed_spec s1 s' b h2'
  have hState := plan5_setSpeeds_state_eq_try s s1 s' a b h1 h2'
  have hBorNe : (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) := by
    intro hne
    have hne1 : s1.borrowState.speed ≠ b := by rw [hBorEq1]; exact hne
    have hle := hBorNe1 hne1
    rw [hBorEq1, hBlk1] at hle
    exact hle
  exact ⟨hSupNe, hBorNe, hState⟩

theorem plan5_setSpeeds_effect_auxwrap (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    SpeedsSet s a b s' :=
  plan5_setSpeeds_effect_test s a b s' h

theorem req_set_speeds_proof_tmp : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact plan5_setSpeeds_effect_test s a b s' h

theorem plan6_setSpeeds_decomp (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ s1, setSupplySpeed s a = some s1 ∧ setBorrowSpeed s1 b = some s' :=
  plan5_setSpeeds_decomp s a b s' h


theorem plan6_supply_step_spec (s s1 : St) (a : Nat)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1.supplyState =
      (if s.supplyState.speed = a then s.supplyState
       else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) ∧
    s1.borrowState = s.borrowState ∧
    s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧
    s1.reserve = s.reserve :=
  plan5_setSupplySpeed_spec_try3 s s1 a h


theorem plan6_borrow_step_spec (s s' : St) (b : Nat)
    (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s'.borrowState =
      (if s.borrowState.speed = b then s.borrowState
       else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) ∧
    s'.supplyState = s.supplyState ∧
    s'.blockNumber = s.blockNumber ∧
    s'.accts = s.accts ∧
    s'.reserve = s.reserve :=
  plan5_setBorrowSpeed_spec s s' b h




theorem plan6_setSpeeds_state_eq_of_steps (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1)
    (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  obtain ⟨_, hSupEq, hBorEq1, hBlk1, hAccts1, hRes1⟩ := plan6_supply_step_spec s s1 a h1
  obtain ⟨_, hBorEq, hSupEq2, hBlk2, hAccts2, hRes2⟩ := plan6_borrow_step_spec s1 s' b h2
  have hBorSpeed : s1.borrowState.speed = s.borrowState.speed := by rw [hBorEq1]
  have hAccEq : accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) =
      accrueSide s.borrowState s.blockNumber (totalBorrows s) :=
    accBor_congr_setSup s s1 a h1
  have hBorEq' : s'.borrowState = (if s.borrowState.speed = b then s.borrowState
      else ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side)) := by
    have e := hBorEq
    rw [hBorSpeed, hAccEq, hBorEq1] at e
    exact e
  have hSupEq' : s'.supplyState = (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
    rw [hSupEq2, hSupEq]
  have hBlk' : s'.blockNumber = s.blockNumber := by rw [hBlk2, hBlk1]
  have hAccts' : s'.accts = s.accts := by rw [hAccts2, hAccts1]
  have hRes' : s'.reserve = s.reserve := by rw [hRes2, hRes1]
  cases s with | mk b0 sup0 bor0 res0 accs0 =>
    cases s' with | mk b2 sup2 bor2 res2 accs2 =>
      simp only at hSupEq' hBorEq' hBlk' hAccts' hRes'
      simp [hSupEq', hBorEq', hBlk', hAccts', hRes']


theorem plan6_setSpeeds_decomp_aux (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ s1, setSupplySpeed s a = some s1 ∧ setBorrowSpeed s1 b = some s' :=
  plan5_setSpeeds_decomp s a b s' h

theorem plan6_setSpeeds_decomp_proof (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ s1, setSupplySpeed s a = some s1 ∧ setBorrowSpeed s1 b = some s' :=
  plan5_setSpeeds_decomp s a b s' h

theorem plan6_decomp_check (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ s1, setSupplySpeed s a = some s1 ∧ setBorrowSpeed s1 b = some s' :=
  plan5_setSpeeds_decomp s a b s' h

theorem plan6_supply_step_spec_new (s s1 : St) (a : Nat)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1.supplyState =
      (if s.supplyState.speed = a then s.supplyState
       else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) ∧
    s1.borrowState = s.borrowState ∧
    s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧
    s1.reserve = s.reserve :=
  plan5_setSupplySpeed_spec_try3 s s1 a h

theorem plan6_borrow_step_spec_helper : ∀ (s s' : St) (b : Nat),
    setBorrowSpeed s b = some s' →
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s'.borrowState =
      (if s.borrowState.speed = b then s.borrowState
       else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) ∧
    s'.supplyState = s.supplyState ∧
    s'.blockNumber = s.blockNumber ∧
    s'.accts = s.accts ∧
    s'.reserve = s.reserve := by
  intro s s' b h
  exact plan5_setBorrowSpeed_spec s s' b h

theorem plan6_borrow_precond_of_steps_aux (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1)
    (h2 : setBorrowSpeed s1 b = some s') :
    s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
  obtain ⟨_, _, hBorEq1, hBlk1, _, _⟩ := plan6_supply_step_spec s s1 a h1
  obtain ⟨hBorNe1, _, _, _, _, _⟩ := plan6_borrow_step_spec s1 s' b h2
  intro hne
  have hne1 : s1.borrowState.speed ≠ b := by rw [hBorEq1]; exact hne
  have hle := hBorNe1 hne1
  rw [hBorEq1, hBlk1] at hle
  exact hle

theorem plan6_borrow_precond_of_steps (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1)
    (h2 : setBorrowSpeed s1 b = some s') :
    s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
  obtain ⟨_, _, hBorEq1, hBlk1, _, _⟩ := plan6_supply_step_spec s s1 a h1
  obtain ⟨hBorNe1, _, _, _, _, _⟩ := plan6_borrow_step_spec s1 s' b h2
  intro hne
  have hne1 : s1.borrowState.speed ≠ b := by rw [hBorEq1]; exact hne
  have hle := hBorNe1 hne1
  rw [hBorEq1, hBlk1] at hle
  exact hle

theorem plan6_setSpeeds_state_eq_of_steps_aux_tmp (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1)
    (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  obtain ⟨_, hSupEq, hBorEq1, hBlk1, hAccts1, hRes1⟩ := plan6_supply_step_spec s s1 a h1
  obtain ⟨_, hBorEq, hSupEq2, hBlk2, hAccts2, hRes2⟩ := plan6_borrow_step_spec s1 s' b h2
  have hBorSpeed : s1.borrowState.speed = s.borrowState.speed := by rw [hBorEq1]
  have hAccEq : accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) =
      accrueSide s.borrowState s.blockNumber (totalBorrows s) :=
    accBor_congr_setSup s s1 a h1
  have hBorEq' : s'.borrowState = (if s.borrowState.speed = b then s.borrowState
      else ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side)) := by
    have e := hBorEq
    rw [hBorSpeed, hAccEq, hBorEq1] at e
    exact e
  have hSupEq' : s'.supplyState = (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) := by
    rw [hSupEq2, hSupEq]
  have hBlk' : s'.blockNumber = s.blockNumber := by rw [hBlk2, hBlk1]
  have hAccts' : s'.accts = s.accts := by rw [hAccts2, hAccts1]
  have hRes' : s'.reserve = s.reserve := by rw [hRes2, hRes1]
  cases s with | mk b0 sup0 bor0 res0 accs0 =>
    cases s' with | mk b2 sup2 bor2 res2 accs2 =>
      simp only at hSupEq' hBorEq' hBlk' hAccts' hRes'
      simp [hSupEq', hBorEq', hBlk', hAccts', hRes']

theorem plan6_setSpeeds_state_eq_of_steps_wrap (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1)
    (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } :=
  plan6_setSpeeds_state_eq_of_steps_aux_tmp s s1 s' a b h1 h2

theorem plan5_setSpeeds_effect (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    SpeedsSet s a b s' :=
  plan5_setSpeeds_effect_test s a b s' h

theorem accrue_idx_bound2 (sd : Side) (now total : Nat) :
    total * ((accrueSide sd now total).index - sd.index) ≤ (now - sd.block) * sd.speed * doubleScale := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · have hpos : (if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then True else False) = True := by simp [h]
    rw [if_pos h]
    have hle : (now - sd.block) * sd.speed * doubleScale / total * total ≤ (now - sd.block) * sd.speed * doubleScale :=
      Nat.div_mul_le_self _ _
    have heq : (sd.index + (now - sd.block) * sd.speed * doubleScale / total) - sd.index
        = (now - sd.block) * sd.speed * doubleScale / total :=
      Nat.add_sub_cancel_left sd.index _
    have hcongr : ({ sd with index := sd.index + (now - sd.block) * sd.speed * doubleScale / total, block := now } : Side).index
        = sd.index + (now - sd.block) * sd.speed * doubleScale / total := rfl
    rw [hcongr, heq]
    calc total * ((now - sd.block) * sd.speed * doubleScale / total)
        = (now - sd.block) * sd.speed * doubleScale / total * total := by rw [Nat.mul_comm]
      _ ≤ (now - sd.block) * sd.speed * doubleScale := hle
  · rw [if_neg h]
    simp

theorem plan7_pendSum_upgrade_le (L : Legacy) (hL : L.WellFormed) :
    pendSum (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by sorry

theorem plan7_unidx_upgrade_le (L : Legacy) :
    unidx (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by sorry

theorem plan7_measure_upgrade_le (L : Legacy) (hL : L.WellFormed) :
    measure (upgrade L) ≤
      ((upgrade L).credited + L.owed) * doubleScale +
        (L.accts.map L.pendingScaled).sum % doubleScale := by sorry

theorem plan7_measure_exec_le (s : St) (op : Op) (hC : Consistent s) :
    measure (exec comptroller s op) ≤
      measure s +
        emittedBy (s.supplyState.speed, s.borrowState.speed) op * doubleScale := by sorry

theorem plan7_measure_run_le (L : Legacy) (ops : List Op) (hL : L.WellFormed) :
    measure (run comptroller (upgrade L) ops) ≤
      measure (upgrade L) +
        emitted (L.compSpeed, L.compSpeed) ops * doubleScale := by sorry

theorem plan7_credited_of_measure_le (s : St) (K r : Nat)
    (hr : r < doubleScale) (h : measure s ≤ K * doubleScale + r) :
    s.credited ≤ K := by sorry

theorem aux_sum_map_le_test123 (f g : Acct → Nat) (xs : List Acct)
    (h : ∀ a ∈ xs, f a ≤ g a) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx : f x ≤ g x := h x (by simp)
    have htail : ∀ a ∈ xs, f a ≤ g a := fun a ha => h a (by simp [ha])
    have iht := ih htail
    omega

theorem aux_upgrade_supply_idx2 (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem px7_legacy_le_S (St0 S r : Nat) (hSt : St0 ≤ S) (hr : r ≤ S) :
    legacyStart St0 r ≤ S := by
  unfold legacyStart
  by_cases h0 : r = 0
  · simp [h0, hSt]
  · simp [h0, hr]

theorem req_calls_succeed       : CallsSucceed comptroller := by
  unfold CallsSucceed
  intro s c hC
  cases c with
  | supplyHook who =>
    unfold comptroller
    simp only
    have hC0 := hC
    obtain ⟨hsupBlk, hborBlk, hall⟩ := hC
    have hUpd : (updateCompSupplyIndex s).isSome = true := t2b s hsupBlk
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at hUpd
    | some t =>
      have hCon_t : Consistent t := updSup_pres_consistent_aux s t hC0 hu
      have hLe : (t.acct who).supplierIndex ≤ t.supplyState.index :=
        plan1_supplier_acct_le t who hCon_t
      have hD : (distributeSupplierComp t who).isSome = true :=
        plan0_distributeSupplier_isSome t who hLe
      cases hd : distributeSupplierComp t who with
      | none => simp [hd] at hD
      | some v => simp [hd]
  | borrowHook who =>
    unfold comptroller
    simp only
    have hC0 := hC
    obtain ⟨hsupBlk, hborBlk, hall⟩ := hC
    have hUpd : (updateCompBorrowIndex s).isSome = true := aux_updBor_some s hborBlk
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at hUpd
    | some t =>
      have hCon_t : Consistent t := updBor_pres_consistent2 s t hC0 hu
      have hLe : (t.acct who).borrowerIndex ≤ t.borrowState.index :=
        plan1_borrower_acct_le t who hCon_t
      have hD : (distributeBorrowerComp t who).isSome = true :=
        plan0_distributeBorrower_isSome t who hLe
      cases hd : distributeBorrowerComp t who with
      | none => simp [hd] at hD
      | some v => simp [hd]
  | claim who =>
    unfold comptroller
    simp only
    have h := plan0_claimComp_isSome s who hC
    cases hc : claimComp s who with
    | none => simp [hc] at h
    | some v => simp
  | setSpeeds a b =>
    unfold comptroller
    simp only
    obtain ⟨hsupBlk, hborBlk, hall⟩ := hC
    have h := plan0_setCompSpeedInternal_isSome s a b hsupBlk hborBlk
    cases hs : setCompSpeedInternal s a b with
    | none => simp [hs] at h
    | some v => simp

theorem req_supply_hook : SupplyHookEffects comptroller := by
  unfold SupplyHookEffects
  intro s who s' h
  unfold comptroller at h
  simp only at h
  obtain ⟨t, ht, hu⟩ := borrow_bind_lemma (updateCompSupplyIndex s) (fun t => distributeSupplierComp t who) s' h
  exact plan2_supply_hook_effect s who t s' ht hu

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  unfold BorrowHookEffects
  intro s who s' h
  unfold comptroller at h
  simp only at h
  obtain ⟨t, ht, hu⟩ := borrow_bind_lemma (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) s' h
  exact plan2_borrow_hook_effect_bh2 s who t s' ht hu

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  exact plan3_claimComp_claimed s who s' h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact plan5_setSpeeds_effect_test s a b s' h

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry

theorem req_account_bounded     : AccountBounded comptroller := sorry

theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
