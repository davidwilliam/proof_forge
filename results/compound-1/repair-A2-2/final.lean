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

theorem aux_sub_some {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]

theorem aux_sub_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked
  simp [h]

def testBorrowUnits : Nat := 18977306140567618322762

def testState : St :=
  { blockNumber := 13322798,
    supplyState := { index := compInitialIndex, block := 13322798, speed := 0 },
    borrowState := { index := compInitialIndex, block := 13322798, speed := 0 },
    reserve := 1000000000000000000000000,
    accts := [{ supply := 0, borrow := testBorrowUnits, supplierIndex := 0, borrowerIndex := 0, accrued := 0, wallet := 0 }] }

def testStateAdv : St := { testState with blockNumber := 13322798 + 139 }
#check (comptroller testStateAdv (.claim 0))
#check (claimComp testStateAdv 0)

def creditAfterClaim : Option St := comptroller testStateAdv (.claim 0)

def creditVal : Nat := match creditAfterClaim with | some s => (s.acct 0).accrued + (s.acct 0).wallet | none => 999
#check creditVal
example : creditVal = 0 := by rfl

theorem req_supply_hook_proof2 : True := trivial

theorem req_supply_hook_proof3 : True := trivial

theorem tmp_check_defs : True := trivial

theorem tmpA : True := trivial

def probe1 : Bool := decide (accrualStart 0 (10^36) = 10^36)
#check probe1

def probe2 : Nat := creditFor 18977306140567618322762 0 (10^36)
#check probe2

def probe3 : Nat := creditFor 18977306140567618322762 (10^36) (10^36)
#check probe3

theorem probe_borrow_eq1 : updateCompBorrowIndex testStateAdv = some { testStateAdv with borrowState := accrueSide testStateAdv.borrowState testStateAdv.blockNumber (totalBorrows testStateAdv) } := by rfl

theorem probe_omega (a b : Nat) (h : a ≤ b) : a - b = 0 := by omega

theorem probe_mod_nil (f : Acct → Acct) (n : Nat) : ([] : List Acct).modify n f = [] := by simp

theorem probe_mod_cons0 (a : Acct) (t : List Acct) (f : Acct → Acct) : (a :: t).modify 0 f = f a :: t := by simp

theorem probe_mod_consS (a : Acct) (t : List Acct) (n : Nat) (f : Acct → Acct) : (a :: t).modify (n+1) f = a :: t.modify n f := by simp

theorem probe_getD_nil (n : Nat) : ([] : List Acct).getD n noAcct = noAcct := by simp

theorem probe_getD_cons0 (a : Acct) (t : List Acct) : (a :: t).getD 0 noAcct = a := by simp

theorem probe_getD_consS (a : Acct) (t : List Acct) (n : Nat) : (a :: t).getD (n+1) noAcct = t.getD n noAcct := by simp

theorem probe_len_mod (l : List Acct) (n : Nat) (f : Acct → Acct) : (l.modify n f).length = l.length := by simp

theorem modify_beyond_len (l : List Acct) (n : Nat) (f : Acct → Acct) (h : l.length ≤ n) : l.modify n f = l := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => simp at h
    | succ n => simp; exact ih n (by simp at h ⊢; omega)

def supplyPend (s : St) : Nat := (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum

def borrowPend (s : St) : Nat := (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum

def pendSum (s : St) : Nat := (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) + a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum

def unidx (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed + (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def potF (s : St) : Nat := s.credited * doubleScale + pendSum s + unidx s * doubleScale

theorem potF_test_true : True := trivial

theorem lem_probe : True := trivial
#check CompRewards.accrueSide
#check CompRewards.totalSupply

theorem lem_probe2 : True := trivial
#check @List.sum
#check @List.map

theorem lem_probe3 : True := trivial
#check CompRewards.doubleScale

theorem t_getmod1 (l : List Acct) (f : Acct → Acct) : (l.modify 0 f) = match l with | [] => [] | a :: t => f a :: t := by cases l <;> rfl

theorem t_getmod2 : True := trivial

theorem tmp_acc_bounded_probe : True := trivial

theorem doubleScale_pos : 0 < doubleScale := by unfold doubleScale; decide

theorem ds_pos2 : 0 < doubleScale := doubleScale_pos
#check List.modify
#check List.getD

theorem snippet_test_trivial : True := trivial

theorem probe_lemmas_exist : True := trivial

theorem try_calls_succeed_aux : True := trivial
#check @CompRewards.comptroller
#check @CompRewards.Consistent
#check @CompRewards.updateCompSupplyIndex
#check @CompRewards.subChecked

theorem aux_upd_supply_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) : (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex
  rw [aux_sub_some h]
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed <;> simp [hc]
  by_cases hc2 : 0 < s.blockNumber - s.supplyState.block <;> simp [hc2]

theorem aux_upd_borrow_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) : (updateCompBorrowIndex s).isSome := by
  unfold updateCompBorrowIndex
  rw [aux_sub_some h]
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed <;> simp [hc]
  by_cases hc2 : 0 < s.blockNumber - s.borrowState.block <;> simp [hc2]

theorem aux_dist_supply_some_of_le (s : St) (who : Nat)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  unfold distributeSupplierComp
  simp only
  by_cases hc : (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
  · simp [hc]
    have : compInitialIndex ≤ s.supplyState.index := hc.2
    have hsub : subChecked s.supplyState.index compInitialIndex = some (s.supplyState.index - compInitialIndex) := aux_sub_some this
    simp [hsub]
  · simp [hc]
    have hsub : subChecked s.supplyState.index (s.acct who).supplierIndex = some (s.supplyState.index - (s.acct who).supplierIndex) := aux_sub_some h
    simp [hsub]

theorem aux_dist_borrow_some_of_le (s : St) (who : Nat)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  unfold distributeBorrowerComp
  simp only
  by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · simp [hc]
    have : compInitialIndex ≤ s.borrowState.index := hc.2
    have hsub : subChecked s.borrowState.index compInitialIndex = some (s.borrowState.index - compInitialIndex) := aux_sub_some this
    simp [hsub]
  · simp [hc]
    have hsub : subChecked s.borrowState.index (s.acct who).borrowerIndex = some (s.borrowState.index - (s.acct who).borrowerIndex) := aux_sub_some h
    simp [hsub]

theorem tmp_shape (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
    (match (s.blockNumber - s.supplyState.block) with
    | d => if d > 0 ∧ s.supplyState.speed > 0 then
      let supplyTokens := totalSupply s
      let compAccrued := d * s.supplyState.speed
      let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
      some { s with supplyState := { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } }
    else if d > 0 then
      some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s) := by
  unfold updateCompSupplyIndex
  rw [aux_sub_some h]













theorem plan0_getD_supplier_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) :
    (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    unfold noAcct
    simp
  | cons a t ih =>
    cases who with
    | zero =>
      simp
      exact h a (by simp)
    | succ n =>
      simp
      exact ih n (fun b hb => h b (by simp [hb]))

theorem plan0_getD_borrower_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) :
    (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    unfold noAcct
    simp
  | cons a t ih =>
    cases who with
    | zero =>
      simp
      exact h a (by simp)
    | succ n =>
      simp
      exact ih n (fun b hb => h b (by simp [hb]))

theorem plan0_updateSupplyIndex_props (s s' : St)
    (hblock : s.supplyState.block ≤ s.blockNumber)
    (h : updateCompSupplyIndex s = some s') :
    s.supplyState.index ≤ s'.supplyState.index ∧
    s'.accts = s.accts ∧
    s'.blockNumber = s.blockNumber ∧
    s'.borrowState = s.borrowState := by
  unfold updateCompSupplyIndex at h
  rw [aux_sub_some hblock] at h
  by_cases hc : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [hc, and_self] at h
    simp only [ite_true] at h
    cases h
    refine ⟨Nat.le_add_right _ _, rfl, rfl, rfl⟩
  · simp only [hc, ite_false] at h
    by_cases hc2 : s.blockNumber - s.supplyState.block > 0
    · simp only [hc2, ite_true] at h
      cases h
      exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
    · simp only [hc2, ite_false] at h
      cases h
      exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩

theorem plan0_updateBorrowIndex_props (s s' : St)
    (hblock : s.borrowState.block ≤ s.blockNumber)
    (h : updateCompBorrowIndex s = some s') :
    s.borrowState.index ≤ s'.borrowState.index ∧
    s'.accts = s.accts ∧
    s'.blockNumber = s.blockNumber ∧
    s'.supplyState = s.supplyState := by
  unfold updateCompBorrowIndex at h
  rw [aux_sub_some hblock] at h
  by_cases hc : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [hc, and_self] at h
    simp only [ite_true] at h
    cases h
    refine ⟨Nat.le_add_right _ _, rfl, rfl, rfl⟩
  · simp only [hc, ite_false] at h
    by_cases hc2 : s.blockNumber - s.borrowState.block > 0
    · simp only [hc2, ite_true] at h
      cases h
      exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
    · simp only [hc2, ite_false] at h
      cases h
      exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩

theorem plan0_getD_modify_supplierIndex (l : List Acct) (n : Nat)
    (f : Acct → Acct) (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD n noAcct).supplierIndex =
      (l.getD n noAcct).supplierIndex := by
  induction l generalizing n with
  | nil =>
    simp only [List.modify_nil, List.getD_nil]
  | cons a t ih =>
    cases n with
    | zero =>
      simp only [probe_mod_cons0, probe_getD_cons0, hf]
    | succ n =>
      rw [probe_mod_consS, probe_getD_consS]
      exact ih n

theorem plan0_test_withAcct (s : St) (who : Nat) (f : Acct → Acct) : (s.withAcct who f).supplyState = s.supplyState := by rfl

theorem plan0_explore6 (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.acct St.withAcct
  simp only
  exact plan0_getD_modify_supplierIndex s.accts who f hf

theorem plan0_explore7 (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    s'.supplyState = s.supplyState := by
  by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · simp only [distributeBorrowerComp, hc] at h
    cases heq : subChecked s.borrowState.index compInitialIndex with
    | none => simp [heq] at h
    | some d =>
      simp [heq] at h
      subst h
      rfl
  · simp only [distributeBorrowerComp, hc] at h
    cases heq : subChecked s.borrowState.index (s.acct who).borrowerIndex with
    | none => simp [heq] at h
    | some d =>
      simp [heq] at h
      subst h
      rfl

theorem plan0_distributeBorrowerComp_preserves (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    s'.supplyState = s.supplyState ∧
    s'.blockNumber = s.blockNumber ∧
    (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by
  by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · simp only [distributeBorrowerComp, hc] at h
    cases heq : subChecked s.borrowState.index compInitialIndex with
    | none => simp [heq] at h
    | some d =>
      simp [heq] at h
      subst h
      refine ⟨rfl, rfl, ?_⟩
      unfold St.acct St.withAcct
      simp only
      exact plan0_getD_modify_supplierIndex s.accts who _ (fun a => rfl)
  · simp only [distributeBorrowerComp, hc] at h
    cases heq : subChecked s.borrowState.index (s.acct who).borrowerIndex with
    | none => simp [heq] at h
    | some d =>
      simp [heq] at h
      subst h
      refine ⟨rfl, rfl, ?_⟩
      unfold St.acct St.withAcct
      simp only
      exact plan0_getD_modify_supplierIndex s.accts who _ (fun a => rfl)

theorem tmp_supply_unfold (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ s1, updateCompSupplyIndex s = some s1 ∧ distributeSupplierComp s1 who = some s' := by
  unfold comptroller at h
  simp only at h
  cases heq : updateCompSupplyIndex s with
  | none => simp [heq] at h
  | some s1 =>
    simp [heq] at h
    exact ⟨s1, rfl, h⟩

theorem hlp_modify_congr (l : List Acct) (n : Nat) (f g : Acct → Acct)
    (h : f (l.getD n noAcct) = g (l.getD n noAcct)) :
    l.modify n f = l.modify n g := by
  induction l generalizing n with
  | nil =>
    simp
  | cons a t ih =>
    cases n with
    | zero =>
      simp only [probe_mod_cons0, probe_getD_cons0] at h ⊢
      rw [h]
    | succ n =>
      simp only [probe_mod_consS, probe_getD_consS] at h ⊢
      rw [ih n h]

theorem hlp_upd_sup_block (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex at h
  cases heq : subChecked s.blockNumber s.supplyState.block with
  | some _ =>
    unfold subChecked at heq
    by_cases hc : s.supplyState.block ≤ s.blockNumber
    · exact hc
    · simp [hc] at heq
  | none =>
    simp [heq] at h

theorem hlp_side_zero_add (sd : Side) (now : Nat) : ({ sd with index := sd.index + 0, block := now } : Side) = { sd with block := now } := by
  cases sd
  simp

theorem hlp_state_block_same3 (s : St) (h : s.supplyState.block = s.blockNumber) :
    ({ s with supplyState := ({ s.supplyState with block := s.blockNumber } : Side) } : St) = s := by
  cases s
  case mk bn sup bor res accts =>
    simp at h
    cases sup
    case mk i b sp =>
      simp at h ⊢
      simp [h]









theorem plan1_accrualStart_eq_if (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by
  unfold accrualStart
  by_cases h0 : recorded = 0
  · subst h0
    by_cases hi : compInitialIndex ≤ index <;> simp [hi]
  · simp [h0]



theorem plan2_accrueSide_not_pos (sd : Side) (now total : Nat)
    (h : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)) :
    accrueSide sd now total = { sd with block := now } := by
  unfold accrueSide
  simp [h]








theorem plan2_accrueSide_pos (sd : Side) (now total : Nat)
    (hd : 0 < now - sd.block) (hsp : 0 < sd.speed) (htot : 0 < total) :
    accrueSide sd now total =
      { sd with index := sd.index + (now - sd.block) * sd.speed * doubleScale / total, block := now } := by
  unfold accrueSide
  simp [hd, hsp, htot]

theorem plan2_accrueSide_not_pos2 (sd : Side) (now total : Nat)
    (h : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)) :
    accrueSide sd now total = { sd with block := now } := by
  unfold accrueSide
  simp [h]

theorem plan2_fraction_eq (d sp total : Nat) :
    fraction (d * sp) total = d * sp * doubleScale / total := by
  unfold fraction
  rfl

theorem plan2_side_block_eq_self (sd : Side) (now : Nat) (h : sd.block = now) :
    { sd with block := now } = sd := by
  cases sd with
  | mk i b sp =>
    simp at h ⊢
    rw [h]

theorem plan2_side_add_zero (sd : Side) (now : Nat) :
    { sd with index := sd.index + 0, block := now } = { sd with block := now } := by
  cases sd with
  | mk i b sp => simp

theorem probe_upd_goal (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    True := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    aux_sub_some h
  have e : updateCompSupplyIndex s =
      match (some (s.blockNumber - s.supplyState.block) : Option Nat) with
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
        else some s := by
    unfold updateCompSupplyIndex
    rw [hsub]
  trivial

theorem plan1_updateCompSupplyIndex_eq (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    aux_sub_some h
  by_cases hpos : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · obtain ⟨hd, hsp, htot⟩ := hpos
    have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) =
        { s.supplyState with index := s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s, block := s.blockNumber } :=
      plan2_accrueSide_pos s.supplyState s.blockNumber (totalSupply s) hd hsp htot
    rw [hacc]
    unfold updateCompSupplyIndex
    rw [hsub]
    have hd' : s.blockNumber - s.supplyState.block > 0 := hd
    have hsp' : s.supplyState.speed > 0 := hsp
    have htot' : totalSupply s > 0 := htot
    simp only [hd', hsp', and_self, ite_true, htot', plan2_fraction_eq]
  · have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) = { s.supplyState with block := s.blockNumber } :=
      plan2_accrueSide_not_pos s.supplyState s.blockNumber (totalSupply s) hpos
    rw [hacc]
    unfold updateCompSupplyIndex
    rw [hsub]
    by_cases hc1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · have hd : s.blockNumber - s.supplyState.block > 0 := hc1.1
      have hsp : s.supplyState.speed > 0 := hc1.2
      simp only [hd, hsp, and_self, ite_true]
      have htot0 : totalSupply s = 0 := by
        by_cases htot : 0 < totalSupply s
        · exact absurd ⟨hd, hsp, htot⟩ hpos
        · omega
      simp only [htot0] at *
      rfl
    · simp only [hc1, ite_false]
      by_cases hc2 : s.blockNumber - s.supplyState.block > 0
      · simp only [hc2, ite_true]
      · simp only [hc2, ite_false]
        have hbeq : s.supplyState.block = s.blockNumber := by omega
        simp only [plan2_side_block_eq_self s.supplyState s.blockNumber hbeq]

theorem plan1_distributeSupplierComp_le (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  unfold distributeSupplierComp at h
  simp only at h
  by_cases hc : (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
  · simp only [hc] at h
    cases heq : subChecked s.supplyState.index compInitialIndex with
    | none =>
      simp [heq] at h
    | some d =>
      have hacc : accrualStart (s.acct who).supplierIndex s.supplyState.index = compInitialIndex := by
        unfold accrualStart
        simp [hc.1, hc.2]
      rw [hacc]
      exact hc.2
  · simp only [hc] at h
    cases heq : subChecked s.supplyState.index (s.acct who).supplierIndex with
    | none =>
      simp [heq] at h
    | some d =>
      have hle : (s.acct who).supplierIndex ≤ s.supplyState.index := by
        by_cases hle2 : (s.acct who).supplierIndex ≤ s.supplyState.index
        · exact hle2
        · unfold subChecked at heq
          simp [hle2] at heq
      unfold accrualStart
      by_cases h0 : (s.acct who).supplierIndex = 0
      · simp only [h0]
        by_cases hi : compInitialIndex ≤ s.supplyState.index
        · simp only [hi]
          exact hi
        · simp only [hi]
          exact Nat.zero_le _
      · simp only [h0]
        exact hle

theorem tmp_probe_dist (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    True := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    rw [plan1_accrualStart_eq_if]
  have hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := aux_sub_some h
  have e : distributeSupplierComp s who = distributeSupplierComp s who := rfl
  unfold distributeSupplierComp at e
  trivial

theorem tmp_probe_dist4 (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) / doubleScale }) := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    rw [plan1_accrualStart_eq_if]
  have hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := aux_sub_some h
  unfold distributeSupplierComp
  simp only [hstart, hsub]
  unfold St.withAcct mulDouble
  rfl

theorem tmp_probe_dist5b (s : St) (who : Account)
    (_h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) / doubleScale }))
    = { s with accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold St.withAcct creditFor
  congr 1
  apply hlp_modify_congr
  simp only [St.acct]

theorem plan1_distributeSupplierComp_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    rw [plan1_accrualStart_eq_if]
  have hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := aux_sub_some h
  have e1 : distributeSupplierComp s who =
      some (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) / doubleScale }) := by
    unfold distributeSupplierComp
    simp only [hstart, hsub]
    unfold St.withAcct mulDouble
    rfl
  have e2 : s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) / doubleScale }))
    = { s with accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
    unfold St.withAcct creditFor
    congr 1
    apply hlp_modify_congr
    simp only [St.acct]
  rw [e1, e2]

theorem tmp_supply_proofB (s : St) (who : Account) (s' s1 : St)
    (hU : updateCompSupplyIndex s = some s1)
    (hDist : distributeSupplierComp s1 who = some s') :
    SupplyDistributed s who s' := by
  have hBlk : s.supplyState.block ≤ s.blockNumber := hlp_upd_sup_block s s1 hU
  have hUeq : updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    plan1_updateCompSupplyIndex_eq s hBlk
  have hSomeEq : (some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : Option St) = some s1 :=
    hUeq.symm.trans hU
  have hs1eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    (Option.some_inj.mp hSomeEq).symm
  subst hs1eq
  have hLe1 : accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex
      (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) ≤
      (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) :=
    plan1_distributeSupplierComp_le _ who s' hDist
  have hDeq := plan1_distributeSupplierComp_eq _ who hLe1
  rw [hDist] at hDeq
  simp only at hLe1 hDeq
  have hAcctEq : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who) = s.acct who := by
    simp [St.acct]
  have hIdxEq : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rfl
  rw [hAcctEq, hIdxEq] at hLe1
  refine ⟨hBlk, hLe1, ?_⟩
  cases hDeq
  rfl

theorem aux_upd_bor_block (s : St) (s1 : St)
    (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex at h
  cases heq : subChecked s.blockNumber s.borrowState.block with
  | some _ =>
    unfold subChecked at heq
    by_cases hc : s.borrowState.block ≤ s.blockNumber
    · exact hc
    · simp [hc] at heq
  | none =>
    simp [heq] at h

theorem aux_borrowUpEq (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    aux_sub_some h
  by_cases hpos : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · obtain ⟨hd, hsp, htot⟩ := hpos
    have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
        { s.borrowState with index := s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s, block := s.blockNumber } :=
      plan2_accrueSide_pos s.borrowState s.blockNumber (totalBorrows s) hd hsp htot
    rw [hacc]
    unfold updateCompBorrowIndex
    rw [hsub]
    have hd' : s.blockNumber - s.borrowState.block > 0 := hd
    have hsp' : s.borrowState.speed > 0 := hsp
    have htot' : totalBorrows s > 0 := htot
    simp only [hd', hsp', and_self, ite_true, htot', plan2_fraction_eq]
  · have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) = { s.borrowState with block := s.blockNumber } :=
      plan2_accrueSide_not_pos s.borrowState s.blockNumber (totalBorrows s) hpos
    rw [hacc]
    unfold updateCompBorrowIndex
    rw [hsub]
    by_cases hc1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · have hd : s.blockNumber - s.borrowState.block > 0 := hc1.1
      have hsp : s.borrowState.speed > 0 := hc1.2
      simp only [hd, hsp, and_self, ite_true]
      have htot0 : totalBorrows s = 0 := by
        by_cases htot : 0 < totalBorrows s
        · exact absurd ⟨hd, hsp, htot⟩ hpos
        · omega
      simp only [htot0] at *
      rfl
    · simp only [hc1, ite_false]
      by_cases hc2 : s.blockNumber - s.borrowState.block > 0
      · simp only [hc2, ite_true]
      · simp only [hc2, ite_false]
        have hbeq : s.borrowState.block = s.blockNumber := by omega
        simp only [plan2_side_block_eq_self s.borrowState s.blockNumber hbeq]

theorem aux_borrowDistLe (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  unfold distributeBorrowerComp at h
  simp only at h
  by_cases hc : (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
  · simp only [hc] at h
    cases heq : subChecked s.borrowState.index compInitialIndex with
    | none =>
      simp [heq] at h
    | some d =>
      have hacc : accrualStart (s.acct who).borrowerIndex s.borrowState.index = compInitialIndex := by
        unfold accrualStart
        simp [hc.1, hc.2]
      rw [hacc]
      exact hc.2
  · simp only [hc] at h
    cases heq : subChecked s.borrowState.index (s.acct who).borrowerIndex with
    | none =>
      simp [heq] at h
    | some d =>
      have hle : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
        by_cases hle2 : (s.acct who).borrowerIndex ≤ s.borrowState.index
        · exact hle2
        · unfold subChecked at heq
          simp [hle2] at heq
      unfold accrualStart
      by_cases h0 : (s.acct who).borrowerIndex = 0
      · simp only [h0]
        by_cases hi : compInitialIndex ≤ s.borrowState.index
        · simp only [hi]
          exact hi
        · simp only [hi]
          exact Nat.zero_le _
      · simp only [h0]
        exact hle

theorem aux_borrowDistEq (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := s.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
    rw [plan1_accrualStart_eq_if]
  have hsub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := aux_sub_some h
  have e1 : distributeBorrowerComp s who =
      some (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) / doubleScale }) := by
    unfold distributeBorrowerComp
    simp only [hstart, hsub]
    unfold St.withAcct mulDouble
    rfl
  have e2 : s.withAcct who (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) / doubleScale }))
    = { s with accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := s.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
    unfold St.withAcct creditFor
    congr 1
    apply hlp_modify_congr
    simp only [St.acct]
  rw [e1, e2]

theorem aux_borrowProofB (s : St) (who : Account) (s' s1 : St)
    (hU : updateCompBorrowIndex s = some s1)
    (hDist : distributeBorrowerComp s1 who = some s') :
    BorrowDistributed s who s' := by
  have hBlk : s.borrowState.block ≤ s.blockNumber := aux_upd_bor_block s s1 hU
  have hUeq : updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    aux_borrowUpEq s hBlk
  have hSomeEq : (some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : Option St) = some s1 :=
    hUeq.symm.trans hU
  have hs1eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    (Option.some_inj.mp hSomeEq).symm
  subst hs1eq
  have hLe1 : accrualStart (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex
      (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) ≤
      (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) :=
    aux_borrowDistLe _ who s' hDist
  have hDeq := aux_borrowDistEq _ who hLe1
  rw [hDist] at hDeq
  simp only at hLe1 hDeq
  have hAcctEq : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who) = s.acct who := by
    simp [St.acct]
  have hIdxEq : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rfl
  rw [hAcctEq, hIdxEq] at hLe1
  refine ⟨hBlk, hLe1, ?_⟩
  cases hDeq
  rfl









theorem plan3_claimed_of_claimComp (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    Claimed s who s' := by
  have hsteps : ∃ b1 m1 b2 m2,
      updateCompBorrowIndex s = some b1 ∧
      distributeBorrowerComp b1 who = some m1 ∧
      updateCompSupplyIndex m1 = some b2 ∧
      distributeSupplierComp b2 who = some m2 ∧
      s' = grantCompInternal m2 who := by
    unfold claimComp at h
    cases hb1 : updateCompBorrowIndex s with
    | none => simp [hb1] at h
    | some b1 =>
      simp [hb1] at h
      cases hm1 : distributeBorrowerComp b1 who with
      | none => simp [hm1] at h
      | some m1 =>
        simp [hm1] at h
        cases hb2 : updateCompSupplyIndex m1 with
        | none => simp [hb2] at h
        | some b2 =>
          simp [hb2] at h
          cases hm2 : distributeSupplierComp b2 who with
          | none => simp [hm2] at h
          | some m2 => simp [hm2] at h; exact ⟨b1, m1, b2, m2, rfl, hm1, hb2, hm2, h.symm⟩
  obtain ⟨b1, m1, b2, m2, hU1, hD1, hU2, hD2, heq⟩ := hsteps
  have hB : BorrowDistributed s who m1 := aux_borrowProofB s who m1 b1 hU1 hD1
  have hS : SupplyDistributed m1 who m2 := tmp_supply_proofB m1 who m2 b2 hU2 hD2
  have hG : grantCompInternal m2 who = grant m2 who := by
    by_cases hc : 0 < (m2.acct who).accrued ∧ (m2.acct who).accrued ≤ m2.reserve
    · have hmod : m2.accts.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + (m2.acct who).accrued })) =
        m2.accts.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued })) := by
        apply hlp_modify_congr
        simp only [St.acct]
      unfold grantCompInternal grant
      simp only [hc, and_self, ↓reduceIte, hmod]
    · have hc2 : ¬ ((m2.acct who).accrued > 0 ∧ (m2.acct who).accrued ≤ m2.reserve) := hc
      unfold grantCompInternal grant
      simp only [hc, hc2, ↓reduceIte]
  exact ⟨m1, m2, hB, hS, heq.trans hG⟩


theorem plan3_bind_some_probe (x : Option St) (f : St → Option St) (y : St)
    (h : x.bind f = some y) : ∃ a, x = some a := by
  cases x with
  | none =>
    simp at h
  | some a =>
    exact ⟨a, rfl⟩

theorem plan3_claimComp_steps_probe6 (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ b1, updateCompBorrowIndex s = some b1 := by
  unfold claimComp at h
  cases hb1 : updateCompBorrowIndex s with
  | none =>
    simp [hb1] at h
  | some b1 =>
    refine ⟨b1, rfl⟩

theorem plan3_claimComp_steps (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ b1 m1 b2 m2,
      updateCompBorrowIndex s = some b1 ∧
      distributeBorrowerComp b1 who = some m1 ∧
      updateCompSupplyIndex m1 = some b2 ∧
      distributeSupplierComp b2 who = some m2 ∧
      s' = grantCompInternal m2 who := by
  unfold claimComp at h
  cases hb1 : updateCompBorrowIndex s with
  | none =>
    simp [hb1] at h
  | some b1 =>
    simp [hb1] at h
    cases hm1 : distributeBorrowerComp b1 who with
    | none =>
      simp [hm1] at h
    | some m1 =>
      simp [hm1] at h
      cases hb2 : updateCompSupplyIndex m1 with
      | none =>
        simp [hb2] at h
      | some b2 =>
        simp [hb2] at h
        cases hm2 : distributeSupplierComp b2 who with
        | none =>
          simp [hm2] at h
        | some m2 =>
          simp [hm2] at h
          exact ⟨b1, m1, b2, m2, rfl, hm1, hb2, hm2, h.symm⟩

theorem plan3_borrowDistributed_of_steps (s : St) (who : Account) (m1 b1 : St)
    (hU : updateCompBorrowIndex s = some b1)
    (hD : distributeBorrowerComp b1 who = some m1) :
    BorrowDistributed s who m1 :=
  aux_borrowProofB s who m1 b1 hU hD

theorem plan3_supplyDistributed_of_steps (s : St) (who : Account) (m2 b2 : St)
    (hU : updateCompSupplyIndex s = some b2)
    (hD : distributeSupplierComp b2 who = some m2) :
    SupplyDistributed s who m2 :=
  tmp_supply_proofB s who m2 b2 hU hD

theorem plan3_grantCompInternal_eq_grant3 (s : St) (who : Account)
    (h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) :
    grantCompInternal s who = grant s who := by
  have hmod : s.accts.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued })) =
    s.accts.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued })) := by
    apply hlp_modify_congr
    simp [St.acct]
  unfold grantCompInternal grant
  simp [h, hmod]

theorem plan3_grant_neg_helper (s : St) (who : Account)
    (h : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve)) :
    grantCompInternal s who = s := by
  unfold grantCompInternal
  have h2 : ¬ ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) := h
  simp [h2]

theorem plan3_grant_neg_helper2 (s : St) (who : Account)
    (h : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve)) :
    grant s who = s := by
  unfold grant
  simp [h]

theorem plan3_grantCompInternal_eq_grant (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · exact plan3_grantCompInternal_eq_grant3 s who h
  · rw [plan3_grant_neg_helper s who h, plan3_grant_neg_helper2 s who h]

theorem plan3_claimed_of_claimComp_aux_proof (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    Claimed s who s' := by
  obtain ⟨b1, m1, b2, m2, hU1, hD1, hU2, hD2, heq⟩ := plan3_claimComp_steps s who s' h
  have hB : BorrowDistributed s who m1 := plan3_borrowDistributed_of_steps s who m1 b1 hU1 hD1
  have hS : SupplyDistributed m1 who m2 := plan3_supplyDistributed_of_steps m1 who m2 b2 hU2 hD2
  have hG : grantCompInternal m2 who = grant m2 who := plan3_grantCompInternal_eq_grant m2 who
  exact ⟨m1, m2, hB, hS, heq.trans hG⟩

theorem aux_probe_setS (s : St) (sup : Nat) :
    setSupplySpeed s sup =
    (if s.supplyState.speed ≠ sup then (updateCompSupplyIndex s).map fun s_1 => ({ s_1 with supplyState := { s_1.supplyState with speed := sup } } : St) else some s) := by rfl

theorem aux_probe_setS2 (s : St) (sup : Nat) (heq : s.supplyState.speed = sup) :
    setSupplySpeed s sup = some s := by unfold setSupplySpeed; simp [heq]

theorem aux_S_supNeed (s : St) (sup : Nat) (sI : St)
    (hS : setSupplySpeed s sup = some sI) (hne : s.supplyState.speed ≠ sup) :
    s.supplyState.block ≤ s.blockNumber := by
  have hMap : setSupplySpeed s sup =
      (updateCompSupplyIndex s).map (fun s_1 => ({ s_1 with supplyState := { s_1.supplyState with speed := sup } } : St)) := by
    unfold setSupplySpeed; simp [hne]
  rw [hMap] at hS
  cases hU : updateCompSupplyIndex s with
  | none => simp [hU] at hS
  | some sU => exact hlp_upd_sup_block s sU hU

theorem aux_S_supEq (s : St) (sup : Nat) (sI : St)
    (hS : setSupplySpeed s sup = some sI) :
    sI.supplyState = (if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup }) := by
  by_cases heq : s.supplyState.speed = sup
  · have hEq : setSupplySpeed s sup = some s := aux_probe_setS2 s sup heq
    rw [hEq] at hS
    have hs : s = sI := Option.some_inj.mp hS
    rw [← hs]
    simp [heq]
  · have hMap : setSupplySpeed s sup =
        (updateCompSupplyIndex s).map (fun s_1 => ({ s_1 with supplyState := { s_1.supplyState with speed := sup } } : St)) := by
      unfold setSupplySpeed; simp [heq]
    rw [hMap] at hS
    cases hU : updateCompSupplyIndex s with
    | none => simp [hU] at hS
    | some sU =>
      simp [hU] at hS
      have hBlk : s.supplyState.block ≤ s.blockNumber := hlp_upd_sup_block s sU hU
      have hUeq := plan1_updateCompSupplyIndex_eq s hBlk
      rw [hU] at hUeq
      have hsU : sU = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
        Option.some_inj.mp hUeq
      rw [hsU] at hS
      rw [← hS]
      simp [heq]







theorem plan4_setBorrowSpeed_state (s : St) (bor : Nat) (s' : St)
    (h : setBorrowSpeed s bor = some s') :
    s' = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  by_cases heq : s.borrowState.speed = bor
  · have hEq : setBorrowSpeed s bor = some s := by unfold setBorrowSpeed; simp [heq]
    rw [hEq] at h
    cases h
    simp [heq]
  · have hMap : setBorrowSpeed s bor =
        (updateCompBorrowIndex s).map (fun s_1 => ({ s_1 with borrowState := { s_1.borrowState with speed := bor } } : St)) := by
      unfold setBorrowSpeed; simp [heq]
    rw [hMap] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      simp [hU] at h
    | some sU =>
      simp [hU] at h
      subst h
      have hBlk : s.borrowState.block ≤ s.blockNumber := aux_upd_bor_block s sU hU
      have hUeq := aux_borrowUpEq s hBlk
      rw [hU] at hUeq
      have hsU : sU = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        Option.some_inj.mp hUeq
      rw [hsU]
      simp [heq]




theorem plan4_setSupplySpeed_block_proof : True := trivial

theorem plan4_setSupplySpeed_block_aux (s : St) (sup : Nat) (sI : St)
    (h : setSupplySpeed s sup = some sI) (hne : s.supplyState.speed ≠ sup) :
    s.supplyState.block ≤ s.blockNumber := aux_S_supNeed s sup sI h hne

theorem plan4_setSupplySpeed_block (s : St) (sup : Nat) (sI : St)
    (h : setSupplySpeed s sup = some sI) (hne : s.supplyState.speed ≠ sup) :
    s.supplyState.block ≤ s.blockNumber := aux_S_supNeed s sup sI h hne

theorem plan4_setBorrowSpeed_block (s : St) (bor : Nat) (s' : St)
    (h : setBorrowSpeed s bor = some s') (hne : s.borrowState.speed ≠ bor) :
    s.borrowState.block ≤ s.blockNumber := by
  have hMap : setBorrowSpeed s bor =
      (updateCompBorrowIndex s).map (fun s_1 => ({ s_1 with borrowState := { s_1.borrowState with speed := bor } } : St)) := by
    unfold setBorrowSpeed
    simp [hne]
  rw [hMap] at h
  cases hU : updateCompBorrowIndex s with
  | none => simp [hU] at h
  | some sU => exact aux_upd_bor_block s sU hU

theorem plan4_setSupplySpeed_state (s : St) (sup : Nat) (sI : St)
    (h : setSupplySpeed s sup = some sI) :
    sI = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by
  by_cases heq : s.supplyState.speed = sup
  · have hEq : setSupplySpeed s sup = some s := by unfold setSupplySpeed; simp [heq]
    rw [hEq] at h
    cases h
    simp [heq]
  · have hMap : setSupplySpeed s sup =
        (updateCompSupplyIndex s).map (fun s_1 => ({ s_1 with supplyState := { s_1.supplyState with speed := sup } } : St)) := by
      unfold setSupplySpeed; simp [heq]
    rw [hMap] at h
    cases hU : updateCompSupplyIndex s with
    | none =>
      simp [hU] at h
    | some sU =>
      simp [hU] at h
      subst h
      have hBlk : s.supplyState.block ≤ s.blockNumber := hlp_upd_sup_block s sU hU
      have hUeq := plan1_updateCompSupplyIndex_eq s hBlk
      rw [hU] at hUeq
      have hsU : sU = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
        Option.some_inj.mp hUeq
      rw [hsU]
      simp [heq]

theorem plan4_setBorrowSpeed_state_proof (s : St) (bor : Nat) (s' : St)
    (h : setBorrowSpeed s bor = some s') :
    s' = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  by_cases heq : s.borrowState.speed = bor
  · have hEq : setBorrowSpeed s bor = some s := by unfold setBorrowSpeed; simp [heq]
    rw [hEq] at h
    cases h
    simp [heq]
  · have hMap : setBorrowSpeed s bor =
        (updateCompBorrowIndex s).map (fun s_1 => ({ s_1 with borrowState := { s_1.borrowState with speed := bor } } : St)) := by
      unfold setBorrowSpeed; simp [heq]
    rw [hMap] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      simp [hU] at h
    | some sU =>
      simp [hU] at h
      subst h
      have hBlk : s.borrowState.block ≤ s.blockNumber := aux_upd_bor_block s sU hU
      have hUeq := aux_borrowUpEq s hBlk
      rw [hU] at hUeq
      have hsU : sU = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        Option.some_inj.mp hUeq
      rw [hsU]
      simp [heq]

theorem plan4_tmp2 (s sI : St) (Y Z : Side)
    (hSIeq : sI = ({ s with supplyState := Y } : St)) :
    ({ sI with borrowState := Z } : St) =
    ({ s with supplyState := Y, borrowState := Z } : St) := by
  rw [hSIeq]











theorem plan5_setCompSpeedInternal_steps (s : St) (sup bor : Nat) (s' : St)
    (h : setCompSpeedInternal s sup bor = some s') :
    ∃ sI, setSupplySpeed s sup = some sI ∧ setBorrowSpeed sI bor = some s' := by
  unfold setCompSpeedInternal at h
  cases hI : setSupplySpeed s sup with
  | none =>
    simp [hI] at h
  | some sI =>
    simp [hI] at h
    exact ⟨sI, rfl, h⟩

theorem plan5_setSupplySpeed_preserves (s : St) (sup : Nat) (sI : St)
    (h : setSupplySpeed s sup = some sI) :
    sI.borrowState = s.borrowState ∧ sI.blockNumber = s.blockNumber ∧
      sI.accts = s.accts ∧ totalBorrows sI = totalBorrows s := by
  by_cases heq : s.supplyState.speed = sup
  · have hEq : setSupplySpeed s sup = some s := by unfold setSupplySpeed; simp [heq]
    rw [hEq] at h
    cases h
    refine ⟨rfl, rfl, rfl, rfl⟩
  · have hMap : setSupplySpeed s sup =
        (updateCompSupplyIndex s).map (fun s_1 => ({ s_1 with supplyState := { s_1.supplyState with speed := sup } } : St)) := by
      unfold setSupplySpeed; simp [heq]
    rw [hMap] at h
    cases hU : updateCompSupplyIndex s with
    | none => simp [hU] at h
    | some sU =>
      simp [hU] at h
      subst h
      have hprops := plan0_updateSupplyIndex_props s sU (hlp_upd_sup_block s sU hU) hU
      obtain ⟨_, haccts, hblk, hborEq⟩ := hprops
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hborEq]
      · simp [hblk]
      · simp [haccts]
      · unfold totalBorrows
        rw [haccts]

theorem plan5_borrow_block_after_supply (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s')
    (hne : s.borrowState.speed ≠ bor) :
    s.borrowState.block ≤ s.blockNumber := by
  have hpres := plan5_setSupplySpeed_preserves s sup sI hI
  obtain ⟨hborEq, hblkEq, _, _⟩ := hpres
  have hneI : sI.borrowState.speed ≠ bor := by rw [hborEq]; exact hne
  have hle := plan4_setBorrowSpeed_block sI bor s' hB hneI
  rw [hborEq, hblkEq] at hle
  exact hle

theorem plan5_final_check (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  have hIeq := plan4_setSupplySpeed_state s sup sI hI
  have hBeq := plan4_setBorrowSpeed_state_proof sI bor s' hB
  have hborEq : sI.borrowState = s.borrowState := by rw [hIeq]
  have hblkEq : sI.blockNumber = s.blockNumber := by rw [hIeq]
  have hacctsEq : sI.accts = s.accts := by rw [hIeq]
  have htotEq : totalBorrows sI = totalBorrows s := by unfold totalBorrows; rw [hacctsEq]
  have hspeedEq : sI.borrowState.speed = s.borrowState.speed := by rw [hborEq]
  have hZ : (if sI.borrowState.speed = bor then sI.borrowState
      else { accrueSide sI.borrowState sI.blockNumber (totalBorrows sI) with speed := bor })
      = (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) := by
    rw [hspeedEq, hborEq]
    by_cases heq : s.borrowState.speed = bor
    · simp [heq]
    · simp only [heq, ite_false]
      have hacc : accrueSide s.borrowState sI.blockNumber (totalBorrows sI)
        = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
        rw [hblkEq, htotEq]
      rw [hacc]
  have hBeq2 : s' = { sI with borrowState :=
      (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) } := by
    rw [hBeq, hZ]
  rw [hIeq] at hBeq2
  rw [hBeq2]

theorem plan5_tmp_selfcontained (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  have hIeq := plan4_setSupplySpeed_state s sup sI hI
  have hBeq := plan4_setBorrowSpeed_state_proof sI bor s' hB
  have hborEq : sI.borrowState = s.borrowState := by rw [hIeq]
  have hblkEq : sI.blockNumber = s.blockNumber := by rw [hIeq]
  have hacctsEq : sI.accts = s.accts := by rw [hIeq]
  have htotEq : totalBorrows sI = totalBorrows s := by unfold totalBorrows; rw [hacctsEq]
  have hspeedEq : sI.borrowState.speed = s.borrowState.speed := by rw [hborEq]
  have hZ : (if sI.borrowState.speed = bor then sI.borrowState
      else { accrueSide sI.borrowState sI.blockNumber (totalBorrows sI) with speed := bor })
      = (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) := by
    rw [hspeedEq, hborEq]
    by_cases heq : s.borrowState.speed = bor
    · simp [heq]
    · simp only [heq, ite_false]
      have hacc : accrueSide s.borrowState sI.blockNumber (totalBorrows sI)
        = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
        rw [hblkEq, htotEq]
      rw [hacc]
  have hBeq2 : s' = { sI with borrowState :=
      (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) } := by
    rw [hBeq, hZ]
  rw [hIeq] at hBeq2
  rw [hBeq2]

theorem plan5_speedsSet_of_steps2 (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s') :
    SpeedsSet s sup bor s' := by
  refine ⟨?h1, ?h2, ?h3⟩
  · intro hne
    exact plan4_setSupplySpeed_block s sup sI hI hne
  · intro hne
    exact plan5_borrow_block_after_supply s sup bor sI s' hI hB hne
  · exact plan5_tmp_selfcontained s sup bor sI s' hI hB

theorem plan4_setCompSpeedInternal_speedsSet2 (s : St) (sup bor : Nat) (s' : St)
    (h : setCompSpeedInternal s sup bor = some s') :
    SpeedsSet s sup bor s' := by
  obtain ⟨sI, hI, hB⟩ := plan5_setCompSpeedInternal_steps s sup bor s' h
  exact plan5_speedsSet_of_steps2 s sup bor sI s' hI hB

theorem plan5_setCompSpeedInternal_final_state (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  have hIeq := plan4_setSupplySpeed_state s sup sI hI
  have hBeq := plan4_setBorrowSpeed_state_proof sI bor s' hB
  have hborEq : sI.borrowState = s.borrowState := by rw [hIeq]
  have hblkEq : sI.blockNumber = s.blockNumber := by rw [hIeq]
  have hacctsEq : sI.accts = s.accts := by rw [hIeq]
  have htotEq : totalBorrows sI = totalBorrows s := by unfold totalBorrows; rw [hacctsEq]
  have hspeedEq : sI.borrowState.speed = s.borrowState.speed := by rw [hborEq]
  have hZ : (if sI.borrowState.speed = bor then sI.borrowState
      else { accrueSide sI.borrowState sI.blockNumber (totalBorrows sI) with speed := bor })
      = (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) := by
    rw [hspeedEq, hborEq]
    by_cases heq : s.borrowState.speed = bor
    · simp [heq]
    · simp only [heq, ite_false]
      have hacc : accrueSide s.borrowState sI.blockNumber (totalBorrows sI)
        = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
        rw [hblkEq, htotEq]
      rw [hacc]
  have hBeq2 : s' = { sI with borrowState :=
      (if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor }) } := by
    rw [hBeq, hZ]
  rw [hIeq] at hBeq2
  rw [hBeq2]

theorem plan5_speedsSet_of_steps (s : St) (sup bor : Nat) (sI s' : St)
    (hI : setSupplySpeed s sup = some sI)
    (hB : setBorrowSpeed sI bor = some s') :
    SpeedsSet s sup bor s' := by
  refine ⟨?h1, ?h2, ?h3⟩
  · intro hne
    exact plan4_setSupplySpeed_block s sup sI hI hne
  · intro hne
    exact plan5_borrow_block_after_supply s sup bor sI s' hI hB hne
  · exact plan5_tmp_selfcontained s sup bor sI s' hI hB

theorem plan4_setCompSpeedInternal_speedsSet_aux_wrap (s : St) (sup bor : Nat) (s' : St)
    (h : setCompSpeedInternal s sup bor = some s') :
    SpeedsSet s sup bor s' := by
  obtain ⟨sI, hI, hB⟩ := plan5_setCompSpeedInternal_steps s sup bor s' h
  exact plan5_speedsSet_of_steps2 s sup bor sI s' hI hB

theorem plan4_setCompSpeedInternal_speedsSet (s : St) (sup bor : Nat) (s' : St)
    (h : setCompSpeedInternal s sup bor = some s') :
    SpeedsSet s sup bor s' := by
  obtain ⟨sI, hI, hB⟩ := plan5_setCompSpeedInternal_steps s sup bor s' h
  exact plan5_speedsSet_of_steps2 s sup bor sI s' hI hB

theorem accrue_block (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrue_index_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, Nat.le_add_right]
  · simp [h]

theorem accrue_index_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index = sd.index + (if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then (now - sd.block) * sd.speed * doubleScale / total else 0) := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem modify_map_sum_eq (l : List Acct) (n : Nat) (f : Acct → Acct) (g : Acct → Nat)
    (h : ∀ a, g (f a) = g a) : ((l.modify n f).map g).sum = (l.map g).sum := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => simp [h a]
    | succ n => simp [ih n]

theorem modify_pres_supply (l : List Acct) (n : Nat) (idx add : Nat) :
    (((l.modify n fun a => ({ a with supplierIndex := idx, accrued := a.accrued + add } : Acct))).map Acct.supply).sum =
    ((l.map Acct.supply).sum) := by
  apply modify_map_sum_eq
  intro a
  rfl

theorem lem_check : True := trivial
#check CompRewards.doubleScale

theorem accrue_block_eq (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := accrue_block sd now total

theorem accrue_speed_eq (sd : Side) (now total : Nat) : (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem totalSupply_withAcct (s : St) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).supply = a.supply) : totalSupply (s.withAcct who f) = totalSupply s := by
  unfold totalSupply St.withAcct
  simp only
  have e : ((s.accts.modify who f).map Acct.supply) = (s.accts.map Acct.supply) := by
    induction s.accts generalizing who with
    | nil => simp
    | cons a t ih =>
      cases who with
      | zero => simp [h a]
      | succ n => simp [ih n]
  rw [e]

theorem totalBorrows_withAcct_sup (s : St) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).borrow = a.borrow) : totalBorrows (s.withAcct who f) = totalBorrows s := by
  unfold totalBorrows St.withAcct
  simp only
  have e : ((s.accts.modify who f).map Acct.borrow) = (s.accts.map Acct.borrow) := by
    induction s.accts generalizing who with
    | nil => simp
    | cons a t ih =>
      cases who with
      | zero => simp [h a]
      | succ n => simp [ih n]
  rw [e]





theorem plan6_consistent_upgrade (L : Legacy) (hWF : L.WellFormed) :
    Consistent (upgrade L) ∧
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs1, hs2, hb1, hb2, hsBlk, hbBlk, hall⟩ := hWF
  have hUblkS : (upgrade L).blockNumber = L.blockNumber := by simp [upgrade]
  have hSblk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
    unfold upgrade initSide
    by_cases h : L.supplyIndex = 0 <;> simp [h]
  have hBblk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
    unfold upgrade initSide
    by_cases h : L.borrowIndex = 0 <;> simp [h]
  have hSidx : (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
    unfold upgrade initSide
    by_cases h : L.supplyIndex = 0 <;> simp [h]
  have hBidx : (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
    unfold upgrade initSide
    by_cases h : L.borrowIndex = 0 <;> simp [h]
  have hAccts : (upgrade L).accts = L.accts := by simp [upgrade]
  have hSpS : (upgrade L).supplyState.speed = L.compSpeed := by unfold upgrade initSide; by_cases h : L.supplyIndex = 0 <;> simp [h]
  have hSpB : (upgrade L).borrowState.speed = L.compSpeed := by unfold upgrade initSide; by_cases h : L.borrowIndex = 0 <;> simp [h]
  refine ⟨⟨?h1, ?h2, ?h3⟩, hSpS, hSpB⟩
  · rw [hSblk, hUblkS]
    by_cases h : L.supplyIndex = 0
    · simp [h]
    · simp [h]; exact hsBlk
  · rw [hBblk, hUblkS]
    by_cases h : L.borrowIndex = 0
    · simp [h]
    · simp [h]; exact hbBlk
  · intro a ha
    rw [hAccts] at ha
    have haL := hall a ha
    obtain ⟨haS, haB⟩ := haL
    rw [hSidx, hBidx]
    constructor
    · by_cases h : L.supplyIndex = 0
      · simp [h]
        rw [h] at haS
        have hz : a.supplierIndex = 0 := Nat.le_zero.mp haS
        omega
      · simp [h]; exact haS
    · by_cases h : L.borrowIndex = 0
      · simp [h]
        rw [h] at haB
        have hz : a.borrowerIndex = 0 := Nat.le_zero.mp haB
        omega
      · simp [h]; exact haB


theorem plan6_exec_potF_le (s : St) (sp : Nat × Nat) (op : Op)
    (hC : Consistent s)
    (hS : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    potF (exec comptroller s op) ≤ potF s + emittedBy sp op * doubleScale := by sorry


theorem plan6_exec_invariant (s : St) (sp : Nat × Nat) (op : Op)
    (hC : Consistent s)
    (hS : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    Consistent (exec comptroller s op) ∧
    (exec comptroller s op).supplyState.speed = (nextSpeeds sp op).1 ∧
    (exec comptroller s op).borrowState.speed = (nextSpeeds sp op).2 := by sorry

theorem plan6_run_potF_le (s : St) (sp : Nat × Nat) (ops : List Op)
    (hC : Consistent s)
    (hS : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    potF (run comptroller s ops) ≤ potF s + emitted sp ops := by sorry

theorem plan6_credited_mul_le_potF_aux_test (s : St) :
    s.credited * doubleScale ≤ potF s := by unfold potF; omega

theorem plan6_credited_mul_le_potF (s : St) :
    s.credited * doubleScale ≤ potF s := by unfold potF; omega

theorem upg_test_unfold (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem sum_le_sum_aux (f g : Acct → Nat) (l : List Acct)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha : f a ≤ g a := h a (by simp)
    have ht : ∀ b ∈ t, f b ≤ g b := fun b hb => h b (by simp [hb])
    have ihle := ih ht
    omega

theorem upg_idx_supply (L : Legacy) :
    (upgrade L).supplyState.index = (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upg_blk_supply (L : Legacy) :
    (upgrade L).supplyState.block = (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock) := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem upg_idx_borrow (L : Legacy) :
    (upgrade L).borrowState.index = (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := by
  unfold upgrade initSide
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upg_blk_borrow (L : Legacy) :
    (upgrade L).borrowState.block = (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock) := by
  unfold upgrade initSide
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem upg_speeds (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed ∧ (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h1 : L.supplyIndex = 0 <;> by_cases h2 : L.borrowIndex = 0 <;> simp [h1, h2]

theorem upg_accts (L : Legacy) : (upgrade L).accts = L.accts := by simp [upgrade]

theorem upg_block (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := by simp [upgrade]

theorem ds_eq_ci : doubleScale = compInitialIndex := by rfl

theorem div_bound_aux2 (n : Nat) (hpos : 0 < doubleScale) :
    n % doubleScale ≤ doubleScale - 1 := by
  have hmod : n % doubleScale < doubleScale := Nat.mod_lt n hpos
  omega

theorem legacy_start_le_accrual2 (start recorded idx : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ idx) :
    legacyStart start recorded ≤ accrualStart recorded idx := by
  unfold legacyStart accrualStart
  by_cases h0 : recorded = 0
  · simp only [h0, ↓reduceIte]
    rcases hstart with rfl | rfl
    · exact Nat.zero_le _
    · by_cases hi : compInitialIndex ≤ idx
      · simp [hi]
      · simp [hi]
        -- here start=CI ≤ idx contradicts ¬ CI ≤ idx? so CI ≤ idx must hold
        omega
  · simp [h0]

theorem div_slack3 (S : Nat) : S ≤ S / doubleScale * doubleScale + (doubleScale - 1) := by
  have hpos : 0 < doubleScale := doubleScale_pos
  have hdm : doubleScale * (S / doubleScale) + S % doubleScale = S := Nat.div_add_mod S doubleScale
  have hmod : S % doubleScale + 1 ≤ doubleScale := Nat.succ_le_of_lt (Nat.mod_lt S hpos)
  have hcomm : doubleScale * (S / doubleScale) = S / doubleScale * doubleScale := Nat.mul_comm _ _
  omega

theorem wf_supply_start_cases (L : Legacy) (hWF : L.WellFormed) :
    (L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex) ∧ L.supplyStart ≤ L.supplyIndex := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨h1, h2, _, _, _, _, _⟩ := hWF
  exact ⟨h1, h2⟩

theorem wf_borrow_start_cases (L : Legacy) (hWF : L.WellFormed) :
    (L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex) ∧ L.borrowStart ≤ L.borrowIndex := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨_, _, h3, h4, _, _, _⟩ := hWF
  exact ⟨h3, h4⟩

theorem wf_acct_le (L : Legacy) (hWF : L.WellFormed) (a : Acct) (ha : a ∈ L.accts) :
    a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨_, _, _, _, _, _, hall⟩ := hWF
  exact hall a ha

theorem plan7_term_le (idx start recorded units : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ idx)
    (hrec : recorded ≤ idx) :
    units * ((if idx = 0 then compInitialIndex else idx) -
      accrualStart recorded (if idx = 0 then compInitialIndex else idx)) ≤
      units * (idx - legacyStart start recorded) := by
  by_cases hidx : idx = 0
  · subst hidx
    have hrec0 : recorded = 0 := Nat.le_zero.mp hrec
    subst hrec0
    have e : accrualStart 0 compInitialIndex = compInitialIndex := by
      unfold accrualStart
      simp
    have hif : (if (0 : Nat) = 0 then compInitialIndex else 0) = compInitialIndex := by simp
    rw [hif, e]
    simp
  · have hif : (if idx = 0 then compInitialIndex else idx) = idx := if_neg hidx
    rw [hif]
    have hle : legacyStart start recorded ≤ accrualStart recorded idx :=
      legacy_start_le_accrual2 start recorded idx hstart hstart_le
    exact Nat.mul_le_mul (Nat.le_refl _) (Nat.sub_le_sub_left hle idx)










theorem plan7_term_le_check2 : accrualStart 0 compInitialIndex = compInitialIndex := by
  unfold accrualStart
  simp

theorem plan7_term_le_check3 (idx start recorded units : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ idx)
    (hrec : recorded ≤ idx) :
    units * ((if idx = 0 then compInitialIndex else idx) -
      accrualStart recorded (if idx = 0 then compInitialIndex else idx)) ≤
      units * (idx - legacyStart start recorded) := by
  by_cases hidx : idx = 0
  · subst hidx
    have hrec0 : recorded = 0 := Nat.le_zero.mp hrec
    subst hrec0
    simp [plan7_term_le_check2]
  · have hif : (if idx = 0 then compInitialIndex else idx) = idx := if_neg hidx
    rw [hif]
    have hle : legacyStart start recorded ≤ accrualStart recorded idx :=
      legacy_start_le_accrual2 start recorded idx hstart hstart_le
    exact Nat.mul_le_mul (Nat.le_refl _) (Nat.sub_le_sub_left hle idx)

theorem plan7_term_le_tmp (idx start recorded units : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ idx)
    (hrec : recorded ≤ idx) :
    units * ((if idx = 0 then compInitialIndex else idx) -
      accrualStart recorded (if idx = 0 then compInitialIndex else idx)) ≤
      units * (idx - legacyStart start recorded) :=
  plan7_term_le_check3 idx start recorded units hstart hstart_le hrec

theorem plan7_term_le_selfcontained (idx start recorded units : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ idx)
    (hrec : recorded ≤ idx) :
    units * ((if idx = 0 then compInitialIndex else idx) -
      accrualStart recorded (if idx = 0 then compInitialIndex else idx)) ≤
      units * (idx - legacyStart start recorded) := by
  by_cases hidx : idx = 0
  · subst hidx
    have hrec0 : recorded = 0 := Nat.le_zero.mp hrec
    subst hrec0
    have e : accrualStart 0 compInitialIndex = compInitialIndex := by
      unfold accrualStart
      simp
    have hif : (if (0 : Nat) = 0 then compInitialIndex else 0) = compInitialIndex := by simp
    rw [hif, e]
    simp
  · have hif : (if idx = 0 then compInitialIndex else idx) = idx := if_neg hidx
    rw [hif]
    have hle : legacyStart start recorded ≤ accrualStart recorded idx :=
      legacy_start_le_accrual2 start recorded idx hstart hstart_le
    exact Nat.mul_le_mul (Nat.le_refl _) (Nat.sub_le_sub_left hle idx)

theorem my_test_upg_rw (L : Legacy) (a : Acct) :
    a.supply * ((upgrade L).supplyState.index - accrualStart a.supplierIndex (upgrade L).supplyState.index) =
    a.supply * ((if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) - accrualStart a.supplierIndex (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex)) := by
  rw [upg_idx_supply]

theorem plan7_pendSum_upgrade_le_aux1 (L : Legacy) (hWF : L.WellFormed) (a : Acct) (ha : a ∈ L.accts) :
    a.supply * ((upgrade L).supplyState.index - accrualStart a.supplierIndex (upgrade L).supplyState.index) +
    a.borrow * ((upgrade L).borrowState.index - accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
    L.pendingScaled a := by
  have hsup_start := wf_supply_start_cases L hWF
  have hbor_start := wf_borrow_start_cases L hWF
  have hacct := wf_acct_le L hWF a ha
  obtain ⟨hs1, hs2⟩ := hsup_start
  obtain ⟨hb1, hb2⟩ := hbor_start
  obtain ⟨hrecS, hrecB⟩ := hacct
  have eS : (upgrade L).supplyState.index = (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := upg_idx_supply L
  have eB : (upgrade L).borrowState.index = (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := upg_idx_borrow L
  rw [eS, eB]
  unfold Legacy.pendingScaled
  have h1 := plan7_term_le_selfcontained L.supplyIndex L.supplyStart a.supplierIndex a.supply hs1 hs2 hrecS
  have h2 := plan7_term_le_selfcontained L.borrowIndex L.borrowStart a.borrowerIndex a.borrow hb1 hb2 hrecB
  omega

theorem plan7_pendSum_upgrade_le_aux2 (L : Legacy) :
    pendSum (upgrade L) = ((L.accts.map fun a => a.supply * ((upgrade L).supplyState.index - accrualStart a.supplierIndex (upgrade L).supplyState.index) + a.borrow * ((upgrade L).borrowState.index - accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum) := by
  unfold pendSum
  rw [upg_accts]

theorem plan7_pendSum_upgrade_le_proof (L : Legacy) (hWF : L.WellFormed) :
    pendSum (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
  rw [plan7_pendSum_upgrade_le_aux2 L]
  apply sum_le_sum_aux
  intro a ha
  exact plan7_pendSum_upgrade_le_aux1 L hWF a ha

theorem plan7_pendSum_selftest (L : Legacy) (hWF : L.WellFormed) :
    pendSum (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
  have hsup_start := wf_supply_start_cases L hWF
  have hbor_start := wf_borrow_start_cases L hWF
  obtain ⟨hs1, hs2⟩ := hsup_start
  obtain ⟨hb1, hb2⟩ := hbor_start
  have eS : (upgrade L).supplyState.index = (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := upg_idx_supply L
  have eB : (upgrade L).borrowState.index = (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := upg_idx_borrow L
  have eA : (upgrade L).accts = L.accts := upg_accts L
  have hfun : ∀ a ∈ L.accts,
      a.supply * ((if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) - accrualStart a.supplierIndex (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex)) +
      a.borrow * ((if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) - accrualStart a.borrowerIndex (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex)) ≤
      L.pendingScaled a := by
    intro a ha
    have hacct := wf_acct_le L hWF a ha
    obtain ⟨hrecS, hrecB⟩ := hacct
    unfold Legacy.pendingScaled
    have h1 := plan7_term_le_selfcontained L.supplyIndex L.supplyStart a.supplierIndex a.supply hs1 hs2 hrecS
    have h2 := plan7_term_le_selfcontained L.borrowIndex L.borrowStart a.borrowerIndex a.borrow hb1 hb2 hrecB
    omega
  unfold pendSum
  rw [eA, eS, eB]
  exact sum_le_sum_aux _ _ _ hfun

theorem plan7_pendSum_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    pendSum (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
  have hsup_start := wf_supply_start_cases L hWF
  have hbor_start := wf_borrow_start_cases L hWF
  obtain ⟨hs1, hs2⟩ := hsup_start
  obtain ⟨hb1, hb2⟩ := hbor_start
  have eS : (upgrade L).supplyState.index = (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := upg_idx_supply L
  have eB : (upgrade L).borrowState.index = (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := upg_idx_borrow L
  have eA : (upgrade L).accts = L.accts := upg_accts L
  have hfun : ∀ a ∈ L.accts,
      a.supply * ((if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) - accrualStart a.supplierIndex (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex)) +
      a.borrow * ((if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) - accrualStart a.borrowerIndex (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex)) ≤
      L.pendingScaled a := by
    intro a ha
    have hacct := wf_acct_le L hWF a ha
    obtain ⟨hrecS, hrecB⟩ := hacct
    unfold Legacy.pendingScaled
    have h1 := plan7_term_le_selfcontained L.supplyIndex L.supplyStart a.supplierIndex a.supply hs1 hs2 hrecS
    have h2 := plan7_term_le_selfcontained L.borrowIndex L.borrowStart a.borrowerIndex a.borrow hb1 hb2 hrecB
    omega
  unfold pendSum
  rw [eA, eS, eB]
  exact sum_le_sum_aux _ _ _ hfun

theorem plan7_unidx_upgrade_le (L : Legacy) :
    unidx (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by
  have hSblk := upg_blk_supply L
  have hBblk := upg_blk_borrow L
  have hBlk := upg_block L
  have hSp := upg_speeds L
  obtain ⟨hSpS, hSpB⟩ := hSp
  unfold unidx Legacy.unindexedSupply Legacy.unindexedBorrow
  rw [hBlk, hSblk, hBblk, hSpS, hSpB]
  by_cases hS : L.supplyIndex = 0
  · by_cases hB : L.borrowIndex = 0
    · simp only [hS, hB, ite_true, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
      omega
    · simp only [hS, hB, ite_true, ite_false, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
      omega
  · by_cases hB : L.borrowIndex = 0
    · simp only [hS, hB, ite_false, ite_true, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      omega
    · simp only [hS, hB, ite_false]
      omega

theorem plan7_owed_mul_bound_aux_check (L : Legacy) :
    ((L.accts.map L.pendingScaled).sum / doubleScale + L.unindexedSupply + L.unindexedBorrow) * doubleScale =
    (L.accts.map L.pendingScaled).sum / doubleScale * doubleScale + (L.unindexedSupply + L.unindexedBorrow) * doubleScale := by
  have e : L.unindexedSupply + L.unindexedBorrow + (L.accts.map L.pendingScaled).sum / doubleScale =
    (L.accts.map L.pendingScaled).sum / doubleScale + (L.unindexedSupply + L.unindexedBorrow) := by omega
  calc ((L.accts.map L.pendingScaled).sum / doubleScale + L.unindexedSupply + L.unindexedBorrow) * doubleScale
      = ((L.accts.map L.pendingScaled).sum / doubleScale + (L.unindexedSupply + L.unindexedBorrow)) * doubleScale := by
        congr 1; omega
    _ = (L.accts.map L.pendingScaled).sum / doubleScale * doubleScale + (L.unindexedSupply + L.unindexedBorrow) * doubleScale := by
        rw [Nat.add_mul]

theorem plan7_owed_mul_bound (L : Legacy) :
    (L.accts.map L.pendingScaled).sum +
        (L.unindexedSupply + L.unindexedBorrow) * doubleScale ≤
      L.owed * doubleScale + (doubleScale - 1) := by
  have hslack := div_slack3 ((L.accts.map L.pendingScaled).sum)
  have hdist := plan7_owed_mul_bound_aux_check L
  have hO : L.owed * doubleScale =
    (L.accts.map L.pendingScaled).sum / doubleScale * doubleScale + (L.unindexedSupply + L.unindexedBorrow) * doubleScale := by
    have e : L.owed = (L.accts.map L.pendingScaled).sum / doubleScale + L.unindexedSupply + L.unindexedBorrow := rfl
    rw [e]
    exact hdist
  omega

theorem plan7_potF_upgrade_bound_aux_try (L : Legacy) (hWF : L.WellFormed) :
    potF (upgrade L) ≤
      (upgrade L).credited * doubleScale + L.owed * doubleScale +
        (doubleScale - 1) := by
  have hP := plan7_pendSum_upgrade_le L hWF
  have hU := plan7_unidx_upgrade_le L
  have hO := plan7_owed_mul_bound L
  have hUds : unidx (upgrade L) * doubleScale ≤ (L.unindexedSupply + L.unindexedBorrow) * doubleScale :=
    Nat.mul_le_mul_right doubleScale hU
  have hPU : pendSum (upgrade L) + unidx (upgrade L) * doubleScale ≤ (L.accts.map L.pendingScaled).sum + (L.unindexedSupply + L.unindexedBorrow) * doubleScale :=
    Nat.add_le_add hP hUds
  have hTrans : pendSum (upgrade L) + unidx (upgrade L) * doubleScale ≤ L.owed * doubleScale + (doubleScale - 1) :=
    Nat.le_trans hPU hO
  have hPot : potF (upgrade L) = (upgrade L).credited * doubleScale + (pendSum (upgrade L) + unidx (upgrade L) * doubleScale) := by
    unfold potF
    omega
  omega

theorem plan7_potF_upgrade_bound (L : Legacy) (hWF : L.WellFormed) :
    potF (upgrade L) ≤
      (upgrade L).credited * doubleScale + L.owed * doubleScale +
        (doubleScale - 1) :=
  plan7_potF_upgrade_bound_aux_try L hWF

theorem plan6_upgrade_helper_test (L : Legacy) (hWF : L.WellFormed) :
    potF (upgrade L) ≤
      ((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1) := by
  have h := plan7_potF_upgrade_bound L hWF
  have e : ((upgrade L).credited + L.owed) * doubleScale =
    (upgrade L).credited * doubleScale + L.owed * doubleScale := by
    rw [Nat.add_mul]
  omega

theorem plan6_potF_upgrade_le_aux2 (L : Legacy) (hWF : L.WellFormed) :
    potF (upgrade L) ≤
      ((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1) := by
  have h := plan7_potF_upgrade_bound L hWF
  have e : ((upgrade L).credited + L.owed) * doubleScale =
    (upgrade L).credited * doubleScale + L.owed * doubleScale := by
    rw [Nat.add_mul]
  omega

theorem plan6_potF_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    potF (upgrade L) ≤
      ((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1) := by
  have h := plan7_potF_upgrade_bound L hWF
  have e : ((upgrade L).credited + L.owed) * doubleScale =
    (upgrade L).credited * doubleScale + L.owed * doubleScale := by
    rw [Nat.add_mul]
  omega

theorem my_plan6_test2 (L : Legacy) (hWF : L.WellFormed) :
    Consistent (upgrade L) ∧
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs1, hs2, hb1, hb2, hsBlk, hbBlk, hall⟩ := hWF
  have hSblk := upg_blk_supply L
  have hBblk := upg_blk_borrow L
  have hSidx := upg_idx_supply L
  have hBidx := upg_idx_borrow L
  have hAccts := upg_accts L
  have hBlk := upg_block L
  have hSp := upg_speeds L
  obtain ⟨hSpS, hSpB⟩ := hSp
  refine ⟨⟨?h1, ?h2, ?h3⟩, hSpS, hSpB⟩
  · rw [hSblk, hBlk]
    by_cases h : L.supplyIndex = 0
    · simp [h]
    · simp [h]; exact hsBlk
  · rw [hBblk, hBlk]
    by_cases h : L.borrowIndex = 0
    · simp [h]
    · simp [h]; exact hbBlk
  · intro a ha
    rw [hAccts] at ha
    have haL := hall a ha
    obtain ⟨haS, haB⟩ := haL
    rw [hSidx, hBidx]
    constructor
    · by_cases h : L.supplyIndex = 0
      · simp [h]
        rw [h] at haS
        have hz : a.supplierIndex = 0 := Nat.le_zero.mp haS
        omega
      · simp [h]; exact haS
    · by_cases h : L.borrowIndex = 0
      · simp [h]
        rw [h] at haB
        have hz : a.borrowerIndex = 0 := Nat.le_zero.mp haB
        omega
      · simp [h]; exact haB

theorem selfContained_upgrade_aux (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem selfContained_upgrade_aux2 (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem selfContained_consistent_proof (L : Legacy) (hWF : L.WellFormed) :
    Consistent (upgrade L) ∧
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs1, hs2, hb1, hb2, hsBlk, hbBlk, hall⟩ := hWF
  have hUblkS : (upgrade L).blockNumber = L.blockNumber := by simp [upgrade]
  have hSblk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
    unfold upgrade initSide
    by_cases h : L.supplyIndex = 0 <;> simp [h]
  have hBblk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
    unfold upgrade initSide
    by_cases h : L.borrowIndex = 0 <;> simp [h]
  have hSidx : (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
    unfold upgrade initSide
    by_cases h : L.supplyIndex = 0 <;> simp [h]
  have hBidx : (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
    unfold upgrade initSide
    by_cases h : L.borrowIndex = 0 <;> simp [h]
  have hAccts : (upgrade L).accts = L.accts := by simp [upgrade]
  have hSpS : (upgrade L).supplyState.speed = L.compSpeed := by unfold upgrade initSide; by_cases h : L.supplyIndex = 0 <;> simp [h]
  have hSpB : (upgrade L).borrowState.speed = L.compSpeed := by unfold upgrade initSide; by_cases h : L.borrowIndex = 0 <;> simp [h]
  refine ⟨⟨?h1, ?h2, ?h3⟩, hSpS, hSpB⟩
  · rw [hSblk, hUblkS]
    by_cases h : L.supplyIndex = 0
    · simp [h]
    · simp [h]; exact hsBlk
  · rw [hBblk, hUblkS]
    by_cases h : L.borrowIndex = 0
    · simp [h]
    · simp [h]; exact hbBlk
  · intro a ha
    rw [hAccts] at ha
    have haL := hall a ha
    obtain ⟨haS, haB⟩ := haL
    rw [hSidx, hBidx]
    constructor
    · by_cases h : L.supplyIndex = 0
      · simp [h]
        rw [h] at haS
        have hz : a.supplierIndex = 0 := Nat.le_zero.mp haS
        omega
      · simp [h]; exact haS
    · by_cases h : L.borrowIndex = 0
      · simp [h]
        rw [h] at haB
        have hz : a.borrowerIndex = 0 := Nat.le_zero.mp haB
        omega
      · simp [h]; exact haB

theorem accrualStart_self (idx : Nat) : accrualStart idx idx = idx := by
  unfold accrualStart
  by_cases h0 : idx = 0
  · subst h0
    simp only [↓reduceIte]
    have hci : ¬ compInitialIndex ≤ 0 := by unfold compInitialIndex; decide
    simp [hci]
  · simp [h0]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hCons
  obtain ⟨hsupBlk, hborBlk, hall⟩ := hCons
  have hallSup : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
    fun a ha => (hall a ha).1
  have hallBor : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
    fun a ha => (hall a ha).2
  cases c with
  | supplyHook who =>
    have hupd_some : (updateCompSupplyIndex s).isSome := aux_upd_supply_some s hsupBlk
    cases hupdE : updateCompSupplyIndex s with
    | none => simp [hupdE] at hupd_some
    | some s1 =>
      have hprops := plan0_updateSupplyIndex_props s s1 hsupBlk hupdE
      obtain ⟨hle, haccts, hblk, hborEq⟩ := hprops
      have hacct_eq : (s1.acct who) = (s.acct who) := by unfold St.acct; rw [haccts]
      have h_orig : (s.acct who).supplierIndex ≤ s.supplyState.index :=
        plan0_getD_supplier_le s.accts who s.supplyState.index hallSup
      have h_le1 : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
        rw [hacct_eq]
        have hidx : s.supplyState.index ≤ s1.supplyState.index := hle
        omega
      have hdist_some : (distributeSupplierComp s1 who).isSome :=
        aux_dist_supply_some_of_le s1 who h_le1
      have hcomp : comptroller s (.supplyHook who) = (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) := rfl
      rw [hcomp, hupdE]
      simp
      exact hdist_some
  | borrowHook who =>
    have hupd_some : (updateCompBorrowIndex s).isSome := aux_upd_borrow_some s hborBlk
    cases hupdE : updateCompBorrowIndex s with
    | none => simp [hupdE] at hupd_some
    | some s1 =>
      have hprops := plan0_updateBorrowIndex_props s s1 hborBlk hupdE
      obtain ⟨hle, haccts, hblk, hsupEq⟩ := hprops
      have hacct_eq : (s1.acct who) = (s.acct who) := by unfold St.acct; rw [haccts]
      have h_orig : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
        plan0_getD_borrower_le s.accts who s.borrowState.index hallBor
      have h_le1 : (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
        rw [hacct_eq]
        have hidx : s.borrowState.index ≤ s1.borrowState.index := hle
        omega
      have hdist_some : (distributeBorrowerComp s1 who).isSome :=
        aux_dist_borrow_some_of_le s1 who h_le1
      have hcomp : comptroller s (.borrowHook who) = (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) := rfl
      rw [hcomp, hupdE]
      simp
      exact hdist_some
  | claim who =>
    have hB_some : (updateCompBorrowIndex s).isSome := aux_upd_borrow_some s hborBlk
    cases hBE : updateCompBorrowIndex s with
    | none => simp [hBE] at hB_some
    | some sB =>
      have hBprops := plan0_updateBorrowIndex_props s sB hborBlk hBE
      obtain ⟨hBle, hBaccts, hBblk, hBsupEq⟩ := hBprops
      have hBacct_eq : (sB.acct who) = (s.acct who) := by unfold St.acct; rw [hBaccts]
      have h_origB : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
        plan0_getD_borrower_le s.accts who s.borrowState.index hallBor
      have h_leB : (sB.acct who).borrowerIndex ≤ sB.borrowState.index := by
        rw [hBacct_eq]; omega
      have hDB_some : (distributeBorrowerComp sB who).isSome :=
        aux_dist_borrow_some_of_le sB who h_leB
      cases hDBE : distributeBorrowerComp sB who with
      | none => simp [hDBE] at hDB_some
      | some sB2 =>
        have hDBpres := plan0_distributeBorrowerComp_preserves sB who sB2 hDBE
        obtain ⟨hDBsup, hDBblk, hDBsupIdx⟩ := hDBpres
        have hsupBlk2 : (sB2.supplyState).block ≤ sB2.blockNumber := by
          rw [hDBsup, hDBblk, hBsupEq, hBblk]; exact hsupBlk
        have hS_some : (updateCompSupplyIndex sB2).isSome := aux_upd_supply_some sB2 hsupBlk2
        cases hSE : updateCompSupplyIndex sB2 with
        | none => simp [hSE] at hS_some
        | some sS =>
          have hSprops := plan0_updateSupplyIndex_props sB2 sS hsupBlk2 hSE
          obtain ⟨hSle, hSaccts, hSblk, hSborEq⟩ := hSprops
          have hSacct_eq : (sS.acct who) = (sB2.acct who) := by unfold St.acct; rw [hSaccts]
          have h_origS : (s.acct who).supplierIndex ≤ s.supplyState.index :=
            plan0_getD_supplier_le s.accts who s.supplyState.index hallSup
          have hsupIdx_eq : (sB2.acct who).supplierIndex = (s.acct who).supplierIndex := by
            have e1 : (sB.acct who) = (s.acct who) := hBacct_eq
            rw [← e1]
            exact hDBsupIdx
          have hsupState_eq : sB2.supplyState.index = s.supplyState.index := by
            rw [hDBsup, hBsupEq]
          have h_leS : (sS.acct who).supplierIndex ≤ sS.supplyState.index := by
            rw [hSacct_eq, hsupIdx_eq]
            have h1 : s.supplyState.index ≤ sS.supplyState.index := by
              rw [← hsupState_eq]
              exact hSle
            omega
          have hDS_some : (distributeSupplierComp sS who).isSome :=
            aux_dist_supply_some_of_le sS who h_leS
          cases hDSE : distributeSupplierComp sS who with
          | none => simp [hDSE] at hDS_some
          | some sS2 =>
            have hcomp : comptroller s (.claim who) = claimComp s who := rfl
            rw [hcomp]
            unfold claimComp
            simp [hBE, hDBE, hSE, hDSE]
  | setSpeeds sup bor =>
    have hcomp : comptroller s (.setSpeeds sup bor) = (setSupplySpeed s sup).bind (fun t => setBorrowSpeed t bor) := rfl
    by_cases hsEq : s.supplyState.speed = sup
    · have hsetS : setSupplySpeed s sup = some s := by unfold setSupplySpeed; simp [hsEq]
      rw [hcomp, hsetS]
      simp only [Option.bind_some]
      have hB_some : (setBorrowSpeed s bor).isSome := by
        unfold setBorrowSpeed
        by_cases hb : s.borrowState.speed = bor
        · simp [hb]
        · simp [hb]
          exact aux_upd_borrow_some s hborBlk
      exact hB_some
    · have hupd_some : (updateCompSupplyIndex s).isSome := aux_upd_supply_some s hsupBlk
      cases hupdE : updateCompSupplyIndex s with
      | none => simp [hupdE] at hupd_some
      | some sU =>
        have hUprops := plan0_updateSupplyIndex_props s sU hsupBlk hupdE
        obtain ⟨hUle, hUaccts, hUblk, hUborEq⟩ := hUprops
        have hsetS : setSupplySpeed s sup = some { sU with supplyState := { sU.supplyState with speed := sup } } := by
          unfold setSupplySpeed
          simp [hsEq, hupdE]
        rw [hcomp, hsetS]
        simp only [Option.bind_some]
        let sI : St := { sU with supplyState := { sU.supplyState with speed := sup } }
        have hIbor : sI.borrowState = s.borrowState := by simp [sI, hUborEq]
        have hIblk : sI.blockNumber = s.blockNumber := by simp [sI, hUblk]
        have hborBlkI : (sI.borrowState).block ≤ sI.blockNumber := by rw [hIbor, hIblk]; exact hborBlk
        have hB_some : (setBorrowSpeed sI bor).isSome := by
          unfold setBorrowSpeed
          by_cases hb : (sI.borrowState).speed = bor
          · simp [hb]
          · simp [hb]
            exact aux_upd_borrow_some sI hborBlkI
        exact hB_some

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hU : updateCompSupplyIndex s with
  | none => simp [hU] at h
  | some s1 =>
    simp [hU] at h
    exact tmp_supply_proofB s who s' s1 hU h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hU : updateCompBorrowIndex s with
  | none => simp [hU] at h
  | some s1 =>
    simp [hU] at h
    exact aux_borrowProofB s who s' s1 hU h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  have h2 : claimComp s who = some s' := h
  exact plan3_claimed_of_claimComp_aux_proof s who s' h2

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact plan4_setCompSpeedInternal_speedsSet s a b s' h

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry

theorem req_account_bounded     : AccountBounded comptroller := sorry

theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
