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
  let supplierIndex := accrualStart (s.acct supplier).supplierIndex supplyIndex
  match subChecked supplyIndex supplierIndex with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex supplyIndex) supplyIndex })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex := accrualStart (s.acct borrower).borrowerIndex borrowIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some _ =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := borrowIndex,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex borrowIndex) borrowIndex })

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

theorem subChecked_eq (a b : Nat) : subChecked a b =
    if b ≤ a then some (a - b) else none := rfl

theorem fraction_eq (a b : Nat) : fraction a b = a * doubleScale / b := rfl

theorem mulDouble_eq (a m : Nat) : mulDouble a m = a * m / doubleScale := rfl

theorem accrualStart_eq (r idx : Nat) :
    accrualStart r idx = if r = 0 then (if compInitialIndex ≤ idx then compInitialIndex else 0) else r := rfl

theorem creditFor_eq (u st idx : Nat) : creditFor u st idx = u * (idx - st) / doubleScale := rfl

theorem grant_some (s : St) (who : Account) : grantCompInternal s who = grant s who := rfl

theorem updateSupply_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have e1 : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompSupplyIndex accrueSide fraction
  rw [e1]
  simp only
  by_cases h1 : 0 < s.blockNumber - s.supplyState.block
  · by_cases h2 : 0 < s.supplyState.speed
    · by_cases h3 : 0 < totalSupply s
      · simp [gt_iff_lt, h1, h2, h3]
      · simp [gt_iff_lt, h1, h2, h3]
    · simp [gt_iff_lt, h1, h2]
  · have heq : s.supplyState.block = s.blockNumber := by omega
    simp [gt_iff_lt, h1, heq]
    cases s with | mk bn sup bor res ac =>
      cases sup with | mk ix bl sp =>
        simp at heq ⊢
        omega

theorem updateBorrow_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have e1 : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompBorrowIndex accrueSide fraction
  rw [e1]
  simp only
  by_cases h1 : 0 < s.blockNumber - s.borrowState.block
  · by_cases h2 : 0 < s.borrowState.speed
    · by_cases h3 : 0 < totalBorrows s
      · simp [gt_iff_lt, h1, h2, h3]
      · simp [gt_iff_lt, h1, h2, h3]
    · simp [gt_iff_lt, h1, h2]
  · have heq : s.borrowState.block = s.blockNumber := by omega
    simp [gt_iff_lt, h1, heq]
    cases s with | mk bn sup bor res ac =>
      cases bor with | mk ix bl sp =>
        simp at heq ⊢
        omega

theorem distSupply_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some
      (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold distributeSupplierComp subChecked
  simp [h]

theorem distBorrow_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some
      (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold distributeBorrowerComp subChecked
  simp [h]

theorem updateSupply_block (s : St) (m : St) (h : updateCompSupplyIndex s = some m) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · simp [hb] at h

theorem updateBorrow_block (s : St) (m : St) (h : updateCompBorrowIndex s = some m) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · exact hb
  · simp [hb] at h

theorem distSupply_start (s : St) (who : Account) (m : St)
    (h : distributeSupplierComp s who = some m) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  unfold distributeSupplierComp subChecked at h
  by_cases hb : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · exact hb
  · simp [hb] at h

theorem distBorrow_start (s : St) (who : Account) (m : St)
    (h : distributeBorrowerComp s who = some m) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  unfold distributeBorrowerComp subChecked at h
  by_cases hb : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · exact hb
  · simp [hb] at h

theorem getD_fallback (l : List Acct) (n : Nat) (h : ¬ n < l.length) :
    l.getD n noAcct = noAcct := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ m =>
      simp at h ⊢
      exact ih m (by omega)

theorem getD_mem (l : List Acct) (n : Nat) (h : n < l.length) :
    l.getD n noAcct ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp
      exact Or.inr (ih m (by simp at h ⊢; omega))

theorem accrue_mono (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hc, Nat.le_add_right]
  · simp [hc]

theorem start_le (r idx : Nat) (h : r ≤ idx) : accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
    by_cases hc : compInitialIndex ≤ idx
    · simp [hc]
    · simp [hc]
  · simp [hr]
    exact h

theorem supplyRec_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  by_cases hm : who < s.accts.length
  · have mem := getD_mem s.accts who hm
    have h2 := hc.2.2
    have h3 := h2 _ mem
    exact h3.1
  · have e := getD_fallback s.accts who (by omega)
    simp only [St.acct, e]
    exact Nat.zero_le _

theorem borrowRec_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  by_cases hm : who < s.accts.length
  · have mem := getD_mem s.accts who hm
    have h2 := hc.2.2
    have h3 := h2 _ mem
    exact h3.2
  · have e := getD_fallback s.accts who (by omega)
    simp only [St.acct, e]
    exact Nat.zero_le _

theorem borPresSup (l : List Acct) (who : Account) (bIdx : Nat) (F : Acct → Nat) :
    ((l.modify who fun a => ({ a with borrowerIndex := bIdx, accrued := a.accrued + F a } : Acct)).getD who noAcct).supplierIndex =
    (l.getD who noAcct).supplierIndex := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ m => rfl
  | cons x xs ih =>
    cases who with
    | zero => rfl
    | succ m => exact ih m

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hu : updateCompSupplyIndex s with
  | none => simp [hu] at h
  | some m =>
    simp [hu] at h
    have hb := updateSupply_block s m hu
    have eU := updateSupply_some s hb
    rw [hu] at eU
    have hm : m = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      simp at eU
      exact eU
    have hs := distSupply_start m who s' h
    have eD := distSupply_some m who hs
    rw [h] at eD
    have eDs : s' = (m.withAcct who fun a =>
        { a with supplierIndex := m.supplyState.index,
                 accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex m.supplyState.index) m.supplyState.index }) := by
      simp at eD
      exact eD
    rw [hm] at hs eDs
    unfold St.acct at hs
    simp at hs
    exact ⟨hb, hs, eDs⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hu : updateCompBorrowIndex s with
  | none => simp [hu] at h
  | some m =>
    simp [hu] at h
    have hb := updateBorrow_block s m hu
    have eU := updateBorrow_some s hb
    rw [hu] at eU
    have hm : m = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      simp at eU
      exact eU
    have hs := distBorrow_start m who s' h
    have eD := distBorrow_some m who hs
    rw [h] at eD
    have eDs : s' = (m.withAcct who fun a =>
        { a with borrowerIndex := m.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex m.borrowState.index) m.borrowState.index }) := by
      simp at eD
      exact eD
    rw [hm] at hs eDs
    unfold St.acct at hs
    simp at hs
    exact ⟨hb, hs, eDs⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp grantCompInternal at h
  simp only at h
  cases hb1 : updateCompBorrowIndex s with
  | none => simp [hb1] at h
  | some t1 =>
    simp [hb1] at h
    cases hd1 : distributeBorrowerComp t1 who with
    | none => simp [hd1] at h
    | some m1 =>
      simp [hd1] at h
      cases hs1 : updateCompSupplyIndex m1 with
      | none => simp [hs1] at h
      | some t2 =>
        simp [hs1] at h
        cases hd2 : distributeSupplierComp t2 who with
        | none => simp [hd2] at h
        | some m2 =>
          simp [hd2] at h
          have hbB := updateBorrow_block s t1 hb1
          have eUB := updateBorrow_some s hbB
          rw [hb1] at eUB
          have hm1t : t1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
            simp at eUB
            exact eUB
          have hsB := distBorrow_start t1 who m1 hd1
          have eDB := distBorrow_some t1 who hsB
          rw [hd1] at eDB
          have eM1 : m1 = (t1.withAcct who fun a =>
              { a with borrowerIndex := t1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }) := by
            simp at eDB
            exact eDB
          rw [hm1t] at hsB eM1
          unfold St.acct at hsB
          simp at hsB
          have hEq1 : BorrowDistributed s who m1 := ⟨hbB, hsB, eM1⟩
          have hbS := updateSupply_block m1 t2 hs1
          have eUS := updateSupply_some m1 hbS
          rw [hs1] at eUS
          have hm2t : t2 = { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } := by
            simp at eUS
            exact eUS
          have hsS := distSupply_start t2 who m2 hd2
          have eDS := distSupply_some t2 who hsS
          rw [hd2] at eDS
          have eM2 : m2 = (t2.withAcct who fun a =>
              { a with supplierIndex := t2.supplyState.index,
                       accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex t2.supplyState.index) t2.supplyState.index }) := by
            simp at eDS
            exact eDS
          rw [hm2t] at hsS eM2
          unfold St.acct at hsS
          simp at hsS
          have hEq2 : SupplyDistributed m1 who m2 := ⟨hbS, hsS, eM2⟩
          exact ⟨m1, m2, hEq1, hEq2, h.symm⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed at h
  simp only at h
  by_cases he1 : s.supplyState.speed ≠ a
  · simp [he1] at h
    cases hu1 : updateCompSupplyIndex s with
    | none => simp [hu1] at h
    | some t1 =>
      simp [hu1] at h
      have hb1 := updateSupply_block s t1 hu1
      have eU1 := updateSupply_some s hb1
      rw [hu1] at eU1
      have hm1 : t1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
        simp at eU1
        exact eU1
      have eBor : t1.borrowState.speed = s.borrowState.speed := by rw [hm1]
      by_cases he2t : t1.borrowState.speed = b
      · simp [he2t] at h
        have he2 : s.borrowState.speed = b := by omega
        unfold SpeedsSet
        refine ⟨?_, ?_, ?_⟩
        · intro _
          exact hb1
        · intro hc
          omega
        · simp [he1, he2, hm1] at h ⊢
          exact h.symm
      · simp [he2t] at h
        have he2 : s.borrowState.speed ≠ b := by omega
        cases hu2 : updateCompBorrowIndex ({ t1 with supplyState := { t1.supplyState with speed := a } }) with
        | none => simp [hu2] at h
        | some t2 =>
          simp [hu2] at h
          have hb2 := updateBorrow_block _ t2 hu2
          have eU2 := updateBorrow_some _ hb2
          rw [hu2] at eU2
          have hm2 : t2 = { ({ t1 with supplyState := { t1.supplyState with speed := a } } : St) with borrowState := accrueSide ({ t1 with supplyState := { t1.supplyState with speed := a } } : St).borrowState ({ t1 with supplyState := { t1.supplyState with speed := a } } : St).blockNumber (totalBorrows ({ t1 with supplyState := { t1.supplyState with speed := a } } : St)) } := by
            simp at eU2
            exact eU2
          have e1 : (({ t1 with supplyState := { t1.supplyState with speed := a } } : St).borrowState.block) = s.borrowState.block := by
            rw [hm1]
          have e2 : (({ t1 with supplyState := { t1.supplyState with speed := a } } : St).blockNumber) = s.blockNumber := by
            rw [hm1]
          have e3 : totalBorrows ({ t1 with supplyState := { t1.supplyState with speed := a } } : St) = totalBorrows s := by
            rw [hm1]
            rfl
          have hb2s : s.borrowState.block ≤ s.blockNumber := by omega
          unfold SpeedsSet
          refine ⟨?_, ?_, ?_⟩
          · intro _
            exact hb1
          · intro _
            exact hb2s
          · simp [he1, he2] at ⊢
            simp [hm1, e1, e2, e3] at hm2 h ⊢
            simp [hm2] at h ⊢
            exact h.symm
  · simp [he1] at h
    have he1e : s.supplyState.speed = a := by omega
    by_cases he2 : s.borrowState.speed ≠ b
    · simp [he2] at h
      cases hu2 : updateCompBorrowIndex s with
      | none => simp [hu2] at h
      | some t2 =>
        simp [hu2] at h
        have hb2 := updateBorrow_block s t2 hu2
        have eU2 := updateBorrow_some s hb2
        rw [hu2] at eU2
        have hm2 : t2 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
          simp at eU2
          exact eU2
        unfold SpeedsSet
        refine ⟨?_, ?_, ?_⟩
        · intro hc
          omega
        · intro _
          exact hb2
        · simp [he1e, he2, hm2] at h ⊢
          exact h.symm
    · have he2e : s.borrowState.speed = b := by omega
      simp [he2e, he1e, he2e] at h ⊢
      unfold SpeedsSet
      simp [he1e, he2e]
      exact h.symm

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have hb : s.supplyState.block ≤ s.blockNumber := hc.1
    have eU := updateSupply_some s hb
    have hm_old : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_mono s.supplyState s.blockNumber (totalSupply s)
    have hrec := supplyRec_le s who hc
    have hle : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by omega
    have hs : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      start_le _ _ hle
    have eD := distSupply_some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) who hs
    unfold comptroller
    simp [eU, eD]
  | borrowHook who =>
    have hb : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have eU := updateBorrow_some s hb
    have hm_old : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_mono s.borrowState s.blockNumber (totalBorrows s)
    have hrec := borrowRec_le s who hc
    have hle : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by omega
    have hs : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      start_le _ _ hle
    have eD := distBorrow_some ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who hs
    unfold comptroller
    simp [eU, eD]
  | claim who =>
    have hbB : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have eUB := updateBorrow_some s hbB
    have hrecB := borrowRec_le s who hc
    have hmB_old : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_mono s.borrowState s.blockNumber (totalBorrows s)
    have hleB : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by omega
    have hsB : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      start_le _ _ hleB
    have eDB := distBorrow_some ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who hsB
    have m1def : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).supplyState.block = s.supplyState.block := rfl
    have m1blk : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).blockNumber = s.blockNumber := rfl
    have m1supIdx : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).supplyState.index = s.supplyState.index := rfl
    have hrecS := supplyRec_le s who hc
    have m1recS : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).acct who).supplierIndex ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).supplyState.index := by
      have eSup : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).acct who).supplierIndex = (s.acct who).supplierIndex := by
        unfold St.acct St.withAcct
        exact borPresSup s.accts who (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index (fun a => creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      rw [eSup, m1supIdx]
      exact hrecS
    have hbS : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).supplyState.block) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index), accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) } : Acct)).blockNumber) := by
      rw [m1def, m1blk]
      exact hc.1
    have eUS := updateSupply_some _ hbS
    sorry
  | setSpeeds a b =>
    have hb1 : s.supplyState.block ≤ s.blockNumber := hc.1
    have hb2 : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have eU1 := updateSupply_some s hb1
    have eU2 := updateBorrow_some s hb2
    unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed
    by_cases he1 : s.supplyState.speed ≠ a
    · simp [he1, eU1]
      by_cases he2 : s.borrowState.speed ≠ b
      · simp [he2, eU2]
      · simp [he2]
    · simp [he1]
      by_cases he2 : s.borrowState.speed ≠ b
      · simp [he2, eU2]
      · simp [he2]
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
