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

/-- `updateCompSupplyIndex(cToken)`: bring the supply index up to date. -/
def updateCompSupplyIndex (s : St) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
  else none

/-- `updateCompBorrowIndex(cToken, marketBorrowIndex)`: bring the borrow index up to date. -/
def updateCompBorrowIndex (s : St) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
  else none

/-- `distributeSupplierComp(cToken, supplier)`: credit supply rewards from the correct start. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  let supplyIndex := s.supplyState.index
  let supplierIndex := accrualStart (s.acct supplier).supplierIndex supplyIndex
  match subChecked supplyIndex supplierIndex with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex supplyIndex) supplyIndex })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`: credit borrow rewards. -/
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
def grantCompInternal (s : St) (user : Account) : St :=
  if 0 < (s.acct user).accrued ∧ (s.acct user).accrued ≤ s.reserve then
    { s with reserve := s.reserve - (s.acct user).accrued,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
  else s

/-- `claimComp([holder], [market], true, true)`. -/
def claimComp (s : St) (holder : Account) : Option St :=
  match updateCompBorrowIndex s with
  | none => none
  | some s1 => match distributeBorrowerComp s1 holder with
    | none => none
    | some s2 => match updateCompSupplyIndex s2 with
      | none => none
      | some s3 => match distributeSupplierComp s3 holder with
        | none => none
        | some s4 => some (grantCompInternal s4 holder)

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
  match setSupplySpeed s supplySpeed with
  | none => none
  | some s1 => setBorrowSpeed s1 borrowSpeed

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => match updateCompSupplyIndex s with
    | none => none
    | some m => distributeSupplierComp m who
  | .borrowHook who => match updateCompBorrowIndex s with
    | none => none
    | some m => distributeBorrowerComp m who
  | .claim who => claimComp s who
  | .setSpeeds a b => setCompSpeedInternal s a b

theorem sub_some_of_le {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]
theorem sub_none_of_lt {a b : Nat} (h : a < b) : subChecked a b = none := by
  unfold subChecked
  simp [Nat.not_le.mpr h]
theorem accrue_block (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]
theorem accrue_index_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, Nat.le_add_right]
  · simp [h]
theorem accrue_speed (sd : Side) (now total : Nat) : (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]
theorem sub_le_of_some {a b c : Nat} (h : subChecked a b = some c) : b ≤ a := by
  unfold subChecked at h
  by_cases hle : b ≤ a
  · exact hle
  · simp [hle] at h
theorem updSupply_some (s m : St) (h : updateCompSupplyIndex s = some m) :
    s.supplyState.block ≤ s.blockNumber ∧
    m = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · simp [hle] at h
    exact ⟨hle, h.symm⟩
  · simp [hle] at h
theorem updBorrow_some (s m : St) (h : updateCompBorrowIndex s = some m) :
    s.borrowState.block ≤ s.blockNumber ∧
    m = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp [hle] at h
    exact ⟨hle, h.symm⟩
  · simp [hle] at h
theorem distSupply_some (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } := by
  unfold distributeSupplierComp at h
  simp only at h
  cases hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none => simp [hsub] at h
  | some _ =>
    simp [hsub] at h
    exact ⟨sub_le_of_some hsub, h.symm⟩
theorem distBorrow_some (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } := by
  unfold distributeBorrowerComp at h
  simp only at h
  cases hsub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none => simp [hsub] at h
  | some _ =>
    simp [hsub] at h
    exact ⟨sub_le_of_some hsub, h.symm⟩
theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := rfl
theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  show SupplyDistributed s who s'
  have hcomp : comptroller s (.supplyHook who) =
      match updateCompSupplyIndex s with
      | none => none
      | some m => distributeSupplierComp m who := rfl
  rw [hcomp] at h
  cases hm : updateCompSupplyIndex s with
  | none => simp [hm] at h
  | some m =>
    simp [hm] at h
    obtain ⟨hblk, rfl⟩ := updSupply_some s m hm
    obtain ⟨hidx, rfl⟩ := distSupply_some _ who s' h
    simp only [St.acct, St.withAcct] at hidx ⊢
    have hacct : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts.getD who noAcct) =
        s.accts.getD who noAcct := rfl
    simp [hacct] at hidx
    refine ⟨hblk, hidx, rfl⟩
theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  show BorrowDistributed s who s'
  have hcomp : comptroller s (.borrowHook who) =
      match updateCompBorrowIndex s with
      | none => none
      | some m => distributeBorrowerComp m who := rfl
  rw [hcomp] at h
  cases hm : updateCompBorrowIndex s with
  | none => simp [hm] at h
  | some m =>
    simp [hm] at h
    obtain ⟨hblk, rfl⟩ := updBorrow_some s m hm
    obtain ⟨hidx, rfl⟩ := distBorrow_some _ who s' h
    simp only [St.acct, St.withAcct] at hidx ⊢
    have hacct : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).accts.getD who noAcct) =
        s.accts.getD who noAcct := rfl
    simp [hacct] at hidx
    refine ⟨hblk, hidx, rfl⟩
theorem claimComp_some (s : St) (who : Account) (s' : St)
    (h : claimComp s who = some s') :
    ∃ m1 m2, BorrowDistributed s who m1 ∧ SupplyDistributed m1 who m2 ∧ s' = grant m2 who := by
  unfold claimComp at h
  cases h1 : updateCompBorrowIndex s with
  | none => simp [h1] at h
  | some s1 =>
    simp [h1] at h
    cases h2 : distributeBorrowerComp s1 who with
    | none => simp [h2] at h
    | some s2 =>
      simp [h2] at h
      cases h3 : updateCompSupplyIndex s2 with
      | none => simp [h3] at h
      | some s3 =>
        simp [h3] at h
        cases h4 : distributeSupplierComp s3 who with
        | none => simp [h4] at h
        | some s4 =>
          simp [h4] at h
          obtain ⟨hb1, hseq1⟩ := updBorrow_some s s1 h1
          obtain ⟨hb2, hseq2⟩ := distBorrow_some s1 who s2 h2
          obtain ⟨hs1, hseq3⟩ := updSupply_some s2 s3 h3
          obtain ⟨hs2, hseq4⟩ := distSupply_some s3 who s4 h4
          have e1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := hseq1
          have e2 : s2 = s1.withAcct who fun a =>
              { a with borrowerIndex := s1.borrowState.index,
                        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } := hseq2
          have e3 : s3 = { s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } := hseq3
          have e4 : s4 = s3.withAcct who fun a =>
              { a with supplierIndex := s3.supplyState.index,
                        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s3.supplyState.index) s3.supplyState.index } := hseq4
          have hacct1 : s1.acct who = s.acct who := by simp [e1, St.acct]
          have hacct2 : s3.acct who = s2.acct who := by simp [e3, St.acct]
          have idx1 : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [e1]
          have idx3 : s3.supplyState.index = (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index := by simp [e3]
          have hb2' : accrualStart (s.acct who).borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
            simp [hacct1, idx1] at hb2
            exact hb2
          have hs2' : accrualStart (s2.acct who).supplierIndex
              (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index ≤
              (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index := by
            simp [hacct2, idx3] at hs2
            exact hs2
          have eb : BorrowDistributed s who s2 := by
            refine ⟨hb1, hb2', ?_⟩
            simp [e1, e2, St.withAcct]
          have es : SupplyDistributed s2 who s4 := by
            refine ⟨hs1, hs2', ?_⟩
            simp [e3, e4, St.withAcct]
          have hg : s' = grant s4 who := by
            simp [grant_eq] at h
            exact h.symm
          exact ⟨s2, s4, eb, es, hg⟩
theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  have hcomp : comptroller s (.claim who) = claimComp s who := rfl
  rw [hcomp] at h
  obtain ⟨m1, m2, hb, hs, hg⟩ := claimComp_some s who s' h
  exact ⟨m1, m2, hb, hs, hg⟩
theorem setSupply_some (s : St) (a : Nat) (s' : St)
    (h : setSupplySpeed s a = some s') :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s' = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    refine ⟨fun hne => False.elim (hne heq), ?_⟩
    simp [heq]
    exact h.symm ▸ rfl
  · simp [heq] at h
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some m =>
      simp [hu] at h
      obtain ⟨hblk, hseq⟩ := updSupply_some s m hu
      refine ⟨fun _ => hblk, ?_⟩
      have hm : m.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by simp [hseq]
      simp [heq]
      rw [←h]
      simp [hseq, hm]
theorem setBorrow_some (s : St) (b : Nat) (s' : St)
    (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s' = { s with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    refine ⟨fun hne => False.elim (hne heq), ?_⟩
    simp [heq]
    exact h.symm ▸ rfl
  · simp [heq] at h
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some m =>
      simp [hu] at h
      obtain ⟨hblk, hseq⟩ := updBorrow_some s m hu
      refine ⟨fun _ => hblk, ?_⟩
      have hm : m.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by simp [hseq]
      simp [heq]
      rw [←h]
      simp [hseq, hm]
theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  have hcomp : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl
  rw [hcomp] at h
  unfold setCompSpeedInternal at h
  cases h1 : setSupplySpeed s a with
  | none => simp [h1] at h
  | some m =>
    simp [h1] at h
    obtain ⟨hsblk, hseq⟩ := setSupply_some s a m h1
    obtain ⟨hbblk, hbeq⟩ := setBorrow_some m b s' h
    have hmblk : m.blockNumber = s.blockNumber := by simp [hseq]
    have hmaccts : m.accts = s.accts := by simp [hseq]
    have hmbor : m.borrowState = s.borrowState := by simp [hseq]
    have hmtot : totalBorrows m = totalBorrows s := by simp [hmaccts, totalBorrows]
    refine ⟨hsblk, ?_, ?_⟩
    · intro hne
      have hne2 : m.borrowState.speed ≠ b := by simp [hmbor, hne]
      have hb := hbblk hne2
      simp [hmbor, hmblk, hmtot] at hb
      exact hb
    · have hbeq2 := hbeq
      rw [hmbor, hmblk, hmtot] at hbeq2
      simp [hseq] at hbeq2 ⊢
      exact hbeq2
theorem acct_sup_le (l : List Acct) (who idx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ idx) : (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    show noAcct.supplierIndex ≤ idx
    unfold noAcct
    exact Nat.zero_le _
  | cons x xs ih =>
    cases who with
    | zero =>
      simp [List.getD]
      exact hall x (by simp)
    | succ n =>
      simp [List.getD]
      apply ih
      intro a ha
      exact hall a (List.mem_cons_of_mem x ha)
theorem acct_bor_le (l : List Acct) (who idx : Nat)
    (hall : ∀ a ∈ l, a.borrowerIndex ≤ idx) : (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    show noAcct.borrowerIndex ≤ idx
    unfold noAcct
    exact Nat.zero_le _
  | cons x xs ih =>
    cases who with
    | zero =>
      simp [List.getD]
      exact hall x (by simp)
    | succ n =>
      simp [List.getD]
      apply ih
      intro a ha
      exact hall a (List.mem_cons_of_mem x ha)
theorem accrualStart_le_new (rec oldIdx newIdx : Nat)
    (hrec : rec ≤ oldIdx) (hold : oldIdx ≤ newIdx) :
    accrualStart rec newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases h0 : rec = 0
  · simp [h0]
    by_cases hc : compInitialIndex ≤ newIdx
    · simp [hc]
    · simp [hc]
  · simp [h0]
    calc rec ≤ oldIdx := hrec
      _ ≤ newIdx := hold
theorem updSupply_isSome (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  unfold updateCompSupplyIndex
  simp [h]
theorem updBorrow_isSome (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  unfold updateCompBorrowIndex
  simp [h]
theorem distSupply_isSome (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome = true := by
  unfold distributeSupplierComp
  simp only
  have hsub : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    sub_some_of_le h
  simp [hsub]
theorem distBorrow_isSome (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome = true := by
  unfold distributeBorrowerComp
  simp only
  have hsub : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    sub_some_of_le h
  simp [hsub]
theorem modify_sup_preserve (l : List Acct) (who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify who f).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex := by
  induction l generalizing who with
  | nil =>
    simp [List.modify, List.getD]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp [List.modify, List.getD, hf]
    | succ n =>
      simp [List.modify, List.getD]
      exact ih n
theorem modify_bor_preserve (l : List Acct) (who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((l.modify who f).getD who noAcct).borrowerIndex = (l.getD who noAcct).borrowerIndex := by
  induction l generalizing who with
  | nil =>
    simp [List.modify, List.getD]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp [List.modify, List.getD, hf]
    | succ n =>
      simp [List.modify, List.getD]
      exact ih n
theorem updSupply_eq_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex
  simp [h]
theorem updBorrow_eq_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex
  simp [h]
theorem distSupply_eq_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold distributeSupplierComp
  simp only
  simp [sub_some_of_le h]
theorem distBorrow_eq_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold distributeBorrowerComp
  simp only
  simp [sub_some_of_le h]
theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsblk, hbblk, hall⟩ := hc
  have hsup_le : ∀ who : Account, (s.acct who).supplierIndex ≤ s.supplyState.index := by
    intro who
    unfold St.acct
    exact acct_sup_le s.accts who s.supplyState.index (fun a ha => (hall a ha).1)
  have hbor_le : ∀ who : Account, (s.acct who).borrowerIndex ≤ s.borrowState.index := by
    intro who
    unfold St.acct
    exact acct_bor_le s.accts who s.borrowState.index (fun a ha => (hall a ha).2)
  cases c with
  | supplyHook who =>
    have hcomp : comptroller s (.supplyHook who) =
        match updateCompSupplyIndex s with
        | none => none
        | some m => distributeSupplierComp m who := rfl
    rw [hcomp]
    have hm := updSupply_eq_some s hsblk
    rw [hm]
    have hrec : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      simp [St.acct]
      exact Nat.le_trans (hsup_le who) (accrue_index_ge s.supplyState s.blockNumber (totalSupply s))
    have hidx : accrualStart ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex)
        (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) ≤
        (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) := by
      simp only
      exact accrualStart_le_new _ _ _ hrec (Nat.le_refl _)
    have hd := distSupply_eq_some _ who hidx
    simp [hd]
  | borrowHook who =>
    have hcomp : comptroller s (.borrowHook who) =
        match updateCompBorrowIndex s with
        | none => none
        | some m => distributeBorrowerComp m who := rfl
    rw [hcomp]
    have hm := updBorrow_eq_some s hbblk
    rw [hm]
    have hrec : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      simp [St.acct]
      exact Nat.le_trans (hbor_le who) (accrue_index_ge s.borrowState s.blockNumber (totalBorrows s))
    have hidx : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex)
        ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤
        ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) := by
      simp only
      exact accrualStart_le_new _ _ _ hrec (Nat.le_refl _)
    have hd := distBorrow_eq_some _ who hidx
    simp [hd]
  | claim who =>
    have hcomp : comptroller s (.claim who) = claimComp s who := rfl
    rw [hcomp]
    unfold claimComp
    let m1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hm1 : updateCompBorrowIndex s = some m1 := updBorrow_eq_some s hbblk
    simp [hm1]
    have hrec1 : (m1.acct who).borrowerIndex ≤ m1.borrowState.index := by
      simp only [m1, St.acct]
      exact Nat.le_trans (hbor_le who) (accrue_index_ge s.borrowState s.blockNumber (totalBorrows s))
    have hidx1 : accrualStart (m1.acct who).borrowerIndex m1.borrowState.index ≤ m1.borrowState.index :=
      accrualStart_le_new _ _ _ hrec1 (Nat.le_refl _)
    let s2 : St := m1.withAcct who fun a =>
      { a with borrowerIndex := m1.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex m1.borrowState.index) m1.borrowState.index }
    have hd1 : distributeBorrowerComp m1 who = some s2 := distBorrow_eq_some m1 who hidx1
    simp [hd1]
    have hm2 : updateCompSupplyIndex s2 = some { s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } :=
      updSupply_eq_some s2 (by simpa [s2, m1, St.withAcct] using hsblk)
    simp [hm2]
    have hsup2 : (s2.acct who).supplierIndex ≤ s2.supplyState.index := by
      have h1 : (s.acct who).supplierIndex ≤ s.supplyState.index := hsup_le who
      have h2 : (s2.acct who).supplierIndex = (m1.acct who).supplierIndex := by
        simp only [s2, St.withAcct, St.acct]
        exact modify_sup_preserve m1.accts who _ (fun a => rfl)
      have h3 : m1.acct who = s.acct who := by simp only [m1, St.acct]
      have h4 : s2.supplyState.index = s.supplyState.index := by simp [s2, m1, St.withAcct]
      simp only [h2, h3, h4] at h1 ⊢
      exact h1
    have hrec2 : (({ s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } : St).acct who).supplierIndex ≤
        (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index := by
      simpa [St.acct] using Nat.le_trans hsup2 (accrue_index_ge s2.supplyState s2.blockNumber (totalSupply s2))
    have hidx2 : accrualStart
        ((({ s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } : St).acct who).supplierIndex)
        ((({ s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } : St).supplyState.index)) ≤
        ((({ s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } : St).supplyState.index)) := by
      simpa using accrualStart_le_new _ _ _ hrec2 (Nat.le_refl _)
    have hd2 : distributeSupplierComp
        ({ s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } : St) who = some _ :=
      distSupply_eq_some _ who (by simpa using hidx2)
    simp [hd2]
  | setSpeeds a b =>
    have hcomp : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl
    rw [hcomp]
    unfold setCompSpeedInternal
    cases hsup : setSupplySpeed s a with
    | none =>
      have hcon : False := by
        unfold setSupplySpeed at hsup
        by_cases heqa : s.supplyState.speed = a
        · simp [heqa] at hsup
        · simp [heqa, updSupply_eq_some s hsblk] at hsup
      exact False.elim hcon
    | some m =>
      simp [hsup]
      obtain ⟨_, hseq⟩ := setSupply_some s a m hsup
      have hmbor : m.borrowState.block ≤ m.blockNumber := by simp [hseq, hbblk]
      cases hbor : setBorrowSpeed m b with
      | none =>
        have hcon : False := by
          unfold setBorrowSpeed at hbor
          by_cases heqb : m.borrowState.speed = b
          · simp [heqb] at hbor
          · simp [heqb, updBorrow_eq_some m hmbor] at hbor
        exact False.elim hcon
      | some _ => simp [hbor]
def pendSup (s : St) : Nat :=
  (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum
def pendBor (s : St) : Nat :=
  (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum
def unSup (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def unBor (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
def Phi (s : St) : Nat :=
  s.credited * doubleScale + pendSup s + pendBor s + unSup s * doubleScale + unBor s * doubleScale
def pendSupWho (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)
def pendBorWho (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)
def phi (s : St) (who : Account) : Nat :=
  (s.creditedTo who) * doubleScale + pendSupWho s who + pendBorWho s who +
  (if 0 < (s.acct who).supply then unSup s * doubleScale else 0) +
  (if 0 < (s.acct who).borrow then unBor s * doubleScale else 0)
theorem mul_div_le (T X : Nat) : T * (X / T) ≤ X := by
  have h := Nat.div_add_mod X T
  have hle : T * (X / T) ≤ T * (X / T) + X % T := Nat.le_add_right _ _
  simp [h] at hle
  exact hle
theorem div_mul_le (X : Nat) : doubleScale * (X / doubleScale) ≤ X := mul_div_le _ _
theorem accrualStart_mono (rec idx idx' : Nat) (hle : idx ≤ idx') :
    accrualStart rec idx ≤ accrualStart rec idx' := by
  unfold accrualStart
  by_cases h0 : rec = 0
  · simp [h0]
    by_cases hc : compInitialIndex ≤ idx
    · have hc' : compInitialIndex ≤ idx' := Nat.le_trans hc hle
      simp [hc, hc']
    · by_cases hc' : compInitialIndex ≤ idx'
      · simp [hc, hc']
      · simp [hc, hc']
  · simp [h0]
theorem single_le_sum_nat (l : List Nat) (i : Nat) : l.getD i 0 ≤ l.sum := by
  induction l generalizing i with
  | nil => simp [List.getD]
  | cons x xs ih =>
    cases i with
    | zero => simp [List.getD, List.sum]
    | succ n =>
      simp [List.getD, List.sum]
      exact Nat.le_trans (ih n) (Nat.le_add_left _ _)
theorem supply_le_total (s : St) (who : Account) : (s.acct who).supply ≤ totalSupply s := by
  unfold St.acct totalSupply
  have hmap : (s.accts.map Acct.supply).getD who 0 = (s.accts.getD who noAcct).supply := by
    induction s.accts generalizing who with
    | nil => cases who with | zero => rfl | succ n => rfl
    | cons x xs ih =>
      cases who with
      | zero => rfl
      | succ n => exact ih n
  rw [←hmap]
  exact single_le_sum_nat _ _
theorem borrow_le_total (s : St) (who : Account) : (s.acct who).borrow ≤ totalBorrows s := by
  unfold St.acct totalBorrows
  have hmap : (s.accts.map Acct.borrow).getD who 0 = (s.accts.getD who noAcct).borrow := by
    induction s.accts generalizing who with
    | nil => cases who with | zero => rfl | succ n => rfl
    | cons x xs ih =>
      cases who with
      | zero => rfl
      | succ n => exact ih n
  rw [←hmap]
  exact single_le_sum_nat _ _
theorem sum_le_of_mem_le (l : List Acct) (f g : Acct → Nat)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.map, List.sum]
    have hx : f x ≤ g x := h x (by simp)
    have ht : (xs.map f).sum ≤ (xs.map g).sum := ih (fun a ha => h a (List.mem_cons_of_mem x ha))
    exact Nat.add_le_add hx ht
theorem sum_add_le (l : List Acct) (f g h : Acct → Nat)
    (hall : ∀ a ∈ l, f a ≤ g a + h a) :
    (l.map f).sum ≤ (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => simp [List.map, List.sum]
  | cons x xs ih =>
    have hx : f x ≤ g x + h x := hall x (by simp)
    have ht := ih (fun a ha => hall a (List.mem_cons_of_mem x ha))
    show f x + (xs.map f).sum ≤ (g x + (xs.map g).sum) + (h x + (xs.map h).sum)
    have hle := Nat.add_le_add hx ht
    have heq : (g x + h x) + ((xs.map g).sum + (xs.map h).sum) =
        (g x + (xs.map g).sum) + (h x + (xs.map h).sum) := by ac_rfl
    have hle2 : f x + (xs.map f).sum ≤ (g x + h x) + ((xs.map g).sum + (xs.map h).sum) := hle
    rw [heq] at hle2
    exact hle2
theorem credited_distSupply (s : St) (who : Account) :
    (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }).credited =
    s.credited + creditFor (s.acct who).supply
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) s.supplyState.index := by
  unfold St.credited St.withAcct St.acct
  induction s.accts generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.modify, List.map, List.sum, creditFor, noAcct]
    | succ n => simp [List.modify, List.map, List.sum, creditFor, noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      show (x.accrued + creditFor x.supply (accrualStart x.supplierIndex s.supplyState.index) s.supplyState.index + x.wallet) +
          (xs.map fun a => a.accrued + a.wallet).sum =
        ((x.accrued + x.wallet) + (xs.map fun a => a.accrued + a.wallet).sum) +
          creditFor (x.supply) (accrualStart (x.supplierIndex) s.supplyState.index) s.supplyState.index
      ac_rfl
    | succ n =>
      show (x.accrued + x.wallet) + (((xs.modify n fun a =>
        { a with supplierIndex := s.supplyState.index,
                  accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }).map fun a => a.accrued + a.wallet).sum) =
        ((x.accrued + x.wallet) + (xs.map fun a => a.accrued + a.wallet).sum) +
          creditFor (xs.getD n noAcct).supply
            (accrualStart (xs.getD n noAcct).supplierIndex s.supplyState.index) s.supplyState.index
      have ht := ih n
      rw [ht]
      ac_rfl
theorem credited_distBorrow (s : St) (who : Account) :
    (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }).credited =
    s.credited + creditFor (s.acct who).borrow
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) s.borrowState.index := by
  unfold St.credited St.withAcct St.acct
  induction s.accts generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.modify, List.map, List.sum, creditFor, noAcct]
    | succ n => simp [List.modify, List.map, List.sum, creditFor, noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      show (x.accrued + creditFor x.borrow (accrualStart x.borrowerIndex s.borrowState.index) s.borrowState.index + x.wallet) +
          (xs.map fun a => a.accrued + a.wallet).sum =
        ((x.accrued + x.wallet) + (xs.map fun a => a.accrued + a.wallet).sum) +
          creditFor (x.borrow) (accrualStart (x.borrowerIndex) s.borrowState.index) s.borrowState.index
      ac_rfl
    | succ n =>
      show (x.accrued + x.wallet) + (((xs.modify n fun a =>
        { a with borrowerIndex := s.borrowState.index,
                  accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }).map fun a => a.accrued + a.wallet).sum) =
        ((x.accrued + x.wallet) + (xs.map fun a => a.accrued + a.wallet).sum) +
          creditFor (xs.getD n noAcct).borrow
            (accrualStart (xs.getD n noAcct).borrowerIndex s.borrowState.index) s.borrowState.index
      have ht := ih n
      rw [ht]
      ac_rfl
theorem accrualStart_self (idx : Nat) : accrualStart idx idx = idx := by
  unfold accrualStart
  by_cases h0 : idx = 0
  · simp [h0]
  · simp [h0]
theorem pendSup_distSupply (s : St) (who : Account) :
    pendSup s = pendSup (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) +
      (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
  unfold pendSup St.withAcct St.acct
  induction s.accts generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.modify, List.map, List.sum, noAcct]
    | succ n => simp [List.modify, List.map, List.sum, noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      show x.supply * (s.supplyState.index - accrualStart x.supplierIndex s.supplyState.index) +
          (xs.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum =
        ((x.supply * (s.supplyState.index - accrualStart s.supplyState.index s.supplyState.index) +
          (xs.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum)) +
          x.supply * (s.supplyState.index - accrualStart x.supplierIndex s.supplyState.index)
      have hself : accrualStart s.supplyState.index s.supplyState.index = s.supplyState.index :=
        accrualStart_self _
      have hnew : x.supply * (s.supplyState.index - accrualStart s.supplyState.index s.supplyState.index) = 0 := by
        simp [hself]
      simp [hnew]
      ac_rfl
    | succ n =>
      show (x.supply * (s.supplyState.index - accrualStart x.supplierIndex s.supplyState.index)) +
          ((xs.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum) =
        (((x.supply * (s.supplyState.index - accrualStart x.supplierIndex s.supplyState.index)) +
          (((xs.modify n fun a =>
            { a with supplierIndex := s.supplyState.index,
                      accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }).map fun a =>
            a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum))) +
          (xs.getD n noAcct).supply * (s.supplyState.index - accrualStart (xs.getD n noAcct).supplierIndex s.supplyState.index)
      have ht := ih n
      rw [ht]
      ac_rfl
theorem pendBor_distBorrow (s : St) (who : Account) :
    pendBor s = pendBor (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) +
      (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
  unfold pendBor St.withAcct St.acct
  induction s.accts generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.modify, List.map, List.sum, noAcct]
    | succ n => simp [List.modify, List.map, List.sum, noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      show x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index) +
          (xs.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum =
        ((x.borrow * (s.borrowState.index - accrualStart s.borrowState.index s.borrowState.index) +
          (xs.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum)) +
          x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index)
      have hself : accrualStart s.borrowState.index s.borrowState.index = s.borrowState.index :=
        accrualStart_self _
      have hnew : x.borrow * (s.borrowState.index - accrualStart s.borrowState.index s.borrowState.index) = 0 := by
        simp [hself]
      simp [hnew]
      ac_rfl
    | succ n =>
      show (x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index)) +
          ((xs.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum) =
        (((x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index)) +
          (((xs.modify n fun a =>
            { a with borrowerIndex := s.borrowState.index,
                      accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }).map fun a =>
            a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum))) +
          (xs.getD n noAcct).borrow * (s.borrowState.index - accrualStart (xs.getD n noAcct).borrowerIndex s.borrowState.index)
      have ht := ih n
      rw [ht]
      ac_rfl
theorem all_sup_modify (l : List Acct) (who : Nat) (f : Acct → Acct) (newIdx : Nat)
    (hold : ∀ a ∈ l, a.supplierIndex ≤ newIdx)
    (hnew : ∀ a, (f a).supplierIndex ≤ newIdx) :
    ∀ a ∈ l.modify who f, a.supplierIndex ≤ newIdx := by
  induction l generalizing who with
  | nil =>
    simp [List.modify_nil]
  | cons x xs ih =>
    cases who with
    | zero =>
      show ∀ a ∈ ((f x :: xs) : List Acct), a.supplierIndex ≤ newIdx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq, hnew]
      | inr hmem => exact hold a (List.mem_cons_of_mem x hmem)
    | succ n =>
      show ∀ a ∈ ((x :: xs.modify n f) : List Acct), a.supplierIndex ≤ newIdx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq]; exact hold x (by simp)
      | inr hmem =>
        have hall_xs : ∀ a ∈ xs, a.supplierIndex ≤ newIdx := fun a ha => hold a (List.mem_cons_of_mem x ha)
        exact ih n hall_xs a hmem
theorem all_bor_modify (l : List Acct) (who : Nat) (f : Acct → Acct) (newIdx : Nat)
    (hold : ∀ a ∈ l, a.borrowerIndex ≤ newIdx)
    (hnew : ∀ a, (f a).borrowerIndex ≤ newIdx) :
    ∀ a ∈ l.modify who f, a.borrowerIndex ≤ newIdx := by
  induction l generalizing who with
  | nil =>
    simp [List.modify_nil]
  | cons x xs ih =>
    cases who with
    | zero =>
      show ∀ a ∈ ((f x :: xs) : List Acct), a.borrowerIndex ≤ newIdx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq, hnew]
      | inr hmem => exact hold a (List.mem_cons_of_mem x hmem)
    | succ n =>
      show ∀ a ∈ ((x :: xs.modify n f) : List Acct), a.borrowerIndex ≤ newIdx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq]; exact hold x (by simp)
      | inr hmem =>
        have hall_xs : ∀ a ∈ xs, a.borrowerIndex ≤ newIdx := fun a ha => hold a (List.mem_cons_of_mem x ha)
        exact ih n hall_xs a hmem
theorem all_sup_modify_preserve (l : List Acct) (who : Nat) (f : Acct → Acct) (idx : Nat)
    (hold : ∀ a ∈ l, a.supplierIndex ≤ idx)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ∀ a ∈ l.modify who f, a.supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp [List.modify_nil]
  | cons x xs ih =>
    cases who with
    | zero =>
      show ∀ a ∈ ((f x :: xs) : List Acct), a.supplierIndex ≤ idx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq, hf, hold x (by simp)]
      | inr hmem => exact hold a (List.mem_cons_of_mem x hmem)
    | succ n =>
      show ∀ a ∈ ((x :: xs.modify n f) : List Acct), a.supplierIndex ≤ idx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq]; exact hold x (by simp)
      | inr hmem =>
        have hall_xs : ∀ a ∈ xs, a.supplierIndex ≤ idx := fun a ha => hold a (List.mem_cons_of_mem x ha)
        exact ih n hall_xs a hmem
theorem all_bor_modify_preserve (l : List Acct) (who : Nat) (f : Acct → Acct) (idx : Nat)
    (hold : ∀ a ∈ l, a.borrowerIndex ≤ idx)
    (hf : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ∀ a ∈ l.modify who f, a.borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp [List.modify_nil]
  | cons x xs ih =>
    cases who with
    | zero =>
      show ∀ a ∈ ((f x :: xs) : List Acct), a.borrowerIndex ≤ idx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq, hf, hold x (by simp)]
      | inr hmem => exact hold a (List.mem_cons_of_mem x hmem)
    | succ n =>
      show ∀ a ∈ ((x :: xs.modify n f) : List Acct), a.borrowerIndex ≤ idx
      intro a ha
      simp at ha
      cases ha with
      | inl heq => simp [heq]; exact hold x (by simp)
      | inr hmem =>
        have hall_xs : ∀ a ∈ xs, a.borrowerIndex ≤ idx := fun a ha => hold a (List.mem_cons_of_mem x ha)
        exact ih n hall_xs a hmem
theorem Consistent_updSupply (s : St) (h : Consistent s) :
    Consistent { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold Consistent at h ⊢
  obtain ⟨hsblk, hbblk, hall⟩ := h
  refine ⟨by simp [accrue_block], hbblk, ?_⟩
  intro a ha
  have hsup : a.supplierIndex ≤ s.supplyState.index := (hall a ha).1
  have hbor : a.borrowerIndex ≤ s.borrowState.index := (hall a ha).2
  refine ⟨Nat.le_trans hsup (accrue_index_ge _ _ _), hbor⟩
theorem Consistent_updBorrow (s : St) (h : Consistent s) :
    Consistent { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold Consistent at h ⊢
  obtain ⟨hsblk, hbblk, hall⟩ := h
  refine ⟨hsblk, by simp [accrue_block], ?_⟩
  intro a ha
  have hsup : a.supplierIndex ≤ s.supplyState.index := (hall a ha).1
  have hbor : a.borrowerIndex ≤ s.borrowState.index := (hall a ha).2
  refine ⟨hsup, Nat.le_trans hbor (accrue_index_ge _ _ _)⟩
theorem Consistent_distSupply (s : St) (who : Account) (h : Consistent s) :
    Consistent (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold Consistent at h ⊢
  unfold St.withAcct at ⊢
  obtain ⟨hsblk, hbblk, hall⟩ := h
  refine ⟨hsblk, hbblk, ?_⟩
  intro a ha
  have hsup_old : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (hall a ha).1
  have hbor_old : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := fun a ha => (hall a ha).2
  have hsup_new : ∀ a ∈ (s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }),
      a.supplierIndex ≤ s.supplyState.index := by
    apply all_sup_modify _ _ _ _ hsup_old
    intro a
    simp
  have hbor_new : ∀ a ∈ (s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }),
      a.borrowerIndex ≤ s.borrowState.index := by
    apply all_bor_modify_preserve _ _ _ _ hbor_old
    intro a
    rfl
  exact ⟨hsup_new a ha, hbor_new a ha⟩
theorem Consistent_distBorrow (s : St) (who : Account) (h : Consistent s) :
    Consistent (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold Consistent at h ⊢
  unfold St.withAcct at ⊢
  obtain ⟨hsblk, hbblk, hall⟩ := h
  refine ⟨hsblk, hbblk, ?_⟩
  intro a ha
  have hsup_old : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (hall a ha).1
  have hbor_old : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := fun a ha => (hall a ha).2
  have hsup_new : ∀ a ∈ (s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }),
      a.supplierIndex ≤ s.supplyState.index := by
    apply all_sup_modify_preserve _ _ _ _ hsup_old
    intro a
    rfl
  have hbor_new : ∀ a ∈ (s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }),
      a.borrowerIndex ≤ s.borrowState.index := by
    apply all_bor_modify _ _ _ _ hbor_old
    intro a
    simp
  exact ⟨hsup_new a ha, hbor_new a ha⟩
theorem sum_mul_supply (l : List Acct) (k : Nat) :
    ((l.map Acct.supply).sum) * k = ((l.map fun a => a.supply * k).sum) := by
  induction l with
  | nil => simp [List.map, List.sum]
  | cons x xs ih =>
    show (x.supply + (xs.map Acct.supply).sum) * k = (x.supply * k + ((xs.map fun a => a.supply * k).sum))
    rw [Nat.add_mul, ih]
theorem pendBor_preserve_supplyDist (s : St) (who : Account) :
    pendBor (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) =
    pendBor s := by
  unfold pendBor St.withAcct
  induction s.accts generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.modify_nil, List.map, List.sum]
    | succ n => simp [List.modify_nil, List.map, List.sum]
  | cons x xs ih =>
    cases who with
    | zero =>
      show x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index) +
          (xs.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum =
        x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index) +
          (xs.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum
      rfl
    | succ n =>
      show (x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index)) +
          (((xs.modify n fun a =>
            { a with supplierIndex := s.supplyState.index,
                      accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }).map fun a =>
            a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum) =
        (x.borrow * (s.borrowState.index - accrualStart x.borrowerIndex s.borrowState.index)) +
          ((xs.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum)
      have ht := ih n
      rw [ht]
theorem Phi_accrueSupply_le (s : St) (h : Consistent s) :
    Phi { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ Phi s := by
  sorry
theorem Phi_distSupply_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    Phi (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) ≤ Phi s := by
  sorry
theorem Phi_accrueBorrow_le (s : St) (h : Consistent s) :
    Phi { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤ Phi s := by
  sorry
theorem Phi_distBorrow_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    Phi (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) ≤ Phi s := by
  sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
