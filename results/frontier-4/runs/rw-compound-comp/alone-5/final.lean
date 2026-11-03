import CompRewards.Spec
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

/-- `distributeSupplierComp(cToken, supplier)`. Fixed: new accounts start at
`compInitialIndex` once the market index has reached it (`≥`), never credited for
rewards emitted before rewards began. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  match subChecked s.supplyState.index (accrualStart (s.acct supplier).supplierIndex s.supplyState.index) with
  | none => none
  | some deltaIndex => some (s.withAcct supplier fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble a.supply deltaIndex }))

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. Fixed as above. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  match subChecked s.borrowState.index (accrualStart (s.acct borrower).borrowerIndex s.borrowState.index) with
  | none => none
  | some deltaIndex => some (s.withAcct borrower fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble a.borrow deltaIndex }))

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  if 0 < (s.acct user).accrued ∧ (s.acct user).accrued ≤ s.reserve then
    { s with reserve := s.reserve - (s.acct user).accrued,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
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

/-- `subChecked a b` succeeds iff `b ≤ a`. -/
theorem subChecked_isSome (a b : Nat) : (subChecked a b).isSome = decide (b ≤ a) := by
  unfold subChecked; split <;> simp_all

theorem subChecked_eq_some (a b d : Nat) :
    subChecked a b = some d ↔ b ≤ a ∧ d = a - b := by
  unfold subChecked
  by_cases h : b ≤ a
  · simp [h, Eq.comm]
  · simp [h]

theorem subChecked_eq_none (a b : Nat) :
    subChecked a b = none ↔ ¬ b ≤ a := by
  unfold subChecked; split
  · next h => simp_all
  · next h => simp_all

theorem accrualStart_le_of_le {recorded index : Nat} (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  split
  · next hr =>
    subst hr
    split
    · next hle => exact hle
    · next _ => exact Nat.zero_le _
  · next _ => exact h

theorem updateSupply_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
  unfold updateCompSupplyIndex accrueSide fraction
  have hb : subChecked s.blockNumber s.supplyState.block
      = some (s.blockNumber - s.supplyState.block) := by
    rw [subChecked_eq_some]; exact ⟨h, rfl⟩
  rw [hb]
  by_cases hd : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
  · simp only [gt_iff_lt, hd]
    by_cases ht : 0 < totalSupply s
    · have ht0 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s := ⟨hd.1, hd.2, ht⟩
      simp [ht, ht0]
    · have ht0 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by omega
      simp [ht, ht0]
  · simp only [gt_iff_lt, hd]
    by_cases hd2 : 0 < s.blockNumber - s.supplyState.block
    · have hsp : s.supplyState.speed = 0 := by omega
      have ht0 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by omega
      simp [hd2, hsp, ht0]
    · have heq : s.supplyState.block = s.blockNumber := by omega
      have ht0 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by omega
      simp only [hd2, ht0]
      obtain ⟨bn, sup, bor, res, accts⟩ := s
      obtain ⟨idx, blk, spd⟩ := sup
      simp only at heq ⊢
      subst heq
      rfl

theorem updateSupply_none (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  have hb : subChecked s.blockNumber s.supplyState.block = none := by
    rw [subChecked_eq_none]; omega
  rw [hb]

theorem updateBorrow_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = some ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
  unfold updateCompBorrowIndex accrueSide fraction
  have hb : subChecked s.blockNumber s.borrowState.block
      = some (s.blockNumber - s.borrowState.block) := by
    rw [subChecked_eq_some]; exact ⟨h, rfl⟩
  rw [hb]
  by_cases hd : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
  · simp only [gt_iff_lt, hd]
    by_cases ht : 0 < totalBorrows s
    · have ht0 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s := ⟨hd.1, hd.2, ht⟩
      simp [ht, ht0]
    · have ht0 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by omega
      simp [ht, ht0]
  · simp only [gt_iff_lt, hd]
    by_cases hd2 : 0 < s.blockNumber - s.borrowState.block
    · have hsp : s.borrowState.speed = 0 := by omega
      have ht0 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by omega
      simp [hd2, hsp, ht0]
    · have heq : s.borrowState.block = s.blockNumber := by omega
      have ht0 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by omega
      simp only [hd2, ht0]
      obtain ⟨bn, sup, bor, res, accts⟩ := s
      obtain ⟨idx, blk, spd⟩ := bor
      simp only at heq ⊢
      subst heq
      rfl

theorem updateBorrow_none (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  have hb : subChecked s.blockNumber s.borrowState.block = none := by
    rw [subChecked_eq_none]; omega
  rw [hb]

theorem list_modify_congr (xs : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (xs.getD who noAcct) = g (xs.getD who noAcct)) :
    xs.modify who f = xs.modify who g := by
  induction xs generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons y ys ih =>
    cases who with
    | zero =>
      simp at h ⊢
      simp [h]
    | succ n =>
      have h2 : f (ys.getD n noAcct) = g (ys.getD n noAcct) := by simpa using h
      simp [ih n h2]

theorem withAcct_congr (s : St) (who : Account) (f g : Acct → Acct)
    (h : f (s.acct who) = g (s.acct who)) :
    s.withAcct who f = s.withAcct who g := by
  unfold St.withAcct
  simp only [St.acct] at h
  congr 1
  exact list_modify_congr _ _ _ _ h

theorem mulDouble_creditFor (u start index : Nat) :
    mulDouble u (index - start) = creditFor u start index := by
  unfold mulDouble creditFor; rfl

theorem distributeSupply_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some (s.withAcct who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })) := by
  unfold distributeSupplierComp
  have hb : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    rw [subChecked_eq_some]; exact ⟨h, rfl⟩
  rw [hb]
  simp only
  congr 1
  apply withAcct_congr
  show _ = _
  rw [mulDouble_creditFor]

theorem distributeSupply_none (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = none := by
  unfold distributeSupplierComp
  have hb : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none := by
    rw [subChecked_eq_none]; exact h
  rw [hb]

theorem distributeBorrow_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some (s.withAcct who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })) := by
  unfold distributeBorrowerComp
  have hb : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    rw [subChecked_eq_some]; exact ⟨h, rfl⟩
  rw [hb]
  simp only
  congr 1
  apply withAcct_congr
  show _ = _
  rw [mulDouble_creditFor]

theorem distributeBorrow_none (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp
  have hb : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none := by
    rw [subChecked_eq_none]; exact h
  rw [hb]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant; rfl

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hu : updateCompSupplyIndex s with
  | none =>
    simp [hu] at h
  | some t =>
    simp [hu] at h
    have hblock : s.supplyState.block ≤ s.blockNumber := by
      by_cases hb : s.supplyState.block ≤ s.blockNumber
      · exact hb
      · exfalso
        have hn : updateCompSupplyIndex s = none := updateSupply_none s hb
        rw [hn] at hu
        simp at hu
    have ht : t = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
      have e1 := updateSupply_some s hblock
      rw [hu] at e1
      simpa using e1
    subst ht
    cases hd : distributeSupplierComp ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) who with
    | none =>
      simp [hd] at h
    | some u =>
      simp [hd] at h
      subst h
      have hstart : accrualStart ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex) ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) := by
        by_cases hb2 : accrualStart ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex) ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index))
        · exact hb2
        · exfalso
          have hn := distributeSupply_none _ who hb2
          rw [hd] at hn
          simp at hn
      have hu2 := distributeSupply_some _ who hstart
      rw [hd] at hu2
      have heq : u = (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).withAcct who fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index })) := by
        simpa using hu2
      unfold SupplyDistributed
      refine ⟨hblock, ?_, ?_⟩
      · have hrr : ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who)) = (s.acct who) := rfl
        rw [hrr] at hstart
        simpa using hstart
      · rw [heq]
        unfold St.withAcct
        rfl

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hu : updateCompBorrowIndex s with
  | none =>
    simp [hu] at h
  | some t =>
    simp [hu] at h
    have hblock : s.borrowState.block ≤ s.blockNumber := by
      by_cases hb : s.borrowState.block ≤ s.blockNumber
      · exact hb
      · exfalso
        have hn : updateCompBorrowIndex s = none := updateBorrow_none s hb
        rw [hn] at hu
        simp at hu
    have ht : t = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
      have e1 := updateBorrow_some s hblock
      rw [hu] at e1
      simpa using e1
    subst ht
    cases hd : distributeBorrowerComp ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who with
    | none =>
      simp [hd] at h
    | some u =>
      simp [hd] at h
      subst h
      have hstart : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) := by
        by_cases hb2 : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index))
        · exact hb2
        · exfalso
          have hn := distributeBorrow_none _ who hb2
          rw [hd] at hn
          simp at hn
      have hu2 := distributeBorrow_some _ who hstart
      rw [hd] at hu2
      have heq : u = (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index })) := by
        simpa using hu2
      unfold BorrowDistributed
      refine ⟨hblock, ?_, ?_⟩
      · have hrr : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who)) = (s.acct who) := rfl
        rw [hrr] at hstart
        simpa using hstart
      · rw [heq]
        unfold St.withAcct
        rfl

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
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
          simp [hd2, grant_eq] at h
          subst h
          have hblockB : s.borrowState.block ≤ s.blockNumber := by
            by_cases hb : s.borrowState.block ≤ s.blockNumber
            · exact hb
            · exfalso
              have hn := updateBorrow_none s hb
              rw [hn] at hb1
              simp at hb1
          have ht1 : t1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
            have e1 := updateBorrow_some s hblockB
            rw [hb1] at e1
            simpa using e1
          subst ht1
          have hstartB : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) := by
            by_cases hb2 : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index))
            · exact hb2
            · exfalso
              have hn := distributeBorrow_none _ who hb2
              rw [hd1] at hn
              simp at hn
          have hu1 := distributeBorrow_some _ who hstartB
          rw [hd1] at hu1
          have heq1 : m1 = (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index })) := by
            simpa using hu1
          have hblockS : m1.supplyState.block ≤ m1.blockNumber := by
            by_cases hb : m1.supplyState.block ≤ m1.blockNumber
            · exact hb
            · exfalso
              have hn := updateSupply_none m1 hb
              rw [hn] at hs1
              simp at hs1
          have ht2 : t2 = ({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) }) := by
            have e1 := updateSupply_some m1 hblockS
            rw [hs1] at e1
            simpa using e1
          subst ht2
          have hstartS : accrualStart ((({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).acct who).supplierIndex) ((({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).supplyState.index)) ≤ ((({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).supplyState.index)) := by
            by_cases hb2 : accrualStart ((({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).acct who).supplierIndex) ((({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).supplyState.index)) ≤ ((({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).supplyState.index))
            · exact hb2
            · exfalso
              have hn := distributeSupply_none _ who hb2
              rw [hd2] at hn
              simp at hn
          have hu2 := distributeSupply_some _ who hstartS
          rw [hd2] at hu2
          have heq2 : m2 = (({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).withAcct who fun a => ({ a with supplierIndex := (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index) (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index })) := by
            simpa using hu2
          unfold Claimed
          refine ⟨m1, m2, ?_, ?_, rfl⟩
          · unfold BorrowDistributed
            refine ⟨hblockB, ?_, ?_⟩
            · have hrr : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who)) = (s.acct who) := rfl
              rw [hrr] at hstartB
              simpa using hstartB
            · rw [heq1]
              unfold St.withAcct
              rfl
          · unfold SupplyDistributed
            refine ⟨hblockS, ?_, ?_⟩
            · have hrr2 : ((({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St).acct who)) = (m1.acct who) := rfl
              rw [hrr2] at hstartS
              simpa using hstartS
            · rw [heq2]
              unfold St.withAcct
              rfl

theorem setSupply_eq (s : St) (a : Nat) (t : St)
    (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = (if s.supplyState.speed = a then s else ({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) })) := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    subst h
    constructor
    · intro hn
      exfalso
      exact hn heq
    · simp [heq]
  · simp [heq] at h
    have hblock : s.supplyState.block ≤ s.blockNumber := by
      by_cases hb : s.supplyState.block ≤ s.blockNumber
      · exact hb
      · exfalso
        have hn := updateSupply_none s hb
        simp [hn] at h
    have e1 := updateSupply_some s hblock
    cases hu : updateCompSupplyIndex s with
    | none =>
      simp [hu] at h
    | some u =>
      simp [hu] at h
      subst h
      have ht : u = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
        rw [hu] at e1
        simpa using e1
      subst ht
      constructor
      · intro _
        exact hblock
      · simp [heq]

theorem setBorrow_eq (s : St) (b : Nat) (t : St)
    (h : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = (if s.borrowState.speed = b then s else ({ s with borrowState := ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) })) := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    subst h
    constructor
    · intro hn
      exfalso
      exact hn heq
    · simp [heq]
  · simp [heq] at h
    have hblock : s.borrowState.block ≤ s.blockNumber := by
      by_cases hb : s.borrowState.block ≤ s.blockNumber
      · exact hb
      · exfalso
        have hn := updateBorrow_none s hb
        simp [hn] at h
    have e1 := updateBorrow_some s hblock
    cases hu : updateCompBorrowIndex s with
    | none =>
      simp [hu] at h
    | some u =>
      simp [hu] at h
      subst h
      have ht : u = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
        rw [hu] at e1
        simpa using e1
      subst ht
      constructor
      · intro _
        exact hblock
      · simp [heq]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  cases hs1 : setSupplySpeed s a with
  | none => simp [hs1] at h
  | some m =>
    simp [hs1] at h
    cases hs2 : setBorrowSpeed m b with
    | none => simp [hs2] at h
    | some t =>
      simp [hs2] at h
      subst h
      have h1 := setSupply_eq s a m hs1
      have h2 := setBorrow_eq m b t hs2
      unfold SpeedsSet
      refine ⟨?_, ?_, ?_⟩
      · intro hn
        exact h1.1 hn
      · intro hn
        have hm_block : m.blockNumber = s.blockNumber := by
          rw [h1.2]
          by_cases heq : s.supplyState.speed = a
          · simp [heq]
          · simp [heq]
        have hm_borrowBlock : m.borrowState.block = s.borrowState.block := by
          rw [h1.2]
          by_cases heq : s.supplyState.speed = a
          · simp [heq]
          · simp [heq]
        have hm_borrowSpeed : m.borrowState.speed = s.borrowState.speed := by
          rw [h1.2]
          by_cases heq : s.supplyState.speed = a
          · simp [heq]
          · simp [heq]
        have hblock : m.borrowState.block ≤ m.blockNumber := h2.1 (by rw [hm_borrowSpeed]; exact hn)
        omega
      · have hm_accts : m.accts = s.accts := by
          rw [h1.2]
          by_cases heq : s.supplyState.speed = a
          · simp [heq]
          · simp [heq]
        have hm_block : m.blockNumber = s.blockNumber := by
          rw [h1.2]
          by_cases heq : s.supplyState.speed = a
          · simp [heq]
          · simp [heq]
        have hm_borrow : m.borrowState = s.borrowState := by
          rw [h1.2]
          by_cases heq : s.supplyState.speed = a
          · simp [heq]
          · simp [heq]
        have hm_totalB : totalBorrows m = totalBorrows s := by
          unfold totalBorrows
          rw [hm_accts]
        have hm_bspeed : m.borrowState.speed = s.borrowState.speed := by
          rw [hm_borrow]
        have haccB : accrueSide m.borrowState m.blockNumber (totalBorrows m) =
            accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
          rw [hm_borrow, hm_block, hm_totalB]
        have hcondB : (m.borrowState.speed = b) = (s.borrowState.speed = b) := by
          rw [hm_bspeed]
        rw [h2.2]
        simp only [hcondB, haccB]
        rw [h1.2]
        by_cases heqS : s.supplyState.speed = a
        · simp [heqS]
          by_cases heqB : s.borrowState.speed = b
          · simp [heqB, hm_accts, hm_block, hm_borrow]
          · simp [heqB]
        · simp [heqS]
          by_cases heqB : s.borrowState.speed = b
          · simp [heqB, hm_accts, hm_block, hm_borrow]
          · simp [heqB]

theorem list_getD_sup_le (xs : List Acct) (idx : Nat)
    (h : ∀ a ∈ xs, a.supplierIndex ≤ idx) (who : Nat) :
    (xs.getD who noAcct).supplierIndex ≤ idx := by
  induction xs generalizing who with
  | nil =>
    exact Nat.zero_le _
  | cons y ys ih =>
    cases who with
    | zero =>
      simp
      exact h y (by simp)
    | succ n =>
      simp
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem list_getD_bor_le (xs : List Acct) (idx : Nat)
    (h : ∀ a ∈ xs, a.borrowerIndex ≤ idx) (who : Nat) :
    (xs.getD who noAcct).borrowerIndex ≤ idx := by
  induction xs generalizing who with
  | nil =>
    exact Nat.zero_le _
  | cons y ys ih =>
    cases who with
    | zero =>
      simp
      exact h y (by simp)
    | succ n =>
      simp
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem acct_sup_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  apply list_getD_sup_le _ _ _ who
  intro a ha
  exact (hall a ha).1

theorem acct_bor_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  apply list_getD_bor_le _ _ _ who
  intro a ha
  exact (hall a ha).2

theorem list_all_modify (xs : List Acct) (who : Nat) (f : Acct → Acct) (P : Acct → Prop)
    (h_all : ∀ a ∈ xs, P a) (h_f : ∀ a ∈ xs, P (f a)) :
    ∀ a ∈ xs.modify who f, P a := by
  induction xs generalizing who with
  | nil =>
    simp
  | cons y ys ih =>
    cases who with
    | zero =>
      simp
      constructor
      · exact h_f y (by simp)
      · intro a ha
        exact h_all a (by simp [ha])
    | succ n =>
      simp
      constructor
      · exact h_all y (by simp)
      · have h1 : ∀ b ∈ ys, P b := fun b hb => h_all b (by simp [hb])
        have h2 : ∀ b ∈ ys, P (f b) := fun b hb => h_f b (by simp [hb])
        intro a ha
        exact ih n h1 h2 a ha

theorem modify_map_supply_eq (xs : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).supply = a.supply) :
    (xs.modify who f).map Acct.supply = xs.map Acct.supply := by
  induction xs generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons y ys ih =>
    cases who with
    | zero =>
      simp [h y]
    | succ n =>
      simp [ih n]

theorem modify_map_borrow_eq (xs : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).borrow = a.borrow) :
    (xs.modify who f).map Acct.borrow = xs.map Acct.borrow := by
  induction xs generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons y ys ih =>
    cases who with
    | zero =>
      simp [h y]
    | succ n =>
      simp [ih n]

theorem accrue_index_mono (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, Nat.le_add_right]
  · simp [h]

theorem accrue_block_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem consistent_updateSupply (s : St) (hc : Consistent s) :
    Consistent ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) := by
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hall⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · simp [accrue_block_eq]
  · simpa using hborB
  · intro a ha
    have heq : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
    constructor
    · have h1 : a.supplierIndex ≤ s.supplyState.index := (hall a ha).1
      have h2 : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
        accrue_index_mono _ _ _
      omega
    · have h1 : a.borrowerIndex ≤ s.borrowState.index := (hall a ha).2
      have hbor_eq : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).borrowState.index) = s.borrowState.index := rfl
      omega

theorem consistent_updateBorrow (s : St) (hc : Consistent s) :
    Consistent ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) := by
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hall⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · simpa using hsupB
  · simp [accrue_block_eq]
  · intro a ha
    have heq : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    constructor
    · have h1 : a.supplierIndex ≤ s.supplyState.index := (hall a ha).1
      have hsup_eq : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).supplyState.index) = s.supplyState.index := rfl
      omega
    · have h1 : a.borrowerIndex ≤ s.borrowState.index := (hall a ha).2
      have h2 : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
        accrue_index_mono _ _ _
      omega

theorem consistent_distributeSupply (s : St) (who : Account) (hc : Consistent s) :
    Consistent (s.withAcct who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })) := by
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hall⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · simpa [St.withAcct] using hsupB
  · simpa [St.withAcct] using hborB
  · have hall_sup : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
      fun a ha => (hall a ha).1
    have hall_bor : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
      fun a ha => (hall a ha).2
    have hsup_all : ∀ a ∈ (s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })), a.supplierIndex ≤ s.supplyState.index := by
      apply list_all_modify _ _ _ _ hall_sup
      intro a ha
      simp
    have hbor_all : ∀ a ∈ (s.accts.modify who fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })), a.borrowerIndex ≤ s.borrowState.index := by
      apply list_all_modify _ _ _ _ hall_bor
      intro a ha
      have hrr : (({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }).borrowerIndex) = a.borrowerIndex := rfl
      rw [hrr]
      exact hall_bor a ha
    intro a ha
    simp [St.withAcct] at ha ⊢
    exact ⟨hsup_all a ha, hbor_all a ha⟩

theorem consistent_distributeBorrow (s : St) (who : Account) (hc : Consistent s) :
    Consistent (s.withAcct who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })) := by
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hall⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · simpa [St.withAcct] using hsupB
  · simpa [St.withAcct] using hborB
  · have hall_sup : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
      fun a ha => (hall a ha).1
    have hall_bor : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
      fun a ha => (hall a ha).2
    have hsup_all : ∀ a ∈ (s.accts.modify who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })), a.supplierIndex ≤ s.supplyState.index := by
      apply list_all_modify _ _ _ _ hall_sup
      intro a ha
      have hrr : (({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }).supplierIndex) = a.supplierIndex := rfl
      rw [hrr]
      exact hall_sup a ha
    have hbor_all : ∀ a ∈ (s.accts.modify who fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })), a.borrowerIndex ≤ s.borrowState.index := by
      apply list_all_modify _ _ _ _ hall_bor
      intro a ha
      simp
    intro a ha
    simp [St.withAcct] at ha ⊢
    exact ⟨hsup_all a ha, hbor_all a ha⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsupB, hborB, hall⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    simp
    have h1 := updateSupply_some s hsupB
    rw [h1]
    simp
    have hle : ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) := by
      have h0 := acct_sup_le s ⟨hsupB, hborB, hall⟩ who
      have hmono : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        unfold accrueSide
        by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
        · simp [h, Nat.le_add_right]
        · simp [h]
      have hrr : ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who).supplierIndex) = (s.acct who).supplierIndex := rfl
      have hidx : ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index)) = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
      omega
    have hstart := accrualStart_le_of_le hle
    have h2 := distributeSupply_some ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) who hstart
    simp [h2]
  | borrowHook who =>
    unfold comptroller
    simp
    have h1 := updateBorrow_some s hborB
    rw [h1]
    simp
    have hle : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) := by
      have h0 := acct_bor_le s ⟨hsupB, hborB, hall⟩ who
      have hmono : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        unfold accrueSide
        by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
        · simp [h, Nat.le_add_right]
        · simp [h]
      have hrr : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) = (s.acct who).borrowerIndex := rfl
      have hidx : ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
      omega
    have hstart := accrualStart_le_of_le hle
    have h2 := distributeBorrow_some ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who hstart
    simp [h2]
  | claim who =>
    unfold comptroller claimComp
    simp
    have h1 := updateBorrow_some s hborB
    rw [h1]
    simp
    have hleB : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      have h0 := acct_bor_le s ⟨hsupB, hborB, hall⟩ who
      have hmono : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        unfold accrueSide
        by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
        · simp [h, Nat.le_add_right]
        · simp [h]
      omega
    have hstartB := accrualStart_le_of_le hleB
    have hb : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex = (s.acct who).borrowerIndex := rfl
    have hstartB' : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index)) := by
      rw [hb]
      simpa using hstartB
    have h2 := distributeBorrow_some _ who hstartB'
    rw [h2]
    simp
    have hc : Consistent s := ⟨hsupB, hborB, hall⟩
    have hc_t1 : Consistent ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) :=
      consistent_updateBorrow s hc
    have hc_m1 : Consistent ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }))) :=
      consistent_distributeBorrow _ who hc_t1
    have hblockS := hc_m1.1
    have h3 := updateSupply_some _ hblockS
    rw [h3]
    simp
    have hc_t2 := consistent_updateSupply _ hc_m1
    have hleS := acct_sup_le _ hc_t2 who
    have hstartS := accrualStart_le_of_le hleS
    have h4 := distributeSupply_some _ who hstartS
    rw [h4]
    simp
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal
    simp only
    cases hs1 : setSupplySpeed s a with
    | none =>
      exfalso
      by_cases heq : s.supplyState.speed = a
      · have h_eq : setSupplySpeed s a = some s := by simp [setSupplySpeed, heq]
        rw [h_eq] at hs1
        simp at hs1
      · have h_eq : setSupplySpeed s a = some ({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) }) := by
          simp [setSupplySpeed, heq, updateSupply_some s hsupB]
        rw [h_eq] at hs1
        simp at hs1
    | some m =>
      simp [hs1]
      have h1 := setSupply_eq s a m hs1
      have hc : Consistent s := ⟨hsupB, hborB, hall⟩
      have hc_m : Consistent m := by
        rw [h1.2]
        by_cases heq : s.supplyState.speed = a
        · simp [heq]
          exact hc
        · simp [heq]
          exact consistent_updateSupply s hc
      have hborB_m : m.borrowState.block ≤ m.blockNumber := hc_m.2.1
      cases hs2 : setBorrowSpeed m b with
      | none =>
        exfalso
        by_cases heq : m.borrowState.speed = b
        · have h_eq : setBorrowSpeed m b = some m := by simp [setBorrowSpeed, heq]
          rw [h_eq] at hs2
          simp at hs2
        · have h_eq : setBorrowSpeed m b = some ({ m with borrowState := ({ accrueSide m.borrowState m.blockNumber (totalBorrows m) with speed := b }) }) := by
            simp [setBorrowSpeed, heq, updateBorrow_some m hborB_m]
          rw [h_eq] at hs2
          simp at hs2
      | some t =>
        simp [hs2]

theorem grant_preserves_consistent (s : St) (who : Account) (hc : Consistent s) :
    Consistent (grant s who) := by
  unfold Consistent at hc
  obtain ⟨hsupB, hborB, hall⟩ := hc
  unfold grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp [h]
    refine ⟨?_, ?_, ?_⟩
    · simpa using hsupB
    · simpa using hborB
    · have hall_sup : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
        fun a ha => (hall a ha).1
      have hall_bor : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
        fun a ha => (hall a ha).2
      have hsup_all : ∀ a ∈ (s.accts.modify who fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued })), a.supplierIndex ≤ s.supplyState.index := by
        apply list_all_modify _ _ _ _ hall_sup
        intro a ha
        simp
        exact hall_sup a ha
      have hbor_all : ∀ a ∈ (s.accts.modify who fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued })), a.borrowerIndex ≤ s.borrowState.index := by
        apply list_all_modify _ _ _ _ hall_bor
        intro a ha
        simp
        exact hall_bor a ha
      intro a ha
      simp at ha ⊢
      exact ⟨hsup_all a ha, hbor_all a ha⟩
  · simp [h]
    exact ⟨hsupB, hborB, hall⟩

theorem advance_preserves_consistent (s : St) (k : Nat) (hc : Consistent s) :
    Consistent ({ s with blockNumber := s.blockNumber + k }) := by
  unfold Consistent at hc
  obtain ⟨hsupB, hborB, hall⟩ := hc
  unfold Consistent
  refine ⟨?_, ?_, ?_⟩
  · have heq1 : (({ s with blockNumber := s.blockNumber + k } : St).supplyState.block) = s.supplyState.block := rfl
    have heq2 : ((({ s with blockNumber := s.blockNumber + k } : St).blockNumber)) = s.blockNumber + k := rfl
    omega
  · have heq1 : ((({ s with blockNumber := s.blockNumber + k } : St).borrowState.block)) = s.borrowState.block := rfl
    have heq2 : ((({ s with blockNumber := s.blockNumber + k } : St).blockNumber)) = s.blockNumber + k := rfl
    omega
  · have heq_accts : ((({ s with blockNumber := s.blockNumber + k } : St).accts)) = s.accts := rfl
    have heq_sup : ((({ s with blockNumber := s.blockNumber + k } : St).supplyState.index)) = s.supplyState.index := rfl
    have heq_bor : ((({ s with blockNumber := s.blockNumber + k } : St).borrowState.index)) = s.borrowState.index := rfl
    intro a ha
    rw [heq_accts] at ha
    have h1 := hall a ha
    rw [heq_sup, heq_bor]
    exact h1

theorem supplyDistributed_preserves (s : St) (who : Account) (s' : St)
    (hc : Consistent s) (h : SupplyDistributed s who s') : Consistent s' := by
  unfold SupplyDistributed at h
  obtain ⟨hblock, hstart, heq⟩ := h
  subst heq
  have hc_up : Consistent ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) :=
    consistent_updateSupply s hc
  have h_eq_accts : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts) = s.accts := rfl
  have h_eq_idx : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
  exact consistent_distributeSupply _ who hc_up

theorem borrowDistributed_preserves (s : St) (who : Account) (s' : St)
    (hc : Consistent s) (h : BorrowDistributed s who s') : Consistent s' := by
  unfold BorrowDistributed at h
  obtain ⟨hblock, hstart, heq⟩ := h
  subst heq
  have hc_up : Consistent ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) :=
    consistent_updateBorrow s hc
  exact consistent_distributeBorrow _ who hc_up

theorem claimed_preserves (s : St) (who : Account) (s' : St)
    (hc : Consistent s) (h : Claimed s who s') : Consistent s' := by
  unfold Claimed at h
  obtain ⟨m1, m2, hb, hs, heq⟩ := h
  have hc1 := borrowDistributed_preserves s who m1 hc hb
  have hc2 := supplyDistributed_preserves m1 who m2 hc1 hs
  subst heq
  exact grant_preserves_consistent _ who hc2

theorem speedsSet_preserves (s : St) (a b : Nat) (s' : St)
    (hc : Consistent s) (h : SpeedsSet s a b s') : Consistent s' := by
  unfold SpeedsSet at h
  obtain ⟨_, _, heq⟩ := h
  subst heq
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hall⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · by_cases heqS : s.supplyState.speed = a
    · simp [heqS]
      exact hsupB
    · simp [heqS, accrue_block_eq]
  · by_cases heqB : s.borrowState.speed = b
    · simp [heqB]
      exact hborB
    · simp [heqB, accrue_block_eq]
  · intro x hx
    have hsup_mono : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrue_index_mono _ _ _
    have hbor_mono : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrue_index_mono _ _ _
    have h1 := hall x hx
    by_cases heqS : s.supplyState.speed = a
    · simp [heqS] at ⊢
      by_cases heqB : s.borrowState.speed = b
      · simp [heqB]
        exact h1
      · simp [heqB]
        constructor
        · exact h1.1
        · omega
    · simp [heqS] at ⊢
      by_cases heqB : s.borrowState.speed = b
      · simp [heqB]
        constructor
        · omega
        · exact h1.2
      · simp [heqB]
        constructor
        · omega
        · omega

theorem withAcct_preserves_consistent (s : St) (who : Account) (f : Acct → Acct) (hc : Consistent s)
    (hsup : ∀ a, (f a).supplierIndex = a.supplierIndex)
    (hbor : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    Consistent (s.withAcct who f) := by
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hall⟩ := hc
  have hsupB' : ((s.withAcct who f).supplyState.block) ≤ ((s.withAcct who f).blockNumber) := by
    have heq1 : ((s.withAcct who f).supplyState.block) = s.supplyState.block := rfl
    have heq2 : ((s.withAcct who f).blockNumber) = s.blockNumber := rfl
    omega
  have hborB' : ((s.withAcct who f).borrowState.block) ≤ ((s.withAcct who f).blockNumber) := by
    have heq1 : ((s.withAcct who f).borrowState.block) = s.borrowState.block := rfl
    have heq2 : ((s.withAcct who f).blockNumber) = s.blockNumber := rfl
    omega
  refine ⟨hsupB', hborB', ?_⟩
  have hall_sup : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
    fun a ha => (hall a ha).1
  have hall_bor : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
    fun a ha => (hall a ha).2
  have heq_sup_idx : ((s.withAcct who f).supplyState.index) = s.supplyState.index := rfl
  have heq_bor_idx : ((s.withAcct who f).borrowState.index) = s.borrowState.index := rfl
  have heq_accts : (s.withAcct who f).accts = s.accts.modify who f := rfl
  have hsup_all : ∀ a ∈ (s.accts.modify who f), a.supplierIndex ≤ s.supplyState.index := by
    apply list_all_modify _ _ _ _ hall_sup
    intro a ha
    rw [hsup a]
    exact hall_sup a ha
  have hbor_all : ∀ a ∈ (s.accts.modify who f), a.borrowerIndex ≤ s.borrowState.index := by
    apply list_all_modify _ _ _ _ hall_bor
    intro a ha
    rw [hbor a]
    exact hall_bor a ha
  intro a ha
  rw [heq_accts] at ha
  rw [heq_sup_idx, heq_bor_idx]
  exact ⟨hsup_all a ha, hbor_all a ha⟩

theorem exec_preserves_consistent (s : St) (op : Op) (hc : Consistent s) :
    Consistent (exec comptroller s op) := by
  cases op with
  | mint who x =>
    unfold exec
    by_cases hw : who < s.accts.length
    · simp [hw]
      cases ht : comptroller s (.supplyHook who) with
      | none =>
        simp
        exact hc
      | some t =>
        simp
        have hdist := req_supply_hook s who t ht
        have hc_t := supplyDistributed_preserves s who t hc hdist
        exact withAcct_preserves_consistent t who _ hc_t (fun a => rfl) (fun a => rfl)
    · simp [hw]
      exact hc
  | redeem who x =>
    unfold exec
    by_cases hw : who < s.accts.length
    · simp [hw]
      cases ht : comptroller s (.supplyHook who) with
      | none =>
        simp
        exact hc
      | some t =>
        simp
        have hdist := req_supply_hook s who t ht
        have hc_t := supplyDistributed_preserves s who t hc hdist
        by_cases hx : x ≤ (t.acct who).supply
        · simp [hx]
          exact withAcct_preserves_consistent t who _ hc_t (fun a => rfl) (fun a => rfl)
        · simp [hx]
          exact hc
    · simp [hw]
      exact hc
  | transfer src dst x =>
    unfold exec
    by_cases h : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · simp [h.1, h.2.1, h.2.2]
      cases ht1 : comptroller s (.supplyHook src) with
      | none =>
        simp
        exact hc
      | some t1 =>
        simp
        have hdist1 := req_supply_hook s src t1 ht1
        have hc_t1 := supplyDistributed_preserves s src t1 hc hdist1
        cases ht2 : comptroller t1 (.supplyHook dst) with
        | none =>
          simp
          exact hc
        | some t2 =>
          simp
          have hdist2 := req_supply_hook t1 dst t2 ht2
          have hc_t2 := supplyDistributed_preserves t1 dst t2 hc_t1 hdist2
          by_cases hx : x ≤ (t2.acct src).supply
          · simp [hx]
            have hc_m1 : Consistent (t2.withAcct src fun a => ({ a with supply := a.supply - x })) :=
              withAcct_preserves_consistent t2 src _ hc_t2 (fun a => rfl) (fun a => rfl)
            exact withAcct_preserves_consistent _ dst _ hc_m1 (fun a => rfl) (fun a => rfl)
          · simp [hx]
            exact hc
    · simp [h]
      exact hc
  | borrow who x =>
    unfold exec
    by_cases hw : who < s.accts.length
    · simp [hw]
      cases ht : comptroller s (.borrowHook who) with
      | none =>
        simp
        exact hc
      | some t =>
        simp
        have hdist := req_borrow_hook s who t ht
        have hc_t := borrowDistributed_preserves s who t hc hdist
        exact withAcct_preserves_consistent t who _ hc_t (fun a => rfl) (fun a => rfl)
    · simp [hw]
      exact hc
  | repay who x =>
    unfold exec
    by_cases hw : who < s.accts.length
    · simp [hw]
      cases ht : comptroller s (.borrowHook who) with
      | none =>
        simp
        exact hc
      | some t =>
        simp
        have hdist := req_borrow_hook s who t ht
        have hc_t := borrowDistributed_preserves s who t hc hdist
        by_cases hx : x ≤ (t.acct who).borrow
        · simp [hx]
          exact withAcct_preserves_consistent t who _ hc_t (fun a => rfl) (fun a => rfl)
        · simp [hx]
          exact hc
    · simp [hw]
      exact hc
  | claim who =>
    unfold exec
    match ht : comptroller s (.claim who) with
    | none =>
      simp [ht, Option.getD_none]
      exact hc
    | some t =>
      simp [ht, Option.getD_some]
      have hcl := req_claim s who t ht
      exact claimed_preserves s who t hc hcl
  | setSpeeds a b =>
    unfold exec
    match ht : comptroller s (.setSpeeds a b) with
    | none =>
      simp [ht, Option.getD_none]
      exact hc
    | some t =>
      simp [ht, Option.getD_some]
      have hss := req_set_speeds s a b t ht
      exact speedsSet_preserves s a b t hc hss
  | advance k =>
    unfold exec
    exact advance_preserves_consistent s k hc
  | drip x =>
    unfold exec
    exact hc

theorem upgrade_consistent (L : Legacy) (h : L.WellFormed) : Consistent (upgrade L) := by
  unfold Legacy.WellFormed at h
  obtain ⟨hsupStart, hsupLe, hborStart, hborLe, hsupB, hborB, hall⟩ := h
  unfold Consistent upgrade initSide
  simp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases hs : L.supplyIndex = 0
    · simp [hs]
    · simp [hs]
      exact hsupB
  · by_cases hb : L.borrowIndex = 0
    · simp [hb]
    · simp [hb]
      exact hborB
  · intro a ha
    have hsup_a := (hall a ha).1
    have hbor_a := (hall a ha).2
    constructor
    · by_cases hs : L.supplyIndex = 0
      · simp [hs]
        have ha0 : a.supplierIndex = 0 := by omega
        rw [ha0]
        exact Nat.zero_le _
      · simp [hs]
        exact hsup_a
    · by_cases hb : L.borrowIndex = 0
      · simp [hb]
        have ha0 : a.borrowerIndex = 0 := by omega
        rw [ha0]
        exact Nat.zero_le _
      · simp [hb]
        exact hbor_a

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
