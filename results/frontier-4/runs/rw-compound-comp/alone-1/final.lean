import CompRewards.Spec
/-!
Fixed port of Compound Comptroller Proposal 62 distribution.
Fix: `distributeSupplierComp` / `distributeBorrowerComp` use
`compInitialIndex ≤ index` (spec `accrualStart`) instead of `index > compInitialIndex`.
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

/-- `distributeSupplierComp(cToken, supplier)` (fixed: `≤`). -/
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

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)` (fixed: `≤`). -/
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

/-- The supply branch of `setCompSpeedInternal`. -/
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

/-- `setCompSpeedInternal(cToken, supplySpeed, borrowSpeed)`. -/
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

-- Helper lemmas (effects)
theorem subChecked_some : subChecked a b = some d ↔ b ≤ a ∧ d = a - b := by
  unfold subChecked
  constructor
  · intro h
    by_cases hb : b ≤ a
    · simp [hb] at h
      exact ⟨hb, h.symm ▸ rfl⟩
    · simp [hb] at h
  · rintro ⟨hb, rfl⟩
    simp [hb]

theorem subChecked_none : subChecked a b = none ↔ ¬ b ≤ a := by
  unfold subChecked
  by_cases hb : b ≤ a <;> simp [hb]

theorem accrueSupply_some (s : St) (s' : St)
    (h : updateCompSupplyIndex s = some s') :
    s.supplyState.block ≤ s.blockNumber ∧
    s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.supplyState.block =
        some (s.blockNumber - s.supplyState.block) := by
      unfold subChecked
      simp [hb]
    unfold updateCompSupplyIndex at h
    rw [hsub] at h
    simp only at h
    by_cases hc : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      refine ⟨hb, ?_⟩
      unfold accrueSide
      have hpos : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed :=
        ⟨hc.1, hc.2⟩
      by_cases ht : 0 < totalSupply s
      · have hcond : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s := ⟨hpos.1, hpos.2, ht⟩
        rw [if_pos hcond]
        have ht2 : totalSupply s > 0 := ht
        unfold fraction
        rw [if_pos ht2]
      · have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := by omega
        rw [if_neg hcond]
        have ht2 : ¬ totalSupply s > 0 := by omega
        unfold fraction
        rw [if_neg ht2]
        simp
    · rw [if_neg hc] at h
      by_cases hd0 : (s.blockNumber - s.supplyState.block) > 0
      · rw [if_pos hd0] at h
        obtain rfl := Option.some_inj.mp h
        refine ⟨hb, ?_⟩
        unfold accrueSide
        have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := by
          intro hcon
          exact hc ⟨by omega, hcon.2.1⟩
        rw [if_neg hneg]
      · rw [if_neg hd0] at h
        obtain rfl := Option.some_inj.mp h
        refine ⟨hb, ?_⟩
        unfold accrueSide
        have hz : s.blockNumber - s.supplyState.block = 0 := by omega
        have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := by omega
        rw [if_neg hneg]
        have heq : s.blockNumber = s.supplyState.block := by omega
        cases s with
        | mk bn sup bor res accts =>
          simp at heq ⊢
          simp [heq]
  · have hsub : subChecked s.blockNumber s.supplyState.block = none := by
      unfold subChecked
      simp [hb]
    unfold updateCompSupplyIndex at h
    rw [hsub] at h
    simp at h

theorem accrueBorrow_some (s : St) (s' : St)
    (h : updateCompBorrowIndex s = some s') :
    s.borrowState.block ≤ s.blockNumber ∧
    s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · have hsub : subChecked s.blockNumber s.borrowState.block =
        some (s.blockNumber - s.borrowState.block) := by
      unfold subChecked
      simp [hb]
    unfold updateCompBorrowIndex at h
    rw [hsub] at h
    simp only at h
    by_cases hc : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
    · rw [if_pos hc] at h
      obtain rfl := Option.some_inj.mp h
      refine ⟨hb, ?_⟩
      unfold accrueSide
      have hpos : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed :=
        ⟨hc.1, hc.2⟩
      by_cases ht : 0 < totalBorrows s
      · have hcond : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s := ⟨hpos.1, hpos.2, ht⟩
        rw [if_pos hcond]
        have ht2 : totalBorrows s > 0 := ht
        unfold fraction
        rw [if_pos ht2]
      · have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := by omega
        rw [if_neg hcond]
        have ht2 : ¬ totalBorrows s > 0 := by omega
        unfold fraction
        rw [if_neg ht2]
        simp
    · rw [if_neg hc] at h
      by_cases hd0 : (s.blockNumber - s.borrowState.block) > 0
      · rw [if_pos hd0] at h
        obtain rfl := Option.some_inj.mp h
        refine ⟨hb, ?_⟩
        unfold accrueSide
        have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := by
          intro hcon
          exact hc ⟨by omega, hcon.2.1⟩
        rw [if_neg hneg]
      · rw [if_neg hd0] at h
        obtain rfl := Option.some_inj.mp h
        refine ⟨hb, ?_⟩
        unfold accrueSide
        have hz : s.blockNumber - s.borrowState.block = 0 := by omega
        have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := by omega
        rw [if_neg hneg]
        have heq : s.blockNumber = s.borrowState.block := by omega
        cases s with
        | mk bn sup bor res accts =>
          simp at heq ⊢
          simp [heq]
  · have hsub : subChecked s.blockNumber s.borrowState.block = none := by
      unfold subChecked
      simp [hb]
    unfold updateCompBorrowIndex at h
    rw [hsub] at h
    simp at h

theorem start_supply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hz : (s.acct who).supplierIndex = 0
  · simp [hz]
  · simp [hz]

theorem start_borrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hz : (s.acct who).borrowerIndex = 0
  · simp [hz]
  · simp [hz]

theorem modify_congr {α : Type} (d : α) (l : List α) (i : Nat) (f g : α → α)
    (h : f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    simp
  | cons x xs ih =>
    cases i with
    | zero =>
      simp at h ⊢
      rw [h]
    | succ n =>
      simp at h ⊢
      rw [ih _ h]

theorem distributeSupply_some (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    start_supply_eq s who
  unfold distributeSupplierComp at h
  simp only at h
  rw [hstart] at h
  have hsub : (if accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index then
      some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)
      else none) =
      subChecked s.supplyState.index
        (accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    unfold subChecked
    simp
  rw [←hsub] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [hle, ite_true] at h
    obtain rfl := Option.some_inj.mp h
    refine ⟨hle, ?_⟩
    unfold St.withAcct
    congr 1
    apply modify_congr noAcct
    simp only [St.acct, creditFor, mulDouble]
  · simp [hle] at h

theorem distributeBorrow_some (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    start_borrow_eq s who
  unfold distributeBorrowerComp at h
  simp only at h
  rw [hstart] at h
  have hsub : (if accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index then
      some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      else none) =
      subChecked s.borrowState.index
        (accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    unfold subChecked
    simp
  rw [←hsub] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ite_true] at h
    obtain rfl := Option.some_inj.mp h
    refine ⟨hle, ?_⟩
    unfold St.withAcct
    congr 1
    apply modify_congr noAcct
    simp only [St.acct, creditFor, mulDouble]
  · simp [hle] at h

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, Nat.le_add_right]
  · simp [h]

theorem accrualStart_le_of_le {recorded index : Nat} (hle : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hz : recorded = 0
  · simp only [hz, ite_true]
    by_cases hge : compInitialIndex ≤ index
    · simp only [hge, ite_true]
    · simp only [hge, ite_false]
      exact Nat.zero_le _
  · simp [hz, hle]

theorem updateSupply_succeeds (s : St) (hb : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' := by
  have hsub : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompSupplyIndex
  rw [hsub]
  simp only
  by_cases hc : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hc]
    exact ⟨_, rfl⟩
  · rw [if_neg hc]
    by_cases hd0 : (s.blockNumber - s.supplyState.block) > 0
    · rw [if_pos hd0]
      exact ⟨_, rfl⟩
    · rw [if_neg hd0]
      exact ⟨_, rfl⟩

theorem updateBorrow_succeeds (s : St) (hb : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' := by
  have hsub : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hb]
  unfold updateCompBorrowIndex
  rw [hsub]
  simp only
  by_cases hc : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hc]
    exact ⟨_, rfl⟩
  · rw [if_neg hc]
    by_cases hd0 : (s.blockNumber - s.borrowState.block) > 0
    · rw [if_pos hd0]
      exact ⟨_, rfl⟩
    · rw [if_neg hd0]
      exact ⟨_, rfl⟩

theorem distributeSupply_succeeds (s : St) (who : Account)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    start_supply_eq s who
  unfold distributeSupplierComp
  simp only
  rw [hstart]
  have hsub : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    unfold subChecked
    simp [hle]
  rw [hsub]
  exact ⟨_, rfl⟩

theorem distributeBorrow_succeeds (s : St) (who : Account)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    start_borrow_eq s who
  unfold distributeBorrowerComp
  simp only
  rw [hstart]
  have hsub : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    unfold subChecked
    simp [hle]
  rw [hsub]
  exact ⟨_, rfl⟩

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  dsimp only
  by_cases h : (s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve
  · have hc : 0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve := by
      omega
    rw [if_pos h, if_pos hc]
    have hmod : (s.accts.modify who fun a =>
        ({ a with accrued := (0 : Nat), wallet := a.wallet + (s.accts.getD who noAcct).accrued } : Acct)) =
        (s.accts.modify who fun a => ({ a with accrued := (0 : Nat), wallet := a.wallet + a.accrued } : Acct)) := by
      apply modify_congr noAcct
      rfl
    rw [hmod]
  · have hc : ¬ (0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve) := by
      omega
    rw [if_neg h, if_neg hc]

theorem supplyHook_ok (s s' : St) (who : Account)
    (h : comptroller s (.supplyHook who) = some s') : SupplyDistributed s who s' := by
  unfold comptroller at h
  simp only at h
  obtain ⟨s1, hs1, hs2⟩ : ∃ s1, updateCompSupplyIndex s = some s1 ∧
      distributeSupplierComp s1 who = some s' := by
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some s1 => exact ⟨s1, rfl, by simpa [hu] using h⟩
  obtain ⟨hblock, hs1eq⟩ := accrueSupply_some s s1 hs1
  obtain ⟨hle, hs2eq⟩ := distributeSupply_some s1 who s' hs2
  have hsup1 : s1.supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [hs1eq]
  have hacct1 : s1.acct who = s.acct who := by
    rw [hs1eq]; rfl
  have htot1 : totalSupply s1 = totalSupply s := by
    rw [hs1eq]; rfl
  refine ⟨hblock, ?_, ?_⟩
  · rw [←hsup1, ←hacct1]
    exact hle
  · rw [hs2eq, hs1eq]

theorem borrowHook_ok (s s' : St) (who : Account)
    (h : comptroller s (.borrowHook who) = some s') : BorrowDistributed s who s' := by
  unfold comptroller at h
  simp only at h
  obtain ⟨s1, hs1, hs2⟩ : ∃ s1, updateCompBorrowIndex s = some s1 ∧
      distributeBorrowerComp s1 who = some s' := by
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some s1 => exact ⟨s1, rfl, by simpa [hu] using h⟩
  obtain ⟨hblock, hs1eq⟩ := accrueBorrow_some s s1 hs1
  obtain ⟨hle, hs2eq⟩ := distributeBorrow_some s1 who s' hs2
  have hbor1 : s1.borrowState.index =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [hs1eq]
  have hacct1 : s1.acct who = s.acct who := by
    rw [hs1eq]; rfl
  refine ⟨hblock, ?_, ?_⟩
  · rw [←hbor1, ←hacct1]
    exact hle
  · rw [hs2eq, hs1eq]

theorem req_supply_hook : SupplyHookEffects comptroller :=
  fun s who s' h => supplyHook_ok s s' who h

theorem req_borrow_hook : BorrowHookEffects comptroller :=
  fun s who s' h => borrowHook_ok s s' who h

theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : x.bind f = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases hx : x with
  | none => simp [hx] at h
  | some a => exact ⟨a, rfl, by simpa [hx] using h⟩

theorem bind_some2 {α β γ : Type} {x : Option α} {f : α → Option β} {g : β → Option γ} {y : γ}
    (h : (x.bind fun a => (f a).bind g) = some y) :
    ∃ a b, x = some a ∧ f a = some b ∧ g b = some y := by
  obtain ⟨a, ha, hrest⟩ := bind_some h
  obtain ⟨b, hb, hg⟩ := bind_some hrest
  exact ⟨a, b, ha, hb, hg⟩

theorem claim_ok (s s' : St) (who : Account)
    (h : comptroller s (.claim who) = some s') : Claimed s who s' := by
  unfold comptroller claimComp at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  -- h : ((updateBorrow s).bind fun b1 => ((distributeBorrow b1).bind fun m1 =>
  --       ((updateSupply m1).bind fun u1 => ((distributeSupply u1).bind fun m2 =>
  --         some (grant m2))))) = some s'
  -- Use manual destructuring via bind_some repeatedly
  obtain ⟨b1, hb1, hrest⟩ := bind_some (α := St) (β := St) h
  obtain ⟨m1, hm1, hrest2⟩ := bind_some hrest
  obtain ⟨u1, hu1, hrest3⟩ := bind_some hrest2
  obtain ⟨m2, hm2, hgrant⟩ : ∃ m2, distributeSupplierComp u1 who = some m2 ∧
      (grantCompInternal m2 who = s') := by
    obtain ⟨m2, hm2, hg⟩ := bind_some hrest3
    exact ⟨m2, hm2, Option.some_inj.mp hg⟩
  obtain ⟨hblockB, hb1eq⟩ := accrueBorrow_some s b1 hb1
  obtain ⟨hleB, hm1eq⟩ := distributeBorrow_some b1 who m1 hm1
  obtain ⟨hblockS, hu1eq⟩ := accrueSupply_some m1 u1 hu1
  obtain ⟨hleS, hm2eq⟩ := distributeSupply_some u1 who m2 hm2
  have hborIdx : b1.borrowState.index =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hb1eq]
  have hacctB : b1.acct who = s.acct who := by rw [hb1eq]; rfl
  have hsupIdx : u1.supplyState.index =
      (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by rw [hu1eq]
  have hacctU : u1.acct who = m1.acct who := by rw [hu1eq]; rfl
  have hBorrow : BorrowDistributed s who m1 := by
    refine ⟨hblockB, ?_, ?_⟩
    · rw [←hborIdx, ←hacctB]; exact hleB
    · rw [hm1eq, hb1eq]
  have hSupply : SupplyDistributed m1 who m2 := by
    refine ⟨hblockS, ?_, ?_⟩
    · have : u1.supplyState.index =
          (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := hsupIdx
      have hac : u1.acct who = m1.acct who := hacctU
      rw [←this, ←hac]; exact hleS
    · rw [hm2eq, hu1eq]
  refine ⟨m1, m2, hBorrow, hSupply, ?_⟩
  rw [←hgrant, grant_eq]

theorem req_claim : ClaimEffects comptroller :=
  fun s who s' h => claim_ok s s' who h

theorem setSupply_some (s s' : St) (a : Nat)
    (h : setSupplySpeed s a = some s') :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s' = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    obtain rfl := h
    refine ⟨fun hne => absurd heq hne, ?_⟩
    simp [heq]
  · simp [heq] at h
    obtain ⟨u, hu, rfl⟩ : ∃ u, updateCompSupplyIndex s = some u ∧
        ({ u with supplyState := { u.supplyState with speed := a } } = s') := by
      cases hu : updateCompSupplyIndex s with
      | none => simp [hu] at h
      | some u =>
        have : ({ u with supplyState := { u.supplyState with speed := a } } = s') := by
          simpa [hu] using h
        exact ⟨u, rfl, this⟩
    obtain ⟨hblock, hueq⟩ := accrueSupply_some s u hu
    refine ⟨fun _ => hblock, ?_⟩
    rw [hueq]
    simp [heq]

theorem setBorrow_some (s s' : St) (b : Nat)
    (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s' = { s with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    obtain rfl := h
    refine ⟨fun hne => absurd heq hne, ?_⟩
    simp [heq]
  · simp [heq] at h
    obtain ⟨u, hu, rfl⟩ : ∃ u, updateCompBorrowIndex s = some u ∧
        ({ u with borrowState := { u.borrowState with speed := b } } = s') := by
      cases hu : updateCompBorrowIndex s with
      | none => simp [hu] at h
      | some u =>
        have : ({ u with borrowState := { u.borrowState with speed := b } } = s') := by
          simpa [hu] using h
        exact ⟨u, rfl, this⟩
    obtain ⟨hblock, hueq⟩ := accrueBorrow_some s u hu
    refine ⟨fun _ => hblock, ?_⟩
    rw [hueq]
    simp [heq]

theorem setSpeeds_ok (s s' : St) (a b : Nat)
    (h : comptroller s (.setSpeeds a b) = some s') : SpeedsSet s a b s' := by
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  obtain ⟨s1, hs1, hs2⟩ := bind_some h
  obtain ⟨hcondS, hs1eq⟩ := setSupply_some s s1 a hs1
  obtain ⟨hcondB1, hs2eq⟩ := setBorrow_some s1 s' b hs2
  have hs1bor : s1.borrowState = s.borrowState := by rw [hs1eq]
  have hs1bn : s1.blockNumber = s.blockNumber := by rw [hs1eq]
  have htotB : totalBorrows s1 = totalBorrows s := by rw [hs1eq]; rfl
  have hcondB : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
    intro hne
    have hne1 : s1.borrowState.speed ≠ b := by rw [hs1bor]; exact hne
    have hle := hcondB1 hne1
    rw [hs1bor, hs1bn] at hle
    exact hle
  refine ⟨hcondS, hcondB, ?_⟩
  rw [hs2eq, htotB, hs1eq]

theorem req_set_speeds : SetSpeedsEffects comptroller :=
  fun s a b s' h => setSpeeds_ok s s' a b h

theorem getD_modify_preserve {α β : Type} (p : α → β) (d : α) (l : List α) (i : Nat) (f : α → α)
    (hpres : ∀ a, p (f a) = p a) : p ((l.modify i f).getD i d) = p (l.getD i d) := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ n => rfl
  | cons x xs ih =>
    cases i with
    | zero => exact hpres x
    | succ n => exact ih n

theorem acct_supplier_preserved (s : St) (who : Account) (f : Acct → Acct)
    (hpres : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.accts.modify who f).getD who noAcct).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.acct
  exact getD_modify_preserve Acct.supplierIndex noAcct s.accts who f hpres

theorem acct_borrower_preserved (s : St) (who : Account) (f : Acct → Acct)
    (hpres : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((s.accts.modify who f).getD who noAcct).borrowerIndex = (s.acct who).borrowerIndex := by
  unfold St.acct
  exact getD_modify_preserve Acct.borrowerIndex noAcct s.accts who f hpres

theorem acct_supply_preserved (s : St) (who : Account) (f : Acct → Acct)
    (hpres : ∀ a, (f a).supply = a.supply) :
    ((s.accts.modify who f).getD who noAcct).supply = (s.acct who).supply := by
  unfold St.acct
  exact getD_modify_preserve Acct.supply noAcct s.accts who f hpres

theorem acct_borrow_preserved (s : St) (who : Account) (f : Acct → Acct)
    (hpres : ∀ a, (f a).borrow = a.borrow) :
    ((s.accts.modify who f).getD who noAcct).borrow = (s.acct who).borrow := by
  unfold St.acct
  exact getD_modify_preserve Acct.borrow noAcct s.accts who f hpres

theorem getD_prop_of_mem {α : Type} (P : α → Prop) (d : α) (l : List α) (i : Nat)
    (hmem : ∀ a ∈ l, P a) (hd : P d) : P (l.getD i d) := by
  induction l generalizing i with
  | nil => exact hd
  | cons x xs ih =>
    cases i with
    | zero => exact hmem x (by simp)
    | succ n =>
      apply ih
      intro a ha
      exact hmem a (by simp [ha])

theorem mem_getD_le_supply (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  have hP : ∀ a ∈ s.accts, (a.supplierIndex ≤ s.supplyState.index) := fun a ha => (hmem a ha).1
  have hd : (noAcct.supplierIndex ≤ s.supplyState.index) := by simp [noAcct]
  have := getD_prop_of_mem (fun a => a.supplierIndex ≤ s.supplyState.index) noAcct s.accts who hP hd
  simpa [St.acct] using this

theorem mem_getD_le_borrow (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  have hP : ∀ a ∈ s.accts, (a.borrowerIndex ≤ s.borrowState.index) := fun a ha => (hmem a ha).2
  have hd : (noAcct.borrowerIndex ≤ s.borrowState.index) := by simp [noAcct]
  have := getD_prop_of_mem (fun a => a.borrowerIndex ≤ s.borrowState.index) noAcct s.accts who hP hd
  simpa [St.acct] using this

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsupB, hborB, hmem⟩ := hc
  cases c with
  | supplyHook who =>
    obtain ⟨s1, hs1⟩ := updateSupply_succeeds s hsupB
    obtain ⟨_, hs1eq⟩ := accrueSupply_some s s1 hs1
    have hacct1 : s1.acct who = s.acct who := by rw [hs1eq]; rfl
    have hidx_ge : s.supplyState.index ≤ s1.supplyState.index := by
      rw [hs1eq]
      exact accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
    have hrec : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
      rw [hacct1]
      have h0 := mem_getD_le_supply s who ⟨hsupB, hborB, hmem⟩
      omega
    have hle := accrualStart_le_of_le hrec
    obtain ⟨s', hs2⟩ := distributeSupply_succeeds s1 who hle
    have h : comptroller s (.supplyHook who) = some s' := by
      unfold comptroller
      simp [hs1, hs2]
    simp [h]
  | borrowHook who =>
    obtain ⟨s1, hs1⟩ := updateBorrow_succeeds s hborB
    obtain ⟨_, hs1eq⟩ := accrueBorrow_some s s1 hs1
    have hacct1 : s1.acct who = s.acct who := by rw [hs1eq]; rfl
    have hidx_ge : s.borrowState.index ≤ s1.borrowState.index := by
      rw [hs1eq]
      exact accrueSide_index_ge s.borrowState s.blockNumber (totalBorrows s)
    have hrec : (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
      rw [hacct1]
      have h0 := mem_getD_le_borrow s who ⟨hsupB, hborB, hmem⟩
      omega
    have hle := accrualStart_le_of_le hrec
    obtain ⟨s', hs2⟩ := distributeBorrow_succeeds s1 who hle
    have h : comptroller s (.borrowHook who) = some s' := by
      unfold comptroller
      simp [hs1, hs2]
    simp [h]
  | claim who =>
    -- borrow part
    obtain ⟨b1, hb1⟩ := updateBorrow_succeeds s hborB
    obtain ⟨_, hb1eq⟩ := accrueBorrow_some s b1 hb1
    have hacctB : b1.acct who = s.acct who := by rw [hb1eq]; rfl
    have hidxB_ge : s.borrowState.index ≤ b1.borrowState.index := by
      rw [hb1eq]
      exact accrueSide_index_ge s.borrowState s.blockNumber (totalBorrows s)
    have hrecB : (b1.acct who).borrowerIndex ≤ b1.borrowState.index := by
      rw [hacctB]
      have h0 := mem_getD_le_borrow s who ⟨hsupB, hborB, hmem⟩
      omega
    have hleB := accrualStart_le_of_le hrecB
    obtain ⟨m1, hm1⟩ := distributeBorrow_succeeds b1 who hleB
    obtain ⟨_, hm1eq⟩ := distributeBorrow_some b1 who m1 hm1
    -- m1 supply fields equal s
    have hm1sup : m1.supplyState = s.supplyState := by rw [hm1eq, hb1eq]
    have hm1bn : m1.blockNumber = s.blockNumber := by rw [hm1eq, hb1eq]
    have hm1supAcct : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have h1 : ((b1.accts.modify who (fun a => { a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index })).getD who noAcct).supplierIndex = (b1.acct who).supplierIndex := by
        have hpres : ∀ a : Acct, ({ a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index }.supplierIndex = a.supplierIndex) := fun a => rfl
        have := getD_modify_preserve Acct.supplierIndex noAcct b1.accts who (fun a => { a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index }) hpres
        simpa [St.acct] using this
      have h2 : (b1.acct who).supplierIndex = (s.acct who).supplierIndex := by rw [hb1eq]; rfl
      have hm1acct : m1.acct who = ((b1.accts.modify who (fun a => { a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index })).getD who noAcct) := by rw [hm1eq]; rfl
      rw [hm1acct, h1, h2]
    -- supply update on m1
    have hsupB_m1 : m1.supplyState.block ≤ m1.blockNumber := by
      rw [hm1sup, hm1bn]; exact hsupB
    obtain ⟨u1, hu1⟩ := updateSupply_succeeds m1 hsupB_m1
    obtain ⟨_, hu1eq⟩ := accrueSupply_some m1 u1 hu1
    have hu1acct : u1.acct who = m1.acct who := by rw [hu1eq]; rfl
    have hidxS_ge : m1.supplyState.index ≤ u1.supplyState.index := by
      rw [hu1eq]
      exact accrueSide_index_ge m1.supplyState m1.blockNumber (totalSupply m1)
    have hrecS : (u1.acct who).supplierIndex ≤ u1.supplyState.index := by
      rw [hu1acct]
      have h0 : (s.acct who).supplierIndex ≤ s.supplyState.index :=
        mem_getD_le_supply s who ⟨hsupB, hborB, hmem⟩
      have h1 : (m1.acct who).supplierIndex ≤ m1.supplyState.index := by
        rw [hm1supAcct, hm1sup]
        exact h0
      omega
    have hleS := accrualStart_le_of_le hrecS
    obtain ⟨m2, hm2⟩ := distributeSupply_succeeds u1 who hleS
    have h : comptroller s (.claim who) = some (grantCompInternal m2 who) := by
      unfold comptroller claimComp
      simp [hb1, hm1, hu1, hm2]
    simp [h]
  | setSpeeds a b =>
    obtain ⟨s1, hs1⟩ : ∃ s1, setSupplySpeed s a = some s1 := by
      unfold setSupplySpeed
      by_cases heq : s.supplyState.speed = a
      · exact ⟨s, by simp [heq]⟩
      · have ⟨u, hu⟩ := updateSupply_succeeds s hsupB
        exact ⟨{ u with supplyState := { u.supplyState with speed := a } },
          by simp [heq, hu]⟩
    obtain ⟨s', hs2⟩ : ∃ s', setBorrowSpeed s1 b = some s' := by
      have hborB1 : s1.borrowState.block ≤ s1.blockNumber := by
        obtain ⟨_, hs1eq⟩ := setSupply_some s s1 a hs1
        rw [hs1eq]
        exact hborB
      unfold setBorrowSpeed
      by_cases heq : s1.borrowState.speed = b
      · exact ⟨s1, by simp [heq]⟩
      · have ⟨u, hu⟩ := updateBorrow_succeeds s1 hborB1
        exact ⟨{ u with borrowState := { u.borrowState with speed := b } },
          by simp [heq, hu]⟩
    have h : comptroller s (.setSpeeds a b) = some s' := by
      unfold comptroller setCompSpeedInternal
      simp [hs1, hs2]
    simp [h]

theorem div_mul_le (m n : Nat) : (m / n) * n ≤ m := by
  have h := Nat.div_add_mod m n
  have hle : n * (m / n) ≤ m := by
    have h1 : n * (m / n) ≤ n * (m / n) + m % n := Nat.le_add_right _ _
    rw [h] at h1
    exact h1
  simpa [Nat.mul_comm] using hle

theorem creditFor_mul_le (units start index : Nat) :
    creditFor units start index * doubleScale ≤ units * (index - start) := by
  unfold creditFor
  have h := div_mul_le (units * (index - start)) doubleScale
  simpa using h

theorem doubleScale_pos : 0 < doubleScale := by unfold doubleScale; omega

theorem accrueDelta_le (delta speed total : Nat) :
    (if 0 < total then (delta * speed * doubleScale / total) else 0) * total ≤ delta * speed * doubleScale := by
  by_cases ht : 0 < total
  · simp [ht]
    have h := div_mul_le (delta * speed * doubleScale) total
    simpa [Nat.mul_comm, Nat.mul_assoc] using h
  · simp [ht]

theorem accrueIndex_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index = sd.index + (if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then (now - sd.block) * sd.speed * doubleScale / total else 0) := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem sum_map_add (l : List Acct) (f g : Acct → Nat) :
    ((l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem map_sum_modify_eq (l : List Acct) (i : Nat) (f : Acct → Acct) (g : Acct → Nat)
    (hpres : ∀ a, g (f a) = g a) : (((l.modify i f).map g).sum = (l.map g).sum) := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ n => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      show g (f x) + (xs.map g).sum = g x + (xs.map g).sum
      rw [hpres x]
    | succ n =>
      show g x + (((xs.modify n f).map g).sum) = g x + ((xs.map g).sum)
      rw [ih n]

theorem map_sum_modify_le (l : List Acct) (i : Nat) (f : Acct → Acct) (g : Acct → Nat)
    (hpres : ∀ a, g (f a) ≤ g a) : (((l.modify i f).map g).sum ≤ (l.map g).sum) := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => exact Nat.le_refl _
    | succ n => exact Nat.le_refl _
  | cons x xs ih =>
    cases i with
    | zero =>
      show g (f x) + (xs.map g).sum ≤ g x + (xs.map g).sum
      have h1 : g (f x) ≤ g x := hpres x
      omega
    | succ n =>
      show g x + (((xs.modify n f).map g).sum) ≤ g x + ((xs.map g).sum)
      have hle : (((xs.modify n f).map g).sum ≤ (xs.map g).sum) := ih n
      omega

theorem modify_eq_self_of_ge (l : List Acct) (i : Nat) (f : Acct → Acct)
    (h : l.length ≤ i) : l.modify i f = l := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ n => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.length_cons] at h
      omega
    | succ n =>
      simp only [List.length_cons] at h
      have hlt : xs.length ≤ n := by omega
      have hih := ih n hlt
      show x :: xs.modify n f = x :: xs
      rw [hih]

theorem sum_modify_add_of_lt (l : List Acct) (i : Nat) (f : Acct → Acct) (g : Acct → Nat) (d : Acct)
    (hlt : i < l.length) :
    (((l.modify i f).map g).sum + g (l.getD i d) = (l.map g).sum + g (f (l.getD i d))) := by
  induction l generalizing i with
  | nil =>
    simp only [List.length_nil] at hlt
    omega
  | cons x xs ih =>
    cases i with
    | zero =>
      show g (f x) + (xs.map g).sum + g x = (g x + (xs.map g).sum) + g (f x)
      omega
    | succ n =>
      simp only [List.length_cons] at hlt
      have hlt' : n < xs.length := by omega
      have hih := ih n hlt'
      show g x + (((xs.modify n f).map g).sum) + g (xs.getD n d) = (g x + (xs.map g).sum) + g (f (xs.getD n d))
      have h1 : (((xs.modify n f).map g).sum + g (xs.getD n d) = (xs.map g).sum + g (f (xs.getD n d))) := hih
      omega

theorem getD_modify_ne {α : Type} (d : α) (l : List α) (i j : Nat) (f : α → α)
    (hne : i ≠ j) : ((l.modify j f).getD i d = l.getD i d) := by
  induction l generalizing i j with
  | nil =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ m => rfl
    | succ n =>
      cases j with
      | zero => rfl
      | succ m => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ m => rfl
    | succ n =>
      cases j with
      | zero => rfl
      | succ m =>
        show (x :: xs.modify m f).getD (n + 1) d = (x :: xs).getD (n + 1) d
        have hne' : n ≠ m := by omega
        have hih := ih n m hne'
        -- Both reduce to xs.getD n d vs (xs.modify m f).getD n d
        show (xs.modify m f).getD n d = xs.getD n d
        exact hih

theorem le_sum_of_mem (l : List Nat) (a : Nat) (hmem : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    simp at hmem
    cases hmem with
    | inl heq =>
      rw [heq]
      simp
    | inr hmem =>
      have hih := ih hmem
      simp
      omega

theorem supply_getD_le_sum (l : List Acct) (i : Nat) :
    (l.getD i noAcct).supply ≤ (l.map Acct.supply).sum := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => simp [noAcct]
    | succ n => simp [noAcct]
  | cons x xs ih =>
    cases i with
    | zero =>
      show x.supply ≤ (x.supply + (xs.map Acct.supply).sum)
      omega
    | succ n =>
      show (xs.getD n noAcct).supply ≤ (x.supply + (xs.map Acct.supply).sum)
      have hih := ih n
      omega

theorem borrow_getD_le_sum (l : List Acct) (i : Nat) :
    (l.getD i noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => simp [noAcct]
    | succ n => simp [noAcct]
  | cons x xs ih =>
    cases i with
    | zero =>
      show x.borrow ≤ (x.borrow + (xs.map Acct.borrow).sum)
      omega
    | succ n =>
      show (xs.getD n noAcct).borrow ≤ (x.borrow + (xs.map Acct.borrow).sum)
      have hih := ih n
      omega

theorem supply_le_total (s : St) (who : Account) : (s.acct who).supply ≤ totalSupply s := by
  unfold totalSupply St.acct
  exact supply_getD_le_sum s.accts who

theorem borrow_le_total (s : St) (who : Account) : (s.acct who).borrow ≤ totalBorrows s := by
  unfold totalBorrows St.acct
  exact borrow_getD_le_sum s.accts who

def pendingSupplyTerm (idx : Nat) (a : Acct) : Nat :=
  a.supply * (idx - accrualStart a.supplierIndex idx)

def pendingBorrowTerm (idx : Nat) (a : Acct) : Nat :=
  a.borrow * (idx - accrualStart a.borrowerIndex idx)

def pendingSupplySum (s : St) : Nat :=
  (s.accts.map (pendingSupplyTerm s.supplyState.index)).sum

def pendingBorrowSum (s : St) : Nat :=
  (s.accts.map (pendingBorrowTerm s.borrowState.index)).sum

def unindexedSupply (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def unindexedBorrow (s : St) : Nat :=
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def globalPot (s : St) : Nat :=
  s.credited * doubleScale + pendingSupplySum s + pendingBorrowSum s +
    (unindexedSupply s + unindexedBorrow s) * doubleScale

theorem mem_modify_forall {α : Type} (P : α → Prop) (l : List α) (i : Nat) (f : α → α) (d : α)
    (hold : ∀ a ∈ l, P a) (hnew : P (f (l.getD i d))) : ∀ a ∈ l.modify i f, P a := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero =>
      intro a ha
      simp at ha
    | succ n =>
      intro a ha
      simp at ha
  | cons x xs ih =>
    cases i with
    | zero =>
      intro a ha
      simp only [List.mem_cons] at ha
      cases ha with
      | inl heq =>
        rw [heq]
        simpa using hnew
      | inr hmem =>
        exact hold a (by simp [hmem])
    | succ n =>
      intro a ha
      simp only [List.mem_cons] at ha ⊢
      cases ha with
      | inl heq =>
        rw [heq]
        exact hold x (by simp)
      | inr hmem =>
        have hxs : ∀ a ∈ xs, P a := fun a ha => hold a (by simp [ha])
        have hget : (x :: xs).getD (n + 1) d = xs.getD n d := rfl
        have hnew' : P (f (xs.getD n d)) := by rw [←hget]; exact hnew
        exact ih n hxs hnew' a hmem

theorem consistent_supply_distrib (s : St) (who : Account) (s' : St)
    (hc : Consistent s) (h : SupplyDistributed s who s') : Consistent s' := by
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hmem⟩ := hc
  obtain ⟨hblock, hle, heq⟩ := h
  rw [heq]
  simp only
  refine ⟨?_, ?_, ?_⟩
  · have hbn : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber :=
      accrueSide_block s.supplyState s.blockNumber (totalSupply s)
    simp [hbn]
  · exact hborB
  · have hP : ∀ a ∈ s.accts, (a.supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧ a.borrowerIndex ≤ s.borrowState.index) := by
      intro a ha
      have hsup := (hmem a ha).1
      have hbor := (hmem a ha).2
      have hge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
        accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
      exact ⟨by omega, hbor⟩
    have hnew : ((fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) (s.accts.getD who noAcct)).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧ ((fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) (s.accts.getD who noAcct)).borrowerIndex ≤ s.borrowState.index := by
      constructor
      · simp
      · have hbor_old : (s.accts.getD who noAcct).borrowerIndex ≤ s.borrowState.index := by
          have hP2 : ∀ a ∈ s.accts, (a.borrowerIndex ≤ s.borrowState.index) := fun a ha => (hmem a ha).2
          have hd : noAcct.borrowerIndex ≤ s.borrowState.index := by simp [noAcct]
          have := getD_prop_of_mem (fun a => a.borrowerIndex ≤ s.borrowState.index) noAcct s.accts who hP2 hd
          simpa [St.acct] using this
        simpa using hbor_old
    exact mem_modify_forall (fun a => a.supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧ a.borrowerIndex ≤ s.borrowState.index) s.accts who _ noAcct hP hnew _

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
