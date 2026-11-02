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

/-- `distributeSupplierComp(cToken, supplier)`. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  match subChecked s.supplyState.index
    (if (s.acct supplier).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct supplier).supplierIndex) with
  | none => none
  | some deltaIndex =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct supplier).supply deltaIndex })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  match subChecked s.borrowState.index
    (if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct borrower).borrowerIndex) with
  | none => none
  | some deltaIndex =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct borrower).borrow deltaIndex })

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
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

-- Helper lemmas below

theorem subChecked_some_iff (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]

theorem subChecked_none_iff (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked
  simp [h]

theorem subChecked_eq_some {a b n : Nat} (h : subChecked a b = some n) : b ≤ a ∧ n = a - b := by
  unfold subChecked at h
  split at h
  · simp at h
    exact ⟨‹b ≤ a›, h.symm⟩
  · simp at h

theorem subChecked_eq_none {a b : Nat} (h : subChecked a b = none) : ¬ b ≤ a := by
  unfold subChecked at h
  split at h
  · simp at h
  · exact ‹¬b ≤ a›

-- accrueSide grows index
theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · omega
  · omega

theorem accrueSide_block_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

-- The chosen start equals accrualStart
theorem supplierStart_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · simp [h0]
  · simp [h0]

theorem borrowerStart_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · simp [h0]
  · simp [h0]

-- update preserves accounts and totals
theorem updateSupply_accts (s s' : St) (h : updateCompSupplyIndex s = some s') :
    s'.accts = s.accts := by
  unfold updateCompSupplyIndex at h
  match hm : subChecked s.blockNumber s.supplyState.block with
  | none =>
    rw [hm] at h
    cases h
  | some d =>
    rw [hm] at h
    simp only at h
    split at h
    · injection h with h_inj
      rw [←h_inj]
    · split at h
      · injection h with h_inj
        rw [←h_inj]
      · injection h with h_inj
        rw [←h_inj]

theorem updateBorrow_accts (s s' : St) (h : updateCompBorrowIndex s = some s') :
    s'.accts = s.accts := by
  unfold updateCompBorrowIndex at h
  match hm : subChecked s.blockNumber s.borrowState.block with
  | none =>
    rw [hm] at h
    cases h
  | some d =>
    rw [hm] at h
    simp only at h
    split at h
    · injection h with h_inj
      rw [←h_inj]
    · split at h
      · injection h with h_inj
        rw [←h_inj]
      · injection h with h_inj
        rw [←h_inj]

theorem updateSupply_totals (s s' : St) (h : updateCompSupplyIndex s = some s') :
    totalSupply s' = totalSupply s ∧ totalBorrows s' = totalBorrows s := by
  have hac : s'.accts = s.accts := updateSupply_accts s s' h
  simp [totalSupply, totalBorrows, hac]

theorem updateBorrow_totals (s s' : St) (h : updateCompBorrowIndex s = some s') :
    totalSupply s' = totalSupply s ∧ totalBorrows s' = totalBorrows s := by
  have hac : s'.accts = s.accts := updateBorrow_accts s s' h
  simp [totalSupply, totalBorrows, hac]

theorem updateSupply_block_le_succ (s s' : St) (h : updateCompSupplyIndex s = some s') :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex at h
  match hm : subChecked s.blockNumber s.supplyState.block with
  | none =>
    rw [hm] at h
    cases h
  | some d =>
    have hle : s.supplyState.block ≤ s.blockNumber := by
      unfold subChecked at hm
      by_cases hc : s.supplyState.block ≤ s.blockNumber
      · exact hc
      · simp [hc] at hm
    exact hle

theorem updateBorrow_block_le_succ (s s' : St) (h : updateCompBorrowIndex s = some s') :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex at h
  match hm : subChecked s.blockNumber s.borrowState.block with
  | none =>
    rw [hm] at h
    cases h
  | some d =>
    have hle : s.borrowState.block ≤ s.blockNumber := by
      unfold subChecked at hm
      by_cases hc : s.borrowState.block ≤ s.blockNumber
      · exact hc
      · simp [hc] at hm
    exact hle

theorem updateSupply_eq (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide fraction
  rw [subChecked_some_iff _ _ hle]
  simp only
  by_cases h_d : s.blockNumber - s.supplyState.block > 0
  · have h_d_lt : 0 < s.blockNumber - s.supplyState.block := h_d
    by_cases h_s : s.supplyState.speed > 0
    · have h_s_lt : 0 < s.supplyState.speed := h_s
      by_cases h_t : totalSupply s > 0
      · have h_t_lt : 0 < totalSupply s := h_t
        simp [h_d, h_d_lt, h_s, h_s_lt, h_t, h_t_lt]
      · have h_t_lt : ¬ 0 < totalSupply s := h_t
        simp [h_d, h_d_lt, h_s, h_s_lt, h_t, h_t_lt]
    · have h_s_lt : ¬ 0 < s.supplyState.speed := h_s
      simp [h_d, h_d_lt, h_s, h_s_lt]
  · have h_d_lt : ¬ 0 < s.blockNumber - s.supplyState.block := h_d
    have h_eq : s.supplyState.block = s.blockNumber := by omega
    have h_upd : updateCompSupplyIndex s = some s := by
      unfold updateCompSupplyIndex
      rw [subChecked_some_iff _ _ hle]
      simp only
      simp [h_d]
    have h_acc_eq : accrueSide s.supplyState s.blockNumber (totalSupply s) = s.supplyState := by
      unfold accrueSide
      simp [h_d_lt, ←h_eq]
    rw [h_upd, h_acc_eq]
    rfl

theorem updateBorrow_eq (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide fraction
  rw [subChecked_some_iff _ _ hle]
  simp only
  by_cases h_d : s.blockNumber - s.borrowState.block > 0
  · have h_d_lt : 0 < s.blockNumber - s.borrowState.block := h_d
    by_cases h_s : s.borrowState.speed > 0
    · have h_s_lt : 0 < s.borrowState.speed := h_s
      by_cases h_t : totalBorrows s > 0
      · have h_t_lt : 0 < totalBorrows s := h_t
        simp [h_d, h_d_lt, h_s, h_s_lt, h_t, h_t_lt]
      · have h_t_lt : ¬ 0 < totalBorrows s := h_t
        simp [h_d, h_d_lt, h_s, h_s_lt, h_t, h_t_lt]
    · have h_s_lt : ¬ 0 < s.borrowState.speed := h_s
      simp [h_d, h_d_lt, h_s, h_s_lt]
  · have h_d_lt : ¬ 0 < s.blockNumber - s.borrowState.block := h_d
    have h_eq : s.borrowState.block = s.blockNumber := by omega
    have h_upd : updateCompBorrowIndex s = some s := by
      unfold updateCompBorrowIndex
      rw [subChecked_some_iff _ _ hle]
      simp only
      simp [h_d]
    have h_acc_eq : accrueSide s.borrowState s.blockNumber (totalBorrows s) = s.borrowState := by
      unfold accrueSide
      simp [h_d_lt, ←h_eq]
    rw [h_upd, h_acc_eq]
    rfl

-- update equals accrueSide when it succeeds
theorem updateSupply_accrue (s s' : St) (h : updateCompSupplyIndex s = some s') :
    s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hle := updateSupply_block_le_succ s s' h
  have heq := updateSupply_eq s hle
  have h_eq : (some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : Option St) = some s' := heq.symm.trans h
  injection h_eq with h_inj
  exact h_inj.symm

theorem updateBorrow_accrue (s s' : St) (h : updateCompBorrowIndex s = some s') :
    s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hle := updateBorrow_block_le_succ s s' h
  have heq := updateBorrow_eq s hle
  have h_eq : (some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : Option St) = some s' := heq.symm.trans h
  injection h_eq with h_inj
  exact h_inj.symm

-- update succeeds iff block ≤ now
theorem updateSupply_some_of_le (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' := by
  unfold updateCompSupplyIndex
  rw [subChecked_some_iff _ _ hle]
  simp only
  by_cases h : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [h]
    exact ⟨_, rfl⟩
  · simp only [h]
    by_cases h2 : s.blockNumber - s.supplyState.block > 0
    · simp only [h2]
      exact ⟨_, rfl⟩
    · simp only [h2]
      exact ⟨_, rfl⟩

theorem updateBorrow_some_of_le (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' := by
  unfold updateCompBorrowIndex
  rw [subChecked_some_iff _ _ hle]
  simp only
  by_cases h : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [h]
    exact ⟨_, rfl⟩
  · simp only [h]
    by_cases h2 : s.blockNumber - s.borrowState.block > 0
    · simp only [h2]
      exact ⟨_, rfl⟩
    · simp only [h2]
      exact ⟨_, rfl⟩

theorem updateSupply_none_of_gt (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  rw [subChecked_none_iff _ _ h]

theorem updateBorrow_none_of_gt (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  rw [subChecked_none_iff _ _ h]

theorem supply_modify_congr (l : List Acct) (who newIdx : Nat) :
    l.modify who (fun a => { a with supplierIndex := newIdx, accrued := a.accrued + (l.getD who noAcct).supply * (newIdx - accrualStart (l.getD who noAcct).supplierIndex newIdx) / doubleScale }) = l.modify who (fun a => { a with supplierIndex := newIdx, accrued := a.accrued + a.supply * (newIdx - accrualStart a.supplierIndex newIdx) / doubleScale }) := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases who with
    | zero => simp
    | succ n => simp; exact ih n

theorem borrow_modify_congr (l : List Acct) (who newIdx : Nat) :
    l.modify who (fun a => { a with borrowerIndex := newIdx, accrued := a.accrued + (l.getD who noAcct).borrow * (newIdx - accrualStart (l.getD who noAcct).borrowerIndex newIdx) / doubleScale }) = l.modify who (fun a => { a with borrowerIndex := newIdx, accrued := a.accrued + a.borrow * (newIdx - accrualStart a.borrowerIndex newIdx) / doubleScale }) := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases who with
    | zero => simp
    | succ n => simp; exact ih n

-- update + distribute together equal the spec relation
theorem supplyHook_of_updates (s s1 s' : St) (who : Account)
    (h1 : updateCompSupplyIndex s = some s1) (h2 : distributeSupplierComp s1 who = some s') :
    SupplyDistributed s who s' := by
  have h_acc := updateSupply_accrue s s1 h1
  have hle_block := updateSupply_block_le_succ s s1 h1
  have h_accts : s1.accts = s.accts := updateSupply_accts s s1 h1
  have h_acct : s1.acct who = s.acct who := by rw [h_acc]; rfl
  have h_idx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [h_acc]
  have h_tot : totalSupply s1 = totalSupply s := (updateSupply_totals s s1 h1).1
  unfold distributeSupplierComp at h2
  have hif : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    unfold accrualStart
    by_cases h0 : (s.acct who).supplierIndex = 0
    · simp [h0]
    · simp [h0]
  have hif_s1 : (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    simp [h_acct, h_idx, hif]
  have h_scrut : subChecked s1.supplyState.index (if (s1.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s1.supplyState.index then compInitialIndex else (s1.acct who).supplierIndex) = subChecked (accrueSide s.supplyState s.blockNumber (totalSupply s)).index (accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) := by
    rw [hif_s1, h_idx]
  rw [h_scrut] at h2
  match hm : subChecked (accrueSide s.supplyState s.blockNumber (totalSupply s)).index (accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) with
  | none =>
    rw [hm] at h2
    cases h2
  | some d =>
    rw [hm] at h2
    have h_eq : (s1.withAcct who fun a => { a with supplierIndex := s1.supplyState.index, accrued := a.accrued + mulDouble (s1.acct who).supply d }) = s' := by
      simpa using h2
    have hsub := subChecked_eq_some hm
    refine ⟨hle_block, hsub.1, ?_⟩
    have h_s1_eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := h_acc
    rw [h_s1_eq] at h_eq
    rw [← h_eq]
    simp only [St.withAcct, creditFor, mulDouble]
    have hd : d = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index - accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := hsub.2
    rw [hd]
    have h_mod := supply_modify_congr s.accts who (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    exact congrArg (fun accts : List Acct => ({ blockNumber := s.blockNumber, supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), borrowState := s.borrowState, reserve := s.reserve, accts := accts } : St)) h_mod

theorem borrowHook_of_updates (s s1 s' : St) (who : Account)
    (h1 : updateCompBorrowIndex s = some s1) (h2 : distributeBorrowerComp s1 who = some s') :
    BorrowDistributed s who s' := by
  have h_acc := updateBorrow_accrue s s1 h1
  have hle_block := updateBorrow_block_le_succ s s1 h1
  have h_acct : s1.acct who = s.acct who := by rw [h_acc]; rfl
  have h_idx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [h_acc]
  unfold distributeBorrowerComp at h2
  have hif : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    unfold accrualStart
    by_cases h0 : (s.acct who).borrowerIndex = 0
    · simp [h0]
    · simp [h0]
  have hif_s1 : (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    simp [h_acct, h_idx, hif]
  have h_scrut : subChecked s1.borrowState.index (if (s1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s1.borrowState.index then compInitialIndex else (s1.acct who).borrowerIndex) = subChecked (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index (accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) := by
    rw [hif_s1, h_idx]
  rw [h_scrut] at h2
  match hm : subChecked (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index (accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) with
  | none =>
    rw [hm] at h2
    cases h2
  | some d =>
    rw [hm] at h2
    have h_eq : (s1.withAcct who fun a => { a with borrowerIndex := s1.borrowState.index, accrued := a.accrued + mulDouble (s1.acct who).borrow d }) = s' := by
      simpa using h2
    have hsub := subChecked_eq_some hm
    refine ⟨hle_block, hsub.1, ?_⟩
    have h_s1_eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := h_acc
    rw [h_s1_eq] at h_eq
    rw [← h_eq]
    simp only [St.withAcct, creditFor, mulDouble]
    have hd : d = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := hsub.2
    rw [hd]
    have h_mod := borrow_modify_congr s.accts who (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    exact congrArg (fun accts : List Acct => ({ blockNumber := s.blockNumber, supplyState := s.supplyState, borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), reserve := s.reserve, accts := accts } : St)) h_mod

theorem distributeSupply_some_of_le (s : St) (who : Account)
    (hle : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) :
    ∃ s', distributeSupplierComp
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who = some s' := by
  have hif2 : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index then compInitialIndex
      else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    unfold accrualStart
    by_cases h0 : (s.acct who).supplierIndex = 0
    · simp [h0]
    · simp [h0]
  have h_acct : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who) =
      s.acct who := rfl
  have h_idx : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index) =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
  unfold distributeSupplierComp
  rw [h_acct, h_idx, hif2, subChecked_some_iff _ _ hle]
  exact ⟨_, rfl⟩

theorem distributeBorrow_some_of_le (s : St) (who : Account)
    (hle : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) :
    ∃ s', distributeBorrowerComp
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who = some s' := by
  have hif2 : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index then compInitialIndex
      else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    unfold accrualStart
    by_cases h0 : (s.acct who).borrowerIndex = 0
    · simp [h0]
    · simp [h0]
  have h_acct : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who) =
      s.acct who := rfl
  have h_idx : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).borrowState.index) =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
  unfold distributeBorrowerComp
  rw [h_acct, h_idx, hif2, subChecked_some_iff _ _ hle]
  exact ⟨_, rfl⟩

-- accrualStart from a recorded index within the old index stays within the new index
theorem accrualStart_mono_le (recorded oldIdx newIdx : Nat) (hrec : recorded ≤ oldIdx)
    (hle : oldIdx ≤ newIdx) : accrualStart recorded newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases h0 : recorded = 0
  · simp [h0]
    by_cases h1 : compInitialIndex ≤ newIdx
    · simp [h1]
    · simp [h1]
  · simp [h0]
    omega

theorem accrualStart_zero_le (newIdx : Nat) : accrualStart 0 newIdx ≤ newIdx := by
  unfold accrualStart
  simp
  by_cases h1 : compInitialIndex ≤ newIdx
  · simp [h1]
  · simp [h1]

-- grant equals spec grant (definitions coincide up to let)
theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve
  · simp [h]
  · simp [h]

end CompRewards
