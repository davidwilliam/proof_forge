import CompRewards.Spec
namespace CompRewards

def fraction (a b : Nat) : Nat := a * doubleScale / b

def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

theorem subChecked_succ {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]

theorem subChecked_fail {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked
  simp [h]

theorem accrualStart_le (recorded index : Nat) (hle : recorded ≤ index)
    : accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · simp [h]
    by_cases h2 : compInitialIndex ≤ index
    · simp [h2]
      exact h2
    · simp [h2]
  · simp [h]
    exact hle

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

def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  match subChecked s.supplyState.index (accrualStart (s.acct supplier).supplierIndex s.supplyState.index) with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })

def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  match subChecked s.borrowState.index (accrualStart (s.acct borrower).borrowerIndex s.borrowState.index) with
  | none => none
  | some _ =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })

def grantCompInternal (s : St) (user : Account) : St :=
  if 0 < (s.acct user).accrued ∧ (s.acct user).accrued ≤ s.reserve then
    { s with reserve := s.reserve - (s.acct user).accrued,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
  else s

def claimComp (s : St) (holder : Account) : Option St := do
  let s ← updateCompBorrowIndex s
  let s ← distributeBorrowerComp s holder
  let s ← updateCompSupplyIndex s
  let s ← distributeSupplierComp s holder
  return grantCompInternal s holder

def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    (updateCompSupplyIndex s).map fun s =>
      { s with supplyState := { s.supplyState with speed := supplySpeed } }
  else some s

def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    (updateCompBorrowIndex s).map fun s =>
      { s with borrowState := { s.borrowState with speed := borrowSpeed } }
  else some s

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

theorem modify_length (l : List Acct) (i : Nat) (f : Acct → Acct) : (l.modify i f).length = l.length :=
  List.length_modify f l i

theorem withAcct_block (s : St) (who : Account) (f : Acct → Acct)
    : (s.withAcct who f).blockNumber = s.blockNumber := rfl

theorem withAcct_supplyState (s : St) (who : Account) (f : Acct → Acct)
    : (s.withAcct who f).supplyState = s.supplyState := rfl

theorem withAcct_borrowState (s : St) (who : Account) (f : Acct → Acct)
    : (s.withAcct who f).borrowState = s.borrowState := rfl

theorem withAcct_reserve (s : St) (who : Account) (f : Acct → Acct)
    : (s.withAcct who f).reserve = s.reserve := rfl

theorem acct_of_ge (s : St) (who : Nat) (h : s.accts.length ≤ who) : s.acct who = noAcct := by
  unfold St.acct List.getD
  have hnone : s.accts[who]? = none := List.getElem?_eq_none h
  simp [hnone]

theorem mem_of_lt_getD (l : List Acct) (i : Nat) (h : i < l.length) : l.getD i noAcct ∈ l := by
  unfold List.getD
  have hsome : l[i]? = some (l[i]'h) := List.getElem?_eq_getElem h
  simp [hsome]
  exact List.getElem_mem h

theorem modify_getD_same_of_lt (l : List Acct) (i : Nat) (f : Acct → Acct) (d : Acct)
    (h : i < l.length) : (l.modify i f).getD i d = f (l.getD i d) := by
  have hlen : i < (l.modify i f).length := by rw [List.length_modify]; exact h
  have h1 : (l.modify i f)[i]'hlen = f (l[i]'h) := by
    have hget := List.getElem_modify f i l i hlen
    rw [if_pos rfl] at hget
    exact hget
  unfold List.getD
  have hsome1 : l[i]? = some (l[i]'h) := List.getElem?_eq_getElem h
  have hsome2 : (l.modify i f)[i]? = some ((l.modify i f)[i]'hlen) :=
    List.getElem?_eq_getElem hlen
  simp [hsome1, hsome2, h1]

theorem consistent_index_supply (s : St) (who : Account) (h : Consistent s)
    : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  by_cases hm : who < s.accts.length
  · have hm2 : s.acct who ∈ s.accts := by
      unfold St.acct
      exact mem_of_lt_getD s.accts who hm
    have := hmem _ hm2
    exact And.left this
  · have hle : s.accts.length ≤ who := Nat.le_of_not_lt hm
    have heq : s.acct who = noAcct := acct_of_ge s who hle
    simp [heq, noAcct]

theorem consistent_index_borrow (s : St) (who : Account) (h : Consistent s)
    : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  by_cases hm : who < s.accts.length
  · have hm2 : s.acct who ∈ s.accts := by
      unfold St.acct
      exact mem_of_lt_getD s.accts who hm
    have := hmem _ hm2
    exact And.right this
  · have hle : s.accts.length ≤ who := Nat.le_of_not_lt hm
    have heq : s.acct who = noAcct := acct_of_ge s who hle
    simp [heq, noAcct]

theorem consistent_block_supply (s : St) (h : Consistent s) : s.supplyState.block ≤ s.blockNumber := by
  unfold Consistent at h
  exact h.1

theorem consistent_block_borrow (s : St) (h : Consistent s) : s.borrowState.block ≤ s.blockNumber := by
  unfold Consistent at h
  exact h.2.1

theorem accrueSide_block (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h, Nat.le_add_right]
  · simp [h]

theorem updateSupply_some_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber)
    : ∃ s', updateCompSupplyIndex s = some s' := by
  unfold updateCompSupplyIndex
  have hb : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    subChecked_succ h
  rw [hb]
  by_cases hd : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · simp [hd]
    exact ⟨_, rfl⟩
  · simp [hd]
    by_cases hd2 : (s.blockNumber - s.supplyState.block) > 0
    · simp [hd2]
      exact ⟨_, rfl⟩
    · simp [hd2]
      exact ⟨_, rfl⟩

theorem updateBorrow_some_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber)
    : ∃ s', updateCompBorrowIndex s = some s' := by
  unfold updateCompBorrowIndex
  have hb : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    subChecked_succ h
  rw [hb]
  by_cases hd : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · simp [hd]
    exact ⟨_, rfl⟩
  · simp [hd]
    by_cases hd2 : (s.blockNumber - s.borrowState.block) > 0
    · simp [hd2]
      exact ⟨_, rfl⟩
    · simp [hd2]
      exact ⟨_, rfl⟩

theorem updateSupply_eq (s s' : St) (h : updateCompSupplyIndex s = some s')
    : s.supplyState.block ≤ s.blockNumber ∧
      s'.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) ∧
      s'.borrowState = s.borrowState ∧ s'.blockNumber = s.blockNumber ∧
      s'.reserve = s.reserve ∧ s'.accts = s.accts := by
  unfold updateCompSupplyIndex at h
  have hle : s.supplyState.block ≤ s.blockNumber := by
    by_cases hle : s.supplyState.block ≤ s.blockNumber
    · exact hle
    · have hf := subChecked_fail hle
      simp [hf] at h
      cases h
  have hb := subChecked_succ hle
  simp only [hb] at h
  by_cases hd : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · simp only [hd, ite_true] at h
    obtain ⟨hpos, hspd⟩ := hd
    by_cases ht : 0 < totalSupply s
    · have hcond : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) :=
        ⟨hpos, hspd, ht⟩
      have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) =
          { s.supplyState with
            index := s.supplyState.index + fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s),
            block := s.blockNumber } := by
        unfold accrueSide fraction
        simp [hcond]
      rw [hacc]
      simp only [ht, ite_true] at h
      simp [fraction] at h ⊢
      obtain rfl := h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
    · have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        simp [ht]
      have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) =
          { s.supplyState with block := s.blockNumber } := by
        unfold accrueSide
        simp [hcond]
      rw [hacc]
      simp only [ht, ite_false] at h
      cases h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hd, ite_false] at h
    by_cases hd2 : (s.blockNumber - s.supplyState.block) > 0
    · simp only [hd2, ite_true] at h
      have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        intro hc
        exact hd ⟨hd2, hc.2.1⟩
      have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) =
          { s.supplyState with block := s.blockNumber } := by
        unfold accrueSide
        simp [hcond]
      rw [hacc]
      cases h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
    · have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have hneg : ¬ ((s.blockNumber - s.supplyState.block) > 0) := by omega
      simp [hneg] at h
      have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        simp [hzero]
      have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) = s.supplyState := by
        unfold accrueSide
        simp [hcond]
        have heq : s.blockNumber = s.supplyState.block := by omega
        simp [heq]
      rw [hacc]
      cases h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩

theorem updateBorrow_eq (s s' : St) (h : updateCompBorrowIndex s = some s')
    : s.borrowState.block ≤ s.blockNumber ∧
      s'.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) ∧
      s'.supplyState = s.supplyState ∧ s'.blockNumber = s.blockNumber ∧
      s'.reserve = s.reserve ∧ s'.accts = s.accts := by
  unfold updateCompBorrowIndex at h
  have hle : s.borrowState.block ≤ s.blockNumber := by
    by_cases hle : s.borrowState.block ≤ s.blockNumber
    · exact hle
    · have hf := subChecked_fail hle
      simp [hf] at h
      cases h
  have hb := subChecked_succ hle
  simp only [hb] at h
  by_cases hd : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · simp only [hd, ite_true] at h
    obtain ⟨hpos, hspd⟩ := hd
    by_cases ht : 0 < totalBorrows s
    · have hcond : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) :=
        ⟨hpos, hspd, ht⟩
      have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
          { s.borrowState with
            index := s.borrowState.index + fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s),
            block := s.blockNumber } := by
        unfold accrueSide fraction
        simp [hcond]
      rw [hacc]
      simp only [ht, ite_true] at h
      simp [fraction] at h ⊢
      obtain rfl := h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
    · have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [ht]
      have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
          { s.borrowState with block := s.blockNumber } := by
        unfold accrueSide
        simp [hcond]
      rw [hacc]
      simp only [ht, ite_false] at h
      cases h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hd, ite_false] at h
    by_cases hd2 : (s.blockNumber - s.borrowState.block) > 0
    · simp only [hd2, ite_true] at h
      have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        intro hc
        exact hd ⟨hd2, hc.2.1⟩
      have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
          { s.borrowState with block := s.blockNumber } := by
        unfold accrueSide
        simp [hcond]
      rw [hacc]
      cases h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩
    · have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have hneg : ¬ ((s.blockNumber - s.borrowState.block) > 0) := by omega
      simp [hneg] at h
      have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp [hzero]
      have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) = s.borrowState := by
        unfold accrueSide
        simp [hcond]
        have heq : s.blockNumber = s.borrowState.block := by omega
        simp [heq]
      rw [hacc]
      cases h
      refine ⟨hle, rfl, rfl, rfl, rfl, rfl⟩

theorem modify_ge_unused : True := trivial

theorem distributeSupply_some (s : St) (who : Account)
    (hle_rec : (s.acct who).supplierIndex ≤ s.supplyState.index)
    : distributeSupplierComp s who =
      some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold distributeSupplierComp
  have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index :=
    accrualStart_le _ _ hle_rec
  have hb := subChecked_succ hle
  rw [hb]

theorem distributeBorrow_some (s : St) (who : Account)
    (hle_rec : (s.acct who).borrowerIndex ≤ s.borrowState.index)
    : distributeBorrowerComp s who =
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold distributeBorrowerComp
  have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index :=
    accrualStart_le _ _ hle_rec
  have hb := subChecked_succ hle
  rw [hb]

theorem modify_congr_unused : True := trivial

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  rfl

theorem setSupply_isSome (s : St) (a : Nat) (h : s.supplyState.block ≤ s.blockNumber)
    : (setSupplySpeed s a).isSome := by
  unfold setSupplySpeed
  by_cases hs : s.supplyState.speed ≠ a
  · simp [hs]
    obtain ⟨t1, ht1⟩ := updateSupply_some_of_le s h
    simp [ht1]
  · simp [hs]

theorem setBorrow_isSome (s : St) (b : Nat) (h : s.borrowState.block ≤ s.blockNumber)
    : (setBorrowSpeed s b).isSome := by
  unfold setBorrowSpeed
  by_cases hb : s.borrowState.speed ≠ b
  · simp [hb]
    obtain ⟨t1, ht1⟩ := updateBorrow_some_of_le s h
    simp [ht1]
  · simp [hb]

theorem setSupply_borrow_le (s t1 : St) (a : Nat) (h : setSupplySpeed s a = some t1)
    (hle : s.borrowState.block ≤ s.blockNumber) (hsup : s.supplyState.block ≤ s.blockNumber)
    : t1.borrowState.block ≤ t1.blockNumber := by
  have hsup2 := updateSupply_some_of_le s hsup
  obtain ⟨t0, ht0⟩ := hsup2
  unfold setSupplySpeed at h
  by_cases hs : s.supplyState.speed ≠ a
  · simp [hs, ht0] at h
    subst h
    simp
    have heq := updateSupply_eq s t0 ht0
    obtain ⟨_, _, ht0bor_eq, ht0blk, _, _⟩ := heq
    rw [ht0bor_eq, ht0blk]
    exact hle
  · simp [hs] at h
    subst h
    exact hle

theorem setSupply_block (s t1 : St) (a : Nat) (h : setSupplySpeed s a = some t1)
    (hsup : s.supplyState.block ≤ s.blockNumber)
    : t1.blockNumber = s.blockNumber := by
  have hsup2 := updateSupply_some_of_le s hsup
  obtain ⟨t0, ht0⟩ := hsup2
  unfold setSupplySpeed at h
  by_cases hs : s.supplyState.speed ≠ a
  · simp [hs, ht0] at h
    subst h
    simp
    have heq := updateSupply_eq s t0 ht0
    exact heq.2.2.2.1
  · simp [hs] at h
    subst h
    rfl

theorem updateSupply_rec_supply_le (s s1 : St) (who : Account)
    (h : updateCompSupplyIndex s = some s1)
    (hle : (s.acct who).supplierIndex ≤ s.supplyState.index)
    : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
  have heq := updateSupply_eq s s1 h
  obtain ⟨_, hsup_eq, _, _, _, haccts⟩ := heq
  have hacct_eq : s1.acct who = s.acct who := by
    unfold St.acct
    rw [haccts]
  rw [hacct_eq, hsup_eq]
  have hge : s.supplyState.index ≤ accrueSide s.supplyState s.blockNumber (totalSupply s) := by
    exact accrueSide_index_ge _ _ _
  omega

theorem updateSupply_rec_borrow_le (s s1 : St) (who : Account)
    (h : updateCompSupplyIndex s = some s1)
    (hle : (s.acct who).borrowerIndex ≤ s.borrowState.index)
    : (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
  have heq := updateSupply_eq s s1 h
  obtain ⟨_, _, hbor_eq, _, _, haccts⟩ := heq
  have hacct_eq : s1.acct who = s.acct who := by
    unfold St.acct
    rw [haccts]
  rw [hacct_eq, hbor_eq]
  exact hle

theorem updateBorrow_rec_borrow_le (s s1 : St) (who : Account)
    (h : updateCompBorrowIndex s = some s1)
    (hle : (s.acct who).borrowerIndex ≤ s.borrowState.index)
    : (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
  have heq := updateBorrow_eq s s1 h
  obtain ⟨_, hbor_eq, _, _, _, haccts⟩ := heq
  have hacct_eq : s1.acct who = s.acct who := by
    unfold St.acct
    rw [haccts]
  rw [hacct_eq, hbor_eq]
  have hge : s.borrowState.index ≤ accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
    exact accrueSide_index_ge _ _ _
  omega

theorem updateBorrow_rec_supply_le (s s1 : St) (who : Account)
    (h : updateCompBorrowIndex s = some s1)
    (hle : (s.acct who).supplierIndex ≤ s.supplyState.index)
    : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
  have heq := updateBorrow_eq s s1 h
  obtain ⟨_, _, hsup_eq, _, _, haccts⟩ := heq
  have hacct_eq : s1.acct who = s.acct who := by
    unfold St.acct
    rw [haccts]
  rw [hacct_eq, hsup_eq]
  exact hle

theorem borrowDistribute_supplyRec_le (t1 : St) (who : Account)
    (hle : (t1.acct who).supplierIndex ≤ t1.supplyState.index)
    : ((t1.withAcct who fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).acct who).supplierIndex
      ≤ (t1.withAcct who fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).supplyState.index := by
  have hsup_eq : (t1.withAcct who fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).supplyState
      = t1.supplyState := rfl
  rw [hsup_eq]
  by_cases hm : who < t1.accts.length
  · have hget := modify_getD_same_of_lt t1.accts who (fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }) noAcct hm
    have hacct_eq : (t1.withAcct who fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).acct who
        = (fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }) (t1.acct who) := by
      unfold St.withAcct St.acct
      exact hget
    rw [hacct_eq]
    simp
    exact hle
  · have hle_len : t1.accts.length ≤ who := Nat.le_of_not_lt hm
    have heq1 : t1.acct who = noAcct := acct_of_ge t1 who hle_len
    have hlen_eq : (t1.accts.modify who fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).length
        = t1.accts.length := List.length_modify _ _ _
    have hle2 : (t1.accts.modify who fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).length ≤ who := by
      rw [hlen_eq]
      exact hle_len
    have heq2 : ((t1.withAcct who fun a =>
        { a with borrowerIndex := t1.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).acct who)
        = noAcct := by
      unfold St.withAcct St.acct
      exact acct_of_ge _ who hle2
    rw [heq1, heq2] at hle ⊢
    simp [noAcct] at hle ⊢
    exact Nat.zero_le _

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold comptroller
  cases c with
  | supplyHook who =>
    show ((updateCompSupplyIndex s).bind fun s => distributeSupplierComp s who).isSome
    have hb := consistent_block_supply s hc
    obtain ⟨s1, hs1⟩ := updateSupply_some_of_le s hb
    have hrec := consistent_index_supply s who hc
    have hrec1 := updateSupply_rec_supply_le s s1 who hs1 hrec
    have hdist := distributeSupply_some s1 who hrec1
    simp [hs1, hdist]
  | borrowHook who =>
    show ((updateCompBorrowIndex s).bind fun s => distributeBorrowerComp s who).isSome
    have hb := consistent_block_borrow s hc
    obtain ⟨s1, hs1⟩ := updateBorrow_some_of_le s hb
    have hrec := consistent_index_borrow s who hc
    have hrec1 := updateBorrow_rec_borrow_le s s1 who hs1 hrec
    have hdist := distributeBorrow_some s1 who hrec1
    simp [hs1, hdist]
  | claim who =>
    show (claimComp s who).isSome
    unfold claimComp
    have hb1 := consistent_block_borrow s hc
    obtain ⟨t1, ht1⟩ := updateBorrow_some_of_le s hb1
    have heq1 := updateBorrow_eq s t1 ht1
    obtain ⟨_, ht1bor, ht1sup, ht1blk, _, haccts1⟩ := heq1
    have hsup_le : t1.supplyState.block ≤ t1.blockNumber := by
      rw [ht1sup, ht1blk]
      exact consistent_block_supply s hc
    have hrec_bor1 := consistent_index_borrow s who hc
    have hrec_bor_t1 := updateBorrow_rec_borrow_le s t1 who ht1 hrec_bor1
    have ht2 : distributeBorrowerComp t1 who =
        some (t1.withAcct who fun a =>
          { a with borrowerIndex := t1.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }) :=
      distributeBorrow_some t1 who hrec_bor_t1
    have hrec_sup_s := consistent_index_supply s who hc
    have hrec_sup_t1 : (t1.acct who).supplierIndex ≤ t1.supplyState.index := by
      have heq_sup : t1.supplyState = s.supplyState := ht1sup
      have hacct_eq : t1.acct who = s.acct who := by unfold St.acct; rw [haccts1]
      rw [hacct_eq, heq_sup]
      exact hrec_sup_s
    have hrec_sup_t2 := borrowDistribute_supplyRec_le t1 who hrec_sup_t1
    have ht2sup : (t1.withAcct who fun a =>
          { a with borrowerIndex := t1.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).supplyState
        = t1.supplyState := rfl
    have ht2blk : (t1.withAcct who fun a =>
          { a with borrowerIndex := t1.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).blockNumber
        = t1.blockNumber := rfl
    have hsup_le2 : (t1.withAcct who fun a =>
          { a with borrowerIndex := t1.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).supplyState.block
        ≤ (t1.withAcct who fun a =>
          { a with borrowerIndex := t1.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).blockNumber := by
      simp [ht2sup, ht2blk, hsup_le]
    obtain ⟨t3, ht3⟩ := updateSupply_some_of_le _ hsup_le2
    have hrec_sup_t3 : (t3.acct who).supplierIndex ≤ t3.supplyState.index :=
      updateSupply_rec_supply_le _ t3 who ht3 hrec_sup_t2
    have hdist_supply := distributeSupply_some t3 who hrec_sup_t3
    simp [ht1, ht2, ht3, hdist_supply]
  | setSpeeds a b =>
    show ((setCompSpeedInternal s a b)).isSome
    unfold setCompSpeedInternal
    have hb1 := consistent_block_supply s hc
    have hb2 := consistent_block_borrow s hc
    have h1 := setSupply_isSome s a hb1
    obtain ⟨t1, ht1⟩ := Option.isSome_iff_exists.mp h1
    have ht1bor := setSupply_borrow_le s t1 a ht1 hb2 hb1
    have h2 := setBorrow_isSome t1 b ht1bor
    obtain ⟨t2, ht2⟩ := Option.isSome_iff_exists.mp h2
    simp [ht1, ht2]
