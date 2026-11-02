import CompRewards.Spec
namespace CompRewards

def fraction (a b : Nat) : Nat := a * doubleScale / b
def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale
def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

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

def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + amount } }
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

theorem subChecked_eq_some_of_le (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem updateSupply_some_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hs : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    subChecked_eq_some_of_le _ _ h
  unfold updateCompSupplyIndex accrueSide fraction totalSupply
  rw [hs]
  simp only
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · obtain ⟨h1, h2⟩ := hd
    simp [h1, h2]
    by_cases ht : (s.accts.map Acct.supply).sum > 0
    · simp [ht]
    · simp [ht]
  · have h3 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < (s.accts.map Acct.supply).sum) := by omega
    simp only [hd, if_false]
    simp only [h3, if_false]
    by_cases hd2 : s.blockNumber - s.supplyState.block > 0
    · simp only [hd2, if_true]
    · simp only [hd2, if_false]
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res accts =>
        simp only at hbeq ⊢
        cases sup with
        | mk idx blk spd =>
          simp at hbeq
          simp [hbeq]

theorem updateBorrow_some_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hs : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    subChecked_eq_some_of_le _ _ h
  unfold updateCompBorrowIndex accrueSide fraction totalBorrows
  rw [hs]
  simp only
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · obtain ⟨h1, h2⟩ := hd
    simp [h1, h2]
    by_cases ht : (s.accts.map Acct.borrow).sum > 0
    · simp [ht]
    · simp [ht]
  · have h3 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < (s.accts.map Acct.borrow).sum) := by omega
    simp only [hd, if_false]
    simp only [h3, if_false]
    by_cases hd2 : s.blockNumber - s.borrowState.block > 0
    · simp only [hd2, if_true]
    · simp only [hd2, if_false]
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res accts =>
        simp only at hbeq ⊢
        cases bor with
        | mk idx blk spd =>
          simp at hbeq
          simp [hbeq]

theorem accrualStart_supply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex)
    = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0 <;> simp [h0]

theorem accrualStart_borrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex)
    = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0 <;> simp [h0]

theorem subChecked_none_of_not_le (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem list_modify_congr (l : List Acct) (n : Nat) (f g : Acct → Acct)
    (h : f (l.getD n noAcct) = g (l.getD n noAcct)) :
    l.modify n f = l.modify n g := by
  induction l generalizing n with
  | nil =>
    cases n <;> rfl
  | cons a as ih =>
    cases n with
    | zero =>
      simp at h ⊢
      rw [h]
    | succ n =>
      simp at h ⊢
      rw [ih _ h]

theorem withAcct_congr (s : St) (who : Account) (f g : Acct → Acct)
    (h : f (s.acct who) = g (s.acct who)) :
    s.withAcct who f = s.withAcct who g := by
  unfold St.withAcct
  exact congrArg _ (list_modify_congr s.accts who f g h)

theorem distributeSupply_rw (s : St) (who : Account) :
    distributeSupplierComp s who =
      match subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
      | none => none
      | some delta =>
        some (s.withAcct who fun a =>
          { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble a.supply delta }) := by
  unfold distributeSupplierComp
  have heq := accrualStart_supply_eq s who
  simp only [heq]
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [subChecked_eq_some_of_le _ _ hle]
    congr 1
    apply withAcct_congr
    rfl
  · simp only [subChecked_none_of_not_le _ _ hle]

theorem distributeBorrow_rw (s : St) (who : Account) :
    distributeBorrowerComp s who =
      match subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
      | none => none
      | some delta =>
        some (s.withAcct who fun a =>
          { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble a.borrow delta }) := by
  unfold distributeBorrowerComp
  have heq := accrualStart_borrow_eq s who
  simp only [heq]
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [subChecked_eq_some_of_le _ _ hle]
    congr 1
    apply withAcct_congr
    rfl
  · simp only [subChecked_none_of_not_le _ _ hle]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases hcond : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve
  · have hcond' : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve := by omega
    simp only [hcond, hcond', if_true]
    let f : Acct → Acct := fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }
    let g : Acct → Acct := fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }
    have hfg : f (s.acct who) = g (s.acct who) := rfl
    have hmod := list_modify_congr s.accts who f g hfg
    simp only [f, g] at hmod
    rw [hmod]
  · have hcond' : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) := by omega
    simp only [hcond, hcond', if_false]

theorem updateSupply_some_implies_le (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) : s.supplyState.block ≤ s.blockNumber := by
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · exact hle
  · have hn : subChecked s.blockNumber s.supplyState.block = none :=
      subChecked_none_of_not_le _ _ hle
    unfold updateCompSupplyIndex at h
    rw [hn] at h
    cases h

theorem updateBorrow_some_implies_le (s : St) (s1 : St)
    (h : updateCompBorrowIndex s = some s1) : s.borrowState.block ≤ s.blockNumber := by
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · exact hle
  · have hn : subChecked s.blockNumber s.borrowState.block = none :=
      subChecked_none_of_not_le _ _ hle
    unfold updateCompBorrowIndex at h
    rw [hn] at h
    cases h

theorem distributeSupply_some_implies_le (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  rw [distributeSupply_rw] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · exact hle
  · have hn := subChecked_none_of_not_le _ _ hle
    rw [hn] at h
    cases h

theorem distributeBorrow_some_implies_le (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  rw [distributeBorrow_rw] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · exact hle
  · have hn := subChecked_none_of_not_le _ _ hle
    rw [hn] at h
    cases h

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompSupplyIndex s with
  | none =>
    simp [hu] at h
  | some s1 =>
    simp [hu] at h
    have hle_block := updateSupply_some_implies_le s s1 hu
    have hs1_eq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      have h1 := updateSupply_some_of_le s hle_block
      rw [hu] at h1
      cases h1
      rfl
    have hdist_le := distributeSupply_some_implies_le s1 who s' h
    have hs1_acct : s1.acct who = s.acct who := by
      rw [hs1_eq]
      rfl
    have hs1_idx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hs1_eq]
    refine ⟨hle_block, ?_, ?_⟩
    · have h_start_le : accrualStart (s.acct who).supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        rw [← hs1_acct, ← hs1_idx]
        exact hdist_le
      exact h_start_le
    · rw [distributeSupply_rw] at h
      have hs_dist := subChecked_eq_some_of_le _ _ hdist_le
      rw [hs_dist] at h
      simp at h
      cases h
      rw [hs1_eq]
      apply withAcct_congr
      rfl

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompBorrowIndex s with
  | none =>
    simp [hu] at h
  | some s1 =>
    simp [hu] at h
    have hle_block := updateBorrow_some_implies_le s s1 hu
    have hs1_eq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have h1 := updateBorrow_some_of_le s hle_block
      rw [hu] at h1
      cases h1
      rfl
    have hdist_le := distributeBorrow_some_implies_le s1 who s' h
    have hs1_acct : s1.acct who = s.acct who := by
      rw [hs1_eq]
      rfl
    have hs1_idx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hs1_eq]
    refine ⟨hle_block, ?_, ?_⟩
    · have h_start_le : accrualStart (s.acct who).borrowerIndex
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        rw [← hs1_acct, ← hs1_idx]
        exact hdist_le
      exact h_start_le
    · rw [distributeBorrow_rw] at h
      have hs_dist := subChecked_eq_some_of_le _ _ hdist_le
      rw [hs_dist] at h
      simp at h
      cases h
      rw [hs1_eq]
      apply withAcct_congr
      rfl

theorem map_supply_modify (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).supply = a.supply) :
    (l.modify n f).map Acct.supply = l.map Acct.supply := by
  induction l generalizing n with
  | nil =>
    cases n <;> rfl
  | cons a as ih =>
    cases n with
    | zero =>
      simp [h a]
    | succ n =>
      simp [ih n]

theorem map_borrow_modify (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).borrow = a.borrow) :
    (l.modify n f).map Acct.borrow = l.map Acct.borrow := by
  induction l generalizing n with
  | nil =>
    cases n <;> rfl
  | cons a as ih =>
    cases n with
    | zero =>
      simp [h a]
    | succ n =>
      simp [ih n]

theorem totalSupply_withAcct (s : St) (who : Account) (f : Acct → Acct)
    (h : ∀ a, (f a).supply = a.supply) :
    totalSupply (s.withAcct who f) = totalSupply s := by
  unfold totalSupply St.withAcct
  rw [map_supply_modify _ _ _ h]

theorem totalBorrows_withAcct (s : St) (who : Account) (f : Acct → Acct)
    (h : ∀ a, (f a).borrow = a.borrow) :
    totalBorrows (s.withAcct who f) = totalBorrows s := by
  unfold totalBorrows St.withAcct
  rw [map_borrow_modify _ _ _ h]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  cases hub1 : updateCompBorrowIndex s with
  | none =>
    simp [hub1] at h
  | some sb1 =>
    simp [hub1] at h
    cases hdb : distributeBorrowerComp sb1 who with
    | none =>
      simp [hdb] at h
    | some m1 =>
      simp [hdb] at h
      cases hus : updateCompSupplyIndex m1 with
      | none =>
        simp [hus] at h
      | some ss1 =>
        simp [hus] at h
        cases hds : distributeSupplierComp ss1 who with
        | none =>
          simp [hds] at h
        | some m2 =>
          simp [hds, grant_eq] at h
          have hle_b := updateBorrow_some_implies_le s sb1 hub1
          have hsb1_eq : sb1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
            have h1 := updateBorrow_some_of_le s hle_b
            rw [hub1] at h1
            cases h1
            rfl
          have hdist_b_le := distributeBorrow_some_implies_le sb1 who m1 hdb
          have hsb1_acct : sb1.acct who = s.acct who := by rw [hsb1_eq]; rfl
          have hsb1_idx : sb1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hsb1_eq]
          have hle_s := updateSupply_some_implies_le m1 ss1 hus
          have hss1_eq : ss1 = { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } := by
            have h1 := updateSupply_some_of_le m1 hle_s
            rw [hus] at h1
            cases h1
            rfl
          have hdist_s_le := distributeSupply_some_implies_le ss1 who m2 hds
          have hss1_acct : ss1.acct who = m1.acct who := by rw [hss1_eq]; rfl
          have hss1_idx : ss1.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by rw [hss1_eq]
          refine ⟨m1, m2, ?_, ?_, ?_⟩
          · refine ⟨hle_b, ?_, ?_⟩
            · have h_start : accrualStart (s.acct who).borrowerIndex
                  (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
                  (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
                rw [← hsb1_acct, ← hsb1_idx]
                exact hdist_b_le
              exact h_start
            · rw [distributeBorrow_rw] at hdb
              have hsdb := subChecked_eq_some_of_le _ _ hdist_b_le
              rw [hsdb] at hdb
              simp at hdb
              cases hdb
              rw [hsb1_eq]
              apply withAcct_congr
              rfl
          · refine ⟨hle_s, ?_, ?_⟩
            · have h_start : accrualStart (m1.acct who).supplierIndex
                  (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≤
                  (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
                rw [← hss1_acct, ← hss1_idx]
                exact hdist_s_le
              exact h_start
            · rw [distributeSupply_rw] at hds
              have hsds := subChecked_eq_some_of_le _ _ hdist_s_le
              rw [hsds] at hds
              simp at hds
              cases hds
              rw [hss1_eq]
              apply withAcct_congr
              rfl
          · exact h.symm

theorem getD_supplier_le (l : List Acct) (idx : Nat) (who : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) :
    (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    exact Nat.zero_le _
  | cons a as ih =>
    cases who with
    | zero =>
      exact h a (List.Mem.head _)
    | succ n =>
      have h' : ∀ a ∈ as, a.supplierIndex ≤ idx := by
        intro b hb
        exact h b (List.Mem.tail _ hb)
      exact ih n h'

theorem getD_borrower_le (l : List Acct) (idx : Nat) (who : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) :
    (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    exact Nat.zero_le _
  | cons a as ih =>
    cases who with
    | zero =>
      exact h a (List.Mem.head _)
    | succ n =>
      have h' : ∀ a ∈ as, a.borrowerIndex ≤ idx := by
        intro b hb
        exact h b (List.Mem.tail _ hb)
      exact ih n h'

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrualStart_le_new_supply (s : St) (who : Account) (newIdx : Nat)
    (hcon : Consistent s) (hge : s.supplyState.index ≤ newIdx) :
    accrualStart (s.acct who).supplierIndex newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · simp [h0]
    by_cases h1 : compInitialIndex ≤ newIdx
    · simp [h1]
    · simp [h1]
  · simp [h0]
    have hrec_le_old : (s.acct who).supplierIndex ≤ s.supplyState.index := by
      unfold Consistent at hcon
      obtain ⟨_, _, hall⟩ := hcon
      exact getD_supplier_le s.accts s.supplyState.index who (fun a ha => (hall a ha).1)
    omega

theorem accrualStart_le_new_borrow (s : St) (who : Account) (newIdx : Nat)
    (hcon : Consistent s) (hge : s.borrowState.index ≤ newIdx) :
    accrualStart (s.acct who).borrowerIndex newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · simp [h0]
    by_cases h1 : compInitialIndex ≤ newIdx
    · simp [h1]
    · simp [h1]
  · simp [h0]
    have hrec_le_old : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
      unfold Consistent at hcon
      obtain ⟨_, _, hall⟩ := hcon
      exact getD_borrower_le s.accts s.borrowState.index who (fun a ha => (hall a ha).2)
    omega

theorem modify_self_of_ge (l : List Acct) (n : Nat) (f : Acct → Acct)
    (h : l.length ≤ n) : l.modify n f = l := by
  induction l generalizing n with
  | nil =>
    cases n <;> rfl
  | cons a as ih =>
    cases n with
    | zero =>
      simp at h
    | succ n =>
      simp at h ⊢
      simp [ih _ (by omega : as.length ≤ n)]

theorem getD_eq_default_of_ge (l : List Acct) (n : Nat) (d : Acct)
    (h : l.length ≤ n) : l.getD n d = d := by
  induction l generalizing n with
  | nil =>
    cases n <;> rfl
  | cons a as ih =>
    cases n with
    | zero =>
      simp at h
    | succ n =>
      simp at h ⊢
      exact ih n (by omega)

theorem getD_modify_eq (l : List Acct) (n : Nat) (f : Acct → Acct) (d : Acct)
    (h : n < l.length) : (l.modify n f).getD n d = f (l.getD n d) := by
  induction l generalizing n with
  | nil =>
    simp at h
  | cons a as ih =>
    cases n with
    | zero =>
      rfl
    | succ n =>
      simp only [List.modify, List.getD, List.length] at h ⊢
      exact ih n (by omega)

theorem withAcct_acct_eq (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).acct who = f (s.acct who) ∨ ¬ (who < s.accts.length) := by
  by_cases h : who < s.accts.length
  · left
    unfold St.withAcct St.acct
    exact getD_modify_eq _ _ _ _ h
  · right
    exact h

theorem withAcct_supplierIndex_eq (s : St) (who : Account) (f : Acct → Acct)
    (h : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  by_cases hlen : who < s.accts.length
  · have heq := getD_modify_eq s.accts who f noAcct hlen
    unfold St.withAcct St.acct
    rw [heq]
    exact h _
  · have hge : s.accts.length ≤ who := Nat.le_of_not_gt hlen
    have hmod := modify_self_of_ge s.accts who f hge
    unfold St.withAcct St.acct
    rw [hmod]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hcon
  cases c with
  | supplyHook who =>
    unfold comptroller
    have hle : s.supplyState.block ≤ s.blockNumber := hcon.1
    have hs1_eq := updateSupply_some_of_le s hle
    have hge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrueSide_index_ge _ _ _
    have hle_start := accrualStart_le_new_supply s who _ hcon hge
    let s1 : St := { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
    have hu : updateCompSupplyIndex s = some s1 := hs1_eq
    have hs1_acct : s1.acct who = s.acct who := rfl
    have hs1_idx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
    have hle_start_s1 : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index := by
      rw [hs1_acct, hs1_idx]
      exact hle_start
    have hsdist := subChecked_eq_some_of_le _ _ hle_start_s1
    have hdist_rw := distributeSupply_rw s1 who
    rw [hsdist] at hdist_rw
    simp at hdist_rw
    simp [hu, hdist_rw]
  | borrowHook who =>
    unfold comptroller
    have hle : s.borrowState.block ≤ s.blockNumber := hcon.2.1
    have hs1_eq := updateBorrow_some_of_le s hle
    have hge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    have hle_start := accrualStart_le_new_borrow s who _ hcon hge
    let s1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hu : updateCompBorrowIndex s = some s1 := hs1_eq
    have hs1_acct : s1.acct who = s.acct who := rfl
    have hs1_idx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    have hle_start_s1 : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
      rw [hs1_acct, hs1_idx]
      exact hle_start
    have hsdist := subChecked_eq_some_of_le _ _ hle_start_s1
    have hdist_rw := distributeBorrow_rw s1 who
    rw [hsdist] at hdist_rw
    simp at hdist_rw
    simp [hu, hdist_rw]
  | claim who =>
    unfold comptroller claimComp
    have hle_b : s.borrowState.block ≤ s.blockNumber := hcon.2.1
    have hs1_eq := updateBorrow_some_of_le s hle_b
    have hge_b : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    have hle_start_b := accrualStart_le_new_borrow s who _ hcon hge_b
    let sb1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hu_b : updateCompBorrowIndex s = some sb1 := hs1_eq
    have hsb1_acct : sb1.acct who = s.acct who := rfl
    have hsb1_idx : sb1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    have hle_start_sb1 : accrualStart (sb1.acct who).borrowerIndex sb1.borrowState.index ≤ sb1.borrowState.index := by
      rw [hsb1_acct, hsb1_idx]
      exact hle_start_b
    have hsdist_b := subChecked_eq_some_of_le _ _ hle_start_sb1
    have hdist_b_rw := distributeBorrow_rw sb1 who
    rw [hsdist_b] at hdist_b_rw
    simp at hdist_b_rw
    let m1 : St := sb1.withAcct who fun a => { a with borrowerIndex := sb1.borrowState.index, accrued := a.accrued + mulDouble a.borrow (sb1.borrowState.index - accrualStart (sb1.acct who).borrowerIndex sb1.borrowState.index) }
    have hm1_eq : distributeBorrowerComp sb1 who = some m1 := hdist_b_rw
    have hm1_supply : m1.supplyState = s.supplyState := rfl
    have hm1_block : m1.blockNumber = s.blockNumber := rfl
    have hm1_totalSupply : totalSupply m1 = totalSupply s := by
      have h1 : totalSupply sb1 = totalSupply s := rfl
      have h2 : totalSupply m1 = totalSupply sb1 := totalSupply_withAcct _ _ _ (by intro a; rfl)
      exact h2.trans h1
    have hm1_acct_supplier : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have hsb : (sb1.acct who).supplierIndex = (s.acct who).supplierIndex := rfl
      have hm : ((sb1.withAcct who fun a => { a with borrowerIndex := sb1.borrowState.index, accrued := a.accrued + mulDouble a.borrow (sb1.borrowState.index - accrualStart (sb1.acct who).borrowerIndex sb1.borrowState.index) }).acct who).supplierIndex = (sb1.acct who).supplierIndex := by
        apply withAcct_supplierIndex_eq
        intro a
        rfl
      exact hm.trans hsb
    have hle_s : m1.supplyState.block ≤ m1.blockNumber := by
      rw [hm1_supply, hm1_block]
      exact hcon.1
    have hs_s_eq := updateSupply_some_of_le m1 hle_s
    have hge_s : m1.supplyState.index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index :=
      accrueSide_index_ge _ _ _
    have hle_start_s : accrualStart (m1.acct who).supplierIndex (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
      have h_old_le_new : s.supplyState.index ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
        rw [hm1_supply, hm1_block, hm1_totalSupply]
        exact accrueSide_index_ge _ _ _
      have hle_start_s' := accrualStart_le_new_supply s who _ hcon h_old_le_new
      rw [hm1_acct_supplier]
      exact hle_start_s'
    sorry
  | setSpeeds a b =>
    sorry

theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
