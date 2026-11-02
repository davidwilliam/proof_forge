import CompRewards.Spec
namespace CompRewards

def fraction (a b : Nat) : Nat := a * doubleScale / b

def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

theorem subChecked_some {a b d : Nat} : subChecked a b = some d ↔ b ≤ a ∧ d = a - b := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h, Eq.comm]

theorem subChecked_none {a b : Nat} : subChecked a b = none ↔ ¬ b ≤ a := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

theorem subChecked_isSome {a b : Nat} : (subChecked a b).isSome = decide (b ≤ a) := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

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
  let st := accrualStart (s.acct supplier).supplierIndex s.supplyState.index
  match subChecked s.supplyState.index st with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })

def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let st := accrualStart (s.acct borrower).borrowerIndex s.borrowState.index
  match subChecked s.borrowState.index st with
  | none => none
  | some _ =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })

def grantCompInternal (s : St) (user : Account) : St := grant s user

def claimComp (s : St) (holder : Account) : Option St := do
  let s ← updateCompBorrowIndex s
  let s ← distributeBorrowerComp s holder
  let s ← updateCompSupplyIndex s
  let s ← distributeSupplierComp s holder
  return grantCompInternal s holder

def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed = supplySpeed then some s
  else if s.supplyState.block ≤ s.blockNumber then
    some { s with supplyState :=
      { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := supplySpeed } }
  else none

def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed = borrowSpeed then some s
  else if s.borrowState.block ≤ s.blockNumber then
    some { s with borrowState :=
      { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := borrowSpeed } }
  else none

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

theorem accrualStart_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded)
      = accrualStart recorded index := by
  simp only [accrualStart]
  by_cases h0 : recorded = 0 <;> simp [h0]

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem updateSupply_eq_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s
      = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex
  have hsc : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked; simp [h]
  rw [hsc]
  by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [h1]
    obtain ⟨p1, p2⟩ := h1
    by_cases h2 : totalSupply s > 0
    · simp [p1, p2, h2, accrueSide, fraction]
    · simp [p1, p2, h2, accrueSide, fraction]
  · simp only [h1]
    by_cases h3 : s.blockNumber - s.supplyState.block > 0
    · have hs0 : s.supplyState.speed = 0 := by omega
      have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        omega
      simp [h3, hs0, hcond, accrueSide]
    · have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have hbl : s.supplyState.block = s.blockNumber := by omega
      have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        omega
      simp only [h3]
      simp [hcond, accrueSide, hzero, hbl]
      cases s with | mk b sup bor res accts =>
        cases sup with | mk i bl sp =>
          simp at hbl ⊢
          simp [hbl]

theorem updateBorrow_eq_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s
      = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex
  have hsc : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [h]
  rw [hsc]
  by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [h1]
    obtain ⟨p1, p2⟩ := h1
    by_cases h2 : totalBorrows s > 0
    · simp [p1, p2, h2, accrueSide, fraction]
    · simp [p1, p2, h2, accrueSide, fraction]
  · simp only [h1]
    by_cases h3 : s.blockNumber - s.borrowState.block > 0
    · have hs0 : s.borrowState.speed = 0 := by omega
      have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        omega
      simp [h3, hs0, hcond, accrueSide]
    · have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have hbl : s.borrowState.block = s.blockNumber := by omega
      have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        omega
      simp only [h3]
      simp [hcond, accrueSide, hzero, hbl]
      cases s with | mk b sup bor res accts =>
        cases bor with | mk i bl sp =>
          simp at hbl ⊢
          simp [hbl]

theorem distributeSupply_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who
      = some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold distributeSupplierComp
  have hsc : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    unfold subChecked; simp [h]
  simp only [hsc]

theorem distributeBorrow_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who
      = some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold distributeBorrowerComp
  have hsc : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    unfold subChecked; simp [h]
  simp only [hsc]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := rfl

theorem accrualStart_le (r idx : Nat) (h : r ≤ idx) : accrualStart r idx ≤ idx := by
  simp only [accrualStart]
  by_cases h0 : r = 0
  · simp only [h0]
    by_cases h1 : compInitialIndex ≤ idx <;> simp [h1]
  · simp [h0, h]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem list_getD_supplier_le (l : List Acct) (idx : Nat)
    (hc : ∀ a ∈ l, a.supplierIndex ≤ idx) (who : Nat) :
    (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp
      exact hc x (by simp)
    | succ n =>
      simp
      apply ih
      intro a ha
      exact hc a (by simp [ha])

theorem list_getD_borrower_le (l : List Acct) (idx : Nat)
    (hc : ∀ a ∈ l, a.borrowerIndex ≤ idx) (who : Nat) :
    (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp
      exact hc x (by simp)
    | succ n =>
      simp
      apply ih
      intro a ha
      exact hc a (by simp [ha])

theorem acct_supplier_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct Consistent at *
  obtain ⟨_, _, hall⟩ := hc
  have h1 : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := by
    intro a ha
    exact (hall a ha).1
  exact list_getD_supplier_le s.accts s.supplyState.index h1 who

theorem acct_borrower_le (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct Consistent at *
  obtain ⟨_, _, hall⟩ := hc
  have h1 : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := by
    intro a ha
    exact (hall a ha).2
  exact list_getD_borrower_le s.accts s.borrowState.index h1 who

theorem updateSupply_some_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber)
    (m : St) (hm : updateCompSupplyIndex s = some m) :
    m = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have heq := updateSupply_eq_some s h
  rw [hm] at heq
  exact Option.some_inj.mp heq

theorem updateSupply_none_of_gt (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  have hsc : subChecked s.blockNumber s.supplyState.block = none := by
    unfold subChecked; simp [h]
  simp [hsc]

theorem updateBorrow_some_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber)
    (m : St) (hm : updateCompBorrowIndex s = some m) :
    m = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have heq := updateBorrow_eq_some s h
  rw [hm] at heq
  exact Option.some_inj.mp heq

theorem updateBorrow_none_of_gt (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  have hsc : subChecked s.blockNumber s.borrowState.block = none := by
    unfold subChecked; simp [h]
  simp [hsc]

theorem updateSupply_implies_le (s : St) (m : St)
    (hm : updateCompSupplyIndex s = some m) : s.supplyState.block ≤ s.blockNumber := by
  by_cases h : s.supplyState.block ≤ s.blockNumber
  · exact h
  · have hnone := updateSupply_none_of_gt s h
    rw [hnone] at hm
    contradiction

theorem updateBorrow_implies_le (s : St) (m : St)
    (hm : updateCompBorrowIndex s = some m) : s.borrowState.block ≤ s.blockNumber := by
  by_cases h : s.borrowState.block ≤ s.blockNumber
  · exact h
  · have hnone := updateBorrow_none_of_gt s h
    rw [hnone] at hm
    contradiction

theorem distributeSupply_implies_le (s : St) (who : Account) (s' : St)
    (hm : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  unfold distributeSupplierComp at hm
  by_cases h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · exact h
  · have hsc : subChecked s.supplyState.index
        (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none := by
      unfold subChecked; simp [h]
    simp [hsc] at hm

theorem distributeBorrow_implies_le (s : St) (who : Account) (s' : St)
    (hm : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  unfold distributeBorrowerComp at hm
  by_cases h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · exact h
  · have hsc : subChecked s.borrowState.index
        (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none := by
      unfold subChecked; simp [h]
    simp [hsc] at hm

theorem distributeSupply_result (s : St) (who : Account) (s' : St)
    (hm : distributeSupplierComp s who = some s')
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    s' = s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } := by
  have heq := distributeSupply_eq s who h
  rw [hm] at heq
  exact Option.some_inj.mp heq

theorem distributeBorrow_result (s : St) (who : Account) (s' : St)
    (hm : distributeBorrowerComp s who = some s')
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    s' = s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } := by
  have heq := distributeBorrow_eq s who h
  rw [hm] at heq
  exact Option.some_inj.mp heq

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hmid : updateCompSupplyIndex s with
  | none =>
    simp [hmid] at h
  | some m =>
    simp [hmid] at h
    have hle1 : s.supplyState.block ≤ s.blockNumber :=
      updateSupply_implies_le s m hmid
    have hm_eq : m = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
      updateSupply_some_of_le s hle1 m hmid
    have hle2 : accrualStart (m.acct who).supplierIndex m.supplyState.index ≤ m.supplyState.index :=
      distributeSupply_implies_le m who s' h
    have hs_eq : s' = m.withAcct who fun a =>
        { a with supplierIndex := m.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex m.supplyState.index) m.supplyState.index } :=
      distributeSupply_result m who s' h hle2
    have haccts : m.accts = s.accts := by rw [hm_eq]
    have hidx : m.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hm_eq]
    have hacct : (m.acct who) = (s.acct who) := by
      unfold St.acct
      rw [haccts]
    have hle2' : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [← hacct, ← hidx]
      exact hle2
    refine ⟨hle1, hle2', ?_⟩
    rw [hs_eq, hm_eq]
    unfold St.withAcct
    simp

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hmid : updateCompBorrowIndex s with
  | none =>
    simp [hmid] at h
  | some m =>
    simp [hmid] at h
    have hle1 : s.borrowState.block ≤ s.blockNumber :=
      updateBorrow_implies_le s m hmid
    have hm_eq : m = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
      updateBorrow_some_of_le s hle1 m hmid
    have hle2 : accrualStart (m.acct who).borrowerIndex m.borrowState.index ≤ m.borrowState.index :=
      distributeBorrow_implies_le m who s' h
    have hs_eq : s' = m.withAcct who fun a =>
        { a with borrowerIndex := m.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex m.borrowState.index) m.borrowState.index } :=
      distributeBorrow_result m who s' h hle2
    have haccts : m.accts = s.accts := by rw [hm_eq]
    have hidx : m.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hm_eq]
    have hacct : (m.acct who) = (s.acct who) := by
      unfold St.acct
      rw [haccts]
    have hle2' : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [← hacct, ← hidx]
      exact hle2
    refine ⟨hle1, hle2', ?_⟩
    rw [hs_eq, hm_eq]
    unfold St.withAcct
    simp

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  cases hb : updateCompBorrowIndex s with
  | none =>
    simp [hb] at h
  | some b1 =>
    simp [hb] at h
    cases hdb : distributeBorrowerComp b1 who with
    | none =>
      simp [hdb] at h
    | some m1 =>
      simp [hdb] at h
      cases hs : updateCompSupplyIndex m1 with
      | none =>
        simp [hs] at h
      | some s1 =>
        simp [hs] at h
        cases hds : distributeSupplierComp s1 who with
        | none =>
          simp [hds] at h
        | some m2 =>
          simp [hds, grant_eq] at h
          have hle_b1 : s.borrowState.block ≤ s.blockNumber :=
            updateBorrow_implies_le s b1 hb
          have hb1_eq : b1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
            updateBorrow_some_of_le s hle_b1 b1 hb
          have hle_db : accrualStart (b1.acct who).borrowerIndex b1.borrowState.index ≤ b1.borrowState.index :=
            distributeBorrow_implies_le b1 who m1 hdb
          have hm1_eq : m1 = b1.withAcct who fun a =>
              { a with borrowerIndex := b1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index } := by
            exact distributeBorrow_result b1 who m1 hdb hle_db
          have haccts_b1 : b1.accts = s.accts := by rw [hb1_eq]
          have hidx_b1 : b1.borrowState.index =
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hb1_eq]
          have hacct_b1 : (b1.acct who) = (s.acct who) := by
            unfold St.acct; rw [haccts_b1]
          have hle_db' : accrualStart (s.acct who).borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
            rw [← hacct_b1, ← hidx_b1]; exact hle_db
          have hBorrow : BorrowDistributed s who m1 := by
            refine ⟨hle_b1, hle_db', ?_⟩
            rw [hm1_eq, hb1_eq]
            unfold St.withAcct
            simp
          have hle_s1' : m1.supplyState.block ≤ m1.blockNumber :=
            updateSupply_implies_le m1 s1 hs
          have hs1_eq : s1 = ({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St) :=
            updateSupply_some_of_le m1 hle_s1' s1 hs
          have hle_ds : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤
              s1.supplyState.index :=
            distributeSupply_implies_le s1 who m2 hds
          have hm2_eq : m2 = s1.withAcct who fun a =>
              { a with supplierIndex := s1.supplyState.index,
                       accrued := a.accrued + creditFor a.supply
                         (accrualStart a.supplierIndex s1.supplyState.index) s1.supplyState.index } :=
            distributeSupply_result s1 who m2 hds hle_ds
          have hs1_accts : s1.accts = m1.accts := by rw [hs1_eq]
          have hs1_idx : s1.supplyState.index =
              (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by rw [hs1_eq]
          have hs1_acct : (s1.acct who) = (m1.acct who) := by
            unfold St.acct; rw [hs1_accts]
          have hle_ds' : accrualStart (m1.acct who).supplierIndex
              (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≤
              (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
            rw [← hs1_acct, ← hs1_idx]; exact hle_ds
          have hSupply : SupplyDistributed m1 who m2 := by
            refine ⟨hle_s1', hle_ds', ?_⟩
            rw [hm2_eq, hs1_eq]
            unfold St.withAcct
            simp
          refine ⟨m1, m2, hBorrow, hSupply, ?_⟩
          rw [h]

theorem setSupplySpeed_result (s : St) (sp : Nat) (s' : St)
    (h : setSupplySpeed s sp = some s') :
    (s.supplyState.speed ≠ sp → s.supplyState.block ≤ s.blockNumber) ∧
    s' = (if s.supplyState.speed = sp then s else
      { (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St))
        with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sp } }) := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = sp
  · simp [heq] at h
    subst h
    refine ⟨fun hne => absurd heq hne, ?_⟩
    simp [heq]
  · simp [heq] at h
    by_cases hle : s.supplyState.block ≤ s.blockNumber
    · simp [hle] at h
      subst h
      refine ⟨fun _ => hle, ?_⟩
      simp [heq]
    · simp [hle] at h

theorem setBorrowSpeed_result (s : St) (sp : Nat) (s' : St)
    (h : setBorrowSpeed s sp = some s') :
    (s.borrowState.speed ≠ sp → s.borrowState.block ≤ s.blockNumber) ∧
    s' = (if s.borrowState.speed = sp then s else
      { (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St))
        with borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := sp } }) := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = sp
  · simp [heq] at h
    subst h
    refine ⟨fun hne => absurd heq hne, ?_⟩
    simp [heq]
  · simp [heq] at h
    by_cases hle : s.borrowState.block ≤ s.blockNumber
    · simp [hle] at h
      subst h
      refine ⟨fun _ => hle, ?_⟩
      simp [heq]
    · simp [hle] at h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  cases hmid : setSupplySpeed s a with
  | none =>
    simp [hmid] at h
  | some m =>
    simp [hmid] at h
    obtain ⟨hle_sup, hsup_eq⟩ := setSupplySpeed_result s a m hmid
    obtain ⟨hle_bor, hbor_eq⟩ := setBorrowSpeed_result m b s' h
    have hm_accts : m.accts = s.accts := by
      rw [hsup_eq]
      by_cases heq : s.supplyState.speed = a <;> simp [heq]
    have hm_borrow : m.borrowState = s.borrowState := by
      rw [hsup_eq]
      by_cases heq : s.supplyState.speed = a <;> simp [heq]
    have hm_block : m.blockNumber = s.blockNumber := by
      rw [hsup_eq]
      by_cases heq : s.supplyState.speed = a <;> simp [heq]
    have htotal_m : totalSupply m = totalSupply s := by
      unfold totalSupply; rw [hm_accts]
    have hle_sup2 : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber := hle_sup
    have hle_bor2 : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
      intro hne
      have hne_m : m.borrowState.speed ≠ b := by rw [hm_borrow]; exact hne
      have := hle_bor hne_m
      rw [hm_borrow, hm_block] at this
      exact this
    refine ⟨hle_sup2, hle_bor2, ?_⟩
    have hm_total_b : totalBorrows m = totalBorrows s := by
      unfold totalBorrows; rw [hm_accts]
    by_cases heq_a : s.supplyState.speed = a
    · have hm_eq : m = s := by
        rw [hsup_eq]
        simp [heq_a]
      by_cases heq_b : s.borrowState.speed = b
      · have heq_bm : m.borrowState.speed = b := by rw [hm_borrow, heq_b]
        have hs_eq : s' = m := by
          rw [hbor_eq]
          simp [heq_bm]
        rw [hs_eq, hm_eq]
        simp [heq_a, heq_b]
      · have heq_bm : ¬ m.borrowState.speed = b := by
          intro heq; apply heq_b; rw [← hm_borrow, heq]
        have hs_eq : s' = ({ m with borrowState :=
            { accrueSide m.borrowState m.blockNumber (totalBorrows m) with speed := b } } : St) := by
          rw [hbor_eq]
          simp [heq_bm]
        rw [hs_eq, hm_eq]
        simp [heq_a, heq_b]
    · have hm_eq : m = ({ s with supplyState :=
          { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } : St) := by
        rw [hsup_eq]
        simp [heq_a]
      by_cases heq_b : s.borrowState.speed = b
      · have heq_bm : m.borrowState.speed = b := by rw [hm_borrow, heq_b]
        have hs_eq : s' = m := by
          rw [hbor_eq]
          simp [heq_bm]
        rw [hs_eq, hm_eq]
        simp [heq_a, heq_b]
      · have heq_bm : ¬ m.borrowState.speed = b := by
          intro heq; apply heq_b; rw [← hm_borrow, heq]
        have hs_eq : s' = ({ m with borrowState :=
            { accrueSide m.borrowState m.blockNumber (totalBorrows m) with speed := b } } : St) := by
          rw [hbor_eq]
          simp [heq_bm]
        rw [hs_eq, hm_total_b, hm_borrow, hm_block, hm_eq]
        simp only [heq_a, heq_b]
        cases s with
        | mk b sup bor res accts =>
          simp

instance instInhabitedAcct : Inhabited Acct := ⟨noAcct⟩

theorem preserve_supplier (l : List Acct) (who : Nat)
    (f : Acct → Acct) (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    (((l.modify who f).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex) := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons x xs ih =>
    cases who with
    | zero =>
      have h1 : (((x :: xs).modify 0 f).getD 0 noAcct = f x) := rfl
      have h2 : ((x :: xs).getD 0 noAcct = x) := rfl
      rw [h1, h2]
      exact hf x
    | succ n =>
      have h1 : (((x :: xs).modify (n+1) f).getD (n+1) noAcct = ((xs.modify n f).getD n noAcct)) := rfl
      have h2 : (((x :: xs).getD (n+1) noAcct) = (xs.getD n noAcct)) := rfl
      rw [h1, h2]
      exact ih n

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsup_bl, hbor_bl, hall⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    have hle : s.supplyState.block ≤ s.blockNumber := hsup_bl
    have hup_eq := updateSupply_eq_some s hle
    have hacct_le : (s.acct who).supplierIndex ≤ s.supplyState.index :=
      acct_supplier_le s ⟨hsup_bl, hbor_bl, hall⟩ who
    have hidx_ge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrueSide_index_ge _ _ _
    have hle_acct : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      omega
    have hle_start := accrualStart_le _ _ hle_acct
    have hdist_eq := distributeSupply_eq
      ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) who hle_start
    simp [hup_eq, hdist_eq]
  | borrowHook who =>
    unfold comptroller
    have hle : s.borrowState.block ≤ s.blockNumber := hbor_bl
    have hup_eq := updateBorrow_eq_some s hle
    have hacct_le : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
      acct_borrower_le s ⟨hsup_bl, hbor_bl, hall⟩ who
    have hidx_ge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    have hle_acct : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      omega
    have hle_start := accrualStart_le _ _ hle_acct
    let b1 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hb1_eq : b1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := rfl
    have hacct_b1 : (b1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
      rw [hb1_eq]; unfold St.acct; simp
    have hidx_b1 : b1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hb1_eq]
    have hle_start_b1 : accrualStart (b1.acct who).borrowerIndex b1.borrowState.index ≤ b1.borrowState.index := by
      rw [hacct_b1, hidx_b1]; exact hle_start
    have hdist_eq := distributeBorrow_eq b1 who hle_start_b1
    simp [hup_eq, hb1_eq, hdist_eq]
  | claim who =>
    unfold comptroller claimComp
    cases hup_b : updateCompBorrowIndex s with
    | none =>
      have hle : s.borrowState.block ≤ s.blockNumber := hbor_bl
      have hup_eq := updateBorrow_eq_some s hle
      rw [hup_b] at hup_eq
      contradiction
    | some b1 =>
      cases hdist_b : distributeBorrowerComp b1 who with
      | none =>
        have hle : s.borrowState.block ≤ s.blockNumber := hbor_bl
        have hb1_eq : b1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) :=
          updateBorrow_some_of_le s hle b1 hup_b
        have hacct_le : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
          acct_borrower_le s ⟨hsup_bl, hbor_bl, hall⟩ who
        have hidx_ge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
          accrueSide_index_ge _ _ _
        have hle_acct : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
          omega
        have hle_start := accrualStart_le _ _ hle_acct
        have hacct_b1 : (b1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
          rw [hb1_eq]; unfold St.acct; simp
        have hidx_b1 : b1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
          rw [hb1_eq]
        have hle_start_b1 : accrualStart (b1.acct who).borrowerIndex b1.borrowState.index ≤ b1.borrowState.index := by
          rw [hacct_b1, hidx_b1]; exact hle_start
        have hdist_eq := distributeBorrow_eq b1 who hle_start_b1
        rw [hdist_b] at hdist_eq
        contradiction
      | some m1 =>
        have hle : s.borrowState.block ≤ s.blockNumber := hbor_bl
        have hb1_eq : b1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) :=
          updateBorrow_some_of_le s hle b1 hup_b
        have hacct_le : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
          acct_borrower_le s ⟨hsup_bl, hbor_bl, hall⟩ who
        have hidx_ge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
          accrueSide_index_ge _ _ _
        have hle_acct : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
          omega
        have hle_start := accrualStart_le _ _ hle_acct
        have hacct_b1 : (b1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
          rw [hb1_eq]; unfold St.acct; simp
        have hidx_b1 : b1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
          rw [hb1_eq]
        have hle_start_b1 : accrualStart (b1.acct who).borrowerIndex b1.borrowState.index ≤ b1.borrowState.index := by
          rw [hacct_b1, hidx_b1]; exact hle_start
        have hdist_eq := distributeBorrow_eq b1 who hle_start_b1
        have hm1_eq : m1 = b1.withAcct who (fun a => ({ a with borrowerIndex := b1.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex b1.borrowState.index) b1.borrowState.index } : Acct)) :=
          distributeBorrow_result b1 who m1 hdist_b hle_start_b1
        sorry
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed
    by_cases heq_a : s.supplyState.speed = a
    · simp [heq_a]
      by_cases heq_b : s.borrowState.speed = b
      · simp [heq_b]
      · simp [heq_b]
        have hle : s.borrowState.block ≤ s.blockNumber := hbor_bl
        simp [hle]
    · simp [heq_a]
      have hle_sup : s.supplyState.block ≤ s.blockNumber := hsup_bl
      simp [hle_sup]
      cases hmid : setSupplySpeed s a with
      | none =>
        have hle2 : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber := by
          have ⟨hle_sup2, _⟩ := setSupplySpeed_result s a _ hmid
          exact hle_sup2
        sorry
      | some m =>
        sorry

theorem req_rewards_bounded : RewardsBounded comptroller := sorry

theorem req_account_bounded : AccountBounded comptroller := sorry

theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
