import CompRewards.Spec
namespace CompRewards

/-- `updateCompSupplyIndex`: bring the supply side up to date. -/
def updateCompSupplyIndex (s : St) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
  else none

/-- `updateCompBorrowIndex`: bring the borrow side up to date. -/
def updateCompBorrowIndex (s : St) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
  else none

/-- `distributeSupplierComp`: credit `supplier` for supply rewards. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  let idx := s.supplyState.index
  let st := accrualStart (s.acct supplier).supplierIndex idx
  if st ≤ idx then
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := idx,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex idx) idx })
  else none

/-- `distributeBorrowerComp`: credit `borrower` for borrow rewards. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let idx := s.borrowState.index
  let st := accrualStart (s.acct borrower).borrowerIndex idx
  if st ≤ idx then
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := idx,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex idx) idx })
  else none

/-- `grantCompInternal`: pay out accrued COMP when the reserve covers it. -/
def grantCompInternal (s : St) (user : Account) : St := grant s user

/-- `claimComp` for one holder and one market. -/
def claimComp (s : St) (holder : Account) : Option St :=
  match updateCompBorrowIndex s with
  | none => none
  | some s1 =>
    match distributeBorrowerComp s1 holder with
    | none => none
    | some m1 =>
      match updateCompSupplyIndex m1 with
      | none => none
      | some s2 =>
        match distributeSupplierComp s2 holder with
        | none => none
        | some m2 => some (grantCompInternal m2 holder)

/-- Supply branch of `setCompSpeedInternal`. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed = supplySpeed then some s
  else
    match updateCompSupplyIndex s with
    | none => none
    | some s => some { s with supplyState := { s.supplyState with speed := supplySpeed } }

/-- Borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed = borrowSpeed then some s
  else
    match updateCompBorrowIndex s with
    | none => none
    | some s => some { s with borrowState := { s.borrowState with speed := borrowSpeed } }

/-- `setCompSpeedInternal`. -/
def setCompSpeedInternal (s : St) (supplySpeed borrowSpeed : Nat) : Option St :=
  match setSupplySpeed s supplySpeed with
  | none => none
  | some s1 => setBorrowSpeed s1 borrowSpeed

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who =>
    match updateCompSupplyIndex s with
    | none => none
    | some s1 => distributeSupplierComp s1 who
  | .borrowHook who =>
    match updateCompBorrowIndex s with
    | none => none
    | some s1 => distributeBorrowerComp s1 who
  | .claim who => claimComp s who
  | .setSpeeds a b => setCompSpeedInternal s a b

theorem accrualStart_le_of_le {r idx : Nat} (h : r ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi]
    · simp [hi]
  · simp [hr]
    exact h

theorem accrualStart_zero_le (idx : Nat) : accrualStart 0 idx ≤ idx :=
  accrualStart_le_of_le (Nat.zero_le idx)

theorem updateSupply_eq (s s' : St) :
    updateCompSupplyIndex s = some s' ↔
      s.supplyState.block ≤ s.blockNumber ∧
        s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex
  by_cases h : s.supplyState.block ≤ s.blockNumber
  · simp [h, eq_comm]
  · simp [h]

theorem updateBorrow_eq (s s' : St) :
    updateCompBorrowIndex s = some s' ↔
      s.borrowState.block ≤ s.blockNumber ∧
        s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex
  by_cases h : s.borrowState.block ≤ s.blockNumber
  · simp [h, eq_comm]
  · simp [h]

theorem distributeSupply_eq (s s' : St) (who : Account) :
    distributeSupplierComp s who = some s' ↔
      accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
        s' = s.withAcct who fun a =>
          { a with supplierIndex := s.supplyState.index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } := by
  unfold distributeSupplierComp
  simp only
  by_cases h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp [h, eq_comm]
  · simp [h]

theorem distributeBorrow_eq (s s' : St) (who : Account) :
    distributeBorrowerComp s who = some s' ↔
      accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
        s' = s.withAcct who fun a =>
          { a with borrowerIndex := s.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } := by
  unfold distributeBorrowerComp
  simp only
  by_cases h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp [h, eq_comm]
  · simp [h]

theorem accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrue_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem getD_prop {l : List Acct} {n : Nat} {d : Acct} {P : Acct → Prop}
    (hd : P d) (hall : ∀ a ∈ l, P a) : P (l.getD n d) := by
  induction l generalizing n with
  | nil =>
    simpa using hd
  | cons hd2 tl ih =>
    cases n with
    | zero =>
      exact hall _ List.mem_cons_self
    | succ n =>
      apply ih
      intro a ha
      exact hall _ (List.mem_cons_of_mem _ ha)

theorem acct_supplier_le (s : St) (who : Account)
    (hc : Consistent s) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  exact getD_prop (P := fun a => a.supplierIndex ≤ s.supplyState.index)
    (by simp [noAcct]) (fun a ha => (hc.2.2 _ ha).1)

theorem acct_borrower_le (s : St) (who : Account)
    (hc : Consistent s) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  exact getD_prop (P := fun a => a.borrowerIndex ≤ s.borrowState.index)
    (by simp [noAcct]) (fun a ha => (hc.2.2 _ ha).2)

theorem modify_getD_prop {l : List Acct} {n : Nat} {d : Acct} {f : Acct → Acct}
    {g : Acct → Nat} (hg : ∀ a, g (f a) = g a) :
    g ((l.modify n f).getD n d) = g (l.getD n d) := by
  induction l generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases n with
    | zero => exact hg hd
    | succ n => exact ih

theorem supply_acct (s : St) (who : Account) (X : Side) :
    ({ s with supplyState := X }).acct who = s.acct who := rfl

theorem supply_total (s : St) (X : Side) :
    totalSupply { s with supplyState := X } = totalSupply s := rfl

theorem borrow_acct (s : St) (who : Account) (X : Side) :
    ({ s with borrowState := X }).acct who = s.acct who := rfl

theorem borrow_total_borrows (s : St) (X : Side) :
    totalBorrows { s with borrowState := X } = totalBorrows s := rfl

theorem borrow_total_supply (s : St) (X : Side) :
    totalSupply { s with borrowState := X } = totalSupply s := rfl

theorem supply_total_borrows (s : St) (X : Side) :
    totalBorrows { s with supplyState := X } = totalBorrows s := rfl

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hupd : updateCompSupplyIndex s with
  | none =>
    simp [hupd] at h
  | some s1 =>
    simp [hupd] at h
    rw [distributeSupply_eq] at h
    rw [updateSupply_eq] at hupd
    obtain ⟨hblock, rfl⟩ := hupd
    obtain ⟨hstart, rfl⟩ := h
    unfold SupplyDistributed
    simp only [St.acct, totalSupply] at hstart ⊢
    refine ⟨hblock, hstart, rfl⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hupd : updateCompBorrowIndex s with
  | none =>
    simp [hupd] at h
  | some s1 =>
    simp [hupd] at h
    rw [distributeBorrow_eq] at h
    rw [updateBorrow_eq] at hupd
    obtain ⟨hblock, rfl⟩ := hupd
    obtain ⟨hstart, rfl⟩ := h
    unfold BorrowDistributed
    simp only [St.acct, totalBorrows] at hstart ⊢
    refine ⟨hblock, hstart, rfl⟩

theorem borrowCombined {s s1 m1 : St} {who : Account}
    (h1 : updateCompBorrowIndex s = some s1)
    (h2 : distributeBorrowerComp s1 who = some m1) :
    BorrowDistributed s who m1 := by
  rw [updateBorrow_eq] at h1
  rw [distributeBorrow_eq] at h2
  obtain ⟨hblock, rfl⟩ := h1
  obtain ⟨hstart, rfl⟩ := h2
  unfold BorrowDistributed
  simp only [St.acct, totalBorrows] at hstart ⊢
  exact ⟨hblock, hstart, rfl⟩

theorem supplyCombined {s s1 m1 : St} {who : Account}
    (h1 : updateCompSupplyIndex s = some s1)
    (h2 : distributeSupplierComp s1 who = some m1) :
    SupplyDistributed s who m1 := by
  rw [updateSupply_eq] at h1
  rw [distributeSupply_eq] at h2
  obtain ⟨hblock, rfl⟩ := h1
  obtain ⟨hstart, rfl⟩ := h2
  unfold SupplyDistributed
  simp only [St.acct, totalSupply] at hstart ⊢
  exact ⟨hblock, hstart, rfl⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  cases h1 : updateCompBorrowIndex s with
  | none =>
    simp [h1] at h
  | some s1 =>
    simp [h1] at h
    cases h2 : distributeBorrowerComp s1 who with
    | none =>
      simp [h2] at h
    | some m1 =>
      simp [h2] at h
      cases h3 : updateCompSupplyIndex m1 with
      | none =>
        simp [h3] at h
      | some s2 =>
        simp [h3] at h
        cases h4 : distributeSupplierComp s2 who with
        | none =>
          simp [h4] at h
        | some m2 =>
          simp [h4] at h
          subst h
          exact ⟨m1, m2, borrowCombined h1 h2, supplyCombined h3 h4, rfl⟩

theorem setSupply_eq (s s' : St) (a : Nat) :
    setSupplySpeed s a = some s' ↔
      ((s.supplyState.speed = a ∧ s' = s) ∨
        (s.supplyState.speed ≠ a ∧ s.supplyState.block ≤ s.blockNumber ∧
          s' = { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
            supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })) := by
  unfold setSupplySpeed
  by_cases h : s.supplyState.speed = a
  · rw [if_pos h]
    constructor
    · intro heq
      have hs : s = s' := Option.some_inj.mp heq
      subst hs
      exact Or.inl ⟨h, rfl⟩
    · intro hor
      cases hor with
      | inl hl =>
        obtain ⟨_, rfl⟩ := hl
        rfl
      | inr hr => exact absurd h hr.1
  · rw [if_neg h]
    constructor
    · intro s1
      cases hupd : updateCompSupplyIndex s with
      | none =>
        simp [hupd] at s1
      | some u =>
        simp [hupd] at s1
        rw [updateSupply_eq] at hupd
        obtain ⟨hb, rfl⟩ := hupd
        subst s1
        exact Or.inr ⟨h, hb, rfl⟩
    · intro hor
      cases hor with
      | inl hl => exact absurd hl.1 h
      | inr hr =>
        obtain ⟨hne, hb, rfl⟩ := hr
        have hupd : updateCompSupplyIndex s =
            some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
          rw [updateSupply_eq]
          exact ⟨hb, rfl⟩
        simp [hupd]

theorem setBorrow_eq (s s' : St) (b : Nat) :
    setBorrowSpeed s b = some s' ↔
      ((s.borrowState.speed = b ∧ s' = s) ∨
        (s.borrowState.speed ≠ b ∧ s.borrowState.block ≤ s.blockNumber ∧
          s' = { { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with
            borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } })) := by
  unfold setBorrowSpeed
  by_cases h : s.borrowState.speed = b
  · rw [if_pos h]
    constructor
    · intro heq
      have hs : s = s' := Option.some_inj.mp heq
      subst hs
      exact Or.inl ⟨h, rfl⟩
    · intro hor
      cases hor with
      | inl hl =>
        obtain ⟨_, rfl⟩ := hl
        rfl
      | inr hr => exact absurd h hr.1
  · rw [if_neg h]
    constructor
    · intro s1
      cases hupd : updateCompBorrowIndex s with
      | none =>
        simp [hupd] at s1
      | some u =>
        simp [hupd] at s1
        rw [updateBorrow_eq] at hupd
        obtain ⟨hb, rfl⟩ := hupd
        subst s1
        exact Or.inr ⟨h, hb, rfl⟩
    · intro hor
      cases hor with
      | inl hl => exact absurd hl.1 h
      | inr hr =>
        obtain ⟨hne, hb, rfl⟩ := hr
        have hupd : updateCompBorrowIndex s =
            some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
          rw [updateBorrow_eq]
          exact ⟨hb, rfl⟩
        simp [hupd]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller, setCompSpeedInternal] at h
  cases hsup : setSupplySpeed s a with
  | none =>
    simp [hsup] at h
  | some mid =>
    simp [hsup] at h
    rw [setSupply_eq] at hsup
    rw [setBorrow_eq] at h
    cases hsup with
    | inl hl =>
      obtain ⟨heq, rfl⟩ := hl
      cases h with
      | inl hr =>
        obtain ⟨heqb, rfl⟩ := hr
        unfold SpeedsSet
        simp [heq, heqb]
      | inr hr =>
        obtain ⟨hne, hb, rfl⟩ := hr
        unfold SpeedsSet
        refine ⟨fun hcon => False.elim (hcon heq), fun _ => hb, ?_⟩
        simp [heq, hne]
    | inr hr =>
      obtain ⟨hne, hb, rfl⟩ := hr
      cases h with
      | inl hl =>
        obtain ⟨heqb, rfl⟩ := hl
        have heqb_s : s.borrowState.speed = b := by simpa using heqb
        unfold SpeedsSet
        refine ⟨fun _ => hb, fun hcon => False.elim (hcon heqb_s), ?_⟩
        simp [heqb_s, hne]
      | inr hc =>
        obtain ⟨hne2, hb2, rfl⟩ := hc
        have hne2_s : s.borrowState.speed ≠ b := by simpa using hne2
        have hb2_s : s.borrowState.block ≤ s.blockNumber := by simpa using hb2
        unfold SpeedsSet
        refine ⟨fun _ => hb, fun _ => hb2_s, ?_⟩
        simp [hne, hne2_s, supply_total_borrows]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    simp only [comptroller]
    have hupd : updateCompSupplyIndex s =
        some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      rw [updateSupply_eq]
      exact ⟨hc.1, rfl⟩
    rw [hupd]
    have hrec : (s.acct who).supplierIndex ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      exact Nat.le_trans (acct_supplier_le s who hc)
        (accrue_index_ge s.supplyState s.blockNumber (totalSupply s))
    have hcond : accrualStart
        (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).acct who).supplierIndex
        (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index) ≤
        (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index) := by
      apply accrualStart_le_of_le
      simpa using hrec
    have hdist : distributeSupplierComp
        { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who =
        some (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).withAcct who fun a =>
          { a with supplierIndex :=
              (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index),
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex
                       (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index))
                     (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index) }) := by
      rw [distributeSupply_eq]
      exact ⟨hcond, rfl⟩
    simp [hdist]
  | borrowHook who =>
    simp only [comptroller]
    have hupd : updateCompBorrowIndex s =
        some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      rw [updateBorrow_eq]
      exact ⟨hc.2.1, rfl⟩
    rw [hupd]
    have hrec : (s.acct who).borrowerIndex ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      exact Nat.le_trans (acct_borrower_le s who hc)
        (accrue_index_ge s.borrowState s.blockNumber (totalBorrows s))
    have hcond : accrualStart
        (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).acct who).borrowerIndex
        (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ≤
        (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) := by
      apply accrualStart_le_of_le
      simpa using hrec
    have hdist : distributeBorrowerComp
        { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who =
        some (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).withAcct who fun a =>
          { a with borrowerIndex :=
              (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index),
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex
                       (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index))
                     (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) }) := by
      rw [distributeBorrow_eq]
      exact ⟨hcond, rfl⟩
    simp [hdist]
  | claim who =>
    simp only [comptroller, claimComp]
    cases hupdB : updateCompBorrowIndex s with
    | none =>
      have hsome : updateCompBorrowIndex s =
          some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
        rw [updateBorrow_eq]
        exact ⟨hc.2.1, rfl⟩
      rw [hsome] at hupdB
      contradiction
    | some s1 =>
      simp only [hupdB]
      cases hdistB : distributeBorrowerComp s1 who with
      | none =>
        rw [updateBorrow_eq] at hupdB
        obtain ⟨_, rfl⟩ := hupdB
        have hrec : (s.acct who).borrowerIndex ≤
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
          Nat.le_trans (acct_borrower_le s who hc)
            (accrue_index_ge s.borrowState s.blockNumber (totalBorrows s))
        have hcond : accrualStart (s.acct who).borrowerIndex
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
          apply accrualStart_le_of_le
          simpa using hrec
        have hsome : distributeBorrowerComp
            { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who =
            some _ := by
          rw [distributeBorrow_eq]
          exact ⟨by simpa using hcond, rfl⟩
        rw [hsome] at hdistB
        contradiction
      | some m1 =>
        simp only [hdistB]
        cases hupdS : updateCompSupplyIndex m1 with
        | none =>
          have hm1b : m1.supplyState.block ≤ m1.blockNumber := by
            rw [distributeBorrow_eq] at hdistB
            obtain ⟨_, rfl⟩ := hdistB
            rw [updateBorrow_eq] at hupdB
            obtain ⟨_, rfl⟩ := hupdB
            exact hc.1
          have hsome : updateCompSupplyIndex m1 = some _ := by
            rw [updateSupply_eq]
            exact ⟨hm1b, rfl⟩
          rw [hsome] at hupdS
          contradiction
        | some s2 =>
          simp only [hupdS]
          cases hdistS : distributeSupplierComp s2 who with
          | none =>
            rw [distributeBorrow_eq] at hdistB
            obtain ⟨_, rfl⟩ := hdistB
            rw [updateBorrow_eq] at hupdB
            obtain ⟨_, rfl⟩ := hupdB
            rw [updateSupply_eq] at hupdS
            obtain ⟨_, rfl⟩ := hupdS
            have hrec : (s.acct who).supplierIndex ≤
                (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
              exact Nat.le_trans (acct_supplier_le s who hc)
                (accrue_index_ge s.supplyState s.blockNumber (totalSupply s))
            have hcond : accrualStart (s.acct who).supplierIndex
                (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
                (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
              apply accrualStart_le_of_le
              simpa using hrec
            have hsome : distributeSupplierComp _ who = some _ := by
              rw [distributeSupply_eq]
              exact ⟨by simpa using hcond, rfl⟩
            rw [hsome] at hdistS
            contradiction
          | some m2 =>
            simp only [hdistS]
            trivial
  | setSpeeds a b =>
    simp only [comptroller, setCompSpeedInternal]
    cases hsup : setSupplySpeed s a with
    | none =>
      have hcontra : setSupplySpeed s a ≠ none := by
        unfold setSupplySpeed
        by_cases heq : s.supplyState.speed = a
        · simp [heq, hsup] at hsup ⊢
          contradiction
        · have hb : s.supplyState.block ≤ s.blockNumber := hc.1
          have hupd : updateCompSupplyIndex s =
              some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
            rw [updateSupply_eq]
            exact ⟨hb, rfl⟩
          simp [heq, hupd] at hsup
      contradiction
    | some mid =>
      simp only [hsup]
      rw [setSupply_eq] at hsup
      have hmid_borrow_block : mid.borrowState.block ≤ mid.blockNumber := by
        cases hsup with
        | inl hl =>
          obtain ⟨_, rfl⟩ := hl
          exact hc.2.1
        | inr hr =>
          obtain ⟨_, _, rfl⟩ := hr
          exact hc.2.1
      have hbor : (setBorrowSpeed mid b).isSome := by
        unfold setBorrowSpeed
        by_cases heq : mid.borrowState.speed = b
        · simp [heq]
        · have hupd : updateCompBorrowIndex mid =
              some { mid with borrowState := accrueSide mid.borrowState mid.blockNumber (totalBorrows mid) } := by
            rw [updateBorrow_eq]
            exact ⟨hmid_borrow_block, rfl⟩
          simp [heq, hupd]
      exact hbor
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
