import CompRewards.Spec

namespace CompRewards

def supplyUp (s : St) : Side :=
  accrueSide s.supplyState s.blockNumber (totalSupply s)

def borrowUp (s : St) : Side :=
  accrueSide s.borrowState s.blockNumber (totalBorrows s)

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem supplyUp_block (s : St) : (supplyUp s).block = s.blockNumber :=
  accrueSide_block _ _ _

theorem borrowUp_block (s : St) : (borrowUp s).block = s.blockNumber :=
  accrueSide_block _ _ _

theorem supplyUp_index_ge (s : St) :
    s.supplyState.index ≤ (supplyUp s).index :=
  accrueSide_index_ge _ _ _

theorem borrowUp_index_ge (s : St) :
    s.borrowState.index ≤ (borrowUp s).index :=
  accrueSide_index_ge _ _ _

theorem accrualStart_le_of_le {recorded index : Nat}
    (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  split
  · next hr =>
    split
    · assumption
    · exact Nat.zero_le _
  · next hr =>
    exact h

theorem accrualStart_le_up (recorded upIdx : Nat) :
    accrualStart recorded upIdx ≤ upIdx ∨ ¬ (recorded ≤ upIdx) := by
  by_cases h : recorded ≤ upIdx
  · exact Or.inl (accrualStart_le_of_le h)
  · exact Or.inr h

-- For recorded = 0, the start is always ≤ index by construction.
theorem accrualStart_zero_le (upIdx : Nat) :
    accrualStart 0 upIdx ≤ upIdx := by
  unfold accrualStart
  simp
  split
  · next h => exact h
  · exact Nat.zero_le _

theorem getD_eq_default_of_ge : ∀ (l : List Acct) (n : Nat),
    l.length ≤ n → l.getD n noAcct = noAcct := by
  intro l n h
  induction l generalizing n with
  | nil =>
    simp [List.getD]
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp at h
    | succ n =>
      simp [List.getD]
      exact ih n (Nat.le_of_succ_le_succ h)

theorem acct_of_ge (s : St) (who : Account) (h : s.accts.length ≤ who) :
    s.acct who = noAcct := by
  unfold St.acct
  exact getD_eq_default_of_ge s.accts who h

theorem mem_of_getD_lt : ∀ (l : List Acct) (n : Nat),
    n < l.length → l.getD n noAcct ∈ l := by
  intro l n h
  induction l generalizing n with
  | nil =>
    simp at h
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp only [List.getD]
      exact List.Mem.head tl
    | succ n =>
      have h2 : n < tl.length := Nat.lt_of_succ_lt_succ h
      have hm := ih n h2
      simp only [List.getD]
      exact List.Mem.tail hd hm

theorem acct_mem_or_default (s : St) (who : Account) :
    s.acct who ∈ s.accts ∨ s.acct who = noAcct := by
  by_cases h : who < s.accts.length
  · exact Or.inl (mem_of_getD_lt s.accts who h)
  · have hle : s.accts.length ≤ who := Nat.le_of_not_lt h
    exact Or.inr (acct_of_ge s who hle)

theorem recorded_le_of_consistent_supply (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨hsup, _, hmem⟩ := hc
  rcases acct_mem_or_default s who with hm | hm
  · exact (hmem _ hm).1
  · rw [hm]
    exact Nat.zero_le _

theorem recorded_le_of_consistent_borrow (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hmem⟩ := hc
  rcases acct_mem_or_default s who with hm | hm
  · exact (hmem _ hm).2
  · rw [hm]
    exact Nat.zero_le _

theorem supplyStart_le_up (s : St) (hc : Consistent s) (who : Account) :
    accrualStart (s.acct who).supplierIndex (supplyUp s).index ≤ (supplyUp s).index := by
  by_cases hr : (s.acct who).supplierIndex = 0
  · rw [hr]
    exact accrualStart_zero_le _
  · have h1 : (s.acct who).supplierIndex ≤ s.supplyState.index :=
      recorded_le_of_consistent_supply s hc who
    have h2 : s.supplyState.index ≤ (supplyUp s).index :=
      supplyUp_index_ge s
    have hle : (s.acct who).supplierIndex ≤ (supplyUp s).index :=
      Nat.le_trans h1 h2
    have : accrualStart (s.acct who).supplierIndex (supplyUp s).index
        = (s.acct who).supplierIndex := by
      unfold accrualStart
      simp [hr]
    rw [this]
    exact hle

theorem borrowStart_le_up (s : St) (hc : Consistent s) (who : Account) :
    accrualStart (s.acct who).borrowerIndex (borrowUp s).index ≤ (borrowUp s).index := by
  by_cases hr : (s.acct who).borrowerIndex = 0
  · rw [hr]
    exact accrualStart_zero_le _
  · have h1 : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
      recorded_le_of_consistent_borrow s hc who
    have h2 : s.borrowState.index ≤ (borrowUp s).index :=
      borrowUp_index_ge s
    have hle : (s.acct who).borrowerIndex ≤ (borrowUp s).index :=
      Nat.le_trans h1 h2
    have : accrualStart (s.acct who).borrowerIndex (borrowUp s).index
        = (s.acct who).borrowerIndex := by
      unfold accrualStart
      simp [hr]
    rw [this]
    exact hle

def doSupply (s : St) (who : Account) : Option St :=
  if _ : s.supplyState.block ≤ s.blockNumber then
    if _ : accrualStart (s.acct who).supplierIndex (supplyUp s).index ≤ (supplyUp s).index then
      some { s with
        supplyState := supplyUp s,
        accts := s.accts.modify who fun a =>
          { a with
            supplierIndex := (supplyUp s).index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex (supplyUp s).index)
              (supplyUp s).index } }
    else none
  else none

def doBorrow (s : St) (who : Account) : Option St :=
  if _ : s.borrowState.block ≤ s.blockNumber then
    if _ : accrualStart (s.acct who).borrowerIndex (borrowUp s).index ≤ (borrowUp s).index then
      some { s with
        borrowState := borrowUp s,
        accts := s.accts.modify who fun a =>
          { a with
            borrowerIndex := (borrowUp s).index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex (borrowUp s).index)
              (borrowUp s).index } }
    else none
  else none

def doClaim (s : St) (who : Account) : Option St :=
  match doBorrow s who with
  | none => none
  | some m₁ =>
    match doSupply m₁ who with
    | none => none
    | some m₂ => some (grant m₂ who)

def doSpeeds (s : St) (a b : Nat) : Option St :=
  if _ : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) then
    if _ : (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) then
      some { s with
        supplyState := if s.supplyState.speed = a then s.supplyState
          else { supplyUp s with speed := a },
        borrowState := if s.borrowState.speed = b then s.borrowState
          else { borrowUp s with speed := b } }
    else none
  else none

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => doSupply s who
  | .borrowHook who => doBorrow s who
  | .claim who => doClaim s who
  | .setSpeeds a b => doSpeeds s a b

theorem doSupply_spec (s : St) (who : Account) (s' : St) (h : doSupply s who = some s') :
    SupplyDistributed s who s' := by
  unfold doSupply at h
  split at h
  · next hb =>
    split at h
    · next hs =>
      cases h
      exact ⟨hb, hs, rfl⟩
    · simp at h
  · simp at h

theorem doBorrow_spec (s : St) (who : Account) (s' : St) (h : doBorrow s who = some s') :
    BorrowDistributed s who s' := by
  unfold doBorrow at h
  split at h
  · next hb =>
    split at h
    · next hs =>
      cases h
      exact ⟨hb, hs, rfl⟩
    · simp at h
  · simp at h

theorem doSpeeds_spec (s : St) (a b : Nat) (s' : St) (h : doSpeeds s a b = some s') :
    SpeedsSet s a b s' := by
  unfold doSpeeds at h
  split at h
  · next h1 =>
    split at h
    · next h2 =>
      cases h
      exact ⟨h1, h2, rfl⟩
    · simp at h
  · simp at h

theorem doClaim_spec (s : St) (who : Account) (s' : St) (h : doClaim s who = some s') :
    Claimed s who s' := by
  unfold doClaim at h
  match hm1 : doBorrow s who with
  | none =>
    simp [hm1] at h
  | some m₁ =>
    simp only [hm1] at h
    match hm2 : doSupply m₁ who with
    | none =>
      simp [hm2] at h
    | some m₂ =>
      simp only [hm2] at h
      cases h
      exact ⟨m₁, m₂, doBorrow_spec s who m₁ hm1, doSupply_spec m₁ who m₂ hm2, rfl⟩

theorem doSupply_some_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    ∃ s', doSupply s who = some s' := by
  have hsup : s.supplyState.block ≤ s.blockNumber := hc.1
  have hle : accrualStart (s.acct who).supplierIndex (supplyUp s).index
      ≤ (supplyUp s).index :=
    supplyStart_le_up s hc who
  unfold doSupply
  simp only [dif_pos hsup, dif_pos hle]
  exact ⟨_, rfl⟩

theorem doBorrow_some_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    ∃ s', doBorrow s who = some s' := by
  have hbor : s.borrowState.block ≤ s.blockNumber := hc.2.1
  have hle : accrualStart (s.acct who).borrowerIndex (borrowUp s).index
      ≤ (borrowUp s).index :=
    borrowStart_le_up s hc who
  unfold doBorrow
  simp only [dif_pos hbor, dif_pos hle]
  exact ⟨_, rfl⟩

theorem length_modify_aux : ∀ (l : List Acct) (n : Nat) (f : Acct → Acct),
    (l.modify n f).length = l.length := fun l n f =>
  List.length_modify f l n

theorem modify_map_congr_aux : ∀ (l : List Acct) (n : Nat) (f : Acct → Acct) (g : Acct → Nat),
    (∀ a, g (f a) = g a) → ((l.modify n f).map g = l.map g) := by
  intro l n f g hg
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_modify]
  by_cases hnm : n = i
  · simp [hnm]
    cases l[i]? with
    | none => simp
    | some a =>
      simp
      rw [hg a]
  · simp [hnm]

-- getD_modify_same_aux removed (unused)

theorem totalSupply_doBorrow_eq (s : St) (who : Account) (m₁ : St)
    (h : doBorrow s who = some m₁) : totalSupply m₁ = totalSupply s := by
  have hspec := doBorrow_spec s who m₁ h
  unfold BorrowDistributed at hspec
  obtain ⟨_, _, rfl⟩ := hspec
  unfold totalSupply
  exact congrArg List.sum
    (modify_map_congr_aux s.accts who _ Acct.supply (fun a => rfl))

theorem acctsLength_doBorrow_eq (s : St) (who : Account) (m₁ : St)
    (h : doBorrow s who = some m₁) : m₁.accts.length = s.accts.length := by
  have hspec := doBorrow_spec s who m₁ h
  unfold BorrowDistributed at hspec
  obtain ⟨_, _, rfl⟩ := hspec
  simp only
  rw [length_modify_aux]

theorem getD_modify_supplier_eq_aux : ∀ (l : List Acct) (n m : Nat) (f : Acct → Acct) (d : Acct),
    (∀ a, (f a).supplierIndex = a.supplierIndex) →
    ((l.modify n f).getD m d).supplierIndex = (l.getD m d).supplierIndex := by
  intro l n m f d hpres
  have h1 : (l.modify n f).getD m d = (((l.modify n f)[m]?.getD d)) := by
    simp [List.getD]
  have h2 : l.getD m d = ((l[m]?.getD d)) := by
    simp [List.getD]
  rw [h1, h2, List.getElem?_modify]
  by_cases hnm : n = m
  · simp [hnm]
    cases l[m]? with
    | none => simp
    | some a => simp [hpres a]
  · simp [hnm]

theorem getD_modify_supply_eq_aux : ∀ (l : List Acct) (n m : Nat) (f : Acct → Acct) (d : Acct),
    (∀ a, (f a).supply = a.supply) →
    ((l.modify n f).getD m d).supply = (l.getD m d).supply := by
  intro l n m f d hpres
  have h1 : (l.modify n f).getD m d = (((l.modify n f)[m]?.getD d)) := by
    simp [List.getD]
  have h2 : l.getD m d = ((l[m]?.getD d)) := by
    simp [List.getD]
  rw [h1, h2, List.getElem?_modify]
  by_cases hnm : n = m
  · simp [hnm]
    cases l[m]? with
    | none => simp
    | some a => simp [hpres a]
  · simp [hnm]

theorem supplyAcct_doBorrow_eq (s : St) (who : Account) (m₁ : St)
    (h : doBorrow s who = some m₁) :
    (m₁.acct who).supplierIndex = (s.acct who).supplierIndex ∧
    (m₁.acct who).supply = (s.acct who).supply := by
  have hspec := doBorrow_spec s who m₁ h
  unfold BorrowDistributed at hspec
  obtain ⟨_, _, rfl⟩ := hspec
  unfold St.acct
  constructor
  · exact getD_modify_supplier_eq_aux s.accts who who _ noAcct (fun a => rfl)
  · exact getD_modify_supply_eq_aux s.accts who who _ noAcct (fun a => rfl)

theorem borrowDist_supplyState_eq (s : St) (who : Account) (m₁ : St)
    (h : BorrowDistributed s who m₁) : m₁.supplyState = s.supplyState := by
  unfold BorrowDistributed at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

theorem borrowDist_block_eq (s : St) (who : Account) (m₁ : St)
    (h : BorrowDistributed s who m₁) : m₁.blockNumber = s.blockNumber := by
  unfold BorrowDistributed at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

theorem supplyUp_doBorrow_eq (s : St) (who : Account) (m₁ : St)
    (h : doBorrow s who = some m₁) : supplyUp m₁ = supplyUp s := by
  have hspec := doBorrow_spec s who m₁ h
  have hss : m₁.supplyState = s.supplyState :=
    borrowDist_supplyState_eq s who m₁ hspec
  have hbl : m₁.blockNumber = s.blockNumber :=
    borrowDist_block_eq s who m₁ hspec
  have htot : totalSupply m₁ = totalSupply s :=
    totalSupply_doBorrow_eq s who m₁ h
  unfold supplyUp
  rw [hss, hbl, htot]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold comptroller
  match c with
  | .supplyHook who =>
    obtain ⟨s', hs⟩ := doSupply_some_of_consistent s who hc
    simp [hs]
  | .borrowHook who =>
    obtain ⟨s', hs⟩ := doBorrow_some_of_consistent s who hc
    simp [hs]
  | .claim who =>
    obtain ⟨m₁, hm1⟩ := doBorrow_some_of_consistent s who hc
    have hspec := doBorrow_spec s who m₁ hm1
    have hsup1 : m₁.supplyState.block ≤ m₁.blockNumber := by
      rw [borrowDist_supplyState_eq s who m₁ hspec,
        borrowDist_block_eq s who m₁ hspec]
      exact hc.1
    have hsupplyUp : supplyUp m₁ = supplyUp s :=
      supplyUp_doBorrow_eq s who m₁ hm1
    have hsupAcct : (m₁.acct who).supplierIndex = (s.acct who).supplierIndex :=
      (supplyAcct_doBorrow_eq s who m₁ hm1).1
    have hle : accrualStart (m₁.acct who).supplierIndex (supplyUp m₁).index
        ≤ (supplyUp m₁).index := by
      rw [hsupAcct, hsupplyUp]
      exact supplyStart_le_up s hc who
    have hm2 : ∃ m₂, doSupply m₁ who = some m₂ := by
      unfold doSupply
      simp only [dif_pos hsup1, dif_pos hle]
      exact ⟨_, rfl⟩
    obtain ⟨m₂, hm2⟩ := hm2
    unfold doClaim
    simp [hm1, hm2]
  | .setSpeeds a b =>
    unfold doSpeeds
    have h1 : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) := by
      intro _
      exact hc.1
    have h2 : (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) := by
      intro _
      exact hc.2.1
    simp [dif_pos h1, dif_pos h2]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  exact doSupply_spec s who s' h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  exact doBorrow_spec s who s' h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  exact doClaim_spec s who s' h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller at h
  exact doSpeeds_spec s a b s' h

theorem doubleScale_pos : 0 < doubleScale := by decide

theorem div_add_le (x y c : Nat) : x / c + y / c ≤ (x + y) / c := by
  by_cases hc : 0 < c
  · rw [Nat.le_div_iff_mul_le hc]
    have h1 : x / c * c ≤ x := Nat.div_mul_le_self x c
    have h2 : y / c * c ≤ y := Nat.div_mul_le_self y c
    have h3 : (x / c + y / c) * c = x / c * c + y / c * c := Nat.add_mul _ _ _
    rw [h3]
    exact Nat.add_le_add h1 h2
  · have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    simp [hc0]

theorem sum_div_le_aux : ∀ (l : List Nat) (c : Nat),
    (l.map (· / c)).sum ≤ l.sum / c := by
  intro l c
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : hd / c + (tl.map (· / c)).sum ≤ hd / c + tl.sum / c :=
      Nat.add_le_add (Nat.le_refl _) ih
    have h2 : hd / c + tl.sum / c ≤ (hd + tl.sum) / c := div_add_le _ _ _
    exact Nat.le_trans h1 h2

theorem getD_supply_le_sum_aux : ∀ (l : List Acct) (n : Nat),
    (l.getD n noAcct).supply ≤ (l.map Acct.supply).sum := by
  intro l n
  induction l generalizing n with
  | nil =>
    simp [List.getD, noAcct]
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp only [List.getD]
      simp only [List.map_cons, List.sum_cons]
      exact Nat.le_add_right _ _
    | succ n =>
      simp only [List.getD]
      have h := ih n
      simp only [List.map_cons, List.sum_cons] at h ⊢
      exact Nat.le_trans h (Nat.le_add_left _ _)

theorem getD_borrow_le_sum_aux : ∀ (l : List Acct) (n : Nat),
    (l.getD n noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  intro l n
  induction l generalizing n with
  | nil =>
    simp [List.getD, noAcct]
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp only [List.getD]
      simp only [List.map_cons, List.sum_cons]
      exact Nat.le_add_right _ _
    | succ n =>
      simp only [List.getD]
      have h := ih n
      simp only [List.map_cons, List.sum_cons] at h ⊢
      exact Nat.le_trans h (Nat.le_add_left _ _)

def supplyPend (s : St) : Nat :=
  (s.accts.map fun a => creditFor a.supply
    (accrualStart a.supplierIndex (supplyUp s).index) (supplyUp s).index).sum

def borrowPend (s : St) : Nat :=
  (s.accts.map fun a => creditFor a.borrow
    (accrualStart a.borrowerIndex (borrowUp s).index) (borrowUp s).index).sum

def totalPot (s : St) : Nat := s.credited + supplyPend s + borrowPend s

def perAcctPot (s : St) (who : Account) : Nat :=
  s.creditedTo who +
  creditFor (s.acct who).supply
    (accrualStart (s.acct who).supplierIndex (supplyUp s).index) (supplyUp s).index +
  creditFor (s.acct who).borrow
    (accrualStart (s.acct who).borrowerIndex (borrowUp s).index) (borrowUp s).index

theorem creditedTo_le_perAcctPot (s : St) (who : Account) :
    s.creditedTo who ≤ perAcctPot s who := by
  unfold perAcctPot
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem credited_le_totalPot (s : St) : s.credited ≤ totalPot s := by
  unfold totalPot
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem upgrade_consistent (L : Legacy) (h : L.WellFormed) : Consistent (upgrade L) := by
  unfold Legacy.WellFormed at h
  obtain ⟨hs1, hsi, hb1, hbi, hsupB, hborB, hmem⟩ := h
  unfold Consistent upgrade initSide
  simp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : L.supplyIndex = 0
    · simp [h0]
    · simp [h0]
      exact hsupB
  · by_cases h0 : L.borrowIndex = 0
    · simp [h0]
    · simp [h0]
      exact hborB
  · intro a ha
    obtain ⟨hsup_le, hbor_le⟩ := hmem a ha
    constructor
    · by_cases h0 : L.supplyIndex = 0
      · simp [h0]
        have hle0 : a.supplierIndex ≤ 0 := by
          have := hsup_le
          rw [h0] at this
          exact this
        exact Nat.le_trans hle0 (Nat.zero_le _)
      · simp [h0]
        exact hsup_le
    · by_cases h0 : L.borrowIndex = 0
      · simp [h0]
        have hle0 : a.borrowerIndex ≤ 0 := by
          have := hbor_le
          rw [h0] at this
          exact this
        exact Nat.le_trans hle0 (Nat.zero_le _)
      · simp [h0]
        exact hbor_le

theorem consistent_supplyDist (s : St) (who : Account) (s' : St)
    (hc : Consistent s) (h : SupplyDistributed s who s') : Consistent s' := by
  unfold SupplyDistributed at h
  obtain ⟨hblock, _, rfl⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨_, hborB, hmem⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber
    rw [accrueSide_block]
    exact Nat.le_refl _
  · exact hborB
  · intro a ha
    rw [List.mem_iff_getElem?] at ha
    obtain ⟨i, hi⟩ := ha
    rw [List.getElem?_modify] at hi
    by_cases hnm : who = i
    · simp [hnm] at hi
      cases hs : s.accts[i]? with
      | none =>
        rw [hs] at hi
        simp at hi
      | some b =>
        rw [hs] at hi
        simp at hi
        cases hi
        simp only
        constructor
        · exact Nat.le_refl _
        · have hbmem : b ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hs⟩
          exact (hmem b hbmem).2
    · simp [hnm] at hi
      have hbmem : a ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hi⟩
      obtain ⟨hsup_le, hbor_le⟩ := hmem a hbmem
      constructor
      · exact Nat.le_trans hsup_le (supplyUp_index_ge s)
      · simp only
        exact hbor_le

theorem consistent_borrowDist (s : St) (who : Account) (s' : St)
    (hc : Consistent s) (h : BorrowDistributed s who s') : Consistent s' := by
  unfold BorrowDistributed at h
  obtain ⟨hblock, _, rfl⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, _, hmem⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · exact hsupB
  · show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block ≤ s.blockNumber
    rw [accrueSide_block]
    exact Nat.le_refl _
  · intro a ha
    rw [List.mem_iff_getElem?] at ha
    obtain ⟨i, hi⟩ := ha
    rw [List.getElem?_modify] at hi
    by_cases hnm : who = i
    · simp [hnm] at hi
      cases hs : s.accts[i]? with
      | none =>
        rw [hs] at hi
        simp at hi
      | some b =>
        rw [hs] at hi
        simp at hi
        cases hi
        simp only
        constructor
        · have hbmem : b ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hs⟩
          exact (hmem b hbmem).1
        · exact Nat.le_refl _
    · simp [hnm] at hi
      have hbmem : a ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hi⟩
      obtain ⟨hsup_le, hbor_le⟩ := hmem a hbmem
      constructor
      · simp only
        exact hsup_le
      · exact Nat.le_trans hbor_le (borrowUp_index_ge s)

theorem consistent_grant (s : St) (who : Account) : Consistent s → Consistent (grant s who) := by
  intro hc
  unfold grant
  split
  · next h =>
    obtain ⟨hc1, hc2, hmem⟩ := hc
    unfold Consistent
    refine ⟨hc1, hc2, ?_⟩
    intro a ha
    rw [List.mem_iff_getElem?] at ha
    obtain ⟨i, hi⟩ := ha
    rw [List.getElem?_modify] at hi
    by_cases hnm : who = i
    · simp [hnm] at hi
      cases hs : s.accts[i]? with
      | none =>
        rw [hs] at hi
        simp at hi
      | some b =>
        rw [hs] at hi
        simp at hi
        cases hi
        have hbmem : b ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hs⟩
        exact hmem b hbmem
    · simp [hnm] at hi
      have hbmem : a ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hi⟩
      exact hmem a hbmem
  · exact hc

theorem consistent_speeds (s : St) (a b : Nat) (s' : St)
    (hc : Consistent s) (h : SpeedsSet s a b s') : Consistent s' := by
  unfold SpeedsSet at h
  obtain ⟨_, _, rfl⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hmem⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · by_cases heq : s.supplyState.speed = a
    · simp [heq]
      exact hsupB
    · simp [heq]
      rw [accrueSide_block]
      exact Nat.le_refl _
  · by_cases heq : s.borrowState.speed = b
    · simp [heq]
      exact hborB
    · simp [heq]
      rw [accrueSide_block]
      exact Nat.le_refl _
  · intro x hx
    obtain ⟨hsup_le, hbor_le⟩ := hmem x hx
    constructor
    · by_cases heq : s.supplyState.speed = a
      · simp [heq]
        exact hsup_le
      · simp [heq]
        exact Nat.le_trans hsup_le (supplyUp_index_ge s)
    · by_cases heq : s.borrowState.speed = b
      · simp [heq]
        exact hbor_le
      · simp [heq]
        exact Nat.le_trans hbor_le (borrowUp_index_ge s)

theorem consistent_claim (s : St) (who : Account) (s' : St)
    (hc : Consistent s) (h : Claimed s who s') : Consistent s' := by
  unfold Claimed at h
  obtain ⟨m₁, m₂, hb, hs, rfl⟩ := h
  have hc1 : Consistent m₁ := consistent_borrowDist s who m₁ hc hb
  have hc2 : Consistent m₂ := consistent_supplyDist m₁ who m₂ hc1 hs
  exact consistent_grant m₂ who hc2

theorem consistent_balance_supply (s : St) (who : Account) (f : Acct → Acct)
    (hc : Consistent s)
    (hpres1 : ∀ a, (f a).supplierIndex = a.supplierIndex)
    (hpres2 : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    Consistent ({s with accts := s.accts.modify who f}) := by
  unfold Consistent at hc ⊢
  obtain ⟨hsupB, hborB, hmem⟩ := hc
  refine ⟨hsupB, hborB, ?_⟩
  intro a ha
  rw [List.mem_iff_getElem?] at ha
  obtain ⟨i, hi⟩ := ha
  rw [List.getElem?_modify] at hi
  by_cases hnm : who = i
  · simp [hnm] at hi
    cases hs : s.accts[i]? with
    | none =>
      rw [hs] at hi
      simp at hi
    | some b =>
      rw [hs] at hi
      simp at hi
      cases hi
      have hbmem : b ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hs⟩
      obtain ⟨hsup_le, hbor_le⟩ := hmem b hbmem
      constructor
      · rw [hpres1 b]
        exact hsup_le
      · rw [hpres2 b]
        exact hbor_le
  · simp [hnm] at hi
    have hbmem : a ∈ s.accts := (List.mem_iff_getElem?).mpr ⟨i, hi⟩
    exact hmem a hbmem

theorem consistent_exec (s : St) (op : Op) (hc : Consistent s) :
    Consistent (exec comptroller s op) := by
  cases op with
  | mint who x =>
    unfold exec
    by_cases hw : who < s.accts.length
    · have hsome : ∃ s', comptroller s (.supplyHook who) = some s' :=
      doSupply_some_of_consistent s who hc
    -- detailed proof needs hook effects + balance preservation; sorry for now
      sorry
    · simp [hw]
      exact hc
  | redeem who x =>
    sorry
  | transfer src dst x =>
    sorry
  | borrow who x =>
    sorry
  | repay who x =>
    sorry
  | claim who =>
    have hsome : ∃ s', comptroller s (.claim who) = some s' := by
      obtain ⟨m₁, hm1⟩ := doBorrow_some_of_consistent s who hc
      have hspec := doBorrow_spec s who m₁ hm1
      have hsup1 : m₁.supplyState.block ≤ m₁.blockNumber := by
        rw [borrowDist_supplyState_eq s who m₁ hspec, borrowDist_block_eq s who m₁ hspec]
        exact hc.1
      have hsupplyUp : supplyUp m₁ = supplyUp s := supplyUp_doBorrow_eq s who m₁ hm1
      have hsupAcct : (m₁.acct who).supplierIndex = (s.acct who).supplierIndex :=
        (supplyAcct_doBorrow_eq s who m₁ hm1).1
      have hle : accrualStart (m₁.acct who).supplierIndex (supplyUp m₁).index ≤ (supplyUp m₁).index := by
        rw [hsupAcct, hsupplyUp]
        exact supplyStart_le_up s hc who
      have hm2 : ∃ m₂, doSupply m₁ who = some m₂ := by
        unfold doSupply
        simp only [dif_pos hsup1, dif_pos hle]
        exact ⟨_, rfl⟩
      obtain ⟨m₂, hm2⟩ := hm2
      unfold comptroller doClaim
      simp [hm1, hm2]
    obtain ⟨s', hs⟩ := hsome
    have hclaim : Claimed s who s' := req_claim s who s' hs
    have heq : exec comptroller s (.claim who) = s' := by simp [exec, hs]
    rw [heq]
    exact consistent_claim s who s' hc hclaim
  | setSpeeds a b =>
    have hsome : ∃ s', comptroller s (.setSpeeds a b) = some s' := by
      unfold comptroller doSpeeds
      have h1 : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) := by
        intro _
        exact hc.1
      have h2 : (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) := by
        intro _
        exact hc.2.1
      simp only [dif_pos h1, dif_pos h2]
      exact ⟨_, rfl⟩
    obtain ⟨s', hs⟩ := hsome
    have hspeed : SpeedsSet s a b s' := req_set_speeds s a b s' hs
    have heq : exec comptroller s (.setSpeeds a b) = s' := by simp [exec, hs]
    rw [heq]
    exact consistent_speeds s a b s' hc hspeed
  | advance k =>
    have heq : exec comptroller s (.advance k) =
        ({s with blockNumber := s.blockNumber + k} : St) := by simp [exec]
    rw [heq]
    unfold Consistent at hc ⊢
    obtain ⟨hsupB, hborB, hmem⟩ := hc
    refine ⟨Nat.le_trans hsupB (Nat.le_add_right _ _), Nat.le_trans hborB (Nat.le_add_right _ _), ?_⟩
    intro a ha
    simp only at ha ⊢
    exact hmem a ha
  | drip x =>
    have heq : exec comptroller s (.drip x) =
        ({s with reserve := s.reserve + x} : St) := by simp [exec]
    rw [heq]
    exact hc

theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
