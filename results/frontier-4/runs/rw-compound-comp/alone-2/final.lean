import CompRewards.Spec
namespace CompRewards

def fraction (a b : Nat) : Nat := a * doubleScale / b

def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

theorem subChecked_some_of_le {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none_of_lt {a b : Nat} (h : a < b) : subChecked a b = none := by
  unfold subChecked; simp [Nat.not_le.mpr h]

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
  match subChecked s.supplyState.index
    (if (s.acct supplier).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
     else (s.acct supplier).supplierIndex) with
  | none => none
  | some deltaIndex =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + mulDouble a.supply deltaIndex })

def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  match subChecked s.borrowState.index
    (if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
     else (s.acct borrower).borrowerIndex) with
  | none => none
  | some deltaIndex =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + mulDouble a.borrow deltaIndex })

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

theorem accrualStart_eq_impl (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded)
      = accrualStart recorded index := by
  unfold accrualStart
  by_cases h1 : recorded = 0
  · subst h1
    by_cases h2 : compInitialIndex ≤ index <;> simp [h2]
  · simp [h1]

theorem getD_supplier_le (l : List Acct) (who bound : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ bound) :
    (l.getD who noAcct).supplierIndex ≤ bound := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
      exact hall a (by simp)
    | succ n =>
      simp
      apply ih
      intro b hb
      exact hall b (by simp [hb])

theorem getD_borrower_le (l : List Acct) (who bound : Nat)
    (hall : ∀ a ∈ l, a.borrowerIndex ≤ bound) :
    (l.getD who noAcct).borrowerIndex ≤ bound := by
  induction l generalizing who with
  | nil =>
    simp [noAcct]
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
      exact hall a (by simp)
    | succ n =>
      simp
      apply ih
      intro b hb
      exact hall b (by simp [hb])

/-- Every account record lies below the market index in a consistent state. -/
theorem acct_supplier_le_of_consistent (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  unfold St.acct
  exact getD_supplier_le s.accts who s.supplyState.index (fun a ha => (hall a ha).1)

theorem acct_borrower_le_of_consistent (s : St) (hc : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  unfold St.acct
  exact getD_borrower_le s.accts who s.borrowState.index (fun a ha => (hall a ha).2)

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h, Nat.le_add_right]

theorem accrueSide_block_eq (sd : Side) (now total : Nat) (h : sd.block ≤ now) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases hcond : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hcond]
  · simp [hcond]

theorem start_le_new_index_supply (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  have hle : (s.acct who).supplierIndex ≤ s.supplyState.index :=
    acct_supplier_le_of_consistent s hc who
  have hge : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_index_ge _ _ _
  have hle' : (s.acct who).supplierIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    omega
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    · simp [hi]
    · simp [hi]
  · simp [hr, hle']

theorem start_le_new_index_borrow (s : St) (who : Account) (hc : Consistent s) :
    accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  have hle : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
    acct_borrower_le_of_consistent s hc who
  have hge : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    accrueSide_index_ge _ _ _
  have hle' : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    omega
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    · simp [hi]
    · simp [hi]
  · simp [hr, hle']

theorem accrueSupply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide fraction
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    subChecked_some_of_le h
  rw [hsub]
  by_cases hd1 : s.blockNumber - s.supplyState.block > 0
  · by_cases hd2 : s.supplyState.speed > 0
    · by_cases ht : totalSupply s > 0
      · simp [hd1, hd2, ht]
      · simp [hd1, hd2, ht]
    · simp [hd1, hd2]
  · have hbeq : s.supplyState.block = s.blockNumber := by omega
    obtain ⟨bn, sup, bor, res, accts⟩ := s
    obtain ⟨sidx, sblk, sspd⟩ := sup
    simp at hbeq hsub hd1 ⊢
    simp [←hbeq, hd1]

theorem accrueBorrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide fraction
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    subChecked_some_of_le h
  rw [hsub]
  by_cases hd1 : s.blockNumber - s.borrowState.block > 0
  · by_cases hd2 : s.borrowState.speed > 0
    · by_cases ht : totalBorrows s > 0
      · simp [hd1, hd2, ht]
      · simp [hd1, hd2, ht]
    · simp [hd1, hd2]
  · have hbeq : s.borrowState.block = s.blockNumber := by omega
    obtain ⟨bn, sup, bor, res, accts⟩ := s
    obtain ⟨bidx, bblk, bspd⟩ := bor
    simp at hbeq hsub hd1 ⊢
    simp [←hbeq, hd1]

theorem modify_congr_target (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simpa using h
    | succ n => rfl
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
      simpa using h
    | succ n =>
      simp
      apply ih
      simpa using h

theorem distributeSupply_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp creditFor mulDouble
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex)
      = accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    accrualStart_eq_impl _ _
  rw [hstart]
  have hsub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index)
      = some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    subChecked_some_of_le h
  rw [hsub]
  simp only [St.withAcct]
  congr 1
  congr 1
  apply modify_congr_target
  rfl

theorem distributeBorrow_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp creditFor mulDouble
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex)
      = accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    accrualStart_eq_impl _ _
  rw [hstart]
  have hsub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index)
      = some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    subChecked_some_of_le h
  rw [hsub]
  simp only [St.withAcct]
  congr 1
  congr 1
  apply modify_congr_target
  rfl

theorem modify_grant_eq (l : List Acct) (who : Nat) (amount : Nat)
    (h : amount = (l.getD who noAcct).accrued) :
    l.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + amount } : Acct))
    = l.modify who (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp [h]
    | succ n => simp [h]
  | cons a rest ih =>
    cases who with
    | zero =>
      simp
      have : amount = a.accrued := by simpa using h
      simp [this]
    | succ n =>
      simp
      apply ih
      simpa using h

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve
  · have hmod := modify_grant_eq s.accts who (s.acct who).accrued rfl
    simp [h, hmod]
  · simp [h]

theorem updateSupply_none_of_gt (s : St) (h : s.blockNumber < s.supplyState.block) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  rw [subChecked_none_of_lt h]

theorem updateBorrow_none_of_gt (s : St) (h : s.blockNumber < s.borrowState.block) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  rw [subChecked_none_of_lt h]

theorem updateSupply_some_block_le {s s1 : St} (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber := by
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · exact hle
  · have hlt : s.blockNumber < s.supplyState.block := by omega
    have hnone := updateSupply_none_of_gt s hlt
    rw [hnone] at h
    cases h

theorem updateBorrow_some_block_le {s s1 : St} (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber := by
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · exact hle
  · have hlt : s.blockNumber < s.borrowState.block := by omega
    have hnone := updateBorrow_none_of_gt s hlt
    rw [hnone] at h
    cases h

theorem distributeSupply_none_of_gt (s : St) (who : Account)
    (h : s.supplyState.index < accrualStart (s.acct who).supplierIndex s.supplyState.index) :
    distributeSupplierComp s who = none := by
  unfold distributeSupplierComp
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex)
      = accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    accrualStart_eq_impl _ _
  rw [hstart]
  have hnone : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none := by
    apply subChecked_none_of_lt
    omega
  rw [hnone]

theorem distributeBorrow_none_of_gt (s : St) (who : Account)
    (h : s.borrowState.index < accrualStart (s.acct who).borrowerIndex s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex)
      = accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    accrualStart_eq_impl _ _
  rw [hstart]
  have hnone : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none := by
    apply subChecked_none_of_lt
    omega
  rw [hnone]

theorem distributeSupply_some_start_le {s s' : St} {who : Account}
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · exact hle
  · have hlt : s.supplyState.index < accrualStart (s.acct who).supplierIndex s.supplyState.index := by omega
    have hnone := distributeSupply_none_of_gt s who hlt
    rw [hnone] at h
    cases h

theorem distributeBorrow_some_start_le {s s' : St} {who : Account}
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · exact hle
  · have hlt : s.borrowState.index < accrualStart (s.acct who).borrowerIndex s.borrowState.index := by omega
    have hnone := distributeBorrow_none_of_gt s who hlt
    rw [hnone] at h
    cases h

theorem getD_mem (l : List Acct) (who : Nat) (h : who < l.length) :
    l.getD who noAcct ∈ l := by
  induction l generalizing who with
  | nil => simp at h
  | cons a rest ih =>
    cases who with
    | zero => simp
    | succ n =>
      simp
      simp at h
      have := ih n (by omega)
      simp [this]

theorem updateSupply_preserves_consistent {s s1 : St} (hc : Consistent s)
    (h : updateCompSupplyIndex s = some s1) : Consistent s1 := by
  have hblock := updateSupply_some_block_le h
  have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
    have hh := accrueSupply_eq s hblock
    rw [h] at hh
    simpa using hh
  subst hs1
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hall⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · have := accrueSide_block_eq s.supplyState s.blockNumber (totalSupply s) hblock
    simpa using this
  · simpa using hbb
  · intro a ha
    have hEq : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index)
        = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
    rw [hEq]
    obtain ⟨hsup, hbor⟩ := hall a ha
    refine ⟨?_, hbor⟩
    have hge := accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
    omega

theorem updateBorrow_preserves_consistent {s s1 : St} (hc : Consistent s)
    (h : updateCompBorrowIndex s = some s1) : Consistent s1 := by
  have hblock := updateBorrow_some_block_le h
  have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
    have hh := accrueBorrow_eq s hblock
    rw [h] at hh
    simpa using hh
  subst hs1
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hall⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · simpa using hsb
  · have := accrueSide_block_eq s.borrowState s.blockNumber (totalBorrows s) hblock
    simpa using this
  · intro a ha
    have hEq : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)
        = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    rw [hEq]
    obtain ⟨hsup, hbor⟩ := hall a ha
    refine ⟨hsup, ?_⟩
    have hge := accrueSide_index_ge s.borrowState s.blockNumber (totalBorrows s)
    omega

theorem modify_supply_preserves (l : List Acct) (who : Nat) (supIdx borIdx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx) :
    ∀ a ∈ l.modify who (fun x => ({ x with supplierIndex := supIdx,
      accrued := x.accrued + creditFor x.supply (accrualStart x.supplierIndex supIdx) supIdx } : Acct)),
      a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx := by
  induction l generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons a rest ih =>
    cases who with
    | zero =>
      intro b hb
      simp at hb
      cases hb with
      | inl heq =>
        rw [heq]
        refine ⟨by simp, ?_⟩
        have := (hall a (by simp)).2
        simpa using this
      | inr hb =>
        exact hall b (by simp [hb])
    | succ n =>
      intro b hb
      simp at hb
      cases hb with
      | inl heq =>
        rw [heq]
        exact hall a (by simp)
      | inr hb =>
        have hall' : ∀ c ∈ rest, c.supplierIndex ≤ supIdx ∧ c.borrowerIndex ≤ borIdx := by
          intro c hc
          exact hall c (by simp [hc])
        exact ih n hall' b hb

theorem distributeSupply_preserves_consistent {s s' : St} {who : Account} (hc : Consistent s)
    (h : distributeSupplierComp s who = some s') : Consistent s' := by
  have hstart := distributeSupply_some_start_le h
  have hdist := distributeSupply_eq s who hstart
  rw [h] at hdist
  have hs' : s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
    simpa using hdist
  subst hs'
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hall⟩ := hc
  refine ⟨hsb, hbb, ?_⟩
  exact modify_supply_preserves s.accts who s.supplyState.index s.borrowState.index hall

theorem modify_borrow_preserves (l : List Acct) (who : Nat) (supIdx borIdx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx) :
    ∀ a ∈ l.modify who (fun x => ({ x with borrowerIndex := borIdx,
      accrued := x.accrued + creditFor x.borrow (accrualStart x.borrowerIndex borIdx) borIdx } : Acct)),
      a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx := by
  induction l generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons a rest ih =>
    cases who with
    | zero =>
      intro b hb
      simp at hb
      cases hb with
      | inl heq =>
        rw [heq]
        refine ⟨?_, by simp⟩
        have := (hall a (by simp)).1
        simpa using this
      | inr hb =>
        exact hall b (by simp [hb])
    | succ n =>
      intro b hb
      simp at hb
      cases hb with
      | inl heq =>
        rw [heq]
        exact hall a (by simp)
      | inr hb =>
        have hall' : ∀ c ∈ rest, c.supplierIndex ≤ supIdx ∧ c.borrowerIndex ≤ borIdx := by
          intro c hc
          exact hall c (by simp [hc])
        exact ih n hall' b hb

theorem distributeBorrow_preserves_consistent {s s' : St} {who : Account} (hc : Consistent s)
    (h : distributeBorrowerComp s who = some s') : Consistent s' := by
  have hstart := distributeBorrow_some_start_le h
  have hdist := distributeBorrow_eq s who hstart
  rw [h] at hdist
  have hs' : s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
    simpa using hdist
  subst hs'
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hall⟩ := hc
  refine ⟨hsb, hbb, ?_⟩
  exact modify_borrow_preserves s.accts who s.supplyState.index s.borrowState.index hall

theorem modify_grant_preserves (l : List Acct) (who : Nat) (supIdx borIdx : Nat)
    (hall : ∀ a ∈ l, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx) :
    ∀ a ∈ l.modify who (fun x => ({ x with accrued := 0, wallet := x.wallet + x.accrued } : Acct)),
      a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx := by
  induction l generalizing who with
  | nil =>
    intro a ha
    simp at ha
  | cons a rest ih =>
    cases who with
    | zero =>
      intro b hb
      simp at hb
      cases hb with
      | inl heq =>
        rw [heq]
        have := hall a (by simp)
        simpa using this
      | inr hb =>
        exact hall b (by simp [hb])
    | succ n =>
      intro b hb
      simp at hb
      cases hb with
      | inl heq =>
        rw [heq]
        exact hall a (by simp)
      | inr hb =>
        have hall' : ∀ c ∈ rest, c.supplierIndex ≤ supIdx ∧ c.borrowerIndex ≤ borIdx := by
          intro c hc
          exact hall c (by simp [hc])
        exact ih n hall' b hb

theorem grant_preserves_consistent {s : St} {who : Account} (hc : Consistent s) :
    Consistent (grant s who) := by
  unfold grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp [h]
    unfold Consistent at hc ⊢
    obtain ⟨hsb, hbb, hall⟩ := hc
    refine ⟨hsb, hbb, ?_⟩
    exact modify_grant_preserves s.accts who s.supplyState.index s.borrowState.index hall
  · simp [h]
    exact hc

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' hs
  unfold comptroller at hs
  cases hup : updateCompSupplyIndex s with
  | none => simp [hup] at hs
  | some s1 =>
    simp [hup] at hs
    have hblock : s.supplyState.block ≤ s.blockNumber :=
      updateSupply_some_block_le hup
    have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      have h := accrueSupply_eq s hblock
      rw [hup] at h
      simpa using h
    subst hs1
    have hstart := distributeSupply_some_start_le hs
    have hdist := distributeSupply_eq _ who hstart
    refine ⟨hblock, hstart, ?_⟩
    simpa using hs.symm.trans hdist

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' hs
  unfold comptroller at hs
  cases hup : updateCompBorrowIndex s with
  | none => simp [hup] at hs
  | some s1 =>
    simp [hup] at hs
    have hblock : s.borrowState.block ≤ s.blockNumber :=
      updateBorrow_some_block_le hup
    have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have h := accrueBorrow_eq s hblock
      rw [hup] at h
      simpa using h
    subst hs1
    have hstart := distributeBorrow_some_start_le hs
    have hdist := distributeBorrow_eq _ who hstart
    refine ⟨hblock, hstart, ?_⟩
    simpa using hs.symm.trans hdist

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' hs
  unfold comptroller claimComp at hs
  cases hb1 : updateCompBorrowIndex s with
  | none => simp [hb1] at hs
  | some b1 =>
    simp [hb1] at hs
    cases hb2 : distributeBorrowerComp b1 who with
    | none => simp [hb2] at hs
    | some m1 =>
      simp [hb2] at hs
      cases hs1 : updateCompSupplyIndex m1 with
      | none => simp [hs1] at hs
      | some s1 =>
        simp [hs1] at hs
        cases hs2 : distributeSupplierComp s1 who with
        | none => simp [hs2] at hs
        | some m2 =>
          simp [hs2, grant_eq] at hs
          have hbblock := updateBorrow_some_block_le hb1
          have hb1eq : b1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
            have h := accrueBorrow_eq s hbblock
            rw [hb1] at h
            simpa using h
          subst hb1eq
          have hbstart := distributeBorrow_some_start_le hb2
          have hbdist := distributeBorrow_eq _ who hbstart
          have hbor : BorrowDistributed s who m1 := by
            refine ⟨hbblock, hbstart, ?_⟩
            simpa using hb2.symm.trans hbdist
          have hsblock := updateSupply_some_block_le hs1
          have hs1eq : s1 = { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } := by
            have h := accrueSupply_eq m1 hsblock
            rw [hs1] at h
            simpa using h
          subst hs1eq
          have hsstart := distributeSupply_some_start_le hs2
          have hsdist := distributeSupply_eq _ who hsstart
          have hsup : SupplyDistributed m1 who m2 := by
            refine ⟨hsblock, hsstart, ?_⟩
            simpa using hs2.symm.trans hsdist
          exact ⟨m1, m2, hbor, hsup, hs.symm⟩

theorem setSupplySpeed_correct {s s' : St} {new : Nat}
    (h : setSupplySpeed s new = some s') :
    (s.supplyState.speed ≠ new → s.supplyState.block ≤ s.blockNumber) ∧
    s' = { s with supplyState := if s.supplyState.speed = new then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := new } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed ≠ new
  · simp [heq] at h
    cases hup : updateCompSupplyIndex s with
    | none => simp [hup] at h
    | some s1 =>
      simp [hup] at h
      have hblock := updateSupply_some_block_le hup
      have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
        have hh := accrueSupply_eq s hblock
        rw [hup] at hh
        simpa using hh
      subst hs1
      simp at h
      subst h
      refine ⟨fun _ => hblock, ?_⟩
      simp [heq]
  · simp [heq] at h
    have hs' : s' = s := by simpa using h.symm
    subst hs'
    refine ⟨fun hne => absurd hne heq, ?_⟩
    have heq' : s.supplyState.speed = new := by omega
    simp [heq']

theorem setBorrowSpeed_correct {s s' : St} {new : Nat}
    (h : setBorrowSpeed s new = some s') :
    (s.borrowState.speed ≠ new → s.borrowState.block ≤ s.blockNumber) ∧
    s' = { s with borrowState := if s.borrowState.speed = new then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := new } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed ≠ new
  · simp [heq] at h
    cases hup : updateCompBorrowIndex s with
    | none => simp [hup] at h
    | some s1 =>
      simp [hup] at h
      have hblock := updateBorrow_some_block_le hup
      have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
        have hh := accrueBorrow_eq s hblock
        rw [hup] at hh
        simpa using hh
      subst hs1
      simp at h
      subst h
      refine ⟨fun _ => hblock, ?_⟩
      simp [heq]
  · simp [heq] at h
    have hs' : s' = s := by simpa using h.symm
    subst hs'
    refine ⟨fun hne => absurd hne heq, ?_⟩
    have heq' : s.borrowState.speed = new := by omega
    simp [heq']

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' hs
  unfold comptroller setCompSpeedInternal at hs
  cases hsup : setSupplySpeed s a with
  | none => simp [hsup] at hs
  | some s1 =>
    simp [hsup] at hs
    have ⟨hsblock, hs1eq⟩ := setSupplySpeed_correct hsup
    subst hs1eq
    have ⟨hbblock, hs2eq⟩ := setBorrowSpeed_correct hs
    refine ⟨hsblock, hbblock, hs2eq⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsb, hbb, hall⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    have hup := accrueSupply_eq s hsb
    have hstart := start_le_new_index_supply s who ⟨hsb, hbb, hall⟩
    have hX : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).acct who) = s.acct who := rfl
    have hY : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState.index)
        = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
    have hdist := distributeSupply_eq
      ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) who (by rw [hX, hY]; exact hstart)
    simp [hup, hdist]
  | borrowHook who =>
    unfold comptroller
    have hup := accrueBorrow_eq s hbb
    have hstart := start_le_new_index_borrow s who ⟨hsb, hbb, hall⟩
    have hX : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).acct who) = s.acct who := rfl
    have hY : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)
        = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    have hdist := distributeBorrow_eq
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who (by rw [hX, hY]; exact hstart)
    simp [hup, hdist]
  | claim who =>
    unfold comptroller claimComp
    have hupb := accrueBorrow_eq s hbb
    have hb1_cons : Consistent { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
      updateBorrow_preserves_consistent ⟨hsb, hbb, hall⟩ hupb
    have hstartb := start_le_new_index_borrow s who ⟨hsb, hbb, hall⟩
    have hXb : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).acct who) = s.acct who := rfl
    have hYb : (({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index)
        = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    have hdistb := distributeBorrow_eq
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) who (by rw [hXb, hYb]; exact hstartb)
    have hm1_cons : Consistent _ := distributeBorrow_preserves_consistent hb1_cons hdistb
    obtain ⟨hsb_m1, _, _⟩ := hm1_cons
    have hups := accrueSupply_eq _ hsb_m1
    have hs1_cons : Consistent _ := updateSupply_preserves_consistent hm1_cons hups
    have hstarts := start_le_new_index_supply _ _ hs1_cons
    have hdist := distributeSupply_eq _ _ hstarts
    simp [hupb, hdistb, hups, hdist]
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed
    by_cases hsa : s.supplyState.speed ≠ a
    · have hup := accrueSupply_eq s hsb
      simp [hsa, hup]
      have hX : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).borrowState) = s.borrowState := rfl
      have hY : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).blockNumber) = s.blockNumber := rfl
      have hbb1 : (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).borrowState.block)
          ≤ (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).blockNumber) := by
        rw [hX, hY]
        exact hbb
      have hup2 := accrueBorrow_eq _ hbb1
      simp [hup2]
    · simp [hsa]
      by_cases hsb2 : s.borrowState.speed ≠ b
      · have hup := accrueBorrow_eq s hbb
        simp [hsb2, hup]
      · simp [hsb2]
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
