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

theorem subChecked_some {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  simp [subChecked, h]

theorem subChecked_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  simp [subChecked, h]

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem updateSupply_some {s s' : St} (h : updateCompSupplyIndex s = some s') :
    s.supplyState.block ≤ s.blockNumber ∧
    s' = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · have hs : subChecked s.blockNumber s.supplyState.block =
        some (s.blockNumber - s.supplyState.block) := subChecked_some hb
    rw [hs] at h
    refine ⟨hb, ?_⟩
    by_cases h1 : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
    · simp [h1] at h
      by_cases hT : totalSupply s > 0
      · simp [hT] at h
        cases h
        unfold accrueSide
        have hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s := ⟨h1.1, h1.2, hT⟩
        simp [hc]
        rfl
      · simp [hT] at h
        cases h
        unfold accrueSide
        have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := fun h => hT h.2.2
        simp [hc]
    · simp [h1] at h
      by_cases h2 : (s.blockNumber - s.supplyState.block) > 0
      · simp [h2] at h
        cases h
        unfold accrueSide
        have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := fun h => h1 ⟨h.1, h.2.1⟩
        simp [hc]
      · simp [h2] at h
        cases h
        have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := fun h => h2 h.1
        have hrw : accrueSide s.supplyState s.blockNumber (totalSupply s) =
            { s.supplyState with block := s.blockNumber } := by
          unfold accrueSide
          simp [hc]
        rw [hrw]
        have hbeq : s.supplyState.block = s.blockNumber := by omega
        cases s with
        | mk bn sup bor res accts =>
          cases sup with
          | mk idx blk spd =>
            simp at hbeq
            simp [hbeq]
  · have hn : subChecked s.blockNumber s.supplyState.block = none := subChecked_none hb
    rw [hn] at h
    contradiction

theorem updateSupply_none {s : St} (h : updateCompSupplyIndex s = none) :
    ¬ s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex at h
  intro hb
  have hs : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := subChecked_some hb
  rw [hs] at h
  by_cases h1 : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · simp [h1] at h
  · simp [h1] at h
    by_cases h2 : (s.blockNumber - s.supplyState.block) > 0
    · simp [h2] at h
    · simp [h2] at h

theorem updateBorrow_some {s s' : St} (h : updateCompBorrowIndex s = some s') :
    s.borrowState.block ≤ s.blockNumber ∧
    s' = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · have hs : subChecked s.blockNumber s.borrowState.block =
        some (s.blockNumber - s.borrowState.block) := subChecked_some hb
    rw [hs] at h
    refine ⟨hb, ?_⟩
    by_cases h1 : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
    · simp [h1] at h
      by_cases hT : totalBorrows s > 0
      · simp [hT] at h
        cases h
        unfold accrueSide
        have hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s := ⟨h1.1, h1.2, hT⟩
        simp [hc]
        rfl
      · simp [hT] at h
        cases h
        unfold accrueSide
        have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := fun h => hT h.2.2
        simp [hc]
    · simp [h1] at h
      by_cases h2 : (s.blockNumber - s.borrowState.block) > 0
      · simp [h2] at h
        cases h
        unfold accrueSide
        have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := fun h => h1 ⟨h.1, h.2.1⟩
        simp [hc]
      · simp [h2] at h
        cases h
        have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := fun h => h2 h.1
        have hrw : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
            { s.borrowState with block := s.blockNumber } := by
          unfold accrueSide
          simp [hc]
        rw [hrw]
        have hbeq : s.borrowState.block = s.blockNumber := by omega
        cases s with
        | mk bn sup bor res accts =>
          cases bor with
          | mk idx blk spd =>
            simp at hbeq
            simp [hbeq]
  · have hn : subChecked s.blockNumber s.borrowState.block = none := subChecked_none hb
    rw [hn] at h
    contradiction

theorem updateBorrow_none {s : St} (h : updateCompBorrowIndex s = none) :
    ¬ s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex at h
  intro hb
  have hs : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := subChecked_some hb
  rw [hs] at h
  by_cases h1 : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · simp [h1] at h
  · simp [h1] at h
    by_cases h2 : (s.blockNumber - s.borrowState.block) > 0
    · simp [h2] at h
    · simp [h2] at h

theorem accrualStart_eq (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) =
      accrualStart rec idx := by
  unfold accrualStart
  by_cases hrec : rec = 0 <;> simp [hrec]

theorem modify_supply_congr (l : List Acct) (i idx : Nat) :
    l.modify i (fun a =>
      { a with supplierIndex := idx,
               accrued := a.accrued +
                 ((l[i]?.getD noAcct).supply) * (idx - accrualStart ((l[i]?.getD noAcct).supplierIndex) idx) /
                   doubleScale }) =
    l.modify i (fun a =>
      { a with supplierIndex := idx,
               accrued := a.accrued +
                 a.supply * (idx - accrualStart a.supplierIndex idx) / doubleScale }) := by
  induction l generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      simp
    | succ n =>
      simp [ih]

theorem modify_borrow_congr (l : List Acct) (i idx : Nat) :
    l.modify i (fun a =>
      { a with borrowerIndex := idx,
               accrued := a.accrued +
                 ((l[i]?.getD noAcct).borrow) * (idx - accrualStart ((l[i]?.getD noAcct).borrowerIndex) idx) /
                   doubleScale }) =
    l.modify i (fun a =>
      { a with borrowerIndex := idx,
               accrued := a.accrued +
                 a.borrow * (idx - accrualStart a.borrowerIndex idx) / doubleScale }) := by
  induction l generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      simp
    | succ n =>
      simp [ih]

theorem modify_grant_congr (l : List Acct) (i : Nat) :
    l.modify i (fun a =>
      { a with accrued := 0, wallet := a.wallet + (l[i]?.getD noAcct).accrued }) =
    l.modify i (fun a =>
      { a with accrued := (0 : Nat), wallet := a.wallet + a.accrued }) := by
  induction l generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      simp
    | succ n =>
      simp [ih]

theorem distributeSupply_some {s s' : St} {who : Account}
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp at h
  dsimp only at h
  have heq : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    accrualStart_eq _ _
  rw [heq] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index
  · have hs : subChecked s.supplyState.index
        (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
        some (s.supplyState.index -
          accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
      subChecked_some hle
    rw [hs] at h
    cases h
    refine ⟨hle, ?_⟩
    have hmod := modify_supply_congr s.accts who s.supplyState.index
    unfold St.withAcct St.acct List.getD
    simp only [mulDouble, creditFor] at hmod ⊢
    rw [hmod]
  · have hn : subChecked s.supplyState.index
        (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none :=
      subChecked_none hle
    rw [hn] at h
    contradiction

theorem distributeSupply_none {s : St} {who : Account}
    (h : distributeSupplierComp s who = none) :
    ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index := by
  unfold distributeSupplierComp at h
  dsimp only at h
  have heq : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    accrualStart_eq _ _
  rw [heq] at h
  intro hle
  have hs : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index -
        accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    subChecked_some hle
  rw [hs] at h
  contradiction

theorem distributeBorrow_some {s s' : St} {who : Account}
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp at h
  dsimp only at h
  have heq : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    accrualStart_eq _ _
  rw [heq] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index
  · have hs : subChecked s.borrowState.index
        (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
        some (s.borrowState.index -
          accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
      subChecked_some hle
    rw [hs] at h
    cases h
    refine ⟨hle, ?_⟩
    have hmod := modify_borrow_congr s.accts who s.borrowState.index
    unfold St.withAcct St.acct List.getD
    simp only [mulDouble, creditFor] at hmod ⊢
    rw [hmod]
  · have hn : subChecked s.borrowState.index
        (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none :=
      subChecked_none hle
    rw [hn] at h
    contradiction

theorem distributeBorrow_none {s : St} {who : Account}
    (h : distributeBorrowerComp s who = none) :
    ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index := by
  unfold distributeBorrowerComp at h
  dsimp only at h
  have heq : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    accrualStart_eq _ _
  rw [heq] at h
  intro hle
  have hs : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index -
        accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    subChecked_some hle
  rw [hs] at h
  contradiction

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct List.getD
  by_cases h : (s.accts[who]?.getD noAcct).accrued > 0 ∧
      (s.accts[who]?.getD noAcct).accrued ≤ s.reserve
  · simp only [h] at ⊢
    have hmod := modify_grant_congr s.accts who
    rw [hmod]
  · simp [h]

theorem totalSupply_updateBorrow (s : St) (s1 : St)
    (h : updateCompBorrowIndex s = some s1) : totalSupply s1 = totalSupply s := by
  have ⟨_, heq⟩ := updateBorrow_some h
  rw [heq]
  rfl

theorem totalBorrows_updateSupply (s : St) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) : totalBorrows s1 = totalBorrows s := by
  have ⟨_, heq⟩ := updateSupply_some h
  rw [heq]
  rfl

theorem acct_updateSupply (s : St) (s1 : St) (who : Account)
    (h : updateCompSupplyIndex s = some s1) : s1.acct who = s.acct who := by
  have ⟨_, heq⟩ := updateSupply_some h
  rw [heq]
  rfl

theorem acct_updateBorrow (s : St) (s1 : St) (who : Account)
    (h : updateCompBorrowIndex s = some s1) : s1.acct who = s.acct who := by
  have ⟨_, heq⟩ := updateBorrow_some h
  rw [heq]
  rfl

theorem setSupply_some {s s1 : St} {a : Nat}
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1 = (if s.supplyState.speed = a then s else
      { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
        supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    cases h
    refine ⟨fun hne => absurd heq hne, ?_⟩
    simp [heq]
  · simp [heq] at h
    cases hU : updateCompSupplyIndex s with
    | none =>
      simp [hU] at h
    | some sMid =>
      simp [hU] at h
      cases h
      have ⟨hb, heq2⟩ := updateSupply_some hU
      refine ⟨fun _ => hb, ?_⟩
      simp only [heq, if_false]
      rw [heq2]

theorem setBorrow_some {s s1 : St} {b : Nat}
    (h : setBorrowSpeed s b = some s1) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s1 = (if s.borrowState.speed = b then s else
      { { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with
        borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    cases h
    refine ⟨fun hne => absurd heq hne, ?_⟩
    simp [heq]
  · simp [heq] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      simp [hU] at h
    | some sMid =>
      simp [hU] at h
      cases h
      have ⟨hb, heq2⟩ := updateBorrow_some hU
      refine ⟨fun _ => hb, ?_⟩
      simp only [heq, if_false]
      rw [heq2]

theorem comptroller_supplyHook {s s' : St} {who : Account}
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' := by
  unfold comptroller at h
  simp only at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    simp [hU] at h
  | some sMid =>
    simp [hU] at h
    have ⟨hb, heqU⟩ := updateSupply_some hU
    have ⟨hle, heqD⟩ := distributeSupply_some (s := sMid) (who := who) h
    have hacct : sMid.acct who = s.acct who := acct_updateSupply s sMid who hU
    have hidx : sMid.supplyState.index =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [heqU]
    rw [hacct, hidx] at hle
    refine ⟨hb, hle, ?_⟩
    rw [heqD, heqU]

theorem comptroller_borrowHook {s s' : St} {who : Account}
    (h : comptroller s (.borrowHook who) = some s') :
    BorrowDistributed s who s' := by
  unfold comptroller at h
  simp only at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    simp [hU] at h
  | some sMid =>
    simp [hU] at h
    have ⟨hb, heqU⟩ := updateBorrow_some hU
    have ⟨hle, heqD⟩ := distributeBorrow_some (s := sMid) (who := who) h
    have hacct : sMid.acct who = s.acct who := acct_updateBorrow s sMid who hU
    have hidx : sMid.borrowState.index =
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [heqU]
    rw [hacct, hidx] at hle
    refine ⟨hb, hle, ?_⟩
    rw [heqD, heqU]

theorem acct_ge_noAcct {l : List Acct} {who : Nat} (h : ¬ who < l.length) :
    l.getD who noAcct = noAcct := by
  induction l generalizing who with
  | nil =>
    simp
  | cons x xs ih =>
    cases who with
    | zero =>
      have hpos : 0 < (x :: xs).length := by simp
      exact absurd hpos h
    | succ n =>
      have hlen : (x :: xs).length = xs.length + 1 := rfl
      have h2 : ¬ n < xs.length := by omega
      exact ih h2

theorem acct_mem_of_lt {s : St} {who : Account} (h : who < s.accts.length) :
    s.acct who ∈ s.accts := by
  unfold St.acct
  have heq : s.accts[who] = s.accts.getD who noAcct :=
    List.getElem_eq_getD noAcct
  rw [← heq]
  exact List.getElem_mem h

theorem acct_eq_getElem {s : St} {who : Account} (h : who < s.accts.length) :
    s.acct who = s.accts[who] := by
  unfold St.acct
  exact (List.getElem_eq_getD noAcct).symm

theorem accrualStart_le_new_supply {s : St} (hc : Consistent s) (who : Account)
    (newIdx : Nat) (hge : s.supplyState.index ≤ newIdx) :
    accrualStart (s.acct who).supplierIndex newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases hrec : (s.acct who).supplierIndex = 0
  · simp [hrec]
    by_cases hle : compInitialIndex ≤ newIdx
    · simp [hle]
    · simp [hle]
  · simp [hrec]
    by_cases hmem : who < s.accts.length
    · have hmem2 : s.acct who ∈ s.accts := acct_mem_of_lt hmem
      have hle_old : (s.acct who).supplierIndex ≤ s.supplyState.index := by
        have hcon := hc.2.2
        exact (hcon (s.acct who) hmem2).1
      omega
    · have heq : s.acct who = noAcct := acct_ge_noAcct hmem
      have h0 : (s.acct who).supplierIndex = 0 := by rw [heq]; rfl
      exact absurd h0 hrec

theorem accrualStart_le_new_borrow {s : St} (hc : Consistent s) (who : Account)
    (newIdx : Nat) (hge : s.borrowState.index ≤ newIdx) :
    accrualStart (s.acct who).borrowerIndex newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases hrec : (s.acct who).borrowerIndex = 0
  · simp [hrec]
    by_cases hle : compInitialIndex ≤ newIdx
    · simp [hle]
    · simp [hle]
  · simp [hrec]
    by_cases hmem : who < s.accts.length
    · have hmem2 : s.acct who ∈ s.accts := acct_mem_of_lt hmem
      have hle_old : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
        have hcon := hc.2.2
        exact (hcon (s.acct who) hmem2).2
      omega
    · have heq : s.acct who = noAcct := acct_ge_noAcct hmem
      have h0 : (s.acct who).borrowerIndex = 0 := by rw [heq]; rfl
      exact absurd h0 hrec

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  exact comptroller_supplyHook h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  exact comptroller_borrowHook h

theorem updateSupply_succeeds {s : St} (hb : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' := by
  unfold updateCompSupplyIndex
  have hs : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := subChecked_some hb
  rw [hs]
  by_cases h1 : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · simp [h1]
  · simp [h1]
    by_cases h2 : (s.blockNumber - s.supplyState.block) > 0
    · simp [h2]
    · simp [h2]

theorem updateBorrow_succeeds {s : St} (hb : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' := by
  unfold updateCompBorrowIndex
  have hs : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := subChecked_some hb
  rw [hs]
  by_cases h1 : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · simp [h1]
  · simp [h1]
    by_cases h2 : (s.blockNumber - s.borrowState.block) > 0
    · simp [h2]
    · simp [h2]

theorem distributeSupply_succeeds {s : St} {who : Account}
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by
  unfold distributeSupplierComp
  dsimp only
  have heq : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    accrualStart_eq _ _
  rw [heq]
  have hs : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index -
        accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    subChecked_some hle
  rw [hs]
  exact ⟨_, rfl⟩

theorem distributeBorrow_succeeds {s : St} {who : Account}
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by
  unfold distributeBorrowerComp
  dsimp only
  have heq : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    accrualStart_eq _ _
  rw [heq]
  have hs : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index -
        accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    subChecked_some hle
  rw [hs]
  exact ⟨_, rfl⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    simp only
    have hb : s.supplyState.block ≤ s.blockNumber := hc.1
    obtain ⟨sMid, hU⟩ := updateSupply_succeeds hb
    have hge : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrueSide_index_ge _ _ _
    have hMid_eq : sMid =
        { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      have ⟨_, heq⟩ := updateSupply_some hU
      exact heq
    have hle : accrualStart (sMid.acct who).supplierIndex sMid.supplyState.index ≤ sMid.supplyState.index := by
      rw [hMid_eq]
      have hacct : St.acct { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who = s.acct who := rfl
      rw [hacct]
      have hidx : (St.supplyState { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
      rw [hidx]
      exact accrualStart_le_new_supply hc who _ hge
    obtain ⟨_, hD⟩ := distributeSupply_succeeds hle
    simp [hU, hD]
  | borrowHook who =>
    unfold comptroller
    simp only
    have hb : s.borrowState.block ≤ s.blockNumber := hc.2.1
    obtain ⟨sMid, hU⟩ := updateBorrow_succeeds hb
    have hge : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    have hMid_eq : sMid =
        { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have ⟨_, heq⟩ := updateBorrow_some hU
      exact heq
    have hle : accrualStart (sMid.acct who).borrowerIndex sMid.borrowState.index ≤
        sMid.borrowState.index := by
      rw [hMid_eq]
      have hacct : St.acct { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who = s.acct who := rfl
      rw [hacct]
      have hidx : (St.borrowState { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
      rw [hidx]
      exact accrualStart_le_new_borrow hc who _ hge
    obtain ⟨_, hD⟩ := distributeBorrow_succeeds hle
    simp [hU, hD]
  | claim who =>
    unfold comptroller claimComp
    simp only
    have hbB : s.borrowState.block ≤ s.blockNumber := hc.2.1
    obtain ⟨s1, hU1⟩ := updateBorrow_succeeds hbB
    have hMid1_eq : s1 =
        { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have ⟨_, heq⟩ := updateBorrow_some hU1
      exact heq
    have hgeB : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    have hle1 : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤
        s1.borrowState.index := by
      rw [hMid1_eq]
      have hacct : St.acct { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who = s.acct who := rfl
      rw [hacct]
      have hidx : (St.borrowState { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
      rw [hidx]
      exact accrualStart_le_new_borrow hc who _ hgeB
    obtain ⟨s2, hD1⟩ := distributeBorrow_succeeds hle1
    have hS2_eq : s2.supplyState = s.supplyState := by
      have ⟨_, heqU1⟩ := updateBorrow_some hU1
      have ⟨_, heqD1⟩ := distributeBorrow_some (s := s1) (who := who) hD1
      rw [heqU1] at heqD1 ⊢
      rw [heqD1]
      rfl
    have hbS2 : s2.supplyState.block ≤ s2.blockNumber := by
      rw [hS2_eq]
      exact hc.1
    obtain ⟨s3, hU2⟩ := updateSupply_succeeds hbS2
    have hMid3_eq : s3 =
        { s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } := by
      have ⟨_, heq⟩ := updateSupply_some hU2
      exact heq
    have hgeS : s2.supplyState.index ≤
        (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index :=
      accrueSide_index_ge _ _ _
    have hS2_supIdx : s2.supplyState.index = s.supplyState.index := by
      rw [hS2_eq]
    have hS2_acctSup : (s2.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have heqU1_accts : s1.accts = s.accts := by
        have ⟨_, heqU1b⟩ := updateBorrow_some hU1
        rw [heqU1b]
      have heqD1_accts : ∀ a ∈ s1.accts, True := fun _ _ => trivial
      by_cases hmem : who < s.accts.length
      · have hmem1 : who < s1.accts.length := by rw [heqU1_accts]; exact hmem
        have hlen2 : s2.accts.length = s1.accts.length := by
          have ⟨_, heqD1b⟩ := distributeBorrow_some (s := s1) (who := who) hD1
          rw [heqD1b]
          exact List.length_modify _ _ _
        have hmem2 : who < s2.accts.length := by rw [hlen2]; exact hmem1
        have heq1 : s1.acct who = s.acct who := by
          unfold St.acct
          rw [heqU1_accts]
        have heq2Sup : (s2.acct who).supplierIndex = (s1.acct who).supplierIndex := by
          have ⟨_, heqD1b⟩ := distributeBorrow_some (s := s1) (who := who) hD1
          have hmod_len : (s1.accts.modify who fun a =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index }).length =
              s1.accts.length := List.length_modify _ _ _
          have hmem2len : who < (s1.accts.modify who fun a =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index }).length := by
            rw [hmod_len]
            exact hmem1
          have hgetmod : ((s1.accts.modify who fun a =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index })[who]) =
              ((fun a : Acct =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index }) (s1.accts[who])) := by
            have h := List.getElem_modify (fun a : Acct =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index }) who s1.accts who hmem2len
            simp at h
            exact h
          have hget1 : s1.accts[who] = s1.accts.getD who noAcct :=
            List.getElem_eq_getD noAcct
          have hget2 : ((s1.accts.modify who fun a =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index })[who]) =
              ((s1.accts.modify who fun a =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index }).getD who noAcct) :=
            List.getElem_eq_getD noAcct
          have hs2eq : s2.accts = s1.accts.modify who fun a =>
              { a with borrowerIndex := s1.borrowState.index,
                       accrued := a.accrued + creditFor a.borrow
                         (accrualStart a.borrowerIndex s1.borrowState.index) s1.borrowState.index } := by
            rw [heqD1b]
          unfold St.acct
          rw [hs2eq]
          rw [← hget2, hgetmod, ← hget1]
          rfl
        have heq2 : (s2.acct who).supplierIndex = (s1.acct who).supplierIndex := heq2Sup
        rw [heq2, heq1]
      · have hno1 : s.acct who = noAcct := acct_ge_noAcct hmem
        have hmem1 : ¬ who < s1.accts.length := by rw [heqU1_accts]; exact hmem
        have hnoS1 : s1.acct who = noAcct := acct_ge_noAcct hmem1
        have hlen2 : s2.accts.length = s1.accts.length := by
          have ⟨_, heqD1b⟩ := distributeBorrow_some (s := s1) (who := who) hD1
          rw [heqD1b]
          exact List.length_modify _ _ _
        have hmem2 : ¬ who < s2.accts.length := by rw [hlen2]; exact hmem1
        have hnoS2 : s2.acct who = noAcct := acct_ge_noAcct hmem2
        rw [hnoS2, hno1]
    have hle2 : accrualStart (s3.acct who).supplierIndex s3.supplyState.index ≤
        s3.supplyState.index := by
      rw [hMid3_eq]
      have hacct : St.acct { s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) } who = s2.acct who := rfl
      rw [hacct]
      have hidx : (St.supplyState { s2 with supplyState := accrueSide s2.supplyState s2.blockNumber (totalSupply s2) }).index = (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index := rfl
      rw [hidx]
      unfold accrualStart
      by_cases hrec : (s2.acct who).supplierIndex = 0
      · simp [hrec]
        by_cases hle : compInitialIndex ≤
            (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index
        · simp [hle]
        · simp [hle]
      · simp [hrec]
        have hrecS : (s.acct who).supplierIndex ≠ 0 := by
          rw [← hS2_acctSup]
          exact hrec
        by_cases hmem : who < s.accts.length
        · have hmem2 : s.acct who ∈ s.accts := acct_mem_of_lt hmem
          have hle_old : (s.acct who).supplierIndex ≤ s.supplyState.index := by
            have hcon := hc.2.2
            exact (hcon (s.acct who) hmem2).1
          have hgeS2 : s2.supplyState.index ≤
              (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index :=
            accrueSide_index_ge _ _ _
          omega
        · have heq : s.acct who = noAcct := acct_ge_noAcct hmem
          have h0 : (s.acct who).supplierIndex = 0 := by rw [heq]; rfl
          exact absurd h0 hrecS
    obtain ⟨_, hD2⟩ := distributeSupply_succeeds hle2
    simp [hU1, hD1, hU2, hD2]
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed
    simp only
    by_cases heqA : s.supplyState.speed = a
    · simp [heqA]
      by_cases heqB : s.borrowState.speed = b
      · simp [heqB]
      · simp [heqB]
        obtain ⟨_, hU⟩ := updateBorrow_succeeds hc.2.1
        simp [hU]
    · simp [heqA]
      obtain ⟨_, hU⟩ := updateSupply_succeeds hc.1
      simp [hU]
      by_cases heqB : (if s.supplyState.speed = a then s else
          { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
            supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).borrowState.speed = b
      · simp [heqB]
      · simp [heqB]
        have hb : (if s.supplyState.speed = a then s else
            { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
              supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).borrowState.block ≤
            (if s.supplyState.speed = a then s else
            { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
              supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).blockNumber := by
          by_cases heqA2 : s.supplyState.speed = a
          · simp [heqA2]
            exact hc.2.1
          · simp [heqA2]
            exact hc.2.1
        obtain ⟨_, hU2⟩ := updateBorrow_succeeds hb
        simp [hU2]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
  cases hB1 : updateCompBorrowIndex s with
  | none =>
    simp [hB1] at h
  | some s1 =>
    simp [hB1] at h
    cases hD1 : distributeBorrowerComp s1 who with
    | none =>
      simp [hD1] at h
    | some s2 =>
      simp [hD1] at h
      cases hU2 : updateCompSupplyIndex s2 with
      | none =>
        simp [hU2] at h
      | some s3 =>
        simp [hU2] at h
        cases hD2 : distributeSupplierComp s3 who with
        | none =>
          simp [hD2] at h
        | some s4 =>
          simp [hD2] at h
          cases h
          refine ⟨s2, s4, ?_, ?_, ?_⟩
          · have ⟨hb1, heqU1⟩ := updateBorrow_some hB1
            have ⟨hle1, heqD1⟩ := distributeBorrow_some (s := s1) (who := who) hD1
            have hacct1 : s1.acct who = s.acct who := acct_updateBorrow s s1 who hB1
            have hidx1 : s1.borrowState.index =
                (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
              rw [heqU1]
            rw [hacct1, hidx1] at hle1
            refine ⟨hb1, hle1, ?_⟩
            rw [heqD1, heqU1]
          · have ⟨hb2, heqU2⟩ := updateSupply_some hU2
            have ⟨hle2, heqD2⟩ := distributeSupply_some (s := s3) (who := who) hD2
            have hacct2 : s3.acct who = s2.acct who := acct_updateSupply s2 s3 who hU2
            have hidx2 : s3.supplyState.index =
                (accrueSide s2.supplyState s2.blockNumber (totalSupply s2)).index := by
              rw [heqU2]
            rw [hacct2, hidx2] at hle2
            refine ⟨hb2, hle2, ?_⟩
            · rw [heqD2, heqU2]
          · rw [grant_eq]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  simp only at h
  cases hS1 : setSupplySpeed s a with
  | none =>
    simp [hS1] at h
  | some sMid =>
    simp [hS1] at h
    cases hS2 : setBorrowSpeed sMid b with
    | none =>
      simp [hS2] at h
    | some s2 =>
      simp [hS2] at h
      cases h
      have ⟨hbS, heqS⟩ := setSupply_some hS1
      have ⟨hbB, heqB⟩ := setBorrow_some (s := sMid) (b := b) hS2
      have hacctsMid : sMid.accts = s.accts := by
        rw [heqS]
        by_cases heq : s.supplyState.speed = a
        · simp [heq]
        · simp [heq]
      have hborMid : sMid.borrowState = s.borrowState := by
        rw [heqS]
        by_cases heq : s.supplyState.speed = a
        · simp [heq]
        · simp [heq]
      have hbnMid : sMid.blockNumber = s.blockNumber := by
        rw [heqS]
        by_cases heq : s.supplyState.speed = a
        · simp [heq]
        · simp [heq]
      have htotB : totalBorrows sMid = totalBorrows s := by
        unfold totalBorrows
        rw [hacctsMid]
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exact hbS hne
      · intro hne
        have hneMid : sMid.borrowState.speed ≠ b := by rw [hborMid]; exact hne
        have hbB2 := hbB hneMid
        rw [hbnMid, hborMid] at hbB2
        exact hbB2
      · rw [heqB, heqS]
        by_cases heqA : s.supplyState.speed = a
        · simp [heqA, hborMid, hbnMid, hacctsMid, htotB]
          by_cases heqBb : s.borrowState.speed = b
          · simp [heqBb, hborMid]
          · simp [heqBb, htotB]
        · simp [heqA, hborMid, hbnMid, hacctsMid, htotB]
          by_cases heqBb : s.borrowState.speed = b
          · simp [heqBb, hborMid]
          · simp [heqBb, htotB]; exact ⟨rfl, rfl⟩
