import CompRewards.Spec
/-!
Fixed COMP distribution (see top of file in previous version).
Fix: `≥ compInitialIndex` in both distributors.
-/
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
  match subChecked s.supplyState.index (if (s.acct supplier).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct supplier).supplierIndex) with
  | none => none
  | some deltaIndex =>
    some (s.withAcct supplier fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + mulDouble (s.acct supplier).supply deltaIndex })

def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  match subChecked s.borrowState.index (if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct borrower).borrowerIndex) with
  | none => none
  | some deltaIndex =>
    some (s.withAcct borrower fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + mulDouble (s.acct borrower).borrow deltaIndex })

def grantCompInternal (s : St) (user : Account) : St :=
  if 0 < (s.acct user).accrued ∧ (s.acct user).accrued ≤ s.reserve then
    { s with
      reserve := s.reserve - (s.acct user).accrued,
      accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + (s.acct user).accrued } }
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
  unfold subChecked; simp [h]

theorem subChecked_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem accrualStart_le_index (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases h0 : recorded = 0
  · subst h0
    by_cases h1 : compInitialIndex ≤ index
    · simp only [h1, ite_true]
    · simp only [h1, ite_false]; exact Nat.zero_le _
  · simp only [h0, ite_false]; exact h

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide; by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide; by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide; by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem fixed_supply_start (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · simp only [h0]
    by_cases h1 : compInitialIndex ≤ s.supplyState.index <;> simp [h1]
  · simp [h0]

theorem fixed_borrow_start (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · simp only [h0]
    by_cases h1 : compInitialIndex ≤ s.borrowState.index <;> simp [h1]
  · simp [h0]

theorem modify_supply_congr (l : List Acct) (who idx : Nat) :
    l.modify who (fun a => { a with supplierIndex := idx, accrued := a.accrued + mulDouble (l.getD who noAcct).supply (idx - accrualStart (l.getD who noAcct).supplierIndex idx) }) =
    l.modify who (fun a => { a with supplierIndex := idx, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex idx) idx }) := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons x xs ih =>
    cases who with
    | zero => rfl
    | succ n =>
      show x :: xs.modify n (fun a => { a with supplierIndex := idx, accrued := a.accrued + mulDouble (xs.getD n noAcct).supply (idx - accrualStart (xs.getD n noAcct).supplierIndex idx) }) =
        x :: xs.modify n (fun a => { a with supplierIndex := idx, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex idx) idx })
      rw [ih]

theorem modify_borrow_congr (l : List Acct) (who idx : Nat) :
    l.modify who (fun a => { a with borrowerIndex := idx, accrued := a.accrued + mulDouble (l.getD who noAcct).borrow (idx - accrualStart (l.getD who noAcct).borrowerIndex idx) }) =
    l.modify who (fun a => { a with borrowerIndex := idx, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex idx) idx }) := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons x xs ih =>
    cases who with
    | zero => rfl
    | succ n =>
      show x :: xs.modify n (fun a => { a with borrowerIndex := idx, accrued := a.accrued + mulDouble (xs.getD n noAcct).borrow (idx - accrualStart (xs.getD n noAcct).borrowerIndex idx) }) =
        x :: xs.modify n (fun a => { a with borrowerIndex := idx, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex idx) idx })
      rw [ih]

theorem modify_grant_congr (l : List Acct) (who : Nat) :
    l.modify who (fun a => { a with accrued := 0, wallet := a.wallet + (l.getD who noAcct).accrued }) =
    l.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons x xs ih =>
    cases who with
    | zero => rfl
    | succ n =>
      show x :: xs.modify n (fun a => { a with accrued := 0, wallet := a.wallet + (xs.getD n noAcct).accrued }) =
        x :: xs.modify n (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued })
      rw [ih]

theorem updateSupply_some_block (s t : St) (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · unfold updateCompSupplyIndex subChecked at h
    simp [hb] at h

theorem updateBorrow_some_block (s t : St) (h : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber := by
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · exact hb
  · unfold updateCompBorrowIndex subChecked at h
    simp [hb] at h

theorem distribSupply_some_start (s t : St) (who : Nat)
    (h : distributeSupplierComp s who = some t) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  by_cases hs : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · exact hs
  · exfalso
    have hn : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none :=
      subChecked_none (by omega)
    have heq : distributeSupplierComp s who = none := by
      unfold distributeSupplierComp
      simp [fixed_supply_start s who, hn]
    rw [heq] at h
    simp at h

theorem distribBorrow_some_start (s t : St) (who : Nat)
    (h : distributeBorrowerComp s who = some t) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  by_cases hs : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · exact hs
  · exfalso
    have hn : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none :=
      subChecked_none (by omega)
    have heq : distributeBorrowerComp s who = none := by
      unfold distributeBorrowerComp
      simp [fixed_borrow_start s who, hn]
    rw [heq] at h
    simp at h

theorem distributeSupply_eq (s : St) (who : Nat)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp St.withAcct
  have hf := fixed_supply_start s who
  rw [hf]
  rw [subChecked_some h]
  have hm := modify_supply_congr s.accts who s.supplyState.index
  simp only [St.acct] at hm ⊢
  rw [hm]

theorem distributeBorrow_eq (s : St) (who : Nat)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := s.borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp St.withAcct
  have hf := fixed_borrow_start s who
  rw [hf]
  rw [subChecked_some h]
  have hm := modify_borrow_congr s.accts who s.borrowState.index
  simp only [St.acct] at hm ⊢
  rw [hm]

theorem grant_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  by_cases hc : 0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve
  · simp only [hc, modify_grant_congr]
  · simp only [hc, ite_false]

theorem updateSupply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked accrueSide fraction
  simp [h]
  by_cases hT : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < totalSupply s
  · have hd : 0 < s.blockNumber - s.supplyState.block := hT.1
    have hs : 0 < s.supplyState.speed := hT.2.1
    have ht : 0 < totalSupply s := hT.2.2
    simp [hd, hs, ht]
  · by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · by_cases hs : 0 < s.supplyState.speed
      · have ht : totalSupply s = 0 := by omega
        simp [hd, hs, ht]
      · simp [hd, hs]
    · have h0 : s.blockNumber - s.supplyState.block = 0 := by omega
      have hbl : s.supplyState.block = s.blockNumber := by omega
      simp [h0]
      cases s with | mk bn sup bor res ac =>
        simp at hbl ⊢
        cases sup with | mk ix blk spd =>
          simp at hbl ⊢; subst hbl; rfl

theorem updateBorrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked accrueSide fraction
  simp [h]
  by_cases hT : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < totalBorrows s
  · have hd : 0 < s.blockNumber - s.borrowState.block := hT.1
    have hs : 0 < s.borrowState.speed := hT.2.1
    have ht : 0 < totalBorrows s := hT.2.2
    simp [hd, hs, ht]
  · by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · by_cases hs : 0 < s.borrowState.speed
      · have ht : totalBorrows s = 0 := by omega
        simp [hd, hs, ht]
      · simp [hd, hs]
    · have h0 : s.blockNumber - s.borrowState.block = 0 := by omega
      have hbl : s.borrowState.block = s.blockNumber := by omega
      simp [h0]
      cases s with | mk bn sup bor res ac =>
        simp at hbl ⊢
        cases bor with | mk ix blk spd =>
          simp at hbl ⊢; subst hbl; rfl

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompSupplyIndex s with
  | none => simp [hu] at h
  | some t =>
    simp [hu] at h
    have hb := updateSupply_some_block s t hu
    have hs0 := distribSupply_some_start t s' who h
    have heq1 := updateSupply_eq s hb
    rw [hu] at heq1
    have ht : t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      cases heq1; rfl
    have hs : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      simpa [ht, St.acct] using hs0
    have heq2 := distributeSupply_eq t who hs0
    rw [h] at heq2
    have hs' : s' = { t with accts := t.accts.modify who fun a =>
        { a with
          supplierIndex := t.supplyState.index,
          accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex t.supplyState.index) t.supplyState.index } } := by
      cases heq2; rfl
    refine ⟨hb, hs, ?_⟩
    rw [hs', ht]

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hu : updateCompBorrowIndex s with
  | none => simp [hu] at h
  | some t =>
    simp [hu] at h
    have hb := updateBorrow_some_block s t hu
    have hs0 := distribBorrow_some_start t s' who h
    have heq1 := updateBorrow_eq s hb
    rw [hu] at heq1
    have ht : t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      cases heq1; rfl
    have hs : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      simpa [ht, St.acct] using hs0
    have heq2 := distributeBorrow_eq t who hs0
    rw [h] at heq2
    have hs' : s' = { t with accts := t.accts.modify who fun a =>
        { a with
          borrowerIndex := t.borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex t.borrowState.index) t.borrowState.index } } := by
      cases heq2; rfl
    refine ⟨hb, hs, ?_⟩
    rw [hs', ht]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  cases hb1 : updateCompBorrowIndex s with
  | none => simp [hb1] at h
  | some t1 =>
    simp [hb1] at h
    cases hd1 : distributeBorrowerComp t1 who with
    | none => simp [hd1] at h
    | some m1 =>
      simp [hd1] at h
      cases hb2 : updateCompSupplyIndex m1 with
      | none => simp [hb2] at h
      | some t2 =>
        simp [hb2] at h
        cases hd2 : distributeSupplierComp t2 who with
        | none => simp [hd2] at h
        | some m2 =>
          simp [hd2] at h
          have hbloc1 := updateBorrow_some_block s t1 hb1
          have hbloc2 := updateSupply_some_block m1 t2 hb2
          have hst1 := distribBorrow_some_start t1 m1 who hd1
          have hst2 := distribSupply_some_start t2 m2 who hd2
          have heqB1 := updateBorrow_eq s hbloc1
          rw [hb1] at heqB1
          have ht1 : t1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
            cases heqB1; rfl
          have heqD1 := distributeBorrow_eq t1 who hst1
          rw [hd1] at heqD1
          have hm1 : m1 = { t1 with accts := t1.accts.modify who fun a =>
              { a with
                borrowerIndex := t1.borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index } } := by
            cases heqD1; rfl
          have heqB2 := updateSupply_eq m1 hbloc2
          rw [hb2] at heqB2
          have ht2 : t2 = { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } := by
            cases heqB2; rfl
          have heqD2 := distributeSupply_eq t2 who hst2
          rw [hd2] at heqD2
          have hm2 : m2 = { t2 with accts := t2.accts.modify who fun a =>
              { a with
                supplierIndex := t2.supplyState.index,
                accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex t2.supplyState.index) t2.supplyState.index } } := by
            cases heqD2; rfl
          have hgrant : grantCompInternal m2 who = grant m2 who := grant_eq m2 who
          simp [hgrant] at h
          have hs' : s' = grant m2 who := by cases h; rfl
          have hbor : BorrowDistributed s who m1 := by
            have hb : s.borrowState.block ≤ s.blockNumber := hbloc1
            have hs : accrualStart (s.acct who).borrowerIndex
                (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
                (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
              simpa [ht1, St.acct] using hst1
            refine ⟨hb, hs, ?_⟩
            rw [hm1, ht1]
          have hsup : SupplyDistributed m1 who m2 := by
            have hb : m1.supplyState.block ≤ m1.blockNumber := hbloc2
            have hs : accrualStart (m1.acct who).supplierIndex
                (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index ≤
                (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
              simpa [ht2, St.acct] using hst2
            refine ⟨hb, hs, ?_⟩
            rw [hm2, ht2]
          exact ⟨m1, m2, hbor, hsup, hs'⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  cases h1 : setSupplySpeed s a with
  | none => simp [h1] at h
  | some mid =>
    simp [h1] at h
    cases h2 : setBorrowSpeed mid b with
    | none => simp [h2] at h
    | some fin =>
      simp [h2] at h
      have hfin : s' = fin := by cases h; rfl
      unfold setSupplySpeed at h1
      unfold setBorrowSpeed at h2
      by_cases hs : s.supplyState.speed ≠ a
      · simp [hs] at h1
        cases hu : updateCompSupplyIndex s with
        | none => simp [hu] at h1
        | some t =>
          simp [hu] at h1
          have hb := updateSupply_some_block s t hu
          have heq := updateSupply_eq s hb
          rw [hu] at heq
          have ht : t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
            cases heq; rfl
          have hmid : mid = { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
            simp [ht] at h1
            cases h1; rfl
          have hmid_accts : mid.accts = s.accts := by simp [hmid]
          have hmid_bn : mid.blockNumber = s.blockNumber := by simp [hmid]
          have hmid_bor : mid.borrowState = s.borrowState := by simp [hmid]
          have hmid_tot : totalBorrows mid = totalBorrows s := by simp [totalBorrows, hmid_accts]
          by_cases hb2 : s.borrowState.speed ≠ b
          · have hbmid : mid.borrowState.speed ≠ b := by simp [hmid_bor, hb2]
            simp [hbmid] at h2
            cases huv : updateCompBorrowIndex mid with
            | none => simp [huv] at h2
            | some tb =>
              simp [huv] at h2
              have hbl := updateBorrow_some_block mid tb huv
              have heqb := updateBorrow_eq mid hbl
              rw [huv] at heqb
              have htb : tb = { mid with borrowState := accrueSide mid.borrowState mid.blockNumber (totalBorrows mid) } := by
                cases heqb; rfl
              have hfin2 : fin = { tb with borrowState := { tb.borrowState with speed := b } } := by
                cases h2; rfl
              refine ⟨fun _ => hb, fun _ => ?_, ?_⟩
              · simp [hmid_bor, hmid_bn] at hbl
                exact hbl
              · rw [hfin, hfin2, htb, hmid]
                simp [hs, hb2, totalBorrows, totalSupply]
          · have hbmid : ¬ mid.borrowState.speed ≠ b := by simp [hmid_bor, hb2]
            simp [hbmid] at h2
            have hfin2 : fin = mid := by cases h2; rfl
            refine ⟨fun _ => hb, fun hne => absurd hne hb2, ?_⟩
            simp [hs, hb2, hfin, hfin2, hmid]
      · simp [hs] at h1
        have hmid : mid = s := by cases h1; rfl
        by_cases hb2 : s.borrowState.speed ≠ b
        · have hbmid : mid.borrowState.speed ≠ b := by simp [hmid, hb2]
          simp [hbmid] at h2
          cases huv : updateCompBorrowIndex mid with
          | none => simp [huv] at h2
          | some tb =>
            simp [huv] at h2
            have hbl := updateBorrow_some_block mid tb huv
            have heqb := updateBorrow_eq mid hbl
            rw [huv] at heqb
            have htb : tb = { mid with borrowState := accrueSide mid.borrowState mid.blockNumber (totalBorrows mid) } := by
              cases heqb; rfl
            have hfin2 : fin = { tb with borrowState := { tb.borrowState with speed := b } } := by
              cases h2; rfl
            have hmid_tot : totalBorrows mid = totalBorrows s := by simp [hmid, totalBorrows]
            have hmid_bn : mid.blockNumber = s.blockNumber := by simp [hmid]
            have hmid_bor : mid.borrowState = s.borrowState := by simp [hmid]
            refine ⟨fun hne => absurd hne hs, fun _ => ?_, ?_⟩
            · simp [hmid] at hbl
              exact hbl
            · cases s with | mk bn sup bor res ac =>
                simp only at hfin hfin2 htb hmid hmid_tot hmid_bn hmid_bor hs hb2 hbl ⊢
                have hseq : sup.speed = a := by omega
                simp [hfin, hfin2, htb, hmid, totalBorrows, hseq, hb2]
        · have hbmid : ¬ mid.borrowState.speed ≠ b := by simp [hmid, hb2]
          simp [hbmid] at h2
          have hfin2 : fin = mid := by cases h2; rfl
          refine ⟨fun hne => absurd hne hs, fun hne => absurd hne hb2, ?_⟩
          have hseq1 : s.supplyState.speed = a := by omega
          have hseq2 : s.borrowState.speed = b := by omega
          simp [hseq1, hseq2, hmid, hfin, hfin2]

theorem getD_modify_preserve_supplier (l : List Acct) (who : Nat) (f : Acct -> Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify who f).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons x xs ih =>
    cases who with
    | zero => exact hf x
    | succ n => show ((xs.modify n f).getD n noAcct).supplierIndex = (xs.getD n noAcct).supplierIndex; exact ih n f hf

theorem acct_supply_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) : (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero => exact h x (List.Mem.head xs)
    | succ n =>
      show (xs.getD n noAcct).supplierIndex ≤ idx
      exact ih n (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem acct_borrow_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) : (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil => simp [noAcct]
  | cons x xs ih =>
    cases who with
    | zero => exact h x (List.Mem.head xs)
    | succ n =>
      show (xs.getD n noAcct).borrowerIndex ≤ idx
      exact ih n (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem consistent_supply_le (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hacc⟩ := hc
  unfold St.acct
  exact acct_supply_le s.accts who s.supplyState.index (fun a ha => (hacc a ha).1)

theorem consistent_borrow_le (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hacc⟩ := hc
  unfold St.acct
  exact acct_borrow_le s.accts who s.borrowState.index (fun a ha => (hacc a ha).2)

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hbs, hbb, hacc⟩ := hc
  have hsup_rec : ∀ who, (s.acct who).supplierIndex ≤ s.supplyState.index := fun who =>
    acct_supply_le s.accts who s.supplyState.index (fun a ha => (hacc a ha).1)
  have hbor_rec : ∀ who, (s.acct who).borrowerIndex ≤ s.borrowState.index := fun who =>
    acct_borrow_le s.accts who s.borrowState.index (fun a ha => (hacc a ha).2)
  cases c with
  | supplyHook who =>
    have hstart : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      apply accrualStart_le_index
      calc (s.acct who).supplierIndex ≤ s.supplyState.index := hsup_rec who
        _ ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
          accrueSide_index_ge s.supplyState s.blockNumber (totalSupply s)
    have hu := updateSupply_eq s hbs
    have hd := distributeSupply_eq
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who (by
        simpa [St.acct] using hstart)
    unfold comptroller
    simp [hu, hd]
  | borrowHook who =>
    have hstart : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      apply accrualStart_le_index
      calc (s.acct who).borrowerIndex ≤ s.borrowState.index := hbor_rec who
        _ ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
          accrueSide_index_ge s.borrowState s.blockNumber (totalBorrows s)
    have hu := updateBorrow_eq s hbb
    have hd := distributeBorrow_eq
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who (by
        simpa [St.acct] using hstart)
    unfold comptroller
    simp [hu, hd]
  | claim who =>
    have hstart_b : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      apply accrualStart_le_index
      calc (s.acct who).borrowerIndex ≤ s.borrowState.index := hbor_rec who
        _ ≤ _ := accrueSide_index_ge _ _ _
    have hstart_s : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      apply accrualStart_le_index
      calc (s.acct who).supplierIndex ≤ s.supplyState.index := hsup_rec who
        _ ≤ _ := accrueSide_index_ge _ _ _
    have hu1 := updateBorrow_eq s hbb
    have hd1 := distributeBorrow_eq
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who (by
        simpa [St.acct] using hstart_b)
    have hm1d_sup_blk : ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
        { a with
          borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).supplyState.block ≤
      ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
        { a with
          borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).blockNumber := by
      simp [hbs]
    have hm1d_sup_rec : ((({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
        { a with
          borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).acct who).supplierIndex ≤
      ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
        { a with
          borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).supplyState.index := by
      have h1 : ((({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
          { a with
            borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).acct who).supplierIndex =
        (s.acct who).supplierIndex := by
        simp only [St.acct]
        exact getD_modify_preserve_supplier _ _ _ (fun a => rfl)
      have h2 : ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
          { a with
            borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).supplyState.index =
        s.supplyState.index := by simp
      rw [h1, h2]; exact hsup_rec who
    have hstart_s2 : accrualStart
        ((({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
          { a with
            borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).acct who).supplierIndex)
        (accrueSide
          ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
          ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
            { a with
              borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
              accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).supplyState
          ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
          ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
            { a with
              borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
              accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).blockNumber
          (totalSupply
            ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
            ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
              { a with
                borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }))).index ≤
        (accrueSide
          ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
          ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
            { a with
              borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
              accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).supplyState
          ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
          ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
            { a with
              borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
              accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).blockNumber
          (totalSupply
            ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
            ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
              { a with
                borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
                accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }))).index := by
      apply accrualStart_le_index
      calc ((({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
          { a with
            borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).acct who).supplierIndex ≤
        ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
          { a with
            borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).supplyState.index := hm1d_sup_rec
        _ ≤ _ := accrueSide_index_ge _ _ _
    have hu2 := updateSupply_eq
      ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
        { a with
          borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } })
      hm1d_sup_blk
    have hd2 := distributeSupply_eq
      ({ ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
      ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
        { a with
          borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } })
      with supplyState := accrueSide
        ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
          { a with
            borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).supplyState
        ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
          { a with
            borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } }).blockNumber
        (totalSupply
          ({ { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with accts :=
          ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).accts.modify who fun a =>
            { a with
              borrowerIndex := ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index,
              accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index) ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState.index } })) }) who (by
        simpa [St.acct] using hstart_s2)
    unfold comptroller claimComp
    simp [hu1, hd1, hu2, hd2]
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed
    by_cases hs : s.supplyState.speed ≠ a
    · have hu := updateSupply_eq s hbs
      simp [hs, hu]
      by_cases hb : s.borrowState.speed ≠ b
      · have hmid_blk : ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).borrowState.block ≤
            ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).blockNumber := by
          simp [hbb]
        have hu2 := updateBorrow_eq
          { s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } hmid_blk
        have hbmid : ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).borrowState.speed ≠ b := by
          simp [hb]
        simp [hbmid, hu2]
      · have hbmid : ¬ ({ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }).borrowState.speed ≠ b := by
          simp [hb]
        simp [hbmid]
    · simp [hs]
      by_cases hb : s.borrowState.speed ≠ b
      · have hu2 := updateBorrow_eq s hbb
        simp [hb, hu2]
      · simp [hb]
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
