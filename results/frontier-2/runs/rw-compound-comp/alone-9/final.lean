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

theorem sub_some {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem sub_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem sub_checked_eq (a b : Nat) : subChecked a b =
    if b ≤ a then some (a - b) else none := by
  unfold subChecked; rfl

theorem supStart_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · by_cases h1 : compInitialIndex ≤ s.supplyState.index <;> simp [h0, h1]
  · simp [h0]

theorem borStart_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · by_cases h1 : compInitialIndex ≤ s.borrowState.index <;> simp [h0, h1]
  · simp [h0]

theorem accrualStart_le_index (r idx : Nat) (h : r ≤ idx ∨ r = 0) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ idx <;> simp [hi] <;> omega
  · simp [hr]; omega

theorem accrualStart_le_succ (r oldIdx newIdx : Nat) (hle : oldIdx ≤ newIdx)
    (h : r ≤ oldIdx ∨ r = 0) : accrualStart r newIdx ≤ newIdx := by
  apply accrualStart_le_index; by_cases hr : r = 0
  · exact Or.inr hr
  · exact Or.inl (by omega)

theorem sub_some_inv {a b d : Nat} (h : subChecked a b = some d) :
    b ≤ a ∧ d = a - b := by
  unfold subChecked at h
  by_cases hb : b ≤ a
  · simp [hb] at h
    exact ⟨hb, h.symm⟩
  · simp [hb] at h

theorem sub_none_inv {a b : Nat} (h : subChecked a b = none) : ¬ b ≤ a := by
  intro hb
  have hs := sub_some hb
  rw [hs] at h
  contradiction

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide; by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide; by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem updateSupply_ok (s s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  cases hsub : subChecked s.blockNumber s.supplyState.block with
  | none =>
    have hn := sub_none_inv hsub
    simp [hsub] at h
  | some d =>
    have ⟨hle, hd⟩ := sub_some_inv hsub
    simp only [hsub] at h
    subst hd
    by_cases hc : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · simp only [hc] at h
      by_cases ht : totalSupply s > 0
      · simp only [ht] at h
        have heq := Option.some_inj.mp h
        subst heq
        refine ⟨hle, ?_⟩
        congr 1
        unfold accrueSide fraction
        have e1 : 0 < s.blockNumber - s.supplyState.block := by omega
        have e2 : 0 < s.supplyState.speed := by omega
        have e3 : 0 < totalSupply s := by omega
        simp [e1, e2, e3]
      · simp only [ht] at h
        have ht0 : totalSupply s = 0 := by omega
        have heq := Option.some_inj.mp h
        subst heq
        refine ⟨hle, ?_⟩
        congr 1
        unfold accrueSide fraction
        have e1 : 0 < s.blockNumber - s.supplyState.block := by omega
        have e2 : 0 < s.supplyState.speed := by omega
        simp [e1, e2, ht0]
    · simp [hc] at h
      by_cases hd0 : s.blockNumber - s.supplyState.block > 0
      · simp [hd0] at h
        subst h
        refine ⟨hle, ?_⟩
        congr 1
        unfold accrueSide
        have e : ¬ (0 < s.blockNumber - s.supplyState.block ∧
            0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
          simp at hc ⊢; omega
        simp [e]
      · simp [hd0] at h
        subst h
        have hbeq : s.supplyState.block = s.blockNumber := by omega
        refine ⟨hle, ?_⟩
        have e : ¬ (0 < s.blockNumber - s.supplyState.block ∧
            0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
        have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) =
            s.supplyState := by
          unfold accrueSide
          simp [e, ←hbeq]
        rw [hacc]

theorem updateBorrow_ok (s s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  cases hsub : subChecked s.blockNumber s.borrowState.block with
  | none =>
    have hn := sub_none_inv hsub
    simp [hsub] at h
  | some d =>
    have ⟨hle, hd⟩ := sub_some_inv hsub
    simp only [hsub] at h
    subst hd
    by_cases hc : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · simp only [hc] at h
      by_cases ht : totalBorrows s > 0
      · simp only [ht] at h
        have heq := Option.some_inj.mp h
        subst heq
        refine ⟨hle, ?_⟩
        congr 1
        unfold accrueSide fraction
        have e1 : 0 < s.blockNumber - s.borrowState.block := by omega
        have e2 : 0 < s.borrowState.speed := by omega
        have e3 : 0 < totalBorrows s := by omega
        simp [e1, e2, e3]
      · simp only [ht] at h
        have ht0 : totalBorrows s = 0 := by omega
        have heq := Option.some_inj.mp h
        subst heq
        refine ⟨hle, ?_⟩
        congr 1
        unfold accrueSide fraction
        have e1 : 0 < s.blockNumber - s.borrowState.block := by omega
        have e2 : 0 < s.borrowState.speed := by omega
        simp [e1, e2, ht0]
    · simp [hc] at h
      by_cases hd0 : s.blockNumber - s.borrowState.block > 0
      · simp [hd0] at h
        subst h
        refine ⟨hle, ?_⟩
        congr 1
        unfold accrueSide
        have e : ¬ (0 < s.blockNumber - s.borrowState.block ∧
            0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
          simp at hc ⊢; omega
        simp [e]
      · simp [hd0] at h
        subst h
        have hbeq : s.borrowState.block = s.blockNumber := by omega
        refine ⟨hle, ?_⟩
        have e : ¬ (0 < s.blockNumber - s.borrowState.block ∧
            0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
        have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
            s.borrowState := by
          unfold accrueSide
          simp [e, ←hbeq]
        rw [hacc]

def supF (s : St) (who : Nat) (d : Nat) (a : Acct) : Acct :=
  { a with supplierIndex := s.supplyState.index,
           accrued := a.accrued + mulDouble (s.acct who).supply d }

def supG (s : St) (a : Acct) : Acct :=
  { a with supplierIndex := s.supplyState.index,
           accrued := a.accrued + creditFor a.supply
             (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }

def borF (s : St) (who : Nat) (d : Nat) (a : Acct) : Acct :=
  { a with borrowerIndex := s.borrowState.index,
           accrued := a.accrued + mulDouble (s.acct who).borrow d }

def borG (s : St) (a : Acct) : Acct :=
  { a with borrowerIndex := s.borrowState.index,
           accrued := a.accrued + creditFor a.borrow
             (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }

theorem modify_target_eq (l : List Acct) (who : Nat) (f g : Acct -> Acct)
    (h : who < l.length -> f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil =>
    cases who <;> rfl
  | cons x xs ih =>
    cases who with
    | zero =>
      simp at h ⊢
      simp [h]
    | succ n =>
      simp at h ⊢
      apply ih
      intro hlt
      apply h
      simp [hlt]

theorem distributeSupply_ok (s s' : St) (who : Account)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who (supG s) } := by
  unfold distributeSupplierComp at h
  simp only at h
  have hstart : (if (s.acct who).supplierIndex = 0 ∧
      compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    supStart_eq s who
  rw [hstart] at h
  cases hsub : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none =>
    simp [hsub] at h
  | some d =>
    have ⟨hle, hd⟩ := sub_some_inv hsub
    simp only [hsub] at h
    simp only [Option.some_inj] at h
    subst h
    refine ⟨hle, ?_⟩
    have hfg : s.accts.modify who (supF s who d) = s.accts.modify who (supG s) := by
      apply modify_target_eq
      intro hlt
      show supF s who d (s.accts.getD who noAcct) = supG s (s.accts.getD who noAcct)
      have hget : s.accts.getD who noAcct = s.acct who := rfl
      rw [hget]
      unfold supF supG
      congr 1
      unfold mulDouble creditFor
      rw [hd]
    unfold St.withAcct
    change { s with accts := s.accts.modify who (supF s who d) } = _
    rw [hfg]

theorem distributeBorrow_ok (s s' : St) (who : Account)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who (borG s) } := by
  unfold distributeBorrowerComp at h
  simp only at h
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧
      compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    borStart_eq s who
  rw [hstart] at h
  cases hsub : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none =>
    simp [hsub] at h
  | some d =>
    have ⟨hle, hd⟩ := sub_some_inv hsub
    simp only [hsub] at h
    simp only [Option.some_inj] at h
    subst h
    refine ⟨hle, ?_⟩
    have hfg : s.accts.modify who (borF s who d) = s.accts.modify who (borG s) := by
      apply modify_target_eq
      intro hlt
      show borF s who d (s.accts.getD who noAcct) = borG s (s.accts.getD who noAcct)
      have hget : s.accts.getD who noAcct = s.acct who := rfl
      rw [hget]
      unfold borF borG
      congr 1
      unfold mulDouble creditFor
      rw [hd]
    unfold St.withAcct
    change { s with accts := s.accts.modify who (borF s who d) } = _
    rw [hfg]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hu : updateCompSupplyIndex s with
  | none =>
    simp [hu] at h
  | some s1 =>
    simp [hu] at h
    obtain ⟨hble, hs1eq⟩ := updateSupply_ok s s1 hu
    obtain ⟨hstart_le, hsprime⟩ := distributeSupply_ok s1 s' who h
    refine ⟨hble, ?_, ?_⟩
    · have hacct : s1.acct who = s.acct who := by
        rw [hs1eq]; rfl
      have hidx : s1.supplyState.index =
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        rw [hs1eq]
      rw [hacct, hidx] at hstart_le
      exact hstart_le
    · rw [hs1eq] at hsprime
      unfold supG at hsprime
      simp at hsprime
      exact hsprime

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hu : updateCompBorrowIndex s with
  | none =>
    simp [hu] at h
  | some s1 =>
    simp [hu] at h
    obtain ⟨hble, hs1eq⟩ := updateBorrow_ok s s1 hu
    obtain ⟨hstart_le, hsprime⟩ := distributeBorrow_ok s1 s' who h
    refine ⟨hble, ?_, ?_⟩
    · have hacct : s1.acct who = s.acct who := by
        rw [hs1eq]; rfl
      have hidx : s1.borrowState.index =
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        rw [hs1eq]
      rw [hacct, hidx] at hstart_le
      exact hstart_le
    · rw [hs1eq] at hsprime
      unfold borG at hsprime
      simp at hsprime
      exact hsprime

def grantF (s : St) (who : Account) (a : Acct) : Acct :=
  { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }

def grantG (a : Acct) : Acct :=
  { a with accrued := 0, wallet := a.wallet + a.accrued }

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [h]
    have hfg : s.accts.modify who (grantF s who) =
        s.accts.modify who grantG := by
      apply modify_target_eq
      intro hlt
      rfl
    unfold grantF grantG at hfg
    simp [hfg]
  · have hneg : ¬ (0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve) := by
      simp at h ⊢
      omega
    simp [h, hneg]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  cases hb1 : updateCompBorrowIndex s with
  | none =>
    simp [hb1] at h
  | some b1 =>
    simp [hb1] at h
    cases hb2 : distributeBorrowerComp b1 who with
    | none =>
      simp [hb2] at h
    | some m1 =>
      simp [hb2] at h
      cases hs1 : updateCompSupplyIndex m1 with
      | none =>
        simp [hs1] at h
      | some t1 =>
        simp [hs1] at h
        cases hs2 : distributeSupplierComp t1 who with
        | none =>
          simp [hs2] at h
        | some m2 =>
          simp [hs2] at h
          have heq : s' = grantCompInternal m2 who := by
            simp [h]
          rw [heq, grant_eq]
          obtain ⟨hble_b, hb1eq⟩ := updateBorrow_ok s b1 hb1
          obtain ⟨hstart_b, hm1eq⟩ := distributeBorrow_ok b1 m1 who hb2
          obtain ⟨hble_s, ht1eq⟩ := updateSupply_ok m1 t1 hs1
          obtain ⟨hstart_s, hm2eq⟩ := distributeSupply_ok t1 m2 who hs2
          refine ⟨m1, m2, ?_, ?_, rfl⟩
          · refine ⟨hble_b, ?_, ?_⟩
            · have hacct : b1.acct who = s.acct who := by
                rw [hb1eq]; rfl
              have hidx : b1.borrowState.index =
                  (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
                rw [hb1eq]
              rw [hacct, hidx] at hstart_b
              exact hstart_b
            · rw [hb1eq] at hm1eq
              unfold borG at hm1eq
              simp at hm1eq
              exact hm1eq
          · refine ⟨?_, ?_, ?_⟩
            · have h1 := (updateSupply_ok m1 t1 hs1).1
              exact h1
            · have hacct : t1.acct who = m1.acct who := by
                have h1 := (updateSupply_ok m1 t1 hs1).2
                rw [h1]; rfl
              have hidx : t1.supplyState.index =
                  (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
                have h1 := (updateSupply_ok m1 t1 hs1).2
                rw [h1]
              rw [hacct, hidx] at hstart_s
              exact hstart_s
            · have h1 := (updateSupply_ok m1 t1 hs1).2
              rw [h1] at hm2eq
              unfold supG at hm2eq
              simp at hm2eq
              exact hm2eq

theorem setSupply_ok (s s' : St) (a : Nat) (h : setSupplySpeed s a = some s') :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s' = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed ≠ a
  · simp [heq] at h
    cases hu : updateCompSupplyIndex s with
    | none =>
      simp [hu] at h
    | some s1 =>
      simp [hu] at h
      obtain ⟨hble, hs1eq⟩ := updateSupply_ok s s1 hu
      subst h
      refine ⟨fun _ => hble, ?_⟩
      rw [hs1eq]
      by_cases heq3 : s.supplyState.speed = a
      · simp [heq, heq3] at *
      · simp [heq3]
  · simp [heq] at h
    subst h
    refine ⟨fun hne => absurd hne heq, ?_⟩
    have heq3 : s.supplyState.speed = a := by
      simp at heq ⊢
      omega
    simp [heq3]

theorem setBorrow_ok (s s' : St) (b : Nat) (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s' = { s with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed ≠ b
  · simp [heq] at h
    cases hu : updateCompBorrowIndex s with
    | none =>
      simp [hu] at h
    | some s1 =>
      simp [hu] at h
      obtain ⟨hble, hs1eq⟩ := updateBorrow_ok s s1 hu
      subst h
      refine ⟨fun _ => hble, ?_⟩
      rw [hs1eq]
      by_cases heq3 : s.borrowState.speed = b
      · simp [heq, heq3] at *
      · simp [heq3]
  · simp [heq] at h
    subst h
    refine ⟨fun hne => absurd hne heq, ?_⟩
    have heq3 : s.borrowState.speed = b := by
      simp at heq ⊢
      omega
    simp [heq3]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller, setCompSpeedInternal] at h
  cases hs : setSupplySpeed s a with
  | none =>
    simp [hs] at h
  | some s1 =>
    simp [hs] at h
    obtain ⟨hble_s, hs1eq⟩ := setSupply_ok s s1 a hs
    obtain ⟨hble_b, hsprime⟩ := setBorrow_ok s1 s' b h
    refine ⟨?_, ?_, ?_⟩
    · intro hne
      exact hble_s hne
    · intro hne
      have h1 : s1.borrowState = s.borrowState := by
        rw [hs1eq]
      have h2 : s1.blockNumber = s.blockNumber := by
        rw [hs1eq]
      rw [h1, h2] at hble_b
      exact hble_b hne
    · rw [hs1eq] at hsprime
      exact hsprime

theorem updateSupply_eq_some (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex
  rw [sub_some hle]
  by_cases hc : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · have hc' : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0 := hc
    simp only [hc']
    by_cases ht : totalSupply s > 0
    · simp only [ht]
      congr 1
      unfold accrueSide fraction
      have e1 : 0 < s.blockNumber - s.supplyState.block := by omega
      have e2 : 0 < s.supplyState.speed := by omega
      have e3 : 0 < totalSupply s := by omega
      simp [e1, e2, e3]
    · simp only [ht]
      have ht0 : totalSupply s = 0 := by omega
      congr 1
      unfold accrueSide fraction
      have e1 : 0 < s.blockNumber - s.supplyState.block := by omega
      have e2 : 0 < s.supplyState.speed := by omega
      simp [e1, e2, ht0]
  · simp only [hc]
    by_cases hd0 : s.blockNumber - s.supplyState.block > 0
    · simp only [hd0]
      congr 1
      unfold accrueSide
      have e : ¬ (0 < s.blockNumber - s.supplyState.block ∧
          0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        simp at hc ⊢
        omega
      simp [e]
    · simp only [hd0]
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      congr 1
      have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) =
          s.supplyState := by
        unfold accrueSide
        have e : ¬ (0 < s.blockNumber - s.supplyState.block ∧
            0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
        simp [e, ←hbeq]
      simp [hacc, hbeq]

theorem updateBorrow_eq_some (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex
  rw [sub_some hle]
  by_cases hc : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [hc]
    by_cases ht : totalBorrows s > 0
    · simp only [ht]
      congr 1
      unfold accrueSide fraction
      have e1 : 0 < s.blockNumber - s.borrowState.block := by omega
      have e2 : 0 < s.borrowState.speed := by omega
      have e3 : 0 < totalBorrows s := by omega
      simp [e1, e2, e3]
    · simp only [ht]
      have ht0 : totalBorrows s = 0 := by omega
      congr 1
      unfold accrueSide fraction
      have e1 : 0 < s.blockNumber - s.borrowState.block := by omega
      have e2 : 0 < s.borrowState.speed := by omega
      simp [e1, e2, ht0]
  · simp only [hc]
    by_cases hd0 : s.blockNumber - s.borrowState.block > 0
    · simp only [hd0]
      congr 1
      unfold accrueSide
      have e : ¬ (0 < s.blockNumber - s.borrowState.block ∧
          0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        simp at hc ⊢
        omega
      simp [e]
    · simp only [hd0]
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      congr 1
      have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
          s.borrowState := by
        unfold accrueSide
        have e : ¬ (0 < s.blockNumber - s.borrowState.block ∧
            0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
        simp [e, ←hbeq]
      simp [hacc, hbeq]

theorem distributeSupply_eq_some (s : St) (who : Account)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who (supG s) } := by
  unfold distributeSupplierComp
  simp only
  have hstart : (if (s.acct who).supplierIndex = 0 ∧
      compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    supStart_eq s who
  rw [hstart, sub_some hle]
  simp only
  congr 1
  unfold St.withAcct
  congr 1
  apply modify_target_eq
  intro hlt
  show supF s who (s.supplyState.index -
    accrualStart (s.acct who).supplierIndex s.supplyState.index)
    (s.accts.getD who noAcct) = supG s (s.accts.getD who noAcct)
  have hget : s.accts.getD who noAcct = s.acct who := rfl
  rw [hget]
  unfold supF supG mulDouble creditFor
  rfl

theorem distributeBorrow_eq_some (s : St) (who : Account)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who (borG s) } := by
  unfold distributeBorrowerComp
  simp only
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧
      compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    borStart_eq s who
  rw [hstart, sub_some hle]
  simp only
  congr 1
  unfold St.withAcct
  congr 1
  apply modify_target_eq
  intro hlt
  show borF s who (s.borrowState.index -
    accrualStart (s.acct who).borrowerIndex s.borrowState.index)
    (s.accts.getD who noAcct) = borG s (s.accts.getD who noAcct)
  have hget : s.accts.getD who noAcct = s.acct who := rfl
  rw [hget]
  unfold borF borG mulDouble creditFor
  rfl

theorem setSupply_eq_some (s : St) (a : Nat)
    (hle : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) :
    setSupplySpeed s a = some { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed ≠ a
  · simp [heq, updateSupply_eq_some s (hle heq)]
  · have heq2 : s.supplyState.speed = a := by
      simp at heq ⊢
      omega
    simp [heq, heq2]

theorem setBorrow_eq_some (s : St) (b : Nat)
    (hle : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :
    setBorrowSpeed s b = some { s with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed
  by_cases heq : s.borrowState.speed ≠ b
  · simp [heq, updateBorrow_eq_some s (hle heq)]
  · have heq2 : s.borrowState.speed = b := by
      simp at heq ⊢
      omega
    simp [heq, heq2]

theorem getD_mem_of_lt (l : List Acct) (who : Nat) (d : Acct) (hlt : who < l.length) :
    l.getD who d ∈ l := by
  induction l generalizing who with
  | nil =>
    exact absurd hlt (Nat.not_lt_zero who)
  | cons x xs ih =>
    cases who with
    | zero =>
      exact List.mem_cons_self
    | succ n =>
      simp at hlt ⊢
      exact Or.inr (ih n hlt)

theorem acct_mem_or_zero (s : St) (who : Account) (hmem : ∀ a ∈ s.accts,
    a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∨ (s.acct who).supplierIndex = 0 := by
  by_cases hlt : who < s.accts.length
  · have hmemd : s.accts.getD who noAcct ∈ s.accts :=
      getD_mem_of_lt s.accts who noAcct hlt
    have h1 := (hmem _ hmemd).1
    have heq : s.acct who = s.accts.getD who noAcct := rfl
    rw [←heq] at h1
    exact Or.inl h1
  · have heq : s.acct who = noAcct := by
      unfold St.acct
      simp [hlt]
    rw [heq]
    exact Or.inr rfl

theorem acct_mem_or_zero_b (s : St) (who : Account) (hmem : ∀ a ∈ s.accts,
    a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index ∨ (s.acct who).borrowerIndex = 0 := by
  by_cases hlt : who < s.accts.length
  · have hmemd : s.accts.getD who noAcct ∈ s.accts :=
      getD_mem_of_lt s.accts who noAcct hlt
    have h1 := (hmem _ hmemd).2
    have heq : s.acct who = s.accts.getD who noAcct := rfl
    rw [←heq] at h1
    exact Or.inl h1
  · have heq : s.acct who = noAcct := by
      unfold St.acct
      simp [hlt]
    rw [heq]
    exact Or.inr rfl

theorem upgrade_consistent (L : Legacy) (h : L.WellFormed) :
    Consistent (upgrade L) := by
  unfold Legacy.WellFormed at h
  obtain ⟨hs0, hsle, hb0, hble, hsup_bl, hbor_bl, hmem⟩ := h
  unfold Consistent upgrade initSide
  refine ⟨?_, ?_, ?_⟩
  · by_cases hs : L.supplyIndex = 0
    · simp [hs]
    · simp [hs]
      omega
  · by_cases hb : L.borrowIndex = 0
    · simp [hb]
    · simp [hb]
      omega
  · intro a ha
    have hm := hmem a ha
    obtain ⟨hsle_a, hble_a⟩ := hm
    constructor
    · by_cases hs : L.supplyIndex = 0
      · have hrec0 : a.supplierIndex = 0 := by omega
        simp [hs, hrec0]
      · simp [hs]
        exact hsle_a
    · by_cases hb : L.borrowIndex = 0
      · have hrec0 : a.borrowerIndex = 0 := by omega
        simp [hb, hrec0]
      · simp [hb]
        exact hble_a

theorem mem_modify (l : List Acct) (who : Nat) (f : Acct -> Acct) (d : Acct) (a : Acct)
    (hm : a ∈ l.modify who f) : a = f (l.getD who d) ∨ a ∈ l := by
  induction l generalizing who with
  | nil =>
    simp at hm
  | cons x xs ih =>
    cases who with
    | zero =>
      simp at hm ⊢
      cases hm with
      | inl heq =>
        exact Or.inl heq
      | inr hm2 =>
        exact Or.inr (Or.inr hm2)
    | succ n =>
      simp at hm ⊢
      cases hm with
      | inl heq =>
        exact Or.inr (Or.inl heq)
      | inr hm2 =>
        have ih2 := ih n hm2
        cases ih2 with
        | inl heq2 =>
          exact Or.inl heq2
        | inr hm3 =>
          exact Or.inr (Or.inr hm3)

theorem supplyDist_consistent (s s' : St) (who : Account)
    (hc : Consistent s) (h : SupplyDistributed s who s') : Consistent s' := by
  obtain ⟨hble_sup, hble_bor, hmem⟩ := hc
  obtain ⟨hbl, hst, heq⟩ := h
  have hge : s.supplyState.index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_index_ge _ _ _
  have hblk : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block =
      s.blockNumber := accrueSide_block _ _ _
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · simp [hblk]
  · simp
    exact hble_bor
  · intro a ha
    have hmem_mod := mem_modify s.accts who
      (supG { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
      noAcct a ha
    cases hmem_mod with
    | inl heq2 =>
      constructor
      · rw [heq2]
        exact Nat.le_refl _
      · rw [heq2]
        by_cases hlt : who < s.accts.length
        · have hmemd : s.accts.getD who noAcct ∈ s.accts :=
            getD_mem_of_lt s.accts who noAcct hlt
          exact (hmem _ hmemd).2
        · have heq_get : s.accts.getD who noAcct = noAcct := by
            simp [hlt]
          have : (supG
              { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
              (s.accts.getD who noAcct)).borrowerIndex = 0 := by
            rw [heq_get]
            rfl
          rw [this]
          exact Nat.zero_le _
    | inr hmem2 =>
      have h1 := hmem _ hmem2
      obtain ⟨hsle, hble⟩ := h1
      constructor
      · simp
        omega
      · simp
        exact hble

theorem borrowDist_consistent (s s' : St) (who : Account)
    (hc : Consistent s) (h : BorrowDistributed s who s') : Consistent s' := by
  obtain ⟨hble_sup, hble_bor, hmem⟩ := hc
  obtain ⟨hbl, hst, heq⟩ := h
  have hge : s.borrowState.index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    accrueSide_index_ge _ _ _
  have hblk : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block =
      s.blockNumber := accrueSide_block _ _ _
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · simp
    exact hble_sup
  · simp [hblk]
  · intro a ha
    have hmem_mod := mem_modify s.accts who
      (borG { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
      noAcct a ha
    cases hmem_mod with
    | inl heq2 =>
      have hget : s.accts.getD who noAcct = s.acct who := rfl
      rw [hget] at heq2
      constructor
      · simp [heq2]
        by_cases hlt : who < s.accts.length
        · have hmemd : s.accts.getD who noAcct ∈ s.accts :=
            getD_mem_of_lt s.accts who noAcct hlt
          have h1 := (hmem _ hmemd).1
          have heq3 : s.acct who = s.accts.getD who noAcct := rfl
          rw [←heq3] at h1
          exact h1
        · have heq3 : s.acct who = noAcct := by
            unfold St.acct
            simp [hlt]
          simp [heq3, borG, noAcct]
      · simp [heq2, borG]
    | inr hmem2 =>
      have h1 := hmem _ hmem2
      obtain ⟨hsle, hble⟩ := h1
      constructor
      · simp
        exact hsle
      · simp
        omega

theorem grant_preserves (s : St) (who : Account) (hc : Consistent s) :
    Consistent (grant s who) := by
  obtain ⟨hble_sup, hble_bor, hmem⟩ := hc
  unfold grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp [h]
    refine ⟨?_, ?_, ?_⟩
    · simp
      exact hble_sup
    · simp
      exact hble_bor
    · intro a ha
      have hmem_mod := mem_modify s.accts who grantG noAcct a ha
      cases hmem_mod with
      | inl heq2 =>
        have hget : s.accts.getD who noAcct = s.acct who := rfl
        rw [hget] at heq2
        have h1 : (s.acct who).supplierIndex ≤ s.supplyState.index ∨
            (s.acct who).supplierIndex = 0 :=
          acct_mem_or_zero s who hmem
        have h2 : (s.acct who).borrowerIndex ≤ s.borrowState.index ∨
            (s.acct who).borrowerIndex = 0 :=
          acct_mem_or_zero_b s who hmem
        constructor
        · simp [heq2, grantG]
          cases h1 with
          | inl hle =>
            exact hle
          | inr heq0 =>
            simp [heq0]
        · simp [heq2, grantG]
          cases h2 with
          | inl hle =>
            exact hle
          | inr heq0 =>
            simp [heq0]
      | inr hmem2 =>
        have h1 := hmem _ hmem2
        obtain ⟨hsle, hble⟩ := h1
        constructor
        · simp
          exact hsle
        · simp
          exact hble
  · simp [h]
    exact ⟨hble_sup, hble_bor, hmem⟩

theorem claim_preserves (s s' : St) (who : Account)
    (hc : Consistent s) (h : Claimed s who s') : Consistent s' := by
  obtain ⟨m1, m2, hb, hs, heq⟩ := h
  have hc1 : Consistent m1 := borrowDist_consistent s m1 who hc hb
  have hc2 : Consistent m2 := supplyDist_consistent m1 m2 who hc1 hs
  rw [heq]
  exact grant_preserves m2 who hc2

theorem speedsSet_preserves (s s' : St) (sup bor : Nat)
    (hc : Consistent s) (h : SpeedsSet s sup bor s') : Consistent s' := by
  obtain ⟨hble_sup, hble_bor, hmem⟩ := hc
  obtain ⟨hbl_sup, hbl_bor, heq⟩ := h
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · by_cases heq_s : s.supplyState.speed = sup
    · simp [heq_s]
      exact hble_sup
    · simp [heq_s, accrueSide_block]
  · by_cases heq_b : s.borrowState.speed = bor
    · simp [heq_b]
      exact hble_bor
    · simp [heq_b, accrueSide_block]
  · intro a ha
    have h1 := hmem _ ha
    obtain ⟨hsle, hble⟩ := h1
    have hge_sup : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrueSide_index_ge _ _ _
    have hge_bor : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    constructor
    · by_cases heq_s : s.supplyState.speed = sup
      · simp [heq_s]
        exact hsle
      · simp [heq_s]
        omega
    · by_cases heq_b : s.borrowState.speed = bor
      · simp [heq_b]
        exact hble
      · simp [heq_b]
        omega

theorem withAcct_supply_preserves (s : St) (who : Nat) (f : Acct -> Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex ∧ (f a).borrowerIndex = a.borrowerIndex)
    (hc : Consistent s) : Consistent (s.withAcct who f) := by
  obtain ⟨hble_sup, hble_bor, hmem⟩ := hc
  unfold Consistent St.withAcct
  refine ⟨?_, ?_, ?_⟩
  · simp
    exact hble_sup
  · simp
    exact hble_bor
  · intro a ha
    have hmem_mod := mem_modify s.accts who f noAcct a ha
    cases hmem_mod with
    | inl heq2 =>
      have hf2 := hf (s.accts.getD who noAcct)
      by_cases hlt : who < s.accts.length
      · have hmemd : s.accts.getD who noAcct ∈ s.accts :=
          getD_mem_of_lt s.accts who noAcct hlt
        have h1 := hmem _ hmemd
        obtain ⟨hsle_d, hble_d⟩ := h1
        constructor
        · simp only [heq2, hf2.1] at ⊢
          exact hsle_d
        · simp only [heq2, hf2.2] at ⊢
          exact hble_d
      · have heq3 : s.accts.getD who noAcct = noAcct := by
          simp [hlt]
        have ha0_sup : a.supplierIndex = 0 := by
          rw [heq2, heq3]
          simp [hf, noAcct]
        have ha0_bor : a.borrowerIndex = 0 := by
          rw [heq2, heq3]
          simp [hf, noAcct]
        constructor
        · rw [ha0_sup]
          exact Nat.zero_le _
        · rw [ha0_bor]
          exact Nat.zero_le _
    | inr hmem2 =>
      have h1 := hmem _ hmem2
      obtain ⟨hsle, hble⟩ := h1
      constructor
      · simp
        exact hsle
      · simp
        exact hble

theorem exec_preserves (s : St) (op : Op) (hc : Consistent s) :
    Consistent (exec comptroller s op) := by
  cases op with
  | mint who x =>
    unfold exec
    by_cases hlt : who < s.accts.length
    · simp [hlt]
      cases hu : comptroller s (.supplyHook who) with
      | none =>
        simp [hu]
        exact hc
      | some s1 =>
        simp [hu]
        have hsd := req_supply_hook s who s1 hu
        have hc1 := supplyDist_consistent s s1 who hc hsd
        have hsup : ∀ a : Acct, (fun a : Acct => ({ a with supply := a.supply + x } : Acct)) a =
            ({ a with supply := a.supply + x } : Acct) := fun _ => rfl
        sorry
    | _ =>
      sorry
  | _ =>
    sorry

theorem req_calls_succeed : CallsSucceed comptroller := sorry
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
