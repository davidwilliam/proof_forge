import CompRewards.Spec
namespace CompRewards

def fraction (a b : Nat) : Nat := a * doubleScale / b

def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

def updateCompSupplyIndex (s : St) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    if 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed then
      some { s with supplyState :=
        { s.supplyState with index := s.supplyState.index +
          (if 0 < totalSupply s then fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s) else 0),
          block := s.blockNumber } }
    else if 0 < s.blockNumber - s.supplyState.block then
      some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s
  else none

def updateCompBorrowIndex (s : St) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    if 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed then
      some { s with borrowState :=
        { s.borrowState with index := s.borrowState.index +
          (if 0 < totalBorrows s then fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s) else 0),
          block := s.blockNumber } }
    else if 0 < s.blockNumber - s.borrowState.block then
      some { s with borrowState := { s.borrowState with block := s.blockNumber } }
    else some s
  else none

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

theorem subChecked_some {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem startSupply_eq (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) =
      accrualStart rec idx := by
  unfold accrualStart; by_cases h1 : rec = 0 <;> simp [h1]
  by_cases h2 : compInitialIndex ≤ idx <;> simp [h2] at *
  · exact h2
  · exact h2

theorem startBorrow_eq (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) =
      accrualStart rec idx :=
  startSupply_eq rec idx

theorem grant_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct; by_cases h : (s.accts.getD who noAcct).accrued > 0 ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve <;> simp [h]

theorem updateSupply_ok (s s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ∧
    s1.blockNumber = s.blockNumber ∧ s1.borrowState = s.borrowState ∧
    s1.reserve = s.reserve ∧ s1.accts = s.accts := by
  unfold updateCompSupplyIndex at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · rw [if_pos hb] at h
    by_cases hpos : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
    · rw [if_pos hpos] at h
      have heqs := Option.some_inj.mp h
      have hI : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
        rw [← heqs]; unfold accrueSide fraction
        have hc1 : 0 < s.blockNumber - s.supplyState.block := hpos.left
        have hc2 : 0 < s.supplyState.speed := hpos.right
        by_cases ht : 0 < totalSupply s
        · simp [hc1, hc2, ht]
        · simp [hc1, hc2, ht] at *
          have : totalSupply s = 0 := by omega
          simp [this]
      have heq2 : s1.blockNumber = s.blockNumber /\ s1.borrowState = s.borrowState /\
          s1.reserve = s.reserve /\ s1.accts = s.accts := by
        rw [← heqs]
      exact ⟨hb, hI, heq2.1, heq2.2.1, heq2.2.2.1, heq2.2.2.2⟩
    · rw [if_neg hpos] at h
      by_cases hd : 0 < s.blockNumber - s.supplyState.block
      · rw [if_pos hd] at h
        have heqs := Option.some_inj.mp h
        have hI : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
          rw [← heqs]; unfold accrueSide
          have hc1 : 0 < s.blockNumber - s.supplyState.block := hd
          simp [hc1, hpos]
        have heq2 : s1.blockNumber = s.blockNumber /\ s1.borrowState = s.borrowState /\
            s1.reserve = s.reserve /\ s1.accts = s.accts := by
          rw [← heqs]
        exact ⟨hb, hI, heq2.1, heq2.2.1, heq2.2.2.1, heq2.2.2.2⟩
      · rw [if_neg hd] at h
        have heq : s.blockNumber - s.supplyState.block = 0 := by omega
        have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) = s.supplyState := by
          unfold accrueSide; simp [heq]
          have : s.blockNumber = s.supplyState.block := by omega
          simp [this]
        have heqs : s = s1 := Option.some_inj.mp h
        have hI : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
          rw [← heqs, hacc]
        have heq2 : s1.blockNumber = s.blockNumber /\ s1.borrowState = s.borrowState /\
            s1.reserve = s.reserve /\ s1.accts = s.accts := by
          rw [← heqs]
        exact ⟨hb, hI, heq2.1, heq2.2.1, heq2.2.2.1, heq2.2.2.2⟩
  · rw [if_neg hb] at h
    cases h

theorem updateBorrow_ok (s s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ∧
    s1.blockNumber = s.blockNumber ∧ s1.supplyState = s.supplyState ∧
    s1.reserve = s.reserve ∧ s1.accts = s.accts := by
  unfold updateCompBorrowIndex at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · rw [if_pos hb] at h
    by_cases hpos : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
    · rw [if_pos hpos] at h
      have heqs := Option.some_inj.mp h
      have hI : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
        rw [← heqs]; unfold accrueSide fraction
        have hc1 : 0 < s.blockNumber - s.borrowState.block := hpos.left
        have hc2 : 0 < s.borrowState.speed := hpos.right
        by_cases ht : 0 < totalBorrows s
        · simp [hc1, hc2, ht]
        · simp [hc1, hc2, ht] at *
          have : totalBorrows s = 0 := by omega
          simp [this]
      have heq2 : s1.blockNumber = s.blockNumber /\ s1.supplyState = s.supplyState /\
          s1.reserve = s.reserve /\ s1.accts = s.accts := by
        rw [← heqs]
      exact ⟨hb, hI, heq2.1, heq2.2.1, heq2.2.2.1, heq2.2.2.2⟩
    · rw [if_neg hpos] at h
      by_cases hd : 0 < s.blockNumber - s.borrowState.block
      · rw [if_pos hd] at h
        have heqs := Option.some_inj.mp h
        have hI : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
          rw [← heqs]; unfold accrueSide
          have hc1 : 0 < s.blockNumber - s.borrowState.block := hd
          simp [hc1, hpos]
        have heq2 : s1.blockNumber = s.blockNumber /\ s1.supplyState = s.supplyState /\
            s1.reserve = s.reserve /\ s1.accts = s.accts := by
          rw [← heqs]
        exact ⟨hb, hI, heq2.1, heq2.2.1, heq2.2.2.1, heq2.2.2.2⟩
      · rw [if_neg hd] at h
        have heq : s.blockNumber - s.borrowState.block = 0 := by omega
        have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) = s.borrowState := by
          unfold accrueSide; simp [heq]
          have : s.blockNumber = s.borrowState.block := by omega
          simp [this]
        have heqs : s = s1 := Option.some_inj.mp h
        have hI : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
          rw [← heqs, hacc]
        have heq2 : s1.blockNumber = s.blockNumber /\ s1.supplyState = s.supplyState /\
            s1.reserve = s.reserve /\ s1.accts = s.accts := by
          rw [← heqs]
        exact ⟨hb, hI, heq2.1, heq2.2.1, heq2.2.2.1, heq2.2.2.2⟩
  · rw [if_neg hb] at h
    cases h

theorem modify_congr_getD (l : List Acct) (i : Nat) (f1 f2 : Acct → Acct)
    (h : f1 (l.getD i noAcct) = f2 (l.getD i noAcct)) : l.modify i f1 = l.modify i f2 := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ n => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      simp at h
      show f1 x :: xs = f2 x :: xs
      rw [h]
    | succ n =>
      simp at h
      show x :: xs.modify n f1 = x :: xs.modify n f2
      rw [ih n h]

theorem distribSupply_ok (s s' : St) (who : Nat) (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp at h
  have heq : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    startSupply_eq _ _
  rw [heq] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · have hs : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
        some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
      subChecked_some hle
    rw [hs] at h
    simp only at h
    have h' := Option.some_inj.mp h
    refine ⟨hle, ?_⟩
    rw [← h']
    unfold St.withAcct
    congr 1
    apply modify_congr_getD
    show (⟨(s.accts.getD who noAcct).supply, (s.accts.getD who noAcct).borrow,
      s.supplyState.index, (s.accts.getD who noAcct).borrowerIndex,
      (s.accts.getD who noAcct).accrued + mulDouble (s.accts.getD who noAcct).supply
        (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index),
      (s.accts.getD who noAcct).wallet⟩ : Acct) =
      (⟨(s.accts.getD who noAcct).supply, (s.accts.getD who noAcct).borrow,
      s.supplyState.index, (s.accts.getD who noAcct).borrowerIndex,
      (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).supply
        (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) s.supplyState.index,
      (s.accts.getD who noAcct).wallet⟩ : Acct)
    have hacc : s.accts.getD who noAcct = s.acct who := rfl
    rw [hacc]
    rfl
  · have hs : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none :=
      subChecked_none hle
    simp only [hs] at h
    cases h

theorem distribBorrow_ok (s s' : St) (who : Nat) (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp at h
  have heq : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    startSupply_eq _ _
  rw [heq] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · have hs : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
        some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
      subChecked_some hle
    rw [hs] at h
    simp only at h
    have h' := Option.some_inj.mp h
    refine ⟨hle, ?_⟩
    rw [← h']
    unfold St.withAcct
    congr 1
    apply modify_congr_getD
    show (⟨(s.accts.getD who noAcct).supply, (s.accts.getD who noAcct).borrow,
      (s.accts.getD who noAcct).supplierIndex, s.borrowState.index,
      (s.accts.getD who noAcct).accrued + mulDouble (s.accts.getD who noAcct).borrow
        (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index),
      (s.accts.getD who noAcct).wallet⟩ : Acct) =
      (⟨(s.accts.getD who noAcct).supply, (s.accts.getD who noAcct).borrow,
      (s.accts.getD who noAcct).supplierIndex, s.borrowState.index,
      (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).borrow
        (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index,
      (s.accts.getD who noAcct).wallet⟩ : Acct)
    have hacc : s.accts.getD who noAcct = s.acct who := rfl
    rw [hacc]
    rfl
  · have hs : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none :=
      subChecked_none hle
    simp only [hs] at h
    cases h

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases h1 : updateCompSupplyIndex s with
  | none => simp [h1] at h
  | some s1 =>
    simp [h1] at h
    obtain ⟨hb, hs1eq, hbn, hbor, hres, haccts⟩ := updateSupply_ok s s1 h1
    obtain ⟨hle, hs'eq⟩ := distribSupply_ok s1 s' who h
    have hI : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hs1eq]
    have hac : s1.acct who = s.acct who := by
      unfold St.acct; rw [haccts]
    have hle2 : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [← hI, ← hac]; exact hle
    refine ⟨hb, hle2, ?_⟩
    rw [hs'eq, haccts, hI, hs1eq]

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases h1 : updateCompBorrowIndex s with
  | none => simp [h1] at h
  | some s1 =>
    simp [h1] at h
    obtain ⟨hb, hs1eq, hbn, hsup, hres, haccts⟩ := updateBorrow_ok s s1 h1
    obtain ⟨hle, hs'eq⟩ := distribBorrow_ok s1 s' who h
    have hI : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hs1eq]
    have hac : s1.acct who = s.acct who := by
      unfold St.acct; rw [haccts]
    have hle2 : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [← hI, ← hac]; exact hle
    refine ⟨hb, hle2, ?_⟩
    rw [hs'eq, haccts, hI, hs1eq]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  cases hb1 : updateCompBorrowIndex s with
  | none => simp [hb1] at h
  | some t1 =>
    simp [hb1] at h
    cases hd1 : distributeBorrowerComp t1 who with
    | none => simp [hd1] at h
    | some m1 =>
      simp [hd1] at h
      cases hs1 : updateCompSupplyIndex m1 with
      | none => simp [hs1] at h
      | some t2 =>
        simp [hs1] at h
        cases hd2 : distributeSupplierComp t2 who with
        | none => simp [hd2] at h
        | some m2 =>
          simp [hd2] at h
          have heq : grantCompInternal m2 who = s' := h
          obtain ⟨hbb, ht1eq, hbn1, hsup1, hres1, hac1⟩ := updateBorrow_ok s t1 hb1
          obtain ⟨hle1, hm1eq⟩ := distribBorrow_ok t1 m1 who hd1
          obtain ⟨hbs, ht2eq, hbn2, hbor2, hres2, hac2⟩ := updateSupply_ok m1 t2 hs1
          obtain ⟨hle2, hm2eq⟩ := distribSupply_ok t2 m2 who hd2
          have hIbor : t1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
            rw [ht1eq]
          have hacbor : t1.acct who = s.acct who := by unfold St.acct; rw [hac1]
          have hIsup : t2.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by
            rw [ht2eq]
          have hacsup : t2.acct who = m1.acct who := by unfold St.acct; rw [hac2]
          have htotBor : totalBorrows t1 = totalBorrows s := by unfold totalBorrows; rw [hac1]
          have htotSup : totalSupply t2 = totalSupply m1 := by unfold totalSupply; rw [hac2]
          refine ⟨m1, m2, ?_, ?_, ?_⟩
          · refine ⟨hbb, ?_, ?_⟩
            · rw [← hIbor, ← hacbor]; exact hle1
            · rw [hm1eq, hac1, hIbor, ht1eq]
          · refine ⟨hbs, ?_, ?_⟩
            · rw [← hIsup, ← hacsup]; exact hle2
            · rw [hm2eq, hac2, hIsup, ht2eq]
          · rw [← heq, grant_eq]

theorem req_calls_succeed : CallsSucceed comptroller := sorry
theorem req_set_speeds : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
