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

theorem subChecked_some {a b d : Nat} : subChecked a b = some d ↔ b ≤ a ∧ d = a - b := by
  unfold subChecked
  by_cases h : b ≤ a
  · simp [h]
    omega
  · simp [h]

theorem subChecked_isSome {a b : Nat} : (subChecked a b).isSome = decide (b ≤ a) := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

theorem subChecked_eq_some (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_eq_none (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem Side_block_self (sd : Side) : ({ sd with block := sd.block } = sd) := by
  cases sd with
  | mk idx blk spd => rfl

theorem St_supply_self (s : St) : ({ s with supplyState := s.supplyState } = s) := by
  cases s with
  | mk b sup bor res accts => rfl

theorem St_borrow_self (s : St) : ({ s with borrowState := s.borrowState } = s) := by
  cases s with
  | mk b sup bor res accts => rfl

theorem modify_congr_at (l : List Acct) (n : Nat) (f g : Acct → Acct)
    (h : f (l.getD n noAcct) = g (l.getD n noAcct)) :
    l.modify n f = l.modify n g := by
  induction l generalizing n with
  | nil =>
    simp [List.modify_nil]
  | cons x xs ih =>
    cases n with
    | zero =>
      have hx : f x = g x := h
      simp [hx]
    | succ n =>
      simp
      have h2 : f (xs.getD n noAcct) = g (xs.getD n noAcct) := by
        have : (x :: xs).getD (n + 1) noAcct = xs.getD n noAcct := rfl
        rw [this] at h
        exact h
      rw [ih n h2]

theorem St_modify_congr (s : St) (who : Account) (f g : Acct → Acct)
    (h : f (s.accts.getD who noAcct) = g (s.accts.getD who noAcct)) :
    ({ s with accts := s.accts.modify who f } = { s with accts := s.accts.modify who g }) := by
  rw [modify_congr_at _ _ _ _ h]

theorem accrualStart_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h1 : recorded = 0 <;> by_cases h2 : compInitialIndex ≤ index <;> simp [h1, h2]

theorem mulDouble_eq_creditFor (units start index : Nat) (h : start ≤ index) :
    mulDouble units (index - start) = creditFor units start index := by
  unfold mulDouble creditFor; rfl

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem accrueSide_index_le_succ (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total <;> simp [h]

theorem St_borrow_block_self (s : St) (h : s.blockNumber = s.borrowState.block) :
    ({ s with borrowState := { s.borrowState with block := s.blockNumber } } = s) := by
  cases s with
  | mk b sup bor res accts =>
    cases bor with
    | mk idx blk spd =>
      dsimp only at h
      simp [h]

theorem St_supply_block_self (s : St) (h : s.blockNumber = s.supplyState.block) :
    ({ s with supplyState := { s.supplyState with block := s.blockNumber } } = s) := by
  cases s with
  | mk b sup bor res accts =>
    cases sup with
    | mk idx blk spd =>
      dsimp only at h
      simp [h]

theorem updateSupply_some_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide fraction
  have hd : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    subChecked_eq_some _ _ h
  rw [hd]
  dsimp only
  by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · by_cases h3 : 0 < totalSupply s
    · have hc : (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := ⟨h1.1, h1.2, h3⟩
      simp [h1, hc]
    · have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by omega
      simp [h1, h3, Nat.add_zero]
  · by_cases h2 : s.blockNumber - s.supplyState.block > 0
    · have hspeed : ¬ 0 < s.supplyState.speed := by omega
      have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := by omega
      simp [h2, hspeed]
    · have hblock : s.blockNumber = s.supplyState.block := by omega
      have hc : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := by omega
      simp [h2]
      rw [St_supply_block_self _ hblock]

theorem updateSupply_none_of_gt (s : St) (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex
  rw [subChecked_eq_none _ _ h]

theorem updateBorrow_some_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide fraction
  have hd : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    subChecked_eq_some _ _ h
  rw [hd]
  dsimp only
  by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · by_cases h3 : 0 < totalBorrows s
    · have hc : (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := ⟨h1.1, h1.2, h3⟩
      simp [h1, hc]
    · have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by omega
      simp [h1, h3, Nat.add_zero]
  · by_cases h2 : s.blockNumber - s.borrowState.block > 0
    · have hspeed : ¬ 0 < s.borrowState.speed := by omega
      have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := by omega
      simp [h2, hspeed]
    · have hblock : s.blockNumber = s.borrowState.block := by omega
      have hc : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := by omega
      simp [h2]
      rw [St_borrow_block_self _ hblock]

theorem updateBorrow_none_of_gt (s : St) (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex
  rw [subChecked_eq_none _ _ h]

theorem distributeSupply_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp; dsimp only
  have he : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index := accrualStart_eq _ _
  rw [he]
  have hd : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) :=
    subChecked_eq_some _ _ h
  rw [hd]
  dsimp only
  simp only [St.withAcct]
  congr 1
  apply St_modify_congr
  simp only [St.acct]
  have hcred : mulDouble (((s.accts.getD who noAcct).supply))
      (s.supplyState.index - accrualStart (((s.accts.getD who noAcct).supplierIndex)) s.supplyState.index) =
      creditFor (((s.accts.getD who noAcct).supply))
        (accrualStart (((s.accts.getD who noAcct).supplierIndex)) s.supplyState.index) s.supplyState.index := rfl
  rw [hcred]

theorem distributeSupply_none (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = none := by
  unfold distributeSupplierComp; dsimp only
  have he : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index := accrualStart_eq _ _
  rw [he, subChecked_eq_none _ _ h]

theorem distributeBorrow_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp; dsimp only
  have he : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index := accrualStart_eq _ _
  rw [he]
  have hd : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) :=
    subChecked_eq_some _ _ h
  rw [hd]
  dsimp only
  simp only [St.withAcct]
  congr 1
  apply St_modify_congr
  simp only [St.acct]
  have hcred : mulDouble (((s.accts.getD who noAcct).borrow))
      (s.borrowState.index - accrualStart (((s.accts.getD who noAcct).borrowerIndex)) s.borrowState.index) =
      creditFor (((s.accts.getD who noAcct).borrow))
        (accrualStart (((s.accts.getD who noAcct).borrowerIndex)) s.borrowState.index) s.borrowState.index := rfl
  rw [hcred]

theorem distributeBorrow_none (s : St) (who : Account)
    (h : ¬ accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp; dsimp only
  have he : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index := accrualStart_eq _ _
  rw [he, subChecked_eq_none _ _ h]

theorem accrualStart_le (r I : Nat) (h : r ≤ I) : accrualStart r I ≤ I := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
    by_cases h2 : compInitialIndex ≤ I <;> simp [h2]
  · simp [hr, h]

theorem getD_all (P : Acct → Prop) (l : List Acct) (n : Nat) (d : Acct)
    (hall : ∀ a ∈ l, P a) (hd : P d) : P (l.getD n d) := by
  induction l generalizing n with
  | nil =>
    simp at *
    exact hd
  | cons x xs ih =>
    cases n with
    | zero =>
      simp
      exact hall x (by simp)
    | succ n =>
      simp
      apply ih
      intro a ha
      exact hall a (by simp [ha])

theorem acct_supply_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  have hP : ∀ a ∈ s.accts, (a.supplierIndex ≤ s.supplyState.index) := by
    intro a ha
    have := hall a ha
    exact this.1
  have hd : (noAcct.supplierIndex ≤ s.supplyState.index) := by
    simp [noAcct]
  unfold St.acct
  exact getD_all (fun a => a.supplierIndex ≤ s.supplyState.index) s.accts who noAcct hP hd

theorem acct_borrow_le (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨_, _, hall⟩ := hc
  have hP : ∀ a ∈ s.accts, (a.borrowerIndex ≤ s.borrowState.index) := by
    intro a ha
    have := hall a ha
    exact this.2
  have hd : (noAcct.borrowerIndex ≤ s.borrowState.index) := by
    simp [noAcct]
  unfold St.acct
  exact getD_all (fun a => a.borrowerIndex ≤ s.borrowState.index) s.accts who noAcct hP hd

theorem supply_start_le (s : St) (who : Account) (hc : Consistent s)
    (t : St) (ht : t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) :
    accrualStart (t.acct who).supplierIndex t.supplyState.index ≤ t.supplyState.index := by
  have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index := acct_supply_le s who hc
  have hmono : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_index_le_succ _ _ _
  have hle : (s.acct who).supplierIndex ≤ t.supplyState.index := by
    rw [ht]
    simp
    exact Nat.le_trans hrec hmono
  have htacct : (t.acct who).supplierIndex = (s.acct who).supplierIndex := by
    rw [ht]
    rfl
  rw [htacct]
  exact accrualStart_le _ _ hle

theorem borrow_start_le (s : St) (who : Account) (hc : Consistent s)
    (t : St) (ht : t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) :
    accrualStart (t.acct who).borrowerIndex t.borrowState.index ≤ t.borrowState.index := by
  have hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index := acct_borrow_le s who hc
  have hmono : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    accrueSide_index_le_succ _ _ _
  have hle : (s.acct who).borrowerIndex ≤ t.borrowState.index := by
    rw [ht]
    simp
    exact Nat.le_trans hrec hmono
  have htacct : (t.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
    rw [ht]
    rfl
  rw [htacct]
  exact accrualStart_le _ _ hle

theorem updateSupply_presCons (s t : St) (hc : Consistent s)
    (h : updateCompSupplyIndex s = some t) : Consistent t := by
  have hsup : s.supplyState.block ≤ s.blockNumber := hc.1
  have hupd := updateSupply_some_of_le s hsup
  have ht : t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    (Option.some_inj.mp (hupd.symm.trans h)).symm
  rw [ht]
  unfold Consistent
  refine ⟨?_, ?_, ?_⟩
  · simp [accrueSide_block]
  · exact hc.2.1
  · intro a ha
    have hall := hc.2.2 a ha
    refine ⟨?_, hall.2⟩
    exact Nat.le_trans hall.1 (accrueSide_index_le_succ _ _ _)

theorem updateBorrow_presCons (s t : St) (hc : Consistent s)
    (h : updateCompBorrowIndex s = some t) : Consistent t := by
  have hbor : s.borrowState.block ≤ s.blockNumber := hc.2.1
  have hupd := updateBorrow_some_of_le s hbor
  have ht : t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    (Option.some_inj.mp (hupd.symm.trans h)).symm
  rw [ht]
  unfold Consistent
  refine ⟨?_, ?_, ?_⟩
  · exact hc.1
  · simp [accrueSide_block]
  · intro a ha
    have hall := hc.2.2 a ha
    refine ⟨hall.1, ?_⟩
    exact Nat.le_trans hall.2 (accrueSide_index_le_succ _ _ _)

theorem mem_modify_all (P : Acct → Prop) (l : List Acct) (n : Nat) (f : Acct → Acct)
    (hall : ∀ a ∈ l, P a) (hf : P (f (l.getD n noAcct))) : ∀ a ∈ l.modify n f, P a := by
  induction l generalizing n with
  | nil =>
    intro a ha
    simp [List.modify_nil] at ha
  | cons x xs ih =>
    cases n with
    | zero =>
      intro a ha
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        have : (x :: xs).getD 0 noAcct = x := rfl
        rw [this] at hf
        exact hf
      | inr hmem =>
        exact hall a (by simp [hmem])
    | succ n =>
      intro a ha
      simp at ha
      cases ha with
      | inl heq =>
        rw [heq]
        exact hall x (by simp)
      | inr hmem =>
        have hall_tail : ∀ b ∈ xs, P b := by
          intro b hb
          exact hall b (by simp [hb])
        have hf_tail : P (f (xs.getD n noAcct)) := by
          have : (x :: xs).getD (n + 1) noAcct = xs.getD n noAcct := rfl
          rw [this] at hf
          exact hf
        exact ih n hall_tail hf_tail a hmem

theorem distributeSupply_presCons (s t : St) (who : Account) (hc : Consistent s)
    (h : distributeSupplierComp s who = some t) : Consistent t := by
  by_cases hstart : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · have hsome := distributeSupply_some s who hstart
    have ht : t = { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                   accrued := a.accrued + creditFor a.supply
                     (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } :=
      (Option.some_inj.mp (hsome.symm.trans h)).symm
    rw [ht]
    unfold Consistent
    refine ⟨?_, ?_, ?_⟩
    · exact hc.1
    · exact hc.2.1
    · apply mem_modify_all _ _ _ _ hc.2.2 _
      simp
      have hbor : ((s.accts.getD who noAcct).borrowerIndex ≤ s.borrowState.index) := by
        have := acct_borrow_le s who hc
        unfold St.acct at this
        exact this
      exact hbor
  · have hnone := distributeSupply_none s who hstart
    rw [hnone] at h
    simp at h

theorem setSupply_presCons (s t : St) (a : Nat) (hc : Consistent s)
    (h : setSupplySpeed s a = some t) : Consistent t := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    rw [h]
    exact hc
  · have hsup : s.supplyState.block ≤ s.blockNumber := hc.1
    have hupd := updateSupply_some_of_le s hsup
    have hcU : Consistent _ := updateSupply_presCons s _ hc hupd
    simp [heq, hupd] at h
    rw [h]
    exact hcU

theorem setBorrow_presCons (s t : St) (b : Nat) (hc : Consistent s)
    (h : setBorrowSpeed s b = some t) : Consistent t := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    rw [h]
    exact hc
  · have hbor : s.borrowState.block ≤ s.blockNumber := hc.2.1
    have hupd := updateBorrow_some_of_le s hbor
    have hcU : Consistent _ := updateBorrow_presCons s _ hc hupd
    simp [heq, hupd] at h
    rw [h]
    exact hcU

theorem distributeBorrow_presCons (s t : St) (who : Account) (hc : Consistent s)
    (h : distributeBorrowerComp s who = some t) : Consistent t := by
  by_cases hstart : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · have hsome := distributeBorrow_some s who hstart
    have ht : t = { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                   accrued := a.accrued + creditFor a.borrow
                     (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } :=
      (Option.some_inj.mp (hsome.symm.trans h)).symm
    rw [ht]
    unfold Consistent
    refine ⟨?_, ?_, ?_⟩
    · exact hc.1
    · exact hc.2.1
    · apply mem_modify_all _ _ _ _ hc.2.2 _
      simp
      have hsup : ((s.accts.getD who noAcct).supplierIndex ≤ s.supplyState.index) := by
        have := acct_supply_le s who hc
        unfold St.acct at this
        exact this
      exact hsup
  · have hnone := distributeBorrow_none s who hstart
    rw [hnone] at h
    simp at h

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  have hsup : s.supplyState.block ≤ s.blockNumber := hc.1
  have hbor : s.borrowState.block ≤ s.blockNumber := hc.2.1
  cases c with
  | supplyHook who =>
    unfold comptroller
    have hupd := updateSupply_some_of_le s hsup
    have hstart := supply_start_le s who hc
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } rfl
    have hdist := distributeSupply_some _ who hstart
    simp [hupd, hdist]
  | borrowHook who =>
    unfold comptroller
    have hupd := updateBorrow_some_of_le s hbor
    have hstart := borrow_start_le s who hc
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } rfl
    have hdist := distributeBorrow_some _ who hstart
    simp [hupd, hdist]
  | claim who =>
    unfold comptroller claimComp
    have hupdB := updateBorrow_some_of_le s hbor
    have hcB : Consistent _ := updateBorrow_presCons s _ hc hupdB
    have hstartB := borrow_start_le s who hc _ rfl
    have hdistB := distributeBorrow_some _ who hstartB
    have hcB2 : Consistent _ := distributeBorrow_presCons _ _ who hcB hdistB
    have hsup2 := hcB2.1
    have hupdS := updateSupply_some_of_le _ hsup2
    have hcS : Consistent _ := updateSupply_presCons _ _ hcB2 hupdS
    have hstartS := supply_start_le _ who hcB2 _ rfl
    have hdistS := distributeSupply_some _ who hstartS
    simp [hupdB, hdistB, hupdS, hdistS]
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal
    have hsupS : ∃ t, setSupplySpeed s a = some t := by
      unfold setSupplySpeed
      by_cases hseq : s.supplyState.speed = a
      · exact ⟨s, by simp [hseq]⟩
      · have hupd := updateSupply_some_of_le s hsup
        exact ⟨_, by simp [hseq, hupd]⟩
    obtain ⟨tS, hsetS⟩ := hsupS
    have hcS : Consistent tS := setSupply_presCons s tS a hc hsetS
    have hborS : tS.borrowState.block ≤ tS.blockNumber := hcS.2.1
    have hsetB : ∃ t, setBorrowSpeed tS b = some t := by
      unfold setBorrowSpeed
      by_cases hbeq : tS.borrowState.speed = b
      · exact ⟨tS, by simp [hbeq]⟩
      · have hupd := updateBorrow_some_of_le tS hborS
        exact ⟨_, by simp [hbeq, hupd]⟩
    obtain ⟨tB, hsetB⟩ := hsetB
    simp [hsetS, hsetB]

theorem req_supply_hook : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook : BorrowHookEffects comptroller := sorry
theorem req_claim : ClaimEffects comptroller := sorry
theorem req_set_speeds : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
