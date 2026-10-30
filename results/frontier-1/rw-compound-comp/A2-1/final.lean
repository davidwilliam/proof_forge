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

def fooTest : Nat := 1

theorem fooTest2 : 1 = 1 := rfl

theorem subChecked_isSome_test : (subChecked 5 3).isSome = true := rfl

theorem subChecked_ok_test (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]

theorem subChecked_none_test (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked
  simp [h]

theorem updSupply_eq_test (s : St) :
  updateCompSupplyIndex s =
  match subChecked s.blockNumber s.supplyState.block with
  | none => none
  | some d => if d > 0 ∧ s.supplyState.speed > 0 then
      let r := if totalSupply s > 0 then (d * s.supplyState.speed) * doubleScale / totalSupply s else 0
      some { s with supplyState := { s.supplyState with index := s.supplyState.index + r, block := s.blockNumber } }
    else if d > 0 then some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s := by
  unfold updateCompSupplyIndex fraction
  rfl

theorem req_borrow_hook_tmp : True := trivial

theorem borrow_update_eq_aux2 (s : St) (d : Nat) (h : subChecked s.blockNumber s.borrowState.block = some d) :
  d = s.blockNumber - s.borrowState.block ∧ s.borrowState.block ≤ s.blockNumber := by
  unfold subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp [hle] at h
    constructor
    · rw [h]
    · exact hle
  · simp [hle] at h

theorem updSup_block_le2 (s : St) (s1 : St)
  (h : updateCompSupplyIndex s = some s1) : s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem subChecked_some_inv (a b d : Nat) (h : subChecked a b = some d) :
  b ≤ a ∧ d = a - b := by
  unfold subChecked at h
  by_cases hle : b ≤ a
  · simp [hle] at h
    exact ⟨hle, h.symm⟩
  · simp [hle] at h

def testLem : Nat := doubleScale
#check totalSupply
#check St.credited
#check accrueSide
#check accrualStart

theorem tmpLen (l : List Acct) (n : Nat) (f : Acct → Acct) : (l.modify n f).length = l.length := by
  simp

def myTest2 : Nat := doubleScale
#check St
#check totalSupply
#check run
#check emitted
#check speedsAfter
#check upgrade
#check NoPosition
#check St.creditedTo

def myTest3 : Nat := 1

def nb_pendingSupply (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) / doubleScale

def nb_test1 : Nat := 1

def scale : Nat := doubleScale

def potSup (s : St) (who : Account) : Nat :=
  (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)

def potBor (s : St) (who : Account) : Nat :=
  (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)

def unSup (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).supply then (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale else 0

def unBor (s : St) (who : Account) : Nat :=
  if 0 < (s.acct who).borrow then (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale else 0

def pot (s : St) (who : Account) : Nat :=
  (s.creditedTo who) * doubleScale + potSup s who + potBor s who + unSup s who + unBor s who

def potTest : Nat := 1

def probeLemmas : Nat := 42

def chkModify1 : Nat := 1
#check List.modify
#check List.getD
#check St.acct
#check St.withAcct
#check totalSupply
#check totalBorrows
#check St.creditedTo
#check accrueSide
#check accrualStart
#check creditFor
#check grant
#check run
#check exec

def chkModify2 : Nat := 2

def arch0_pendingAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def arch0_totalPot (s : St) : Nat :=
  s.credited * doubleScale +
  (s.accts.map (arch0_pendingAcct s)).sum +
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale

def arch0_Inv (s : St) : Prop :=
  Consistent s

theorem arch0_updSupply_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by sorry

theorem arch0_updBorrow_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem arch0_distSupply_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by sorry

theorem arch0_distBorrow_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by sorry







theorem arch0_setSpeeds_some (s : St) (a b : Nat) (h : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome := by sorry

theorem arch0_supply_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') : SupplyDistributed s who s' := by sorry

theorem arch0_borrow_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') : BorrowDistributed s who s' := by sorry

theorem arch0_claim_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') : Claimed s who s' := by sorry

theorem arch0_setSpeeds_effect (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') : SpeedsSet s a b s' := by sorry

theorem arch0_inv_upgrade (L : Legacy) (h : L.WellFormed) :
    arch0_Inv (upgrade L) := by sorry

theorem arch0_inv_exec (s : St) (op : Op) (h : arch0_Inv s) :
    arch0_Inv (exec comptroller s op) := by sorry

theorem arch0_inv_run (s : St) (ops : List Op) (h : arch0_Inv s) :
    arch0_Inv (run comptroller s ops) := by sorry

theorem arch0_speeds_exec (s : St) (op : Op) :
    ((exec comptroller s op).supplyState.speed, (exec comptroller s op).borrowState.speed) =
      nextSpeeds (s.supplyState.speed, s.borrowState.speed) op := by sorry

theorem arch0_upgrade_speeds (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by sorry

theorem arch0_speeds_run_upgrade (L : Legacy) (history : List Op) :
    ((run comptroller (upgrade L) history).supplyState.speed,
     (run comptroller (upgrade L) history).borrowState.speed) =
      speedsAfter (L.compSpeed, L.compSpeed) history := by sorry

theorem arch0_totalPot_exec (s : St) (op : Op) (h : arch0_Inv s) :
    arch0_totalPot (exec comptroller s op) ≤
      arch0_totalPot s + emittedBy (s.supplyState.speed, s.borrowState.speed) op * doubleScale := by sorry

theorem arch0_pot_exec (s : St) (op : Op) (who : Account) (h : arch0_Inv s) :
    pot (exec comptroller s op) who ≤
      pot s who + emittedBy (s.supplyState.speed, s.borrowState.speed) op * doubleScale := by sorry

theorem arch0_totalPot_run (s : St) (ops : List Op) (h : arch0_Inv s) :
    arch0_totalPot (run comptroller s ops) ≤
      arch0_totalPot s + emitted (s.supplyState.speed, s.borrowState.speed) ops * doubleScale := by sorry

theorem arch0_pot_run (s : St) (ops : List Op) (who : Account) (h : arch0_Inv s) :
    pot (run comptroller s ops) who ≤
      pot s who + emitted (s.supplyState.speed, s.borrowState.speed) ops * doubleScale := by sorry

theorem arch0_totalPot_upgrade (L : Legacy) (h : L.WellFormed) :
    arch0_totalPot (upgrade L) ≤
      (upgrade L).credited * doubleScale +
      (L.accts.map L.pendingScaled).sum +
      (L.unindexedSupply + L.unindexedBorrow) * doubleScale := by sorry

theorem arch0_pot_upgrade (L : Legacy) (who : Account) (h : L.WellFormed) :
    pot (upgrade L) who ≤
      (upgrade L).creditedTo who * doubleScale +
      L.pendingScaled (L.accts.getD who noAcct) +
      ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
       (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) * doubleScale := by sorry

theorem arch0_credited_le_totalPot (s : St) :
    s.credited * doubleScale ≤ arch0_totalPot s := by sorry

theorem arch0_creditedTo_le_pot (s : St) (who : Account) :
    (s.creditedTo who) * doubleScale ≤ pot s who := by sorry

theorem arch0_pot_of_noPosition (s : St) (who : Account) (h : NoPosition s who) :
    pot s who = (s.creditedTo who) * doubleScale := by sorry

theorem arch0_div_bound (c c0 p u e : Nat)
    (h : c * doubleScale ≤ c0 * doubleScale + p + u * doubleScale + e * doubleScale) :
    c ≤ c0 + p / doubleScale + u + e := by sorry

theorem arch0_le_of_mul_le_emitted (c c0 e : Nat)
    (h : c * doubleScale ≤ c0 * doubleScale + e * doubleScale) :
    c ≤ c0 + e := by sorry

theorem probe_bind_eq (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
    Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) := rfl











theorem tmp_getD_unfold (l : List Acct) (n : Nat) : l.getD n noAcct = (l[n]?).getD noAcct := by rfl

theorem tmp_a : ([noAcct].getD 1 noAcct) = noAcct := by rfl

theorem tmp_b (hd : Acct) (tl : List Acct) : ((hd :: tl).getD 0 noAcct) = hd := by rfl

theorem tmp_c (hd : Acct) (tl : List Acct) (n : Nat) : ((hd :: tl).getD (n+1) noAcct) = tl.getD n noAcct := by rfl

theorem tmp_mem1 (hd : Acct) (tl : List Acct) : hd ∈ hd :: tl := by simp

theorem tmp_mem2 (hd a : Acct) (tl : List Acct) (ha : a ∈ tl) : a ∈ hd :: tl := by simp [ha]

theorem plan0_getD_supplierIndex_le (l : List Acct) (idx who : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) :
    (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    show (0 : Nat) ≤ idx
    exact Nat.zero_le idx
  | cons hd tl ih =>
    cases who with
    | zero =>
      have hmem : hd ∈ hd :: tl := tmp_mem1 hd tl
      have hle : hd.supplierIndex ≤ idx := h hd hmem
      have heq : ((hd :: tl).getD 0 noAcct) = hd := rfl
      rw [heq]
      exact hle
    | succ n =>
      have heq : ((hd :: tl).getD (n + 1) noAcct) = tl.getD n noAcct := rfl
      rw [heq]
      exact ih n (fun a ha => h a (tmp_mem2 hd a tl ha))

theorem plan0_accrualStart_le (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr, h]

theorem plan0_updateCompSupplyIndex_step (s : St) (who : Account)
    (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s₁, updateCompSupplyIndex s = some s₁ ∧
      s.supplyState.index ≤ s₁.supplyState.index ∧
      (s₁.acct who).supplierIndex = (s.acct who).supplierIndex := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) :=
    subChecked_ok_test _ _ h
  unfold updateCompSupplyIndex
  rw [hsub]
  simp only
  by_cases hc : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hc]
    refine ⟨_, rfl, ?_, rfl⟩
    show s.supplyState.index ≤ _
    simp only
    apply Nat.le_add_right
  · rw [if_neg hc]
    by_cases hc2 : (s.blockNumber - s.supplyState.block) > 0
    · rw [if_pos hc2]
      exact ⟨_, rfl, Nat.le_refl _, rfl⟩
    · rw [if_neg hc2]
      exact ⟨_, rfl, Nat.le_refl _, rfl⟩

theorem plan0_distributeSupplierComp_isSome (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  have heq : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    unfold accrualStart
    by_cases hr : (s.acct who).supplierIndex = 0 <;> simp [hr]
  have hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) ≤ s.supplyState.index := heq ▸ h
  have hsub := subChecked_ok_test s.supplyState.index
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) hle
  unfold distributeSupplierComp
  simp only [hsub, Option.isSome_some]

theorem plan0_option_bind_isSome {α β : Type} (m : Option α) (f : α → Option β)
    (hm : m.isSome) (hf : ∀ a, m = some a → (f a).isSome) :
    (Option.bind m f).isSome := by
  match m with
  | none => simp at hm
  | some a => exact hf a rfl

theorem arch0_supplyHook_some (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.supplyHook who)).isSome := by
  have hsup : s.supplyState.block ≤ s.blockNumber := h.1
  have hall : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := by
    intro a ha
    exact (h.2.2 a ha).1
  have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index := by
    unfold St.acct
    exact plan0_getD_supplierIndex_le s.accts s.supplyState.index who hall
  obtain ⟨s₁, hs₁eq, hle, hacct⟩ := plan0_updateCompSupplyIndex_step s who hsup
  have hs₁some : (updateCompSupplyIndex s).isSome := by rw [hs₁eq]; rfl
  have hrec1 : (s₁.acct who).supplierIndex ≤ s₁.supplyState.index := by
    rw [hacct]; exact Nat.le_trans hrec hle
  have hacc : accrualStart (s₁.acct who).supplierIndex s₁.supplyState.index ≤ s₁.supplyState.index :=
    plan0_accrualStart_le _ _ hrec1
  have hdist : ∀ a, updateCompSupplyIndex s = some a → (distributeSupplierComp a who).isSome := by
    intro a ha
    have heq : a = s₁ := by
      have h2 : some a = some s₁ := by rw [← ha, hs₁eq]
      cases h2
      rfl
    rw [heq]
    exact plan0_distributeSupplierComp_isSome s₁ who hacc
  have hbind : (Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who)).isSome :=
    plan0_option_bind_isSome _ _ hs₁some hdist
  have heq2 : comptroller s (.supplyHook who) =
    Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) := rfl
  rw [heq2]
  exact hbind

theorem plan0_getD_borrowerIndex_le_aux (idx : Nat) (l : List Acct) (who : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) :
    (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    show (0 : Nat) ≤ idx
    exact Nat.zero_le idx
  | cons hd tl ih =>
    cases who with
    | zero =>
      have hmem : hd ∈ hd :: tl := tmp_mem1 hd tl
      have hle : hd.borrowerIndex ≤ idx := h hd hmem
      have heq : ((hd :: tl).getD 0 noAcct) = hd := rfl
      rw [heq]
      exact hle
    | succ n =>
      have heq : ((hd :: tl).getD (n + 1) noAcct) = tl.getD n noAcct := rfl
      rw [heq]
      exact ih n (fun a ha => h a (tmp_mem2 hd a tl ha))

theorem plan0_updateCompBorrowIndex_step_aux (s : St) (who : Account)
    (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s₁, updateCompBorrowIndex s = some s₁ ∧
      s.borrowState.index ≤ s₁.borrowState.index ∧
      (s₁.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) :=
    subChecked_ok_test _ _ h
  unfold updateCompBorrowIndex
  rw [hsub]
  simp only
  by_cases hc : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hc]
    refine ⟨_, rfl, ?_, rfl⟩
    show s.borrowState.index ≤ _
    simp only
    apply Nat.le_add_right
  · rw [if_neg hc]
    by_cases hc2 : (s.blockNumber - s.borrowState.block) > 0
    · rw [if_pos hc2]
      exact ⟨_, rfl, Nat.le_refl _, rfl⟩
    · rw [if_neg hc2]
      exact ⟨_, rfl, Nat.le_refl _, rfl⟩

theorem plan0_distributeBorrowerComp_isSome_aux (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  have heq : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
    unfold accrualStart
    by_cases hr : (s.acct who).borrowerIndex = 0
    · simp [hr]
    · simp [hr]
  have hle : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) ≤ s.borrowState.index := heq ▸ h
  have hsub := subChecked_ok_test s.borrowState.index
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) hle
  unfold distributeBorrowerComp
  simp only [hsub, Option.isSome_some]

theorem arch0_borrowHook_some (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.borrowHook who)).isSome := by
  have hbor : s.borrowState.block ≤ s.blockNumber := h.2.1
  have hall : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := by
    intro a ha
    exact (h.2.2 a ha).2
  have hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
    unfold St.acct
    exact plan0_getD_borrowerIndex_le_aux s.borrowState.index s.accts who hall
  obtain ⟨s₁, hs₁eq, hle, hacct⟩ := plan0_updateCompBorrowIndex_step_aux s who hbor
  have hs₁some : (updateCompBorrowIndex s).isSome := by rw [hs₁eq]; rfl
  have hrec1 : (s₁.acct who).borrowerIndex ≤ s₁.borrowState.index := by
    rw [hacct]
    exact Nat.le_trans hrec hle
  have hacc : accrualStart (s₁.acct who).borrowerIndex s₁.borrowState.index ≤ s₁.borrowState.index :=
    plan0_accrualStart_le _ _ hrec1
  have hdist : ∀ a, updateCompBorrowIndex s = some a → (distributeBorrowerComp a who).isSome := by
    intro a ha
    have heq : a = s₁ := by
      have h2 : some a = some s₁ := by rw [← ha, hs₁eq]
      cases h2
      rfl
    rw [heq]
    exact plan0_distributeBorrowerComp_isSome_aux s₁ who hacc
  have hbind : (Option.bind (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who)).isSome :=
    plan0_option_bind_isSome _ _ hs₁some hdist
  have heq2 : comptroller s (.borrowHook who) =
    Option.bind (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who) := rfl
  rw [heq2]
  exact hbind

theorem probe_claim_rw (s : St) (who : Account) (sB : St)
  (hsB : updateCompBorrowIndex s = some sB) :
  (Option.bind (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who)) =
  distributeBorrowerComp sB who := by
  rw [hsB]; rfl

theorem probe_option_some_inj {A : Type} (x y : A) (h : some x = some y) : x = y := by
  simpa using h

theorem probe_subst_test (s : St) (s1 : St)
  (h : some s = some s1) : s1.supplyState = s.supplyState := by
  have h2 : s = s1 := probe_option_some_inj s s1 h
  rw [h2]

theorem helper_modify_accts_eq (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).blockNumber = s.blockNumber := by unfold St.withAcct; simp

theorem helper_modify_supply_eq (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).supplyState = s.supplyState := by unfold St.withAcct; simp

theorem helper_modify_borrow_eq (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).borrowState = s.borrowState := by unfold St.withAcct; simp

theorem helper_modify_reserve_eq (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).reserve = s.reserve := by unfold St.withAcct; simp

theorem plan1_borrow_step_preserves_supply (s : St) (who : Account) (h : Consistent s) :
    ∃ s₁, Option.bind (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) = some s₁ ∧
      s₁.supplyState.block ≤ s₁.blockNumber ∧
      (s₁.acct who).supplierIndex ≤ s₁.supplyState.index := by sorry



theorem plan1_claim_isSome_of_steps (s : St) (who : Account) (s₁ s₂ : St)
    (h₁ : Option.bind (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) = some s₁)
    (h₂ : Option.bind (updateCompSupplyIndex s₁) (fun t => distributeSupplierComp t who) = some s₂) :
    (comptroller s (.claim who)).isSome := by sorry

theorem plan1_test_extract (s : St) (who : Account) (h : (Option.bind (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who)).isSome) : ∃ s₁, Option.bind (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) = some s₁ := by
  cases hb : Option.bind (updateCompBorrowIndex s) (fun t => distributeBorrowerComp t who) with
  | some s₁ => exact ⟨s₁, rfl⟩
  | none => simp [hb] at h

theorem plan1_updBorrow_preserves (s sB : St) (h : updateCompBorrowIndex s = some sB) :
    sB.supplyState = s.supplyState ∧ sB.blockNumber = s.blockNumber ∧ sB.accts = s.accts := by
  unfold updateCompBorrowIndex at h
  cases hd : subChecked s.blockNumber s.borrowState.block with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    by_cases hc : d > 0 ∧ s.borrowState.speed > 0
    · simp [hc] at h
      rw [← h]; exact ⟨rfl, rfl, rfl⟩
    · simp [hc] at h
      by_cases hc2 : d > 0
      · simp [hc2] at h
        rw [← h]; exact ⟨rfl, rfl, rfl⟩
      · simp [hc2] at h
        rw [← h]; exact ⟨rfl, rfl, rfl⟩

theorem plan1_bind_inv {A B : Type} (m : Option A) (f : A → Option B) (y : B)
  (h : Option.bind m f = some y) : ∃ x, m = some x ∧ f x = some y := by
  cases hm : m with
  | none => simp [hm] at h
  | some x => exact ⟨x, rfl, by simpa [hm] using h⟩

theorem plan1_dist_preserves_supply2 (s s1 : St) (who : Account)
  (h : distributeBorrowerComp s who = some s1) :
    s1.supplyState = s.supplyState ∧ s1.blockNumber = s.blockNumber := by
  unfold distributeBorrowerComp at h
  simp only at h
  cases hc : subChecked s.borrowState.index
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
  | none => simp [hc] at h
  | some d =>
    simp [hc] at h
    rw [← h]
    exact ⟨by simp [St.withAcct], by simp [St.withAcct]⟩

theorem plan1_probe_get_modify (l : List Acct) (n : Nat) (f : Acct → Acct) (who : Nat) :
    (({ blockNumber := 0, supplyState := ⟨0,0,0⟩, borrowState := ⟨0,0,0⟩, reserve := 0, accts := l.modify n f } : St).acct who).supplierIndex =
    ((l.modify n f).getD who noAcct).supplierIndex := rfl

theorem plan1_probe_modify_nil (f : Acct → Acct) : ([] : List Acct).modify 0 f = [] := rfl

theorem plan1_probe_modify_nil2 (f : Acct → Acct) (n : Nat) : ([] : List Acct).modify (n+1) f = [] := rfl

theorem plan1_supply_step_some (s : St) (who : Account)
    (hblock : s.supplyState.block ≤ s.blockNumber)
    (hidx : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s₂, Option.bind (updateCompSupplyIndex s) (fun t => distributeSupplierComp t who) = some s₂ := by
  obtain ⟨s₁, h_eq, h_le, h_acct⟩ := plan0_updateCompSupplyIndex_step s who hblock
  have h_idx1 : (s₁.acct who).supplierIndex ≤ s₁.supplyState.index := by
    rw [h_acct]
    exact Nat.le_trans hidx h_le
  have h_acc := plan0_accrualStart_le (s₁.acct who).supplierIndex s₁.supplyState.index h_idx1
  have h_some := plan0_distributeSupplierComp_isSome s₁ who h_acc
  have hbind : Option.bind (updateCompSupplyIndex s) (fun t => distributeSupplierComp t who) =
      distributeSupplierComp s₁ who := by
    simp [h_eq]
  rw [hbind]
  cases he : distributeSupplierComp s₁ who with
  | none =>
    simp [he] at h_some
  | some s₂ =>
    exact ⟨s₂, rfl⟩

theorem plan1_claim_isSome_of_steps_auxcheck (s : St) (who : Account) :
    claimComp s who =
    Option.bind (updateCompBorrowIndex s) (fun s1 =>
      Option.bind (distributeBorrowerComp s1 who) (fun s2 =>
        Option.bind (updateCompSupplyIndex s2) (fun s3 =>
          Option.bind (distributeSupplierComp s3 who) (fun s4 =>
            some (grantCompInternal s4 who))))) := rfl

theorem plan1_claim_nested_check (s : St) (who : Account) :
    claimComp s who =
    Option.bind (updateCompBorrowIndex s) (fun s1 =>
      Option.bind (distributeBorrowerComp s1 who) (fun s2 =>
        Option.bind (updateCompSupplyIndex s2) (fun s3 =>
          Option.bind (distributeSupplierComp s3 who) (fun s4 =>
            some (grantCompInternal s4 who))))) := rfl

theorem plan1_bind_some_check (a : St) (f : St → Option St) :
    Option.bind (some a) f = f a := rfl

theorem plan1_probe_opt_lemmas : True := by
  have h1 : ∀ (a : St) (f : St → Option St), (some a).bind f = f a := fun a f => rfl
  trivial

theorem plan1_probe_bind_lemmas2 : True := by
  have h : ∀ (a : Nat) (f : Nat → Option Nat), Option.bind (some a) f = f a := by
    intro a f
    rfl
  trivial

theorem arch0_claim_some (s : St) (who : Account) (h : Consistent s) :
    (comptroller s (.claim who)).isSome := by
  obtain ⟨s₁, h₁, hblock, hidx⟩ := plan1_borrow_step_preserves_supply s who h
  obtain ⟨s₂, h₂⟩ := plan1_supply_step_some s₁ who hblock hidx
  exact plan1_claim_isSome_of_steps s who s₁ s₂ h₁ h₂

theorem updSupply_preserves_borrow2 (s s1 : St)
  (h : updateCompSupplyIndex s = some s1) :
    s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber := by
  unfold updateCompSupplyIndex at h
  cases hd : subChecked s.blockNumber s.supplyState.block with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    by_cases hc : d > 0 ∧ s.supplyState.speed > 0
    · simp [hc] at h
      rw [← h]; exact ⟨rfl, rfl⟩
    · simp [hc] at h
      by_cases hc2 : d > 0
      · simp [hc2] at h
        rw [← h]; exact ⟨rfl, rfl⟩
      · simp [hc2] at h
        rw [← h]; exact ⟨rfl, rfl⟩

theorem updBorrow_preserves_supply2 (s s1 : St)
  (h : updateCompBorrowIndex s = some s1) :
    s1.supplyState = s.supplyState ∧ s1.blockNumber = s.blockNumber := by
  unfold updateCompBorrowIndex at h
  cases hd : subChecked s.blockNumber s.borrowState.block with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    by_cases hc : d > 0 ∧ s.borrowState.speed > 0
    · simp [hc] at h
      rw [← h]; exact ⟨rfl, rfl⟩
    · simp [hc] at h
      by_cases hc2 : d > 0
      · simp [hc2] at h
        rw [← h]; exact ⟨rfl, rfl⟩
      · simp [hc2] at h
        rw [← h]; exact ⟨rfl, rfl⟩

theorem isSome_map_probe (m : Option St) (f : St → St) :
    (Option.map f m).isSome = m.isSome := by
  cases m <;> rfl

#check Option.isSome_map
#check Option.map_eq_some_iff

theorem updSupply_isSome_of_le4 (s : St)
  (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  obtain ⟨s₁, heq, _, _⟩ := plan0_updateCompSupplyIndex_step s 0 h
  rw [heq]; rfl

theorem updBorrow_isSome_of_le4 (s : St)
  (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  obtain ⟨s₁, heq, _, _⟩ := plan0_updateCompBorrowIndex_step_aux s 0 h
  rw [heq]; rfl

theorem setSupply_isSome_of_le4 (s : St) (a : Nat)
  (h : s.supplyState.block ≤ s.blockNumber) :
    (setSupplySpeed s a).isSome = true := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed ≠ a
  · simp only [if_pos heq]
    have h1 := updSupply_isSome_of_le4 s h
    have h2 : ((updateCompSupplyIndex s).map fun s_1 : St =>
      ({ s_1 with supplyState := { s_1.supplyState with speed := a } } : St)).isSome =
      (updateCompSupplyIndex s).isSome := by
      cases updateCompSupplyIndex s <;> rfl
    rw [h2, h1]
  · simp [heq]

theorem setBorrow_isSome_of_le4 (s : St) (b : Nat)
  (h : s.borrowState.block ≤ s.blockNumber) :
    (setBorrowSpeed s b).isSome = true := by
  unfold setBorrowSpeed
  by_cases heq : s.borrowState.speed ≠ b
  · simp only [if_pos heq]
    have h1 := updBorrow_isSome_of_le4 s h
    have h2 : ((updateCompBorrowIndex s).map fun s_1 : St =>
      ({ s_1 with borrowState := { s_1.borrowState with speed := b } } : St)).isSome =
      (updateCompBorrowIndex s).isSome := by
      cases updateCompBorrowIndex s <;> rfl
    rw [h2, h1]
  · simp [heq]

theorem setSupply_preserves_borrow5 (s mid : St) (a : Nat)
  (h : setSupplySpeed s a = some mid) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed ≠ a
  · simp only [if_pos heq] at h
    cases hm : updateCompSupplyIndex s with
    | none =>
      have hnone : ((updateCompSupplyIndex s).map fun s_1 : St =>
        ({ s_1 with supplyState := { s_1.supplyState with speed := a } } : St)) = none := by
        rw [hm]; rfl
      rw [hnone] at h
      simp at h
    | some s1 =>
      have hmid : (({ s1 with supplyState := { s1.supplyState with speed := a } } : St)) = mid := by
        have heq2 : ((updateCompSupplyIndex s).map fun s_1 : St =>
          ({ s_1 with supplyState := { s_1.supplyState with speed := a } } : St)) =
          some (({ s1 with supplyState := { s1.supplyState with speed := a } } : St)) := by
          rw [hm]; rfl
        rw [heq2] at h
        simpa using h
      have hpres := updSupply_preserves_borrow2 s s1 hm
      rw [← hmid]
      simp only
      exact hpres
  · simp only [if_neg heq] at h
    have hsm : s = mid := by simpa using h
    rw [← hsm]
    exact ⟨rfl, rfl⟩

theorem plan2_bind_isSome_true (m : Option St) (f : St → Option St)
    (hm : m.isSome = true)
    (hf : ∀ t, m = some t → (f t).isSome = true) :
    (Option.bind m f).isSome = true := by sorry

theorem plan2_setSupplySpeed_isSome (s : St) (a : Nat) (h : Consistent s) :
    (setSupplySpeed s a).isSome = true := by sorry

theorem plan2_setSupplySpeed_borrow_le (s s' : St) (a : Nat)
    (h : Consistent s) (hs : setSupplySpeed s a = some s') :
    s'.borrowState.block ≤ s'.blockNumber := by sorry

theorem plan2_setBorrowSpeed_isSome (s : St) (b : Nat)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (setBorrowSpeed s b).isSome = true := by sorry

theorem plan2_setCompSpeedInternal_isSome (s : St) (a b : Nat) (h : Consistent s) :
    (setCompSpeedInternal s a b).isSome = true := by sorry

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hs
  cases c with
  | supplyHook who => exact arch0_supplyHook_some s who hs
  | borrowHook who => exact arch0_borrowHook_some s who hs
  | claim who => exact arch0_claim_some s who hs
  | setSpeeds a b => exact arch0_setSpeeds_some s a b hs

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  exact arch0_supply_effect s who s' h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  exact arch0_borrow_effect s who s' h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  exact arch0_claim_effect s who s' h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact arch0_setSpeeds_effect s a b s' h

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hL
  have h1 := arch0_credited_le_totalPot (run comptroller (upgrade L) ops)
  have h2 := arch0_totalPot_run (upgrade L) ops (arch0_inv_upgrade L hL)
  have h3 := arch0_totalPot_upgrade L hL
  have hsp := arch0_upgrade_speeds L
  have hemit : emitted ((upgrade L).supplyState.speed, (upgrade L).borrowState.speed) ops =
      emitted (L.compSpeed, L.compSpeed) ops := by
    rw [hsp.1, hsp.2]
  rw [hemit] at h2
  have hcomb : (run comptroller (upgrade L) ops).credited * doubleScale ≤
      (upgrade L).credited * doubleScale +
      (L.accts.map L.pendingScaled).sum +
      (L.unindexedSupply + L.unindexedBorrow) * doubleScale +
      emitted (L.compSpeed, L.compSpeed) ops * doubleScale := by
    omega
  have hd := arch0_div_bound _ _ _ _ _ hcomb
  show (run comptroller (upgrade L) ops).credited ≤
    (upgrade L).credited +
      ((L.accts.map L.pendingScaled).sum / doubleScale +
        L.unindexedSupply + L.unindexedBorrow) +
      emitted (L.compSpeed, L.compSpeed) ops
  omega

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hL
  have h1 := arch0_creditedTo_le_pot (run comptroller (upgrade L) ops) who
  have h2 := arch0_pot_run (upgrade L) ops who (arch0_inv_upgrade L hL)
  have h3 := arch0_pot_upgrade L who hL
  have hsp := arch0_upgrade_speeds L
  have hemit : emitted ((upgrade L).supplyState.speed, (upgrade L).borrowState.speed) ops =
      emitted (L.compSpeed, L.compSpeed) ops := by
    rw [hsp.1, hsp.2]
  rw [hemit] at h2
  have hcomb : (run comptroller (upgrade L) ops).creditedTo who * doubleScale ≤
      (upgrade L).creditedTo who * doubleScale +
      L.pendingScaled (L.accts.getD who noAcct) +
      ((if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
       (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) * doubleScale +
      emitted (L.compSpeed, L.compSpeed) ops * doubleScale := by
    omega
  have hd := arch0_div_bound _ _ _ _ _ hcomb
  show (run comptroller (upgrade L) ops).creditedTo who ≤
    (upgrade L).creditedTo who +
      (L.pendingScaled (L.accts.getD who noAcct) / doubleScale +
       (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
       (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)) +
      emitted (L.compSpeed, L.compSpeed) ops
  omega

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hL hNP
  have hinvT : arch0_Inv (run comptroller (upgrade L) history) :=
    arch0_inv_run (upgrade L) history (arch0_inv_upgrade L hL)
  have h2 := arch0_pot_run (run comptroller (upgrade L) history) ops who hinvT
  have hsp := arch0_speeds_run_upgrade L history
  rw [hsp] at h2
  have heq := arch0_pot_of_noPosition (run comptroller (upgrade L) history) who hNP
  rw [heq] at h2
  have h1 := arch0_creditedTo_le_pot
    (run comptroller (run comptroller (upgrade L) history) ops) who
  have hcomb : (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who *
        doubleScale ≤
      (run comptroller (upgrade L) history).creditedTo who * doubleScale +
      emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops * doubleScale := by
    omega
  exact arch0_le_of_mul_le_emitted _ _ _ hcomb

end CompRewards
