import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
import ProofForgeFin.Ledger
import ProofForgeFin.DeFi.Rewards
/-!
Fixed COMP distribution: Proposal 64 condition (`compInitialIndex ≤ index`).
-/
namespace CompRewards

open ProofForgeFin ProofForgeFin.DeFi.Rewards ProofForgeFin.Accumulator

/-- `fraction(a, b)` (ExponentialNoError.sol): `Double(div_(mul_(a, doubleScale), b))`. -/
def fraction (a b : Nat) : Nat := a * doubleScale / b

/-- `mul_(uint a, Double b)` (ExponentialNoError.sol): `a * b.mantissa / doubleScale`. -/
def mulDouble (a mantissa : Nat) : Nat := a * mantissa / doubleScale

/-- `sub_(a, b)` (ExponentialNoError.sol): reverts on underflow. -/
def subChecked (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

/-- `updateCompSupplyIndex(cToken)`. -/
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

/-- `updateCompBorrowIndex(cToken, marketBorrowIndex)`. -/
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

/-- `distributeSupplierComp(cToken, supplier)`. -/
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

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
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

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if 0 < amount ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + amount } }
  else s

/-- `claimComp([holder], [market], true, true)`. -/
def claimComp (s : St) (holder : Account) : Option St := do
  let s ← updateCompBorrowIndex s
  let s ← distributeBorrowerComp s holder
  let s ← updateCompSupplyIndex s
  let s ← distributeSupplierComp s holder
  return grantCompInternal s holder

/-- The supply branch of `setCompSpeedInternal`: when the supply speed changes, accrue at the
old speed, then store the new one. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    (updateCompSupplyIndex s).map fun s =>
      { s with supplyState := { s.supplyState with speed := supplySpeed } }
  else some s

/-- The borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    (updateCompBorrowIndex s).map fun s =>
      { s with borrowState := { s.borrowState with speed := borrowSpeed } }
  else some s

/-- `setCompSpeedInternal(cToken, supplySpeed, borrowSpeed)`: the supply branch, then the borrow
branch. -/
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

theorem sub_some {a b d : Nat} (h : subChecked a b = some d) : b ≤ a ∧ d = a - b := by
  unfold subChecked at h
  split at h
  · next hb => simp at h; subst h; exact ⟨hb, rfl⟩
  · next hb => simp at h

theorem modify_congr {α : Type} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp at h ⊢; simp [h]
    | succ i => simp at h ⊢; exact ih i h

theorem start_supply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
     else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0 <;> simp [hr]

theorem start_borrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
     else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0 <;> simp [hr]

theorem grant_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  simp only [grantCompInternal, grant, St.acct]
  by_cases h : 0 < (s.accts.getD who noAcct).accrued ∧
      (s.accts.getD who noAcct).accrued ≤ s.reserve
  · simp only [h, and_true, ↓reduceIte]
    cases s with
    | mk bn sup bor res ac =>
      simp only
      congr 1
      apply modify_congr _ _ _ _ noAcct
      rfl
  · simp only [h, ↓reduceIte]

theorem upd_supply_some (s : St) (s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  simp only [updateCompSupplyIndex, subChecked, accrueSide, totalSupply, fraction] at h ⊢
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · simp [hle] at h
    by_cases hd : 0 < s.blockNumber - s.supplyState.block
    · by_cases hs : 0 < s.supplyState.speed
      · by_cases ht : 0 < (s.accts.map Acct.supply).sum
        · simp [hd, hs, ht] at h ⊢
          exact ⟨hle, h.symm⟩
        · simp [hd, hs, ht] at h ⊢
          exact ⟨hle, h.symm⟩
      · simp [hd, hs] at h ⊢
        exact ⟨hle, h.symm⟩
    · simp [hd] at h ⊢
      have heq : s.supplyState.block = s.blockNumber := by omega
      obtain ⟨bn, sup, bor, res, ac⟩ := s
      simp at heq h ⊢
      obtain ⟨si, sb, ss⟩ := sup
      simp at heq h ⊢
      subst heq
      exact ⟨Nat.le_refl _, h.symm⟩
  · simp [hle] at h

theorem dist_supply_some (s : St) (who : Nat) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart := start_supply_eq s who
  simp only [St.acct] at hstart
  simp only [distributeSupplierComp, St.acct, St.withAcct] at h
  simp only [hstart] at h
  simp only [creditFor, mulDouble, St.withAcct] at h ⊢
  cases hd : subChecked s.supplyState.index
      (accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) with
  | none => simp only [hd] at h; cases h
  | some delta =>
    simp only [hd] at h
    have hsub := sub_some hd
    refine ⟨hsub.1, ?_⟩
    cases h
    congr 1
    apply modify_congr _ _ _ _ noAcct
    have hget : (s.accts.getD who noAcct).supply * delta / doubleScale =
        (s.accts.getD who noAcct).supply *
          (s.supplyState.index -
            accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) /
          doubleScale := by rw [hsub.2]
    rw [hget]

theorem dist_borrow_some (s : St) (who : Nat) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart := start_borrow_eq s who
  simp only [St.acct] at hstart
  simp only [distributeBorrowerComp, St.acct, St.withAcct] at h
  simp only [hstart] at h
  simp only [creditFor, mulDouble, St.withAcct] at h ⊢
  cases hd : subChecked s.borrowState.index
      (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) with
  | none => simp only [hd] at h; cases h
  | some delta =>
    simp only [hd] at h
    have hsub := sub_some hd
    refine ⟨hsub.1, ?_⟩
    cases h
    congr 1
    apply modify_congr _ _ _ _ noAcct
    have hget : (s.accts.getD who noAcct).borrow * delta / doubleScale =
        (s.accts.getD who noAcct).borrow *
          (s.borrowState.index -
            accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) /
          doubleScale := by rw [hsub.2]
    rw [hget]

theorem upd_borrow_some (s : St) (s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  simp only [updateCompBorrowIndex, subChecked, accrueSide, totalBorrows, fraction] at h ⊢
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · simp [hle] at h
    by_cases hd : 0 < s.blockNumber - s.borrowState.block
    · by_cases hs : 0 < s.borrowState.speed
      · by_cases ht : 0 < (s.accts.map Acct.borrow).sum
        · simp [hd, hs, ht] at h ⊢
          exact ⟨hle, h.symm⟩
        · simp [hd, hs, ht] at h ⊢
          exact ⟨hle, h.symm⟩
      · simp [hd, hs] at h ⊢
        exact ⟨hle, h.symm⟩
    · simp [hd] at h ⊢
      have heq : s.borrowState.block = s.blockNumber := by omega
      obtain ⟨bn, sup, bor, res, ac⟩ := s
      simp at heq h ⊢
      obtain ⟨bi, bb, bs⟩ := bor
      simp at heq h ⊢
      subst heq
      exact ⟨Nat.le_refl _, h.symm⟩
  · simp [hle] at h

theorem setSupply_some (s : St) (a : Nat) (t : St) (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases hs : s.supplyState.speed = a
  · simp only [hs, ↓reduceIte] at h
    cases h
    refine ⟨fun hn => absurd hs hn, ?_⟩
    simp only [hs, ↓reduceIte]
  · simp only [hs, ↓reduceIte] at h
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      have hupd := upd_supply_some s u hu
      cases h
      obtain ⟨hble, hs1eq⟩ := hupd
      refine ⟨fun _ => hble, ?_⟩
      simp only [hs, ↓reduceIte]
      subst hs1eq
      rfl

theorem setBorrow_some (s : St) (b : Nat) (t : St) (h : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases hb : s.borrowState.speed = b
  · simp [hb] at h
    cases h
    refine ⟨fun hn => absurd hb hn, ?_⟩
    simp [hb]
  · simp [hb] at h
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      have hupd := upd_borrow_some s u hu
      cases h
      obtain ⟨hble, hs1eq⟩ := hupd
      refine ⟨fun _ => hble, ?_⟩
      simp [hb]
      subst hs1eq
      rfl

theorem supply_hook_eq (s : St) (who : Nat) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ s1, updateCompSupplyIndex s = some s1 ∧ distributeSupplierComp s1 who = some s' := by
  unfold comptroller at h
  cases hu : updateCompSupplyIndex s with
  | none => simp [hu] at h
  | some s1 => simp [hu] at h; exact ⟨s1, rfl, h⟩

theorem borrow_hook_eq (s : St) (who : Nat) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ s1, updateCompBorrowIndex s = some s1 ∧ distributeBorrowerComp s1 who = some s' := by
  unfold comptroller at h
  cases hu : updateCompBorrowIndex s with
  | none => simp [hu] at h
  | some s1 => simp [hu] at h; exact ⟨s1, rfl, h⟩

theorem accrualStart_le {recorded index : Nat} (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [hr]; exact h

theorem upd_supply_isSome (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  unfold updateCompSupplyIndex subChecked
  simp only [hle, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem upd_borrow_isSome (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  unfold updateCompBorrowIndex subChecked
  simp only [hle, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · rfl

theorem acct_supplier_le (s : St)
    (hrec : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index)
    (who : Nat) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  rcases Ledger.getD_mem_or s.accts who noAcct with h | h
  · exact (hrec _ h).1
  · rw [h]; unfold noAcct; simp

theorem acct_borrower_le (s : St)
    (hrec : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index)
    (who : Nat) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  rcases Ledger.getD_mem_or s.accts who noAcct with h | h
  · exact (hrec _ h).2
  · rw [h]; unfold noAcct; simp

theorem accrueSupply_index_le (s s1 : St)
    (hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) :
    s.supplyState.index ≤ s1.supplyState.index := by
  rw [hs1]
  show s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrueBorrow_index_le (s s1 : St)
    (hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) :
    s.borrowState.index ≤ s1.borrowState.index := by
  rw [hs1]
  show s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem acct_eq_of_supply_upd (s s1 : St) (who : Nat)
    (hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }) :
    s1.acct who = s.acct who := by
  rw [hs1]; rfl

theorem acct_eq_of_borrow_upd (s s1 : St) (who : Nat)
    (hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }) :
    s1.acct who = s.acct who := by
  rw [hs1]; rfl

theorem setSupply_isSome (s : St) (hle : s.supplyState.block ≤ s.blockNumber) (a : Nat) :
    (setSupplySpeed s a).isSome = true := by
  unfold setSupplySpeed
  by_cases hs : s.supplyState.speed ≠ a
  · simp [hs]
    have h1 := upd_supply_isSome s hle
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h1
    | some t1 => simp [hu]
  · simp [hs]

theorem setBorrow_isSome (s : St) (hle : s.borrowState.block ≤ s.blockNumber) (b : Nat) :
    (setBorrowSpeed s b).isSome = true := by
  unfold setBorrowSpeed
  by_cases hb : s.borrowState.speed ≠ b
  · simp [hb]
    have h1 := upd_borrow_isSome s hle
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h1
    | some t1 => simp [hu]
  · simp [hb]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsup, hbor, hrec⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    have h1 : (updateCompSupplyIndex s).isSome = true := upd_supply_isSome s hsup
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h1
    | some s1 =>
      simp [hu]
      have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
        (upd_supply_some s s1 hu).2
      have hle : accrualStart (s1.acct who).supplierIndex s1.supplyState.index ≤ s1.supplyState.index := by
        apply accrualStart_le
        have hre := acct_supplier_le s hrec who
        have hsup_le := accrueSupply_index_le s s1 hs1
        have hacct_eq := acct_eq_of_supply_upd s s1 who hs1
        rw [hacct_eq]
        exact Nat.le_trans hre hsup_le
      have hstart := start_supply_eq s1 who
      unfold distributeSupplierComp
      simp only [hstart]
      simp [subChecked, hle]
  | borrowHook who =>
    unfold comptroller
    have h1 : (updateCompBorrowIndex s).isSome = true := upd_borrow_isSome s hbor
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h1
    | some s1 =>
      simp [hu]
      have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        (upd_borrow_some s s1 hu).2
      have hle : accrualStart (s1.acct who).borrowerIndex s1.borrowState.index ≤ s1.borrowState.index := by
        apply accrualStart_le
        have hre := acct_borrower_le s hrec who
        have hbor_le := accrueBorrow_index_le s s1 hs1
        have hacct_eq := acct_eq_of_borrow_upd s s1 who hs1
        rw [hacct_eq]
        exact Nat.le_trans hre hbor_le
      have hstart := start_borrow_eq s1 who
      unfold distributeBorrowerComp
      simp only [hstart]
      simp [subChecked, hle]
  | claim who =>
    unfold comptroller claimComp
    have h1 : (updateCompBorrowIndex s).isSome = true := upd_borrow_isSome s hbor
    cases hu1 : updateCompBorrowIndex s with
    | none => simp [hu1] at h1
    | some t1 =>
      simp [hu1]
      have ht1 := upd_borrow_some s t1 hu1
      have hle1 : accrualStart (t1.acct who).borrowerIndex t1.borrowState.index ≤ t1.borrowState.index := by
        apply accrualStart_le
        have hre := acct_borrower_le s hrec who
        have hbor_le := accrueBorrow_index_le s t1 ht1.2
        have hacct_eq := acct_eq_of_borrow_upd s t1 who ht1.2
        rw [hacct_eq]
        exact Nat.le_trans hre hbor_le
      have hd1 : (distributeBorrowerComp t1 who).isSome = true := by
        have hstart := start_borrow_eq t1 who
        unfold distributeBorrowerComp
        simp only [hstart]
        simp [subChecked, hle1]
      cases hd1' : distributeBorrowerComp t1 who with
      | none => simp [hd1'] at hd1
      | some t2 =>
        simp [hd1']
        have ht2 := dist_borrow_some t1 who t2 hd1'
        have hsup2 : t2.supplyState.block ≤ t2.blockNumber := by
          rw [ht2.2]
          simp [ht1.2]
          exact hsup
        have h1s : (updateCompSupplyIndex t2).isSome = true := upd_supply_isSome t2 hsup2
        cases hu2 : updateCompSupplyIndex t2 with
        | none => simp [hu2] at h1s
        | some t3 =>
          simp [hu2]
          have ht3 := upd_supply_some t2 t3 hu2
          have hsup_t2 : (t2.acct who).supplierIndex ≤ t2.supplyState.index := by
            have h0 := acct_supplier_le s hrec who
            have e1 : (t1.acct who).supplierIndex = (s.acct who).supplierIndex := by
              rw [ht1.2]; rfl
            have e2 : (t2.acct who).supplierIndex = (t1.acct who).supplierIndex := by
              have h1 : t2.acct who =
                  (t1.accts.modify who fun a =>
                    { a with borrowerIndex := t1.borrowState.index,
                             accrued := a.accrued + creditFor a.borrow
                               (accrualStart a.borrowerIndex t1.borrowState.index) t1.borrowState.index }).getD who noAcct := by
                rw [ht2.2]; rfl
              rw [h1, Ledger.getD_modify]
              split <;> rfl
            have e3 : t2.supplyState.index = s.supplyState.index := by
              rw [ht2.2, ht1.2]
            omega
          have hle2 : accrualStart (t3.acct who).supplierIndex t3.supplyState.index ≤
              t3.supplyState.index := by
            apply accrualStart_le
            have hsup_le := accrueSupply_index_le t2 t3 ht3.2
            have hacct_eq := acct_eq_of_supply_upd t2 t3 who ht3.2
            rw [hacct_eq]
            exact Nat.le_trans hsup_t2 hsup_le
          have hd2 : (distributeSupplierComp t3 who).isSome = true := by
            have hstart := start_supply_eq t3 who
            unfold distributeSupplierComp
            simp only [hstart]
            simp [subChecked, hle2]
          cases hd2' : distributeSupplierComp t3 who with
          | none => simp [hd2'] at hd2
          | some t4 => simp [hd2']
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal
    have h1 : (setSupplySpeed s a).isSome = true := setSupply_isSome s hsup a
    cases hs1 : setSupplySpeed s a with
    | none => simp [hs1] at h1
    | some t1 =>
      simp [hs1]
      have hbor1 : t1.borrowState.block ≤ t1.blockNumber := by
        unfold setSupplySpeed at hs1
        by_cases hs : s.supplyState.speed ≠ a
        · simp [hs] at hs1
          cases hu : updateCompSupplyIndex s with
          | none =>
            have h0 := upd_supply_isSome s hsup
            simp [hu] at h0
          | some u =>
            simp [hu] at hs1
            subst hs1
            simp [(upd_supply_some s u hu).2]
            exact hbor
        · simp [hs] at hs1
          subst hs1
          exact hbor
      have h2 : (setBorrowSpeed t1 b).isSome = true := setBorrow_isSome t1 hbor1 b
      cases hb1 : setBorrowSpeed t1 b with
      | none => simp [hb1] at h2
      | some t2 => simp [hb1]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  obtain ⟨s1, hu, hd⟩ := supply_hook_eq s who s' h
  have hupd := upd_supply_some s s1 hu
  have hdist := dist_supply_some s1 who s' hd
  obtain ⟨hble, hs1eq⟩ := hupd
  obtain ⟨hstart_le, hs'eq⟩ := hdist
  have hacct : s1.acct who = s.acct who := by rw [hs1eq]; rfl
  have hidx : s1.supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hs1eq]
  refine ⟨hble, ?_, ?_⟩
  · rw [hacct, hidx] at hstart_le; exact hstart_le
  · subst hs1eq
    subst hs'eq
    rfl

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  obtain ⟨s1, hu, hd⟩ := borrow_hook_eq s who s' h
  have hupd := upd_borrow_some s s1 hu
  have hdist := dist_borrow_some s1 who s' hd
  obtain ⟨hble, hs1eq⟩ := hupd
  obtain ⟨hstart_le, hs'eq⟩ := hdist
  have hacct : s1.acct who = s.acct who := by rw [hs1eq]; rfl
  have hidx : s1.borrowState.index =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hs1eq]
  refine ⟨hble, ?_, ?_⟩
  · rw [hacct, hidx] at hstart_le; exact hstart_le
  · subst hs1eq
    subst hs'eq
    rfl

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  cases hu1 : updateCompBorrowIndex s with
  | none => simp [hu1] at h
  | some t1 =>
    simp [hu1] at h
    cases hd1 : distributeBorrowerComp t1 who with
    | none => simp [hd1] at h
    | some t2 =>
      simp [hd1] at h
      cases hu2 : updateCompSupplyIndex t2 with
      | none => simp [hu2] at h
      | some t3 =>
        simp [hu2] at h
        cases hd2 : distributeSupplierComp t3 who with
        | none => simp [hd2] at h
        | some t4 =>
          simp [hd2] at h
          subst h
          have hupd1 := upd_borrow_some s t1 hu1
          have hdist1 := dist_borrow_some t1 who t2 hd1
          have hupd2 := upd_supply_some t2 t3 hu2
          have hdist2 := dist_supply_some t3 who t4 hd2
          refine ⟨t2, t4, ?_, ?_, ?_⟩
          · obtain ⟨hble1, hs1eq⟩ := hupd1
            obtain ⟨hstart1, hs2eq⟩ := hdist1
            have hacct1 : t1.acct who = s.acct who := by rw [hs1eq]; rfl
            have hidx1 : t1.borrowState.index =
                (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
              rw [hs1eq]
            refine ⟨hble1, ?_, ?_⟩
            · rw [hacct1, hidx1] at hstart1; exact hstart1
            · subst hs1eq
              subst hs2eq
              rfl
          · obtain ⟨hble2, hs3eq⟩ := hupd2
            obtain ⟨hstart2, hs4eq⟩ := hdist2
            have hacct2 : t3.acct who = t2.acct who := by rw [hs3eq]; rfl
            have hidx2 : t3.supplyState.index =
                (accrueSide t2.supplyState t2.blockNumber (totalSupply t2)).index := by
              rw [hs3eq]
            refine ⟨hble2, ?_, ?_⟩
            · rw [hacct2, hidx2] at hstart2; exact hstart2
            · subst hs3eq
              subst hs4eq
              rfl
          · exact grant_eq t4 who

theorem req_set_speeds : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
