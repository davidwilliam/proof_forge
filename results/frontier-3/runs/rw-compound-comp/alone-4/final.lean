import CompRewards.Spec
/-!
Fixed port of the COMP distribution of Compound's Comptroller as deployed by Proposal 62.
The bug was in `distributeSupplierComp` / `distributeBorrowerComp`: a fresh account
(`supplierIndex = 0` / `borrowerIndex = 0`) in a market whose index is exactly
`compInitialIndex` (i.e. a market that never had rewards, initialized by the upgrade)
was credited from 0 instead of from `compInitialIndex`. The deployed code tested
`index > compInitialIndex`; the correct threshold is `index >= compInitialIndex`,
matching `accrualStart` in the spec.
-/
namespace CompRewards

instance : Inhabited Acct where
  default := noAcct

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

/-- `distributeSupplierComp(cToken, supplier)` (fixed: `>= compInitialIndex`). -/
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

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)` (fixed). -/
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
  if amount > 0 ∧ amount ≤ s.reserve then
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

/-- The supply branch of `setCompSpeedInternal`. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    match updateCompSupplyIndex s with
    | none => none
    | some m => some { m with supplyState := { m.supplyState with speed := supplySpeed } }
  else some s

/-- The borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    match updateCompBorrowIndex s with
    | none => none
    | some m => some { m with borrowState := { m.borrowState with speed := borrowSpeed } }
  else some s

/-- `setCompSpeedInternal(cToken, supplySpeed, borrowSpeed)`. -/
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

-- Helper lemmas linking implementation pieces to the spec. --
theorem subChecked_some {a b d : Nat} : subChecked a b = some d ↔ b ≤ a ∧ a - b = d := by
  unfold subChecked
  by_cases h : b ≤ a <;> simp [h]

theorem subChecked_eq_some (a b : Nat) (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked; simp [h]

theorem subChecked_none (a b : Nat) (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked; simp [h]

theorem accrue_update_supply (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide totalSupply fraction
  rw [subChecked_eq_some _ _ hle]
  dsimp only
  by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos h1]
    by_cases hT : (s.accts.map Acct.supply).sum > 0
    · rw [if_pos hT]
      have hcond : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (s.accts.map Acct.supply).sum := ⟨h1.1, h1.2, hT⟩
      rw [if_pos hcond]
    · rw [if_neg hT]
      have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (s.accts.map Acct.supply).sum) := fun hh => hT hh.2.2
      rw [if_neg hcond]
      have hT0 : (s.accts.map Acct.supply).sum = 0 := Nat.eq_zero_of_not_pos hT
      simp [hT0]
  · rw [if_neg h1]
    by_cases hd : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos hd]
      have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (s.accts.map Acct.supply).sum) := fun hh => h1 ⟨hh.1, hh.2.1⟩
      rw [if_neg hcond]
    · rw [if_neg hd]
      have hd0 : s.blockNumber - s.supplyState.block = 0 := Nat.eq_zero_of_not_pos hd
      have hcond : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (s.accts.map Acct.supply).sum) := fun hh => hd hh.1
      rw [if_neg hcond]
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      cases s with
      | mk bn ss bs r ac =>
        cases ss with
        | mk idx blk spd =>
          simp at hbeq
          simp [hbeq]

theorem accrue_update_borrow (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide totalBorrows fraction
  rw [subChecked_eq_some _ _ hle]
  dsimp only
  by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos h1]
    by_cases hT : (s.accts.map Acct.borrow).sum > 0
    · rw [if_pos hT]
      have hcond : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (s.accts.map Acct.borrow).sum := ⟨h1.1, h1.2, hT⟩
      rw [if_pos hcond]
    · rw [if_neg hT]
      have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (s.accts.map Acct.borrow).sum) := fun hh => hT hh.2.2
      rw [if_neg hcond]
      have hT0 : (s.accts.map Acct.borrow).sum = 0 := Nat.eq_zero_of_not_pos hT
      simp [hT0]
  · rw [if_neg h1]
    by_cases hd : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos hd]
      have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (s.accts.map Acct.borrow).sum) := fun hh => h1 ⟨hh.1, hh.2.1⟩
      rw [if_neg hcond]
    · rw [if_neg hd]
      have hcond : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (s.accts.map Acct.borrow).sum) := fun hh => hd hh.1
      rw [if_neg hcond]
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      cases s with
      | mk bn ss bs r ac =>
        cases bs with
        | mk idx blk spd =>
          simp at hbeq
          simp [hbeq]

theorem start_supply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then
      compInitialIndex else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0
  · simp only [hr, true_and]
    by_cases hs : compInitialIndex ≤ s.supplyState.index <;> simp [hs, hr]
  · simp [hr]

theorem start_borrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then
      compInitialIndex else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0
  · simp only [hr, true_and]
    by_cases hs : compInitialIndex ≤ s.borrowState.index <;> simp [hs, hr]
  · simp [hr]

theorem modify_congr (l : List Acct) (n : Nat) (f g : Acct → Acct)
    (h : f (l.getD n noAcct) = g (l.getD n noAcct)) :
    l.modify n f = l.modify n g := by
  have hdef : (default : Acct) = noAcct := rfl
  have e1 : l.modify n f = l.set n (f (l.getD n noAcct)) := by
    have hme := List.modify_eq_set f n l
    simp only [hme, hdef, List.getD]
  have e2 : l.modify n g = l.set n (g (l.getD n noAcct)) := by
    have hme := List.modify_eq_set g n l
    simp only [hme, hdef, List.getD]
  rw [e1, e2, h]

theorem distribute_supply_eq (s : St) (who : Account)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then
      compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    start_supply_eq s who
  unfold distributeSupplierComp
  dsimp only
  rw [hstart, subChecked_eq_some _ _ hle]
  simp only [St.withAcct, creditFor, mulDouble, St.acct]
  apply congrArg
  apply congrArg
  apply modify_congr
  rfl

theorem distribute_borrow_eq (s : St) (who : Account)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then
      compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    start_borrow_eq s who
  unfold distributeBorrowerComp
  dsimp only
  rw [hstart, subChecked_eq_some _ _ hle]
  simp only [St.withAcct, creditFor, mulDouble, St.acct]
  apply congrArg
  apply congrArg
  apply modify_congr
  rfl

theorem accrualStart_le_self (r idx : Nat) (h : r ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · subst hr
    by_cases hs : compInitialIndex ≤ idx
    · rw [if_pos rfl, if_pos hs]; exact hs
    · rw [if_pos rfl, if_neg hs]; exact Nat.zero_le _
  · rw [if_neg hr]; exact h

theorem accrueSide_mono_index (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos h]; exact Nat.le_add_right _ _
  · rw [if_neg h]; exact Nat.le_refl _

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  dsimp only
  cases s with
  | mk bn ss bs r ac =>
    by_cases h : 0 < (ac.getD who noAcct).accrued ∧ (ac.getD who noAcct).accrued ≤ r
    · have hgt : (ac.getD who noAcct).accrued > 0 ∧ (ac.getD who noAcct).accrued ≤ r := h
      rw [if_pos hgt, if_pos h]
      congr 1
      exact modify_congr _ _ _ _ rfl
    · have hgt : ¬ ((ac.getD who noAcct).accrued > 0 ∧ (ac.getD who noAcct).accrued ≤ r) := h
      rw [if_neg hgt, if_neg h]

theorem supply_hook_some (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ m, updateCompSupplyIndex s = some m ∧ distributeSupplierComp m who = some s' := by
  unfold comptroller at h
  cases hup : updateCompSupplyIndex s with
  | none =>
    simp [hup] at h
  | some m =>
    simp [hup] at h
    exact ⟨m, rfl, h⟩

theorem borrow_hook_some (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ m, updateCompBorrowIndex s = some m ∧ distributeBorrowerComp m who = some s' := by
  unfold comptroller at h
  cases hup : updateCompBorrowIndex s with
  | none =>
    simp [hup] at h
  | some m =>
    simp [hup] at h
    exact ⟨m, rfl, h⟩

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  obtain ⟨m, hup, hdist⟩ := supply_hook_some s who s' h
  have hblt : s.supplyState.block ≤ s.blockNumber := by
    unfold updateCompSupplyIndex at hup
    cases hsub : subChecked s.blockNumber s.supplyState.block with
    | none => simp [hsub] at hup
    | some d =>
      exact (subChecked_some.mp (by rw [hsub])).1
  have hup_eq := accrue_update_supply s hblt
  rw [hup] at hup_eq
  have hmeq := Option.some.inj hup_eq
  have hle_m : accrualStart (m.acct who).supplierIndex
      m.supplyState.index ≤ m.supplyState.index := by
    have hdist' := hdist
    unfold distributeSupplierComp at hdist'
    dsimp only at hdist'
    cases hsub : subChecked m.supplyState.index
        (if (m.acct who).supplierIndex = 0 ∧
          compInitialIndex ≤ m.supplyState.index then compInitialIndex
        else (m.acct who).supplierIndex) with
    | none => simp [hsub] at hdist'
    | some d =>
      have hle := (subChecked_some.mp (by rw [hsub])).1
      have hstart := start_supply_eq m who
      rw [hstart] at hle
      exact hle
  have hdist_eq := distribute_supply_eq m who hle_m
  rw [hdist] at hdist_eq
  have hs_eq := Option.some.inj hdist_eq
  subst hmeq
  subst hs_eq
  unfold SupplyDistributed
  refine ⟨hblt, hle_m, rfl⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  obtain ⟨m, hup, hdist⟩ := borrow_hook_some s who s' h
  have hblt : s.borrowState.block ≤ s.blockNumber := by
    unfold updateCompBorrowIndex at hup
    cases hsub : subChecked s.blockNumber s.borrowState.block with
    | none => simp [hsub] at hup
    | some d =>
      exact (subChecked_some.mp (by rw [hsub])).1
  have hup_eq := accrue_update_borrow s hblt
  rw [hup] at hup_eq
  have hmeq := Option.some.inj hup_eq
  have hle_m : accrualStart (m.acct who).borrowerIndex
      m.borrowState.index ≤ m.borrowState.index := by
    have hdist' := hdist
    unfold distributeBorrowerComp at hdist'
    dsimp only at hdist'
    cases hsub : subChecked m.borrowState.index
        (if (m.acct who).borrowerIndex = 0 ∧
          compInitialIndex ≤ m.borrowState.index then compInitialIndex
        else (m.acct who).borrowerIndex) with
    | none => simp [hsub] at hdist'
    | some d =>
      have hle := (subChecked_some.mp (by rw [hsub])).1
      have hstart := start_borrow_eq m who
      rw [hstart] at hle
      exact hle
  have hdist_eq := distribute_borrow_eq m who hle_m
  rw [hdist] at hdist_eq
  have hs_eq := Option.some.inj hdist_eq
  subst hmeq
  subst hs_eq
  unfold BorrowDistributed
  refine ⟨hblt, hle_m, rfl⟩

theorem claim_some (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    ∃ m1 m2 m3 m4, updateCompBorrowIndex s = some m1 ∧
      distributeBorrowerComp m1 who = some m2 ∧ updateCompSupplyIndex m2 = some m3 ∧
      distributeSupplierComp m3 who = some m4 ∧ grantCompInternal m4 who = s' := by
  unfold comptroller claimComp at h
  cases h1 : updateCompBorrowIndex s with
  | none => simp [h1] at h
  | some m1 =>
    simp [h1] at h
    cases h2 : distributeBorrowerComp m1 who with
    | none => simp [h2] at h
    | some m2 =>
      simp [h2] at h
      cases h3 : updateCompSupplyIndex m2 with
      | none => simp [h3] at h
      | some m3 =>
        simp [h3] at h
        cases h4 : distributeSupplierComp m3 who with
        | none => simp [h4] at h
        | some m4 =>
          simp [h4] at h
          exact ⟨m1, m2, m3, m4, rfl, rfl, rfl, rfl, h⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  obtain ⟨m1, m2, m3, m4, hupB, hdistB, hupS, hdistS, hgrant⟩ :=
    claim_some s who s' h
  have hbltB : s.borrowState.block ≤ s.blockNumber := by
    unfold updateCompBorrowIndex at hupB
    cases hsub : subChecked s.blockNumber s.borrowState.block with
    | none => simp [hsub] at hupB
    | some d => exact (subChecked_some.mp (by rw [hsub])).1
  have hupB_eq := accrue_update_borrow s hbltB
  rw [hupB] at hupB_eq
  have hmeqB := Option.some.inj hupB_eq
  have hleB : accrualStart (m1.acct who).borrowerIndex
      m1.borrowState.index ≤ m1.borrowState.index := by
    have hd := hdistB
    unfold distributeBorrowerComp at hd
    dsimp only at hd
    cases hsub : subChecked m1.borrowState.index
        (if (m1.acct who).borrowerIndex = 0 ∧
          compInitialIndex ≤ m1.borrowState.index then compInitialIndex
        else (m1.acct who).borrowerIndex) with
    | none => simp [hsub] at hd
    | some d =>
      have hle := (subChecked_some.mp (by rw [hsub])).1
      have hstart := start_borrow_eq m1 who
      rw [hstart] at hle
      exact hle
  have hdistB_eq := distribute_borrow_eq m1 who hleB
  rw [hdistB] at hdistB_eq
  have hm2_eq := Option.some.inj hdistB_eq
  have hbltS : m2.supplyState.block ≤ m2.blockNumber := by
    unfold updateCompSupplyIndex at hupS
    cases hsub : subChecked m2.blockNumber m2.supplyState.block with
    | none => simp [hsub] at hupS
    | some d => exact (subChecked_some.mp (by rw [hsub])).1
  have hupS_eq := accrue_update_supply m2 hbltS
  rw [hupS] at hupS_eq
  have hmeqS := Option.some.inj hupS_eq
  have hleS : accrualStart (m3.acct who).supplierIndex
      m3.supplyState.index ≤ m3.supplyState.index := by
    have hd := hdistS
    unfold distributeSupplierComp at hd
    dsimp only at hd
    cases hsub : subChecked m3.supplyState.index
        (if (m3.acct who).supplierIndex = 0 ∧
          compInitialIndex ≤ m3.supplyState.index then compInitialIndex
        else (m3.acct who).supplierIndex) with
    | none => simp [hsub] at hd
    | some d =>
      have hle := (subChecked_some.mp (by rw [hsub])).1
      have hstart := start_supply_eq m3 who
      rw [hstart] at hle
      exact hle
  have hdistS_eq := distribute_supply_eq m3 who hleS
  rw [hdistS] at hdistS_eq
  have hm4_eq := Option.some.inj hdistS_eq
  have hB : BorrowDistributed s who m2 := by
    rw [hmeqB] at hm2_eq hleB
    refine ⟨hbltB, hleB, hm2_eq⟩
  have hS : SupplyDistributed m2 who m4 := by
    rw [hmeqS] at hm4_eq hleS
    refine ⟨hbltS, hleS, hm4_eq⟩
  have hgr : s' = grant m4 who := by
    have he := grant_eq m4 who
    rw [hgrant] at he
    exact he
  unfold Claimed
  exact ⟨m2, m4, hB, hS, hgr⟩

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem setSupply_res (s : St) (a : Nat) (t : St) (hs : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState ∧
    t.reserve = s.reserve ∧ t.accts = s.accts ∧
    (s.supplyState.speed = a → t = s) ∧
    (s.supplyState.speed ≠ a →
      t.supplyState.index =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧
      t.supplyState.block = s.blockNumber ∧ t.supplyState.speed = a) := by
  have hsup : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber := by
    intro hne
    unfold setSupplySpeed at hs
    rw [if_pos hne] at hs
    cases hup : updateCompSupplyIndex s with
    | none => simp [hup] at hs
    | some m =>
      unfold updateCompSupplyIndex at hup
      cases hsub : subChecked s.blockNumber s.supplyState.block with
      | none => simp [hsub] at hup
      | some d => exact (subChecked_some.mp (by rw [hsub])).1
  unfold setSupplySpeed at hs
  by_cases hne : s.supplyState.speed ≠ a
  · rw [if_pos hne] at hs
    cases hup : updateCompSupplyIndex s with
    | none => simp [hup] at hs; cases hs
    | some m =>
      simp only [hup] at hs
      have hbl := hsup hne
      have heq := accrue_update_supply s hbl
      rw [hup] at heq
      have hm := Option.some.inj heq
      have ht := Option.some.inj hs
      subst hm
      subst ht
      refine ⟨hsup, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro heq2
        exact absurd heq2 hne
      · intro _
        refine ⟨rfl, accrueSide_block _ _ _, rfl⟩
  · rw [if_neg hne] at hs
    have ht := Option.some.inj hs
    subst ht
    refine ⟨hsup, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro _
      rfl
    · intro heq2
      exact absurd heq2 hne

theorem setBorrow_res (t : St) (b : Nat) (u : St) (hb : setBorrowSpeed t b = some u) :
    (t.borrowState.speed ≠ b → t.borrowState.block ≤ t.blockNumber) ∧
    u.blockNumber = t.blockNumber ∧ u.supplyState = t.supplyState ∧
    u.reserve = t.reserve ∧ u.accts = t.accts ∧
    (t.borrowState.speed = b → u = t) ∧
    (t.borrowState.speed ≠ b →
      u.borrowState.index =
        (accrueSide t.borrowState t.blockNumber (totalBorrows t)).index ∧
      u.borrowState.block = t.blockNumber ∧ u.borrowState.speed = b) := by
  have hbor : t.borrowState.speed ≠ b → t.borrowState.block ≤ t.blockNumber := by
    intro hne
    unfold setBorrowSpeed at hb
    simp [hne] at hb
    cases hup : updateCompBorrowIndex t with
    | none => simp [hup] at hb
    | some m =>
      simp [hup] at hb
      unfold updateCompBorrowIndex at hup
      cases hsub : subChecked t.blockNumber t.borrowState.block with
      | none => simp [hsub] at hup
      | some d => exact (subChecked_some.mp (by rw [hsub])).1
  unfold setBorrowSpeed at hb
  by_cases hne : t.borrowState.speed ≠ b
  · simp only [hne] at hb
    cases hup : updateCompBorrowIndex t with
    | none => simp [hup] at hb
    | some m =>
      simp only [hup] at hb
      have hbl := hbor hne
      have heq := accrue_update_borrow t hbl
      rw [hup] at heq
      have hm := Option.some.inj heq
      have hu := Option.some.inj hb
      subst hm
      subst hu
      refine ⟨hbor, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro heq2
        exact absurd heq2 hne
      · intro _
        refine ⟨rfl, accrueSide_block _ _ _, rfl⟩
  · simp only [hne] at hb
    have hu := Option.some.inj hb
    subst hu
    refine ⟨hbor, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro _
      rfl
    · intro heq2
      exact absurd heq2 hne

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  cases hs : setSupplySpeed s a with
  | none => simp [hs] at h
  | some t =>
    simp [hs] at h
    cases hb : setBorrowSpeed t b with
    | none => simp [hb] at h
    | some u =>
      simp [hb] at h
      subst h
      obtain ⟨hsup, hbn, hbs, hres, haccts, hsameS, hdiffS⟩ := setSupply_res s a t hs
      obtain ⟨hbor_t, hubn, hubsupply, hubres, hubaccts, hsameB, hdiffB⟩ :=
        setBorrow_res t b u hb
      have hbor : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
        intro hne
        have htb : t.borrowState = s.borrowState := hbs
        have htn : t.blockNumber = s.blockNumber := hbn
        by_cases htb2 : t.borrowState.speed ≠ b
        · have hle := hbor_t htb2
          rw [htb, htn] at hle
          exact hle
        · have hteq : t.borrowState.speed = s.borrowState.speed := by rw [htb]
          have hne_t : t.borrowState.speed ≠ b := by rw [hteq]; exact hne
          exact absurd hne_t htb2
      refine ⟨hsup, hbor, ?_⟩
      by_cases hsa : s.supplyState.speed = a
      · have ht : t = s := hsameS hsa
        have htb : t.borrowState.speed = s.borrowState.speed := congrArg Side.speed hbs
        by_cases hsb : s.borrowState.speed = b
        · have hsb_t : t.borrowState.speed = b := by rw [htb]; exact hsb
          have hu : u = t := hsameB hsb_t
          rw [if_pos hsa, if_pos hsb]
          simp_all [accrueSide_block]
        · have hne : s.borrowState.speed ≠ b := fun he => hsb he
          have hne_t : t.borrowState.speed ≠ b := by rw [htb]; exact hne
          obtain ⟨hidx, hblk, hspd⟩ := hdiffB hne_t
          have htot : totalBorrows t = totalBorrows s := by
            have h2 := haccts
            simp [totalBorrows] at h2 ⊢
            rw [h2]
          rw [if_pos hsa, if_neg hne]
          cases s with | mk bn ss bs r ac =>
          cases t with | mk bn_t ss_t bs_t r_t ac_t =>
          cases u with | mk bn_u ss_u bs_u r_u ac_u =>
          cases ss with | mk si sb sp =>
          cases bs with | mk bi bb bp =>
          cases ss_t with | mk si_t sb_t sp_t =>
          cases bs_t with | mk bi_t bb_t bp_t =>
          cases ss_u with | mk si_u sb_u sp_u =>
          cases bs_u with | mk bi_u bb_u bp_u =>
          simp_all [accrueSide_block]
      · have hneS : s.supplyState.speed ≠ a := hsa
        obtain ⟨hidxS, hblkS, hspdS⟩ := hdiffS hneS
        have ht_bn : t.blockNumber = s.blockNumber := hbn
        have ht_ac : t.accts = s.accts := haccts
        by_cases hsb : t.borrowState.speed = b
        · have hu : u = t := hsameB hsb
          have hteq : t.borrowState.speed = s.borrowState.speed := congrArg Side.speed hbs
          have hsb_s : s.borrowState.speed = b := by rw [← hteq, hsb]
          rw [if_neg hneS, if_pos hsb_s]
          cases s with | mk bn ss bs r ac =>
          cases t with | mk bn_t ss_t bs_t r_t ac_t =>
          cases u with | mk bn_u ss_u bs_u r_u ac_u =>
          cases ss with | mk si sb sp =>
          cases bs with | mk bi bb bp =>
          cases ss_t with | mk si_t sb_t sp_t =>
          cases bs_t with | mk bi_t bb_t bp_t =>
          cases ss_u with | mk si_u sb_u sp_u =>
          cases bs_u with | mk bi_u bb_u bp_u =>
          simp_all [accrueSide_block]
        · obtain ⟨hidxB, hblkB, hspdB⟩ := hdiffB hsb
          have hteq : t.borrowState.speed = s.borrowState.speed := congrArg Side.speed hbs
          have hneB : s.borrowState.speed ≠ b := by rw [← hteq]; exact hsb
          have htot : totalBorrows t = totalBorrows s := by
            have := haccts
            simp [totalBorrows] at this ⊢
            rw [this]
          rw [if_neg hneS, if_neg hneB]
          cases s with | mk bn ss bs r ac =>
          cases t with | mk bn_t ss_t bs_t r_t ac_t =>
          cases u with | mk bn_u ss_u bs_u r_u ac_u =>
          cases ss with | mk si sb sp =>
          cases ss_t with | mk si_t sb_t sp_t =>
          cases ss_u with | mk si_u sb_u sp_u =>
          cases bs with | mk bi bb bp =>
          cases bs_t with | mk bi_t bb_t bp_t =>
          cases bs_u with | mk bi_u bb_u bp_u =>
          simp_all [accrueSide_block]

theorem req_calls_succeed       : CallsSucceed comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
