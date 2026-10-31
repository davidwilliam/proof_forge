import CompRewards.Spec
import ProofForgeFin
/-!
Port of the COMP distribution of Compound's Comptroller as deployed by Proposal 62
(implementation 0x374ABb8cE19A73f2c4EFAd642bda76c797f19233, active on mainnet from block
13322798 to block 13382884). Source: compound-finance/compound-protocol, commit
f73b29373eb65cedf24896d7be46eed38435fc91, `contracts/Comptroller.sol`, byte-identical to the
verified source of the deployed implementation, and `contracts/ExponentialNoError.sol`.

* `updateCompSupplyIndex` (lines 1163 to 1177) and `updateCompBorrowIndex` (lines 1184 to 1198).
* `distributeSupplierComp` (lines 1205 to 1236) and `distributeBorrowerComp` (lines 1244 to 1275).
* `claimComp(holders, cTokens, true, true)` (lines 1320 to 1341) for one holder and one market,
  and `grantCompInternal` (lines 1350 to 1358).
* `setCompSpeedInternal` (lines 1130 to 1156).

The cToken's borrow index is taken as 1e18, so `div_(borrowBalanceStored, borrowIndex)` is the
account's borrow units. A `sub_` underflow or a `require` failure is `none`.
-/
namespace CompRewards

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
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
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

/-- `doubleScale` is positive. -/
theorem doubleScale_pos : 0 < doubleScale := by
  unfold doubleScale
  decide



/-- `accrualStart` is the library's `firstStart` at `compInitialIndex`. -/
theorem accrualStart_eq_firstStart (r i : Nat) :
    accrualStart r i =
      ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex r i := rfl

/-- `creditFor` is the library's `credit` at `doubleScale`. -/
theorem creditFor_eq_credit (u s i : Nat) :
    creditFor u s i =
      ProofForgeFin.DeFi.Rewards.credit doubleScale u s i := rfl

/-- `fraction` is the library's `indexDelta` at `doubleScale`. -/
theorem fraction_eq_indexDelta (e t : Nat) :
    fraction e t =
      ProofForgeFin.DeFi.Rewards.indexDelta doubleScale e t := rfl

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split <;> rfl

theorem accrueSide_index_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · show sd.index ≤ sd.index + _
    exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- Reading beyond the list gives the default. -/
theorem getD_eq_default_of_le {α : Type} (l : List α) (n : Nat) (d : α)
    (h : l.length ≤ n) : l.getD n d = d := by
  induction l generalizing n with
  | nil => simp [List.getD]
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ n => simp only [List.getD]; exact ih n (by simpa using h)

/-- Reading in bounds gives a member. -/
theorem getD_mem_of_lt {α : Type} (l : List α) (n : Nat) (d : α)
    (h : n < l.length) : l.getD n d ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => simp [List.getD]
    | succ n =>
      have e : (x :: xs).getD (n + 1) d = xs.getD n d := rfl
      rw [e]
      exact List.mem_cons_of_mem _ (ih n (by simpa using h))

/-- `modify` preserves length. -/
theorem length_modify {α : Type} (l : List α) (i : Nat) (f : α → α) :
    (l.modify i f).length = l.length := by
  simp

/-- Reading the modified position applies the function. -/
theorem getD_modify_self {α : Type} (l : List α) (i : Nat) (f : α → α) (d : α)
    (h : i < l.length) : (l.modify i f).getD i d = f (l.getD i d) := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [List.modify]
    | succ n => simp [List.modify]; exact ih n (by simpa using h)

/-- Reading elsewhere is unaffected by `modify`. -/
theorem getD_modify_ne {α : Type} (l : List α) (i w : Nat) (f : α → α) (d : α)
    (h : i ≠ w) : (l.modify i f).getD w d = l.getD w d := by
  induction l generalizing i w with
  | nil => simp [List.modify]
  | cons x xs ih =>
    cases i with
    | zero =>
      cases w with
      | zero => simp at h
      | succ w => simp [List.modify]
    | succ i =>
      cases w with
      | zero => simp [List.modify]
      | succ w => simp [List.modify]; exact ih i w (by simpa using h)

/-- Two `modify`s with functions agreeing at the read position agree. -/
theorem modify_congr {α : Type} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : f (l.getD i d) = g (l.getD i d)) :
    l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil => simp [List.modify_nil]
  | cons x xs ih =>
    cases i with
    | zero =>
      have hx : f x = g x := by
        have e : (x :: xs).getD 0 d = x := by simp [List.getD]
        rw [e] at h
        exact h
      simp [List.modify, hx]
    | succ n =>
      have e : (x :: xs).getD (n + 1) d = xs.getD n d := rfl
      rw [e] at h
      have ih' := ih n h
      simp [ih']

/-- `map` after `modify` when the mapped function is preserved. -/
theorem map_modify_eq_of_pres {α β : Type} (l : List α) (i : Nat) (f : α → α)
    (g : α → β) (h : ∀ a, g (f a) = g a) :
    (l.modify i f).map g = l.map g := by
  induction l generalizing i with
  | nil => simp [List.modify_nil]
  | cons x xs ih =>
    cases i with
    | zero => simp [List.modify, h]
    | succ n =>
      have ih' := ih n
      simp [ih']

theorem updateSupply_eq {s : St} (h : s.supplyState.block ≤ s.blockNumber) : updateCompSupplyIndex s =
    some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hsub : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    rw [if_pos h]
  simp only [updateCompSupplyIndex, hsub]
  by_cases hd : s.blockNumber - s.supplyState.block > 0
  · by_cases hs : s.supplyState.speed > 0
    · by_cases ht : totalSupply s > 0
      · rw [if_pos ⟨hd, hs⟩]
        have hacc : (if totalSupply s > 0
            then fraction ((s.blockNumber - s.supplyState.block) *
              s.supplyState.speed) (totalSupply s) else 0)
            = (s.blockNumber - s.supplyState.block) * s.supplyState.speed *
              doubleScale / totalSupply s := by
          rw [if_pos ht]
          rfl
        rw [hacc]
        unfold accrueSide
        rw [if_pos ⟨hd, hs, ht⟩]
      · rw [if_pos ⟨hd, hs⟩, if_neg ht]
        unfold accrueSide
        rw [if_neg (fun hcon => ht hcon.2.2), Nat.add_zero]
    · have hcon : ¬ (s.blockNumber - s.supplyState.block > 0 ∧
        s.supplyState.speed > 0) := fun h => hs h.2
      rw [if_neg hcon, if_pos hd]
      unfold accrueSide
      rw [if_neg (fun hcon2 => hs hcon2.2.1)]
  · have heq : s.blockNumber = s.supplyState.block := by omega
    have hcon : ¬ (s.blockNumber - s.supplyState.block > 0 ∧
      s.supplyState.speed > 0) := fun h => hd h.1
    rw [if_neg hcon, if_neg hd]
    have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) =
        s.supplyState := by
      unfold accrueSide
      rw [if_neg (fun hcon2 => hd hcon2.1), heq]
    rw [hacc]

theorem updateBorrow_eq {s : St} (h : s.borrowState.block ≤ s.blockNumber) : updateCompBorrowIndex s =
    some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hsub : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    rw [if_pos h]
  simp only [updateCompBorrowIndex, hsub]
  by_cases hd : s.blockNumber - s.borrowState.block > 0
  · by_cases hs : s.borrowState.speed > 0
    · by_cases ht : totalBorrows s > 0
      · rw [if_pos ⟨hd, hs⟩]
        have hacc : (if totalBorrows s > 0
            then fraction ((s.blockNumber - s.borrowState.block) *
              s.borrowState.speed) (totalBorrows s) else 0)
            = (s.blockNumber - s.borrowState.block) * s.borrowState.speed *
              doubleScale / totalBorrows s := by
          rw [if_pos ht]
          rfl
        rw [hacc]
        unfold accrueSide
        rw [if_pos ⟨hd, hs, ht⟩]
      · rw [if_pos ⟨hd, hs⟩, if_neg ht]
        unfold accrueSide
        rw [if_neg (fun hcon => ht hcon.2.2), Nat.add_zero]
    · have hcon : ¬ (s.blockNumber - s.borrowState.block > 0 ∧
        s.borrowState.speed > 0) := fun h => hs h.2
      rw [if_neg hcon, if_pos hd]
      unfold accrueSide
      rw [if_neg (fun hcon2 => hs hcon2.2.1)]
  · have heq : s.blockNumber = s.borrowState.block := by omega
    have hcon : ¬ (s.blockNumber - s.borrowState.block > 0 ∧
      s.borrowState.speed > 0) := fun h => hd h.1
    rw [if_neg hcon, if_neg hd]
    have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) =
        s.borrowState := by
      unfold accrueSide
      rw [if_neg (fun hcon2 => hd hcon2.1), heq]
    rw [hacc]

theorem updateSupply_none {s : St} (h : s.blockNumber < s.supplyState.block) :
    updateCompSupplyIndex s = none := by
  unfold updateCompSupplyIndex subChecked
  rw [if_neg (by omega)]

theorem updateBorrow_none {s : St} (h : s.blockNumber < s.borrowState.block) :
    updateCompBorrowIndex s = none := by
  unfold updateCompBorrowIndex subChecked
  rw [if_neg (by omega)]

theorem updateSupply_some_block {s : St} {t : St}
    (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  by_cases hc : s.supplyState.block ≤ s.blockNumber
  · exact hc
  · have hc' : s.blockNumber < s.supplyState.block := by omega
    rw [updateSupply_none hc'] at h
    simp at h

theorem updateBorrow_some_block {s : St} {t : St}
    (h : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber := by
  by_cases hc : s.borrowState.block ≤ s.blockNumber
  · exact hc
  · have hc' : s.blockNumber < s.borrowState.block := by omega
    rw [updateBorrow_none hc'] at h
    simp at h

theorem startSupply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
      else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0
  · by_cases hi : compInitialIndex ≤ s.supplyState.index
    · simp [hr, hi]
    · simp [hr, hi]
  · simp [hr]

theorem startBorrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
      else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0
  · by_cases hi : compInitialIndex ≤ s.borrowState.index
    · simp [hr, hi]
    · simp [hr, hi]
  · simp [hr]

theorem distributeSupply_some {s : St} {who : Account} {s' : St}
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart := startSupply_eq s who
  simp only [distributeSupplierComp, hstart] at h
  unfold subChecked at h
  split at h
  · next h1 =>
    have hnone : (none : Option St) = some s' := h
    simp at hnone
  · next h2 h3 =>
    by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
        s.supplyState.index
    · rw [if_pos hle] at h3
      have hde : s.supplyState.index - accrualStart (s.acct who).supplierIndex
          s.supplyState.index = h2 := by
        simpa using h3
      have hs' : s.withAcct who (fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + mulDouble (s.acct who).supply h2 }) = s' := by
        simpa using h
      have hagree : mulDouble (s.acct who).supply h2 = creditFor (s.acct who).supply
          (accrualStart (s.acct who).supplierIndex s.supplyState.index) s.supplyState.index := by
        unfold mulDouble creditFor
        rw [hde]
      have hfg : (fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + mulDouble (s.acct who).supply h2 }) (s.acct who) =
          (fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })
          (s.acct who) := by
        dsimp only
        rw [hagree]
      refine ⟨hle, ?_⟩
      rw [← hs']
      simp only [St.withAcct]
      congr 1
      exact modify_congr s.accts who _ _ noAcct hfg
    · exfalso
      rw [if_neg hle] at h3
      simp at h3

theorem distributeBorrow_some {s : St} {who : Account} {s' : St}
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := s.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart := startBorrow_eq s who
  simp only [distributeBorrowerComp, hstart] at h
  unfold subChecked at h
  split at h
  · next h1 =>
    have hnone : (none : Option St) = some s' := h
    simp at hnone
  · next h2 h3 =>
    by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
        s.borrowState.index
    · rw [if_pos hle] at h3
      have hde : s.borrowState.index - accrualStart (s.acct who).borrowerIndex
          s.borrowState.index = h2 := by
        simpa using h3
      have hs' : s.withAcct who (fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + mulDouble (s.acct who).borrow h2 }) = s' := by
        simpa using h
      have hagree : mulDouble (s.acct who).borrow h2 = creditFor (s.acct who).borrow
          (accrualStart (s.acct who).borrowerIndex s.borrowState.index) s.borrowState.index := by
        unfold mulDouble creditFor
        rw [hde]
      have hfg : (fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + mulDouble (s.acct who).borrow h2 }) (s.acct who) =
          (fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })
          (s.acct who) := by
        dsimp only
        rw [hagree]
      refine ⟨hle, ?_⟩
      rw [← hs']
      simp only [St.withAcct]
      congr 1
      exact modify_congr s.accts who _ _ noAcct hfg
    · exfalso
      rw [if_neg hle] at h3
      simp at h3

theorem grant_eq (s : St) (who : Account) :
    grant s who = grantCompInternal s who := rfl

theorem distributeBorrow_keep_supplyState {s who s'}
    (h : distributeBorrowerComp s who = some s') :
    s'.supplyState = s.supplyState := by
  obtain ⟨-, hdist⟩ := distributeBorrow_some h
  rw [hdist]

theorem distributeBorrow_keep_block {s who s'}
    (h : distributeBorrowerComp s who = some s') :
    s'.blockNumber = s.blockNumber := by
  obtain ⟨-, hdist⟩ := distributeBorrow_some h
  rw [hdist]

theorem distributeBorrow_acct_supplier {s who s'}
    (h : distributeBorrowerComp s who = some s') :
    (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by
  obtain ⟨-, hdist⟩ := distributeBorrow_some h
  have e1 : s'.acct who = (s.accts.modify who (fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })).getD
      who noAcct := by
    rw [hdist]
    simp only [St.withAcct, St.acct]
  rw [e1]
  exact acct_proj_pres_after_modify _ _ _ _ _ (fun a => rfl)

theorem distributeSupply_keep_borrowState {s who s'}
    (h : distributeSupplierComp s who = some s') :
    s'.borrowState = s.borrowState := by
  obtain ⟨-, hdist⟩ := distributeSupply_some h
  rw [hdist]

theorem distributeSupply_keep_block {s who s'}
    (h : distributeSupplierComp s who = some s') :
    s'.blockNumber = s.blockNumber := by
  obtain ⟨-, hdist⟩ := distributeSupply_some h
  rw [hdist]

theorem withAcct_acct_self (s : St) (who : Account) (f : Acct → Acct)
    (h : who < s.accts.length) :
    (s.withAcct who f).acct who = f (s.acct who) := by
  simp only [St.withAcct, St.acct]
  exact getD_modify_self _ _ _ _ h

theorem withAcct_acct_ne (s : St) (i who : Account) (f : Acct → Acct) (h : i ≠ who) :
    (s.withAcct i f).acct who = s.acct who := by
  simp only [St.withAcct, St.acct]
  exact getD_modify_ne _ _ _ _ _ h

theorem acct_proj_pres_after_modify (l : List Acct) (i who : Nat) (f : Acct → Acct)
    (proj : Acct → Nat) (hpres : ∀ a, proj (f a) = proj a) :
    proj ((l.modify i f).getD who noAcct) = proj (l.getD who noAcct) := by
  by_cases heq : i = who
  · subst heq
    by_cases hlen : who < l.length
    · rw [getD_modify_self _ _ _ _ hlen]
      exact hpres _
    · rw [getD_eq_default_of_le _ _ _ (Nat.not_lt.mp hlen)]
      rw [getD_eq_default_of_le _ _ _ (Nat.not_lt.mp hlen)]
  · rw [getD_modify_ne _ _ _ _ _ heq]

theorem acct_supplier_le_of_consistent (s : St)
    (hc : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  by_cases h : who < s.accts.length
  · exact hc _ (getD_mem_of_lt _ _ _ h)
  · have e : s.acct who = noAcct := by
      simp only [St.acct]
      exact getD_eq_default_of_le s.accts who noAcct (Nat.not_lt.mp h)
    rw [e]
    exact Nat.zero_le _

theorem acct_borrower_le_of_consistent (s : St)
    (hc : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  by_cases h : who < s.accts.length
  · exact hc _ (getD_mem_of_lt _ _ _ h)
  · have e : s.acct who = noAcct := by
      simp only [St.acct]
      exact getD_eq_default_of_le s.accts who noAcct (Nat.not_lt.mp h)
    rw [e]
    exact Nat.zero_le _

theorem distributeSupply_exists {s : St} {who : Account}
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by
  have hstart := startSupply_eq s who
  have e : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
      some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    unfold subChecked
    rw [if_pos hle]
  simp only [distributeSupplierComp, hstart, e]
  exact ⟨_, rfl⟩

theorem distributeBorrow_exists {s : St} {who : Account}
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by
  have hstart := startBorrow_eq s who
  have e : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
      some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    unfold subChecked
    rw [if_pos hle]
  simp only [distributeBorrowerComp, hstart, e]
  exact ⟨_, rfl⟩

theorem comptroller_supplyHook (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind fun mid => distributeSupplierComp mid who := rfl

theorem comptroller_borrowHook (s : St) (who : Account) :
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind fun mid => distributeBorrowerComp mid who := rfl

theorem comptroller_claim (s : St) (who : Account) :
    comptroller s (.claim who) = claimComp s who := rfl

theorem comptroller_setSpeeds (s : St) (a b : Nat) :
    comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl

theorem isSome_bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : α} {z : β}
    (hx : x = some y) (hf : f y = some z) : (x.bind f).isSome := by
  rw [hx]
  have hbind : Option.bind (some y) f = some z := hf
  rw [hbind]
  rfl

theorem supplyDist_of_parts {s mid s' : St} {who : Account}
    (eU : updateCompSupplyIndex s = some mid)
    (eD : distributeSupplierComp mid who = some s') :
    SupplyDistributed s who s' := by
  have hblock : s.supplyState.block ≤ s.blockNumber := updateSupply_some_block eU
  have hmid : mid = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
    have eU' := updateSupply_eq hblock
    rw [eU'] at eU
    simpa using eU.symm
  obtain ⟨hle, hdist⟩ := distributeSupply_some eD
  rw [hmid] at hle hdist
  exact ⟨hblock, hle, hdist⟩

theorem borrowDist_of_parts {s mid s' : St} {who : Account}
    (eU : updateCompBorrowIndex s = some mid)
    (eD : distributeBorrowerComp mid who = some s') :
    BorrowDistributed s who s' := by
  have hblock : s.borrowState.block ≤ s.blockNumber := updateBorrow_some_block eU
  have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
    have eU' := updateBorrow_eq hblock
    rw [eU'] at eU
    simpa using eU.symm
  obtain ⟨hle, hdist⟩ := distributeBorrow_some eD
  rw [hmid] at hle hdist
  exact ⟨hblock, hle, hdist⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  have hblockS : s.supplyState.block ≤ s.blockNumber := hc.1
  have hblockB : s.borrowState.block ≤ s.blockNumber := hc.2.1
  have hmemS : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
    fun a ha => (hc.2.2 a ha).1
  have hmemB : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
    fun a ha => (hc.2.2 a ha).2
  cases c with
  | supplyHook who =>
    have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index :=
      acct_supplier_le_of_consistent s hmemS who
    have hle : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [accrualStart_eq_firstStart]
      exact ProofForgeFin.DeFi.Rewards.firstStart_le_index _
        (Nat.le_trans hrec (accrueSide_index_le _ _ _))
    rw [comptroller_supplyHook, updateSupply_eq hblockS]
    obtain ⟨d, hd⟩ := distributeSupply_exists (s := { s with supplyState :=
      accrueSide s.supplyState s.blockNumber (totalSupply s) }) hle
    exact isSome_bind_some (updateSupply_eq hblockS) hd
  | borrowHook who =>
    have hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
      acct_borrower_le_of_consistent s hmemB who
    have hle : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [accrualStart_eq_firstStart]
      exact ProofForgeFin.DeFi.Rewards.firstStart_le_index _
        (Nat.le_trans hrec (accrueSide_index_le _ _ _))
    rw [comptroller_borrowHook, updateBorrow_eq hblockB]
    obtain ⟨d, hd⟩ := distributeBorrow_exists (s := { s with borrowState :=
      accrueSide s.borrowState s.blockNumber (totalBorrows s) }) hle
    exact isSome_bind_some (updateBorrow_eq hblockB) hd
  | claim who =>
    have hrecS : (s.acct who).supplierIndex ≤ s.supplyState.index :=
      acct_supplier_le_of_consistent s hmemS who
    have hrecB : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
      acct_borrower_le_of_consistent s hmemB who
    have hupdB := updateBorrow_eq hblockB
    have hleB : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [accrualStart_eq_firstStart]
      exact ProofForgeFin.DeFi.Rewards.firstStart_le_index _
        (Nat.le_trans hrecB (accrueSide_index_le _ _ _))
    obtain ⟨b1, hb1⟩ := distributeBorrow_exists (s := { s with borrowState :=
      accrueSide s.borrowState s.blockNumber (totalBorrows s) }) hleB
    have hupdS : updateCompSupplyIndex b1 = some { b1 with supplyState :=
        accrueSide b1.supplyState b1.blockNumber (totalSupply b1) } := by
      apply updateSupply_eq
      show b1.supplyState.block ≤ b1.blockNumber
      have e1 : b1.supplyState = s.supplyState := by rw [hb1]
      have e2 : b1.blockNumber = s.blockNumber := by rw [hb1]
      rw [e1, e2]
      exact hblockS
    have hleS : accrualStart (b1.acct who).supplierIndex
        (accrueSide b1.supplyState b1.blockNumber (totalSupply b1)).index ≤
        (accrueSide b1.supplyState b1.blockNumber (totalSupply b1)).index := by
      rw [accrualStart_eq_firstStart]
      apply ProofForgeFin.DeFi.Rewards.firstStart_le_index
      have hr1 : (b1.acct who).supplierIndex ≤ b1.supplyState.index := by
        have e1 : b1.supplyState = s.supplyState := by rw [hb1]
        have e3 : (b1.acct who).supplierIndex = (s.acct who).supplierIndex := by
          rw [hb1]
        rw [e3, e1]
        exact hrecS
      exact Nat.le_trans hr1 (accrueSide_index_le _ _ _)
    obtain ⟨s1, hs1⟩ := distributeSupply_exists (s := { b1 with supplyState :=
      accrueSide b1.supplyState b1.blockNumber (totalSupply b1) }) hleS
    rw [comptroller_claim]
    have hc1 : claimComp s who = some (grantCompInternal s1 who) := by
      unfold claimComp
      rw [hupdB, hb1, hupdS, hs1]
      rfl
    rw [hc1, Option.isSome_some]
  | setSpeeds a b =>
    have hss : (setSupplySpeed s a).isSome := by
      unfold setSupplySpeed
      by_cases heq : s.supplyState.speed = a
      · have hc : ¬ s.supplyState.speed ≠ a := fun hcon => heq (hcon rfl)
        rw [if_neg hc]
        rfl
      · rw [if_pos heq, updateSupply_eq hblockS]
        rfl
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hss
    have hsb : (setBorrowSpeed t b).isSome := by
      unfold setBorrowSpeed
      by_cases heq : t.borrowState.speed = b
      · have hc : ¬ t.borrowState.speed ≠ b := fun hcon => heq (hcon rfl)
        rw [if_neg hc]
        rfl
      · have hblock : t.borrowState.block ≤ t.blockNumber := by
          have e1 : t.borrowState = s.borrowState := by
            rw [ht]
            unfold setSupplySpeed
            by_cases heq2 : s.supplyState.speed = a
            · have hc2 : ¬ s.supplyState.speed ≠ a := fun hcon => heq2 (hcon rfl)
              rw [if_neg hc2]
            · rw [if_pos heq2, updateSupply_eq hblockS]
          have e2 : t.blockNumber = s.blockNumber := by
            rw [ht]
            unfold setSupplySpeed
            by_cases heq2 : s.supplyState.speed = a
            · have hc2 : ¬ s.supplyState.speed ≠ a := fun hcon => heq2 (hcon rfl)
              rw [if_neg hc2]
            · rw [if_pos heq2, updateSupply_eq hblockS]
          rw [e1, e2]
          exact hblockB
        rw [if_pos heq, updateBorrow_eq hblock]
        rfl
    rw [comptroller_setSpeeds]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hsb
    have hset : setCompSpeedInternal s a b = some u := by
      unfold setCompSpeedInternal
      rw [ht, hu]
      rfl
    rw [hset, Option.isSome_some]

theorem req_supply_hook         : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook         : BorrowHookEffects comptroller := sorry
theorem req_claim               : ClaimEffects comptroller := sorry
theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
