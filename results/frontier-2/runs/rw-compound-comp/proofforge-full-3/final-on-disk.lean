import CompRewards.Spec
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Index
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Seq
import ProofForgeFin.Ledger
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

/-- The index scale is positive. -/
theorem ds_pos : 0 < doubleScale := by
  unfold doubleScale
  exact Nat.pow_pos (by decide)

/-- The two names for 1e36 agree. -/
theorem init_eq_ds : compInitialIndex = doubleScale := rfl

/-- The deployed checkpoint rule is the specified start. -/
theorem start_eq_sup (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0 <;> simp [h0]

/-- The deployed checkpoint rule is the specified start (borrow side). -/
theorem start_eq_bor (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0 <;> simp [h0]

/-- The specified start is the library's `firstStart`. -/
theorem accrualStart_eq_firstStart (recorded index : Nat) :
    accrualStart recorded index =
      ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex recorded index := by
  unfold accrualStart ProofForgeFin.DeFi.Rewards.firstStart
  rfl

/-- The supply index never decreases. -/
theorem accrueSide_le_sup (s : St) :
    s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- The borrow index never decreases. -/
theorem accrueSide_le_bor (s : St) :
    s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- `updateCompSupplyIndex` brings the supply side up to date. -/
theorem updSup_eq {s : St} (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have e : subChecked s.blockNumber s.supplyState.block
      = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompSupplyIndex
  rw [e]
  unfold accrueSide
  by_cases h1 : 0 < s.blockNumber - s.supplyState.block
  · by_cases h2 : 0 < s.supplyState.speed
    · by_cases h3 : 0 < totalSupply s
      · simp [h1, h2, h3, fraction]
      · simp [h1, h2, h3]
    · simp [h1, h2]
  · have hb : s.supplyState.block = s.blockNumber := by omega
    have g1 : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) :=
      fun hcon => h1 hcon.1
    have g2 : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
        0 < totalSupply s) := fun hcon => h1 hcon.1
    simp only [g1, h1, g2, ↓reduceIte]
    obtain ⟨bn, sup, bor, res, accts⟩ := s
    obtain ⟨idx, blk, spd⟩ := sup
    simp only at hb
    subst hb
    rfl

/-- `updateCompSupplyIndex` fails exactly when the side block is ahead. -/
theorem updSup_none {s : St} (h : ¬ s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s = none := by
  have e : subChecked s.blockNumber s.supplyState.block = none := by
    unfold subChecked
    simp [h]
  unfold updateCompSupplyIndex
  rw [e]

/-- `updateCompBorrowIndex` brings the borrow side up to date. -/
theorem updBor_eq {s : St} (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have e : subChecked s.blockNumber s.borrowState.block
      = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [h]
  unfold updateCompBorrowIndex
  rw [e]
  unfold accrueSide
  by_cases h1 : 0 < s.blockNumber - s.borrowState.block
  · by_cases h2 : 0 < s.borrowState.speed
    · by_cases h3 : 0 < totalBorrows s
      · simp [h1, h2, h3, fraction]
      · simp [h1, h2, h3]
    · simp [h1, h2]
  · have hb : s.borrowState.block = s.blockNumber := by omega
    have g1 : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) :=
      fun hcon => h1 hcon.1
    have g2 : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
        0 < totalBorrows s) := fun hcon => h1 hcon.1
    simp only [g1, h1, g2, ↓reduceIte]
    obtain ⟨bn, sup, bor, res, accts⟩ := s
    obtain ⟨idx, blk, spd⟩ := bor
    simp only at hb
    subst hb
    rfl

/-- `updateCompBorrowIndex` fails exactly when the side block is ahead. -/
theorem updBor_none {s : St} (h : ¬ s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s = none := by
  have e : subChecked s.blockNumber s.borrowState.block = none := by
    unfold subChecked
    simp [h]
  unfold updateCompBorrowIndex
  rw [e]

/-- Two pointwise updates that agree on the updated account give the same list. -/
theorem modify_congr {α : Type} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ i => rfl
  | cons a l ih =>
    cases i with
    | zero =>
      have h' : f a = g a := h
      show f a :: l = g a :: l
      rw [h']
    | succ i =>
      have h' : f (l.getD i d) = g (l.getD i d) := h
      show a :: l.modify i f = a :: l.modify i g
      rw [ih _ h']

/-- `distributeSupplierComp` succeeds with the specified crediting when the start is set. -/
theorem distSup_some_eq {s : St} {who : Account}
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hs := start_eq_sup s who
  unfold distributeSupplierComp
  simp only [hs]
  have esub : subChecked s.supplyState.index
        (accrualStart (s.acct who).supplierIndex s.supplyState.index) =
        some (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) := by
    unfold subChecked
    simp [h]
  rw [esub]
  simp only []
  unfold St.withAcct mulDouble creditFor
  have hmod : s.accts.modify who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) / doubleScale }) = s.accts.modify who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) / doubleScale }) := by
    apply modify_congr _ _ _ _ noAcct
    rfl
  rw [hmod]

/-- `distributeSupplierComp` meets its specification on success. -/
theorem distSup_eq {s : St} {who : Account} {s' : St}
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index
      ≤ s.supplyState.index
  · have e := distSup_some_eq hle
    rw [e] at h
    cases h
    exact ⟨hle, rfl⟩
  · have esub : subChecked s.supplyState.index
        (accrualStart (s.acct who).supplierIndex s.supplyState.index) = none := by
      unfold subChecked
      simp [hle]
    have hs := start_eq_sup s who
    unfold distributeSupplierComp at h
    simp only [hs] at h
    rw [esub] at h
    simp only [] at h
    cases h

/-- `distributeBorrowerComp` succeeds with the specified crediting when the start is set. -/
theorem distBor_some_eq {s : St} {who : Account}
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hs := start_eq_bor s who
  unfold distributeBorrowerComp
  simp only [hs]
  have esub : subChecked s.borrowState.index
        (accrualStart (s.acct who).borrowerIndex s.borrowState.index) =
        some (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) := by
    unfold subChecked
    simp [h]
  rw [esub]
  simp only []
  unfold St.withAcct mulDouble creditFor
  have hmod : s.accts.modify who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) / doubleScale }) = s.accts.modify who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index) / doubleScale }) := by
    apply modify_congr _ _ _ _ noAcct
    rfl
  rw [hmod]

/-- `distributeBorrowerComp` meets its specification on success. -/
theorem distBor_eq {s : St} {who : Account} {s' : St}
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index
      ≤ s.borrowState.index
  · have e := distBor_some_eq hle
    rw [e] at h
    cases h
    exact ⟨hle, rfl⟩
  · have esub : subChecked s.borrowState.index
        (accrualStart (s.acct who).borrowerIndex s.borrowState.index) = none := by
      unfold subChecked
      simp [hle]
    have hs := start_eq_bor s who
    unfold distributeBorrowerComp at h
    simp only [hs] at h
    rw [esub] at h
    simp only [] at h
    cases h

/-- The supply start never lies above the index when the recorded index does not. -/
theorem start_le_sup {s : St} {who : Account}
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  rw [accrualStart_eq_firstStart]
  exact ProofForgeFin.DeFi.Rewards.firstStart_le_index compInitialIndex h

/-- The borrow start never lies above the index when the recorded index does not. -/
theorem start_le_bor {s : St} {who : Account}
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  rw [accrualStart_eq_firstStart]
  exact ProofForgeFin.DeFi.Rewards.firstStart_le_index compInitialIndex h

/-- An account's recorded supply index is set when the account is known. -/
theorem rec_le_sup {s : St} {who : Account}
    (hmem : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm' | heq
  · exact hmem _ hm'
  · have e : St.acct s who = noAcct := heq
    rw [e]
    exact Nat.zero_le _

/-- An account's recorded borrow index is set when the account is known. -/
theorem rec_le_bor {s : St} {who : Account}
    (hmem : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm' | heq
  · exact hmem _ hm'
  · have e : St.acct s who = noAcct := heq
    rw [e]
    exact Nat.zero_le _

/-- The specified payment is the implemented one. -/
theorem grant_eq (s : St) (who : Account) : grant s who = grantCompInternal s who := by
  unfold grant grantCompInternal
  simp only []
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · have hc' : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve := hc
    simp only [hc, hc', ↓reduceIte]
    have hmod : s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) = s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) := by
      apply modify_congr _ _ _ _ noAcct
      rfl
    simp only [hmod]
  · have hc' : ¬ ((s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve) := hc
    simp only [hc, hc', ↓reduceIte]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · rw [updSup_eq hb] at h
    unfold Bind.bind at h
    obtain ⟨hle, hs'⟩ := distSup_eq h
    exact ⟨hb, hle, hs'⟩
  · rw [updSup_none hb] at h
    unfold Bind.bind at h
    cases h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · rw [updBor_eq hb] at h
    unfold Bind.bind at h
    obtain ⟨hle, hs'⟩ := distBor_eq h
    exact ⟨hb, hle, hs'⟩
  · rw [updBor_none hb] at h
    unfold Bind.bind at h
    cases h

theorem setSup_eq {s : St} {a : Nat} {t : St} (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t.borrowState = s.borrowState ∧ t.blockNumber = s.blockNumber ∧ t.accts = s.accts ∧
    t.reserve = s.reserve ∧
    t.supplyState = (if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) := by
  simp only [setSupplySpeed] at h
  by_cases ha : s.supplyState.speed ≠ a
  · simp [ha] at h
    cases eu : updateCompSupplyIndex s with
    | none => simp [eu] at h
    | some t1 =>
      simp [eu] at h
      cases h
      have hb : s.supplyState.block ≤ s.blockNumber := by
        by_cases hbb : s.supplyState.block ≤ s.blockNumber
        · exact hbb
        · simp [updSup_none hbb] at eu
      have e1' : t1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
        rw [updSup_eq hb] at eu
        cases eu
        rfl
      rw [e1'] at *
      refine ⟨fun _ => hb, rfl, rfl, rfl, rfl, ?_⟩
      rw [if_neg ha]
  · have heq : s.supplyState.speed = a := by
      by_cases heq : s.supplyState.speed = a
      · exact heq
      · exact absurd heq ha
    simp [heq] at h
    cases h
    refine ⟨fun hcon => absurd hcon ha, rfl, rfl, rfl, rfl, ?_⟩
    simp [heq]

theorem setBor_eq {s : St} {b : Nat} {t : St} (h : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t.supplyState = s.supplyState ∧ t.blockNumber = s.blockNumber ∧ t.accts = s.accts ∧
    t.reserve = s.reserve ∧
    t.borrowState = (if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) := by
  simp only [setBorrowSpeed] at h
  by_cases hb2 : s.borrowState.speed ≠ b
  · simp [hb2] at h
    cases eu : updateCompBorrowIndex s with
    | none => simp [eu] at h
    | some t1 =>
      simp [eu] at h
      cases h
      have hb : s.borrowState.block ≤ s.blockNumber := by
        by_cases hbb : s.borrowState.block ≤ s.blockNumber
        · exact hbb
        · simp [updBor_none hbb] at eu
      have e1' : t1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
        rw [updBor_eq hb] at eu
        cases eu
        rfl
      rw [e1'] at *
      refine ⟨fun _ => hb, rfl, rfl, rfl, rfl, ?_⟩
      rw [if_neg hb2]
  · simp [hb2] at h
    cases h
    refine ⟨fun hcon => absurd hcon hb2, rfl, rfl, rfl, rfl, ?_⟩
    simp [hb2]

/-- A borrow-side settlement for `who` keeps `who`'s supply checkpoint. -/
theorem supplierIndex_borrow_settle (l : List Acct) (i : Nat) (IDX : Nat) (G : Acct → Nat) :
    (((l.modify i fun a => { a with borrowerIndex := IDX, accrued := a.accrued + G a }).getD i noAcct).supplierIndex = (l.getD i noAcct).supplierIndex) := by
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases hc : i = i ∧ i < l.length
  · rw [if_pos hc]
  · rw [if_neg hc]

/-- States with equal fields over an updated base are equal. -/
theorem st_eq_upd {s s' : St} {SUP BOR : Side}
    (hbn : s'.blockNumber = s.blockNumber) (hsup : s'.supplyState = SUP)
    (hbor : s'.borrowState = BOR) (hres : s'.reserve = s.reserve)
    (hac : s'.accts = s.accts) :
    s' = { s with supplyState := SUP, borrowState := BOR } := by
  obtain ⟨bn', sup', bor', res', accts'⟩ := s'
  obtain ⟨bn, sup, bor, res, accts⟩ := s
  simp only [] at hbn hsup hbor hres hac ⊢
  rw [hbn, hsup, hbor, hres, hac]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  obtain ⟨hsup, hbor, hmem⟩ := hc
  have hsup_all : ∀ who, (s.acct who).supplierIndex ≤ s.supplyState.index :=
    fun who => rec_le_sup (fun a ha => (hmem a ha).1)
  have hbor_all : ∀ who, (s.acct who).borrowerIndex ≤ s.borrowState.index :=
    fun who => rec_le_bor (fun a ha => (hmem a ha).2)
  cases c with
  | supplyHook who =>
    simp only [comptroller] at ⊢
    cases eu : updateCompSupplyIndex s with
    | none => rw [updSup_eq hsup] at eu; cases eu
    | some t1 =>
      simp [eu] at ⊢
      have e1' : t1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
        rw [updSup_eq hsup] at eu
        cases eu
        rfl
      have hrec : accrualStart (t1.acct who).supplierIndex t1.supplyState.index
          ≤ t1.supplyState.index := by
        rw [e1']
        exact start_le_sup (Nat.le_trans (hsup_all who) (accrueSide_le_sup s))
      rw [distSup_some_eq hrec] at ⊢
      rfl
  | borrowHook who =>
    simp only [comptroller] at ⊢
    cases eu : updateCompBorrowIndex s with
    | none => rw [updBor_eq hbor] at eu; cases eu
    | some t1 =>
      simp [eu] at ⊢
      have e1' : t1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
        rw [updBor_eq hbor] at eu
        cases eu
        rfl
      have hrec : accrualStart (t1.acct who).borrowerIndex t1.borrowState.index
          ≤ t1.borrowState.index := by
        rw [e1']
        exact start_le_bor (Nat.le_trans (hbor_all who) (accrueSide_le_bor s))
      rw [distBor_some_eq hrec] at ⊢
      rfl
  | claim who =>
    simp only [comptroller, claimComp] at ⊢
    cases e1 : updateCompBorrowIndex s with
    | none => rw [updBor_eq hbor] at e1; cases e1
    | some t1 =>
      simp [e1] at ⊢
      have e1' : t1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
        rw [updBor_eq hbor] at e1
        cases e1
        rfl
      cases e2 : distributeBorrowerComp t1 who with
      | none =>
        have hrec : accrualStart (t1.acct who).borrowerIndex t1.borrowState.index
            ≤ t1.borrowState.index := by
          rw [e1']
          exact start_le_bor (Nat.le_trans (hbor_all who) (accrueSide_le_bor s))
        rw [distBor_some_eq hrec] at e2
        cases e2
      | some t2 =>
        simp [e2] at ⊢
        obtain ⟨hleB, ht2⟩ := distBor_eq e2
        rw [e1'] at ht2
        cases e3 : updateCompSupplyIndex t2 with
        | none =>
          have hs : t2.supplyState.block ≤ t2.blockNumber := by rw [ht2]; exact hsup
          rw [updSup_eq hs] at e3
          cases e3
        | some t3 =>
          simp [e3] at ⊢
          have e3' : t3 = { t2 with supplyState := accrueSide t2.supplyState t2.blockNumber (totalSupply t2) } := by
            have hs : t2.supplyState.block ≤ t2.blockNumber := by rw [ht2]; exact hsup
            rw [updSup_eq hs] at e3
            cases e3
            rfl
          cases e4 : distributeSupplierComp t3 who with
          | none =>
            have hrec : accrualStart (t3.acct who).supplierIndex t3.supplyState.index
                ≤ t3.supplyState.index := by
              rw [e3']
              have hrec0 : (t2.acct who).supplierIndex ≤
                  (accrueSide t2.supplyState t2.blockNumber (totalSupply t2)).index := by
                have h1 : (t2.acct who).supplierIndex ≤ t2.supplyState.index := by
                  have e1 : (t2.acct who).supplierIndex = (s.acct who).supplierIndex := by
                    rw [ht2]
                    exact supplierIndex_borrow_settle _ who _ _
                  have e2 : t2.supplyState.index = s.supplyState.index := by rw [ht2]
                  rw [e1, e2]
                  exact hsup_all who
                exact Nat.le_trans h1 (accrueSide_le_sup t2)
              exact start_le_sup hrec0
            rw [distSup_some_eq hrec] at e4
            cases e4
          | some t4 => simp [e4] at ⊢
  | setSpeeds a b =>
    simp only [comptroller, setCompSpeedInternal] at ⊢
    cases es : setSupplySpeed s a with
    | none =>
      by_cases ha : s.supplyState.speed = a
      · have hs1 : setSupplySpeed s a = some s := by simp [setSupplySpeed, ha]
        rw [hs1] at es
        cases es
      · have eu : updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := updSup_eq hsup
        have hs1 : setSupplySpeed s a ≠ none := by simp [setSupplySpeed, ha, eu]
        exact absurd es hs1
    | some t =>
      simp [es] at ⊢
      cases eb : setBorrowSpeed t b with
      | none =>
        obtain ⟨hs1, tbor, tblk, taccts, tres, tsup⟩ := setSup_eq es
        by_cases hb2 : t.borrowState.speed = b
        · have hs2 : setBorrowSpeed t b = some t := by simp [setBorrowSpeed, hb2]
          rw [hs2] at eb
          cases eb
        · have hb : t.borrowState.block ≤ t.blockNumber := by rw [tbor, tblk]; exact hbor
          have eu : updateCompBorrowIndex t = some { t with borrowState := accrueSide t.borrowState t.blockNumber (totalBorrows t) } := updBor_eq hb
          have hs2 : setBorrowSpeed t b ≠ none := by simp [setBorrowSpeed, hb2, eu]
          exact absurd eb hs2
      | some t2 => simp [eb] at ⊢
theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  have hbB : s.borrowState.block ≤ s.blockNumber := by
    by_cases hbb : s.borrowState.block ≤ s.blockNumber
    · exact hbb
    · simp [updBor_none hbb] at h
  cases e1 : updateCompBorrowIndex s with
  | none => simp [e1] at h
  | some t1 =>
    simp [e1] at h
    have e1' : t1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      rw [updBor_eq hbB] at e1
      cases e1
      rfl
    cases e2 : distributeBorrowerComp t1 who with
    | none => simp [e2] at h
    | some t2 =>
      simp [e2] at h
      obtain ⟨hleB, ht2⟩ := distBor_eq e2
      rw [e1'] at hleB ht2
      have hsup : s.supplyState.block ≤ s.blockNumber := by
        by_cases hss : s.supplyState.block ≤ s.blockNumber
        · exact hss
        · have hn : updateCompSupplyIndex t2 = none := updSup_none (by rw [ht2]; exact hss)
          simp [hn] at h
      have hs : t2.supplyState.block ≤ t2.blockNumber := by rw [ht2]; exact hsup
      cases e3 : updateCompSupplyIndex t2 with
      | none => simp [e3] at h
      | some t3 =>
        simp [e3] at h
        have e3' : t3 = { t2 with supplyState := accrueSide t2.supplyState t2.blockNumber (totalSupply t2) } := by
          rw [updSup_eq hs] at e3
          cases e3
          rfl
        cases e4 : distributeSupplierComp t3 who with
        | none => simp [e4] at h
        | some t4 =>
          simp [e4] at h
          obtain ⟨hleS, ht4⟩ := distSup_eq e4
          rw [e3'] at hleS ht4
          cases h
          exact ⟨t2, t4, ⟨hbB, hleB, ht2⟩, ⟨hs, hleS, ht4⟩, (grant_eq t4 who).symm⟩
theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller, setCompSpeedInternal] at h
  cases es : setSupplySpeed s a with
  | none => simp [es] at h
  | some t =>
    simp [es] at h
    obtain ⟨hs1, tbor, tblk, taccts, tres, tsup⟩ := setSup_eq es
    obtain ⟨hb1, ssup, sblk, saccts, sres, sbor⟩ := setBor_eq h
    refine ⟨hs1, ?_, ?_⟩
    · intro hne
      have hne' : t.borrowState.speed ≠ b := by rw [tbor]; exact hne
      have hbb := hb1 hne'
      rw [tbor, tblk] at hbb
      exact hbb
    · have ebor : (if t.borrowState.speed = b then t.borrowState
          else { accrueSide t.borrowState t.blockNumber (totalBorrows t) with speed := b }) =
          (if s.borrowState.speed = b then s.borrowState
          else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) := by
        unfold totalBorrows
        rw [tbor, tblk, taccts]
      rw [ebor] at sbor
      have hbn : s'.blockNumber = s.blockNumber := by rw [sblk, tblk]
      have hsup : s'.supplyState = (if s.supplyState.speed = a then s.supplyState
          else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) := by
        rw [ssup, tsup]
      have hac : s'.accts = s.accts := by rw [saccts, taccts]
      have hres : s'.reserve = s.reserve := by rw [sres, tres]
      exact st_eq_upd hbn hsup sbor hres hac
/-- Supply emission not yet in the index. -/
def unidxS (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- Borrow emission not yet in the index. -/
def unidxB (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- Potential term of an account at indices `sI`, `bI`. -/
def acctTerm (a : Acct) (sI bI : Nat) : Nat :=
  (a.accrued + a.wallet) * doubleScale
  + a.supply * (sI - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex sI)
  + a.borrow * (bI - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex bI)

/-- Global potential: credited rewards at scale plus pending plus unindexed. -/
def pot (s : St) : Nat :=
  (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum
  + doubleScale * (unidxS s + unidxB s)

/-- Per-account potential of `who`. -/
def potTo (s : St) (who : Account) : Nat :=
  acctTerm (s.acct who) s.supplyState.index s.borrowState.index
  + doubleScale * (if 0 < (s.acct who).supply then unidxS s else 0)
  + doubleScale * (if 0 < (s.acct who).borrow then unidxB s else 0)

/-- An update always stamps the current block. -/
theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split <;> rfl

/-- An update keeps the speed. -/
theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split <;> rfl

/-- The supply update is covered by the unindexed emission. -/
theorem covered_supply (s : St) :
    ProofForgeFin.Accumulator.Covered (totalSupply s) (doubleScale * unidxS s)
      s.supplyState.index (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold ProofForgeFin.Accumulator.Covered
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < totalSupply s
  · have eA : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
        s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed *
        doubleScale / totalSupply s := by
      unfold accrueSide
      simp [hc]
    rw [eA]
    refine ⟨Nat.le_add_right _ _, ?_⟩
    have h2 : s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed *
        doubleScale / totalSupply s - s.supplyState.index
        = (s.blockNumber - s.supplyState.block) * s.supplyState.speed *
        doubleScale / totalSupply s := Nat.add_sub_cancel_left _ _
    rw [h2]
    calc totalSupply s * (((s.blockNumber - s.supplyState.block) * s.supplyState.speed *
          doubleScale) / totalSupply s)
        = (((s.blockNumber - s.supplyState.block) * s.supplyState.speed *
          doubleScale) / totalSupply s) * totalSupply s := Nat.mul_comm _ _
      _ ≤ (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale :=
          Nat.div_mul_le_self _ _
      _ = doubleScale * unidxS s := by
          unfold unidxS
          ac_rfl
  · have eA : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
        s.supplyState.index := by
      unfold accrueSide
      simp [hc]
    rw [eA]
    refine ⟨Nat.le_refl _, ?_⟩
    have h0 : s.supplyState.index - s.supplyState.index = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_refl _)
    rw [h0, Nat.mul_zero]
    exact Nat.zero_le _

/-- The borrow update is covered by the unindexed emission. -/
theorem covered_borrow (s : St) :
    ProofForgeFin.Accumulator.Covered (totalBorrows s) (doubleScale * unidxB s)
      s.borrowState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold ProofForgeFin.Accumulator.Covered
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < totalBorrows s
  · have eA : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
        s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed *
        doubleScale / totalBorrows s := by
      unfold accrueSide
      simp [hc]
    rw [eA]
    refine ⟨Nat.le_add_right _ _, ?_⟩
    have h2 : s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed *
        doubleScale / totalBorrows s - s.borrowState.index
        = (s.blockNumber - s.borrowState.block) * s.borrowState.speed *
        doubleScale / totalBorrows s := Nat.add_sub_cancel_left _ _
    rw [h2]
    calc totalBorrows s * (((s.blockNumber - s.borrowState.block) * s.borrowState.speed *
          doubleScale) / totalBorrows s)
        = (((s.blockNumber - s.borrowState.block) * s.borrowState.speed *
          doubleScale) / totalBorrows s) * totalBorrows s := Nat.mul_comm _ _
      _ ≤ (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale :=
          Nat.div_mul_le_self _ _
      _ = doubleScale * unidxB s := by
          unfold unidxB
          ac_rfl
  · have eA : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
        s.borrowState.index := by
      unfold accrueSide
      simp [hc]
    rw [eA]
    refine ⟨Nat.le_refl _, ?_⟩
    have h0 : s.borrowState.index - s.borrowState.index = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_refl _)
    rw [h0, Nat.mul_zero]
    exact Nat.zero_le _

/-- Settling the supply side never raises the term. -/
theorem term_settle_supply (x : Acct) (sI bI : Nat) :
    acctTerm { x with supplierIndex := sI, accrued := x.accrued + creditFor x.supply (accrualStart x.supplierIndex sI) sI } sI bI ≤ acctTerm x sI bI := by
  have heq := accrualStart_eq_firstStart x.supplierIndex sI
  have hpq : ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex x.supplierIndex sI
      ≤ accrualStart x.supplierIndex sI := by omega
  have hq' : sI ≤ ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex sI sI :=
    ProofForgeFin.Accumulator.le_firstStart_self compInitialIndex sI
  have h := ProofForgeFin.Accumulator.settle_scaled_le_of_le (one := doubleScale)
    (c := x.accrued + x.wallet) (u := x.supply) (i := sI)
    (p := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex x.supplierIndex sI)
    (q := accrualStart x.supplierIndex sI)
    (q' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex sI sI)
    hpq hq'
  have hnorm : x.accrued + x.supply * (sI - accrualStart x.supplierIndex sI) / doubleScale + x.wallet
      = (x.accrued + x.wallet) + x.supply * (sI - accrualStart x.supplierIndex sI) / doubleScale := by
    omega
  unfold acctTerm creditFor
  simp only []
  rw [hnorm]
  omega

/-- Settling the borrow side never raises the term. -/
theorem term_settle_borrow (x : Acct) (sI bI : Nat) :
    acctTerm { x with borrowerIndex := bI, accrued := x.accrued + creditFor x.borrow (accrualStart x.borrowerIndex bI) bI } sI bI ≤ acctTerm x sI bI := by
  have heq := accrualStart_eq_firstStart x.borrowerIndex bI
  have hpq : ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex x.borrowerIndex bI
      ≤ accrualStart x.borrowerIndex bI := by omega
  have hq' : bI ≤ ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex bI bI :=
    ProofForgeFin.Accumulator.le_firstStart_self compInitialIndex bI
  have h := ProofForgeFin.Accumulator.settle_scaled_le_of_le (one := doubleScale)
    (c := x.accrued + x.wallet) (u := x.borrow) (i := bI)
    (p := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex x.borrowerIndex bI)
    (q := accrualStart x.borrowerIndex bI)
    (q' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex bI bI)
    hpq hq'
  have hnorm : x.accrued + x.borrow * (bI - accrualStart x.borrowerIndex bI) / doubleScale + x.wallet
      = (x.accrued + x.wallet) + x.borrow * (bI - accrualStart x.borrowerIndex bI) / doubleScale := by
    omega
  unfold acctTerm creditFor
  simp only []
  rw [hnorm]
  omega

/-- A supply hook (accrue then settle) never raises the potential. -/
theorem pot_supply_distrib {s : St} {who : Account} {s' : St}
    (h : SupplyDistributed s who s') : pot s' ≤ pot s := by
  obtain ⟨hblock, hstart, rfl⟩ := h
  have hAblock : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber :=
    accrueSide_block _ _ _
  have hAle : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_le_sup s
  have ht : ∀ a ∈ s.accts, acctTerm a (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
        s.borrowState.index ≤
        acctTerm a s.supplyState.index s.borrowState.index +
        a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        s.supplyState.index) := by
    intro a ha
    have hmono := ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.supplierIndex hAle
    have hle := ProofForgeFin.Accumulator.owed_le_add (u := a.supply)
      (i := s.supplyState.index)
      (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (s := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex s.supplyState.index)
      (s' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      hmono
    unfold acctTerm
    omega
  have hU : (s.accts.map fun a => a.supply).sum *
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) +
        doubleScale * (0 + unidxB s) ≤ doubleScale * (unidxS s + unidxB s) := by
    have hb := ProofForgeFin.Accumulator.accrue_budget (one := doubleScale)
      (T := totalSupply s) (i := s.supplyState.index)
      (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (E := unidxS s) (V := unidxB s) (covered_supply s)
    unfold totalSupply at hb
    exact hb
  have hf : who < s.accts.length →
      (fun sI x => acctTerm x sI s.borrowState.index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
        ((fun a =>
          { a with
            supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
            accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) (s.accts.getD who noAcct)) ≤
      (fun sI x => acctTerm x sI s.borrowState.index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
        (s.accts.getD who noAcct) :=
    fun _ => term_settle_supply _ _ _
  have hpot := ProofForgeFin.Accumulator.pot_accrue_settle_le s.accts who
    (fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index })
    noAcct (fun sI x => acctTerm x sI s.borrowState.index) (fun a => a.supply) ht hU hf
  have eU : unidxS { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } = 0 := by
    unfold unidxS
    simp only []
    rw [hAblock, Nat.sub_eq_zero_of_le (Nat.le_refl _), Nat.zero_mul]
  have eUb : unidxB { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } = unidxB s := rfl
  have e1 : pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } =
      ((s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).map fun a => acctTerm a (accrueSide s.supplyState s.blockNumber (totalSupply s)).index s.borrowState.index).sum +
      doubleScale * (0 + unidxB s) := by
    unfold pot
    simp only []
    rw [eU, eUb]
  have e2 : pot s = (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum +
      doubleScale * (unidxS s + unidxB s) := rfl
  rw [e1, e2]
  exact hpot

/-- A borrow hook (accrue then settle) never raises the potential. -/
theorem pot_borrow_distrib {s : St} {who : Account} {s' : St}
    (h : BorrowDistributed s who s') : pot s' ≤ pot s := by
  obtain ⟨hblock, hstart, rfl⟩ := h
  have hAblock : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber :=
    accrueSide_block _ _ _
  have hAle : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    accrueSide_le_bor s
  have ht : ∀ a ∈ s.accts, acctTerm a s.supplyState.index
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        acctTerm a s.supplyState.index s.borrowState.index +
        a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        s.borrowState.index) := by
    intro a ha
    have hmono := ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.borrowerIndex hAle
    have hle := ProofForgeFin.Accumulator.owed_le_add (u := a.borrow)
      (i := s.borrowState.index)
      (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (s := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex s.borrowState.index)
      (s' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      hmono
    unfold acctTerm
    omega
  have hU : (s.accts.map fun a => a.borrow).sum *
        ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) +
        doubleScale * (unidxS s + 0) ≤ doubleScale * (unidxS s + unidxB s) := by
    have hb := ProofForgeFin.Accumulator.accrue_budget' (one := doubleScale)
      (T := totalBorrows s) (i := s.borrowState.index)
      (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (E := unidxB s) (V := unidxS s) (covered_borrow s)
    unfold totalBorrows at hb
    exact hb
  have hf : who < s.accts.length →
      (fun bI x => acctTerm x s.supplyState.index bI)
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
        ((fun a =>
          { a with
            borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
            accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) (s.accts.getD who noAcct)) ≤
      (fun bI x => acctTerm x s.supplyState.index bI)
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
        (s.accts.getD who noAcct) :=
    fun _ => term_settle_borrow _ _ _
  have hpot := ProofForgeFin.Accumulator.pot_accrue_settle_le s.accts who
    (fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index })
    noAcct (fun bI x => acctTerm x s.supplyState.index bI) (fun a => a.borrow) ht hU hf
  have eU : unidxB { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } = 0 := by
    unfold unidxB
    simp only []
    rw [hAblock, Nat.sub_eq_zero_of_le (Nat.le_refl _), Nat.zero_mul]
  have eUb : unidxS { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } = unidxS s := rfl
  have e1 : pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } =
      ((s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }).map fun a => acctTerm a s.supplyState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index).sum +
      doubleScale * (unidxS s + 0) := by
    unfold pot
    simp only []
    rw [eU, eUb]
  have e2 : pot s = (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum +
      doubleScale * (unidxS s + unidxB s) := rfl
  rw [e1, e2]
  exact hpot

/-- A supply accrue alone never raises the potential. -/
theorem pot_accrue_supply (s : St) :
    pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ pot s := by
  have hAblock : (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber :=
    accrueSide_block _ _ _
  have hAle : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_le_sup s
  have ht : ∀ a ∈ s.accts, acctTerm a (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
        s.borrowState.index ≤
        acctTerm a s.supplyState.index s.borrowState.index +
        a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        s.supplyState.index) := by
    intro a ha
    have hmono := ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.supplierIndex hAle
    have hle := ProofForgeFin.Accumulator.owed_le_add (u := a.supply)
      (i := s.supplyState.index)
      (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (s := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex s.supplyState.index)
      (s' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      hmono
    unfold acctTerm
    omega
  have hU : (s.accts.map fun a => a.supply).sum *
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) +
        doubleScale * (0 + unidxB s) ≤ doubleScale * (unidxS s + unidxB s) := by
    have hb := ProofForgeFin.Accumulator.accrue_budget (one := doubleScale)
      (T := totalSupply s) (i := s.supplyState.index)
      (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (E := unidxS s) (V := unidxB s) (covered_supply s)
    unfold totalSupply at hb
    exact hb
  have hpot := ProofForgeFin.Accumulator.pot_accrue_le s.accts
    (fun sI x => acctTerm x sI s.borrowState.index) (fun a => a.supply) ht hU
  have eU : unidxS { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } = 0 := by
    unfold unidxS
    simp only []
    rw [hAblock, Nat.sub_eq_zero_of_le (Nat.le_refl _), Nat.zero_mul]
  have eUb : unidxB { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } =
      unidxB s := rfl
  have e1 : pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } =
      (s.accts.map fun a => acctTerm a (accrueSide s.supplyState s.blockNumber (totalSupply s)).index s.borrowState.index).sum +
      doubleScale * (0 + unidxB s) := by
    unfold pot
    simp only []
    rw [eU, eUb]
  have e2 : pot s = (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum +
      doubleScale * (unidxS s + unidxB s) := rfl
  rw [e1, e2]
  exact hpot

/-- A borrow accrue alone never raises the potential. -/
theorem pot_accrue_borrow (s : St) :
    pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤ pot s := by
  have hAblock : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber :=
    accrueSide_block _ _ _
  have hAle : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    accrueSide_le_bor s
  have ht : ∀ a ∈ s.accts, acctTerm a s.supplyState.index
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        acctTerm a s.supplyState.index s.borrowState.index +
        a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
        s.borrowState.index) := by
    intro a ha
    have hmono := ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.borrowerIndex hAle
    have hle := ProofForgeFin.Accumulator.owed_le_add (u := a.borrow)
      (i := s.borrowState.index)
      (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (s := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex s.borrowState.index)
      (s' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      hmono
    unfold acctTerm
    omega
  have hU : (s.accts.map fun a => a.borrow).sum *
        ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) +
        doubleScale * (unidxS s + 0) ≤ doubleScale * (unidxS s + unidxB s) := by
    have hb := ProofForgeFin.Accumulator.accrue_budget' (one := doubleScale)
      (T := totalBorrows s) (i := s.borrowState.index)
      (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (E := unidxB s) (V := unidxS s) (covered_borrow s)
    unfold totalBorrows at hb
    exact hb
  have hpot := ProofForgeFin.Accumulator.pot_accrue_le s.accts
    (fun bI x => acctTerm x s.supplyState.index bI) (fun a => a.borrow) ht hU
  have eU : unidxB { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } = 0 := by
    unfold unidxB
    simp only []
    rw [hAblock, Nat.sub_eq_zero_of_le (Nat.le_refl _), Nat.zero_mul]
  have eUb : unidxS { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } =
      unidxS s := rfl
  have e1 : pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } =
      (s.accts.map fun a => acctTerm a s.supplyState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index).sum +
      doubleScale * (unidxS s + 0) := by
    unfold pot
    simp only []
    rw [eU, eUb]
  have e2 : pot s = (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum +
      doubleScale * (unidxS s + unidxB s) := rfl
  rw [e1, e2]
  exact hpot

/-- Paying out accrued COMP never raises the potential. -/
theorem pot_grant (s : St) (who : Account) : pot (grant s who) ≤ pot s := by
  unfold grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp [hc]
    have hterm : ∀ x, acctTerm ({ x with accrued := 0, wallet := x.wallet + x.accrued })
        s.supplyState.index s.borrowState.index = acctTerm x s.supplyState.index s.borrowState.index := by
      intro x
      unfold acctTerm
      simp only []
      have hc0 : (0 : Nat) + (x.wallet + x.accrued) = x.accrued + x.wallet := by omega
      rw [hc0]
    have hsum : ((s.accts.modify who fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }).map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum
        = (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum :=
      ProofForgeFin.Ledger.sum_map_modify_eq _ _ _ _ noAcct (fun _ => hterm _)
    unfold pot unidxS unidxB
    simp only []
    rw [hsum]
    exact Nat.le_refl _
  · simp [hc]

/-- An update with no time passed leaves the index. -/
theorem accrueSide_noop {sd : Side} {now total : Nat} (h : sd.block = now) :
    (accrueSide sd now total).index = sd.index := by
  unfold accrueSide
  have h0 : ¬ (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total) := by
    intro hc
    omega
  simp [h0]

/-- After a supply distribution, `who` is settled at the supply index. -/
theorem settled_supply_after {s : St} {who : Account} {s₁ : St}
    (h : SupplyDistributed s who s₁) (hm : who < s.accts.length) :
    (s₁.acct who).supplierIndex = s₁.supplyState.index := by
  obtain ⟨hblock, hstart, hs1⟩ := h
  rw [hs1, ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hm]

/-- After a borrow distribution, `who` is settled at the borrow index. -/
theorem settled_borrow_after {s : St} {who : Account} {s₁ : St}
    (h : BorrowDistributed s who s₁) (hm : who < s.accts.length) :
    (s₁.acct who).borrowerIndex = s₁.borrowState.index := by
  obtain ⟨hblock, hstart, hs1⟩ := h
  rw [hs1, ProofForgeFin.Ledger.getD_modify_self _ _ _ _ hm]

/-- Changing the supply of a settled account keeps its term. -/
theorem term_supply_units (x : Acct) (sI bI ns : Nat) (hset : x.supplierIndex = sI) :
    acctTerm ({ x with supply := ns }) sI bI = acctTerm x sI bI := by
  unfold acctTerm
  simp only []
  have hz : sI - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex sI sI = 0 :=
    Nat.sub_eq_zero_of_le (ProofForgeFin.Accumulator.le_firstStart_self compInitialIndex sI)
  rw [hset, hz, Nat.mul_zero, Nat.mul_zero]

/-- Changing the borrow of a settled account keeps its term. -/
theorem term_borrow_units (x : Acct) (sI bI nb : Nat) (hset : x.borrowerIndex = bI) :
    acctTerm ({ x with borrow := nb }) sI bI = acctTerm x sI bI := by
  unfold acctTerm
  simp only []
  have hz : bI - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex bI bI = 0 :=
    Nat.sub_eq_zero_of_le (ProofForgeFin.Accumulator.le_firstStart_self compInitialIndex bI)
  rw [hset, hz, Nat.mul_zero, Nat.mul_zero]

/-- Changing the supply of a settled account never raises the potential. -/
theorem pot_withAcct_supply (s : St) (who : Account) (ns : Nat)
    (hset : (s.acct who).supplierIndex = s.supplyState.index) :
    pot (s.withAcct who fun a => { a with supply := ns }) ≤ pot s := by
  have hmod : ((s.accts.modify who fun a => { a with supply := ns }).map fun a =>
      acctTerm a s.supplyState.index s.borrowState.index).sum ≤
      (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum := by
    apply ProofForgeFin.Ledger.sum_map_modify_le
    intro hw
    have hx : ((s.accts.getD who noAcct)).supplierIndex = s.supplyState.index := hset
    have e := term_supply_units (s.accts.getD who noAcct) s.supplyState.index s.borrowState.index ns hx
    exact Nat.le_of_eq e
  unfold pot St.withAcct unidxS unidxB
  simp only []
  exact Nat.add_le_add_right hmod _

/-- Changing the borrow of a settled account never raises the potential. -/
theorem pot_withAcct_borrow (s : St) (who : Account) (nb : Nat)
    (hset : (s.acct who).borrowerIndex = s.borrowState.index) :
    pot (s.withAcct who fun a => { a with borrow := nb }) ≤ pot s := by
  have hmod : ((s.accts.modify who fun a => { a with borrow := nb }).map fun a =>
      acctTerm a s.supplyState.index s.borrowState.index).sum ≤
      (s.accts.map fun a => acctTerm a s.supplyState.index s.borrowState.index).sum := by
    apply ProofForgeFin.Ledger.sum_map_modify_le
    intro hw
    have hx : ((s.accts.getD who noAcct)).borrowerIndex = s.borrowState.index := hset
    have e := term_borrow_units (s.accts.getD who noAcct) s.supplyState.index s.borrowState.index nb hx
    exact Nat.le_of_eq e
  unfold pot St.withAcct unidxS unidxB
  simp only []
  exact Nat.add_le_add_right hmod _

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
