import CompRewards.Spec
import ProofForgeFin.Accumulator.Market

open ProofForgeFin.Accumulator.Market
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

open ProofForgeFin.Accumulator (catchUp) in
/-- The supply/borrow index update computes `catchUp` at scale `doubleScale`. -/
theorem accrue_idx (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  split
  · rfl
  · rfl

/-- Bringing a side up to date sets its block to now. -/
theorem accrue_blk (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

/-- Bringing a side up to date keeps its speed. -/
theorem accrue_spd (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split
  · rfl
  · rfl

/-- The fixed checkpoint logic agrees with the safe start `firstStart`. -/
theorem start_eq (r idx : Nat) :
    (if r = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else r) =
      ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex r idx := by
  unfold ProofForgeFin.DeFi.Rewards.firstStart
  by_cases hr : r = 0
  · subst hr
    simp only [true_and]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi]
    · simp [hi]
  · simp [hr]

/-- The fixed checkpoint logic agrees with the specified `accrualStart`. -/
theorem codeStart_eq (r idx : Nat) :
    (if r = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else r) =
      accrualStart r idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp [hr]
  · simp [hr]

/-- Two ways to change account `i` agree when they agree on its record. -/
theorem modify_congr {α : Type} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    rw [ProofForgeFin.Ledger.modify_of_length_le _ _ (Nat.zero_le _),
      ProofForgeFin.Ledger.modify_of_length_le _ _ (Nat.zero_le _)]
  | cons a l ih =>
    cases i with
    | zero => simpa using h
    | succ i =>
      have h2 : f (l.getD i d) = g (l.getD i d) := h
      rw [List.modify_succ_cons, List.modify_succ_cons, ih _ h2]

/-- A successful supply-index update leaves the block bound behind. -/
theorem updSup_some (s : St) (s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  split at h
  · simp at h
  · rename_i heq
    by_cases hc : s.supplyState.block ≤ s.blockNumber
    · exact hc
    · simp [hc] at heq

/-- A successful supply-index update brings the side up to date. -/
theorem updSup_eq (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with
        supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex accrueSide totalSupply subChecked fraction doubleScale
  simp only [h, ↓reduceIte]
  by_cases hd : s.blockNumber - s.supplyState.block > 0
  · by_cases hs : s.supplyState.speed > 0
    · by_cases ht : (s.accts.map Acct.supply).sum > 0
      · simp_all
      · simp_all [Nat.add_zero]
    · simp_all
  · have hb : s.blockNumber - s.supplyState.block = 0 := by omega
    have heq : s.supplyState.block = s.blockNumber := by omega
    cases s with
    | mk bn ss bs r al =>
      simp_all only
      cases ss with
      | mk i b sp =>
        simp_all only [heq]
        simp

/-- A successful borrow-index update leaves the block bound behind. -/
theorem updBor_some (s : St) (s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  split at h
  · simp at h
  · rename_i heq
    by_cases hc : s.borrowState.block ≤ s.blockNumber
    · exact hc
    · simp [hc] at heq

/-- A successful borrow-index update brings the side up to date. -/
theorem updBor_eq (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with
        borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex accrueSide totalBorrows subChecked fraction doubleScale
  simp only [h, ↓reduceIte]
  by_cases hd : s.blockNumber - s.borrowState.block > 0
  · by_cases hs : s.borrowState.speed > 0
    · by_cases ht : (s.accts.map Acct.borrow).sum > 0
      · simp_all
      · simp_all [Nat.add_zero]
    · simp_all
  · have hb : s.blockNumber - s.borrowState.block = 0 := by omega
    have heq : s.borrowState.block = s.blockNumber := by omega
    cases s with
    | mk bn ss bs r al =>
      simp_all only
      cases bs with
      | mk i b sp =>
        simp_all only [heq]
        simp

/-- A successful supplier distribution leaves the start bound behind. -/
theorem distSup_some (s : St) (who : Nat) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
  have hcode := codeStart_eq (s.acct who).supplierIndex s.supplyState.index
  unfold distributeSupplierComp subChecked at h
  dsimp only at h
  rw [hcode] at h
  by_cases hc : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · exact hc
  · simp [hc] at h

/-- A successful supplier distribution credits the account. -/
theorem distSup_eq (s : St) (who : Nat)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some { s with accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + (s.acct who).supply *
          (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) /
          doubleScale } } := by
  unfold distributeSupplierComp St.withAcct subChecked mulDouble
  dsimp only
  rw [codeStart_eq]
  simp only [hle, ↓reduceIte]

/-- A successful borrower distribution leaves the start bound behind. -/
theorem distBor_some (s : St) (who : Nat) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
  have hcode := codeStart_eq (s.acct who).borrowerIndex s.borrowState.index
  unfold distributeBorrowerComp subChecked at h
  dsimp only at h
  rw [hcode] at h
  by_cases hc : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · exact hc
  · simp [hc] at h

/-- A successful borrower distribution credits the account. -/
theorem distBor_eq (s : St) (who : Nat)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some { s with accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + (s.acct who).borrow *
          (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) /
          doubleScale } } := by
  unfold distributeBorrowerComp St.withAcct subChecked mulDouble
  dsimp only
  rw [codeStart_eq]
  simp only [hle, ↓reduceIte]

/-- A successful supplier distribution in the specified shape. -/
theorem distSup_spec (s : St) (who : Nat)
    (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some { s with accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index)
          s.supplyState.index } } := by
  rw [distSup_eq s who hle]
  congr 1
  congr 1
  exact modify_congr _ _ _ _ noAcct rfl

/-- A successful borrower distribution in the specified shape. -/
theorem distBor_spec (s : St) (who : Nat)
    (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some { s with accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } } := by
  rw [distBor_eq s who hle]
  congr 1
  congr 1
  exact modify_congr _ _ _ _ noAcct rfl

/-- An index update never lowers the index. -/
theorem accrue_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- In a consistent state every recorded supply index is at most the market's. -/
theorem supRec_le (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hc.2.2 _ hm).1
  · rw [hm]
    exact Nat.zero_le _

/-- In a consistent state every recorded borrow index is at most the market's. -/
theorem borRec_le (s : St) (who : Nat) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (hc.2.2 _ hm).2
  · rw [hm]
    exact Nat.zero_le _

/-- An account's supply start never lies above a later index. -/
theorem supStart_le (rec idx idx' : Nat) (hrec : rec ≤ idx) (hle : idx ≤ idx') :
    accrualStart rec idx' ≤ idx' := by
  unfold accrualStart
  by_cases hr : rec = 0
  · simp only [hr, ↓reduceIte]
    split
    · omega
    · omega
  · simp only [hr, ↓reduceIte]
    omega

/-- An account's borrow start never lies above a later index. -/
theorem borStart_le (rec idx idx' : Nat) (hrec : rec ≤ idx) (hle : idx ≤ idx') :
    accrualStart rec idx' ≤ idx' := by
  unfold accrualStart
  by_cases hr : rec = 0
  · simp only [hr, ↓reduceIte]
    split
    · omega
    · omega
  · simp only [hr, ↓reduceIte]
    omega

/-- The specified start is the library's safe start. -/
theorem accrualStart_eq_firstStart (r idx : Nat) :
    accrualStart r idx = ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex r idx := by
  rw [← codeStart_eq]
  exact start_eq _ _

/-- Reading the Comptroller state as a two-sided reward market. -/
def M : ProofForgeFin.Accumulator.Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock := fun s => ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed,
    s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts := St.accts
  dflt := noAcct
  units₁ := Acct.supply
  units₂ := Acct.borrow
  rec₁ := Acct.supplierIndex
  rec₂ := Acct.borrowerIndex
  credited := fun a => a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

/-- A supply hook preserves consistency. -/
theorem consistent_supplyHook (s : St) (who : Nat) (s' : St) (hc : Consistent s)
    (h : comptroller s (.supplyHook who) = some s') : Consistent s' := by
  unfold comptroller at h
  dsimp only at h
  cases hm : updateCompSupplyIndex s with
  | none => simp [hm] at h
  | some s1 =>
    simp [hm] at h
    have hb := updSup_some s s1 hm
    have hs1 : s1 = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by
      have e := updSup_eq s hb
      rw [hm] at e
      simpa using e
    have hd := distSup_some s1 who s' h
    have heq := distSup_spec s1 who hd
    have e2 : s' = {s1 with accts := s1.accts.modify who fun a =>
      { a with
        supplierIndex := s1.supplyState.index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index)
          s1.supplyState.index } } :=
      (Option.some_inj.mp (heq.symm.trans h)).symm
    rw [hs1] at e2
    dsimp only at e2
    have hidx : s'.supplyState.index =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [e2]
    have hbor : s'.borrowState.index = s.borrowState.index := by rw [e2]
    have hsup_blk : s'.supplyState.block = s.blockNumber := by rw [e2]; exact accrue_blk _ _ _
    have hnum : s'.blockNumber = s.blockNumber := by rw [e2]
    have hbor_blk : s'.borrowState.block = s.borrowState.block := by rw [e2]
    have hac : s'.accts = s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } := by rw [e2]
    unfold Consistent
    refine ⟨?_, ?_, ?_⟩
    · rw [hsup_blk, hnum]
      exact Nat.le_refl _
    · rw [hbor_blk, hnum]
      exact hc.2.1
    · rw [hac]
      refine ProofForgeFin.DeFi.Rewards.forall_mem_modify ?_ ?_
      · intro a ha
        have h1 := (hc.2.2 a ha).1
        have h2 := (hc.2.2 a ha).2
        refine ⟨?_, ?_⟩
        · rw [hidx]
          exact Nat.le_trans h1 (accrue_ge _ _ _)
        · rw [hbor]
          exact h2
      · intro a ha
        have h2 := (hc.2.2 a ha).2
        refine ⟨?_, ?_⟩
        · rw [hidx]
          exact Nat.le_refl _
        · rw [hbor]
          exact h2

/-- A borrow hook preserves consistency. -/
theorem consistent_borrowHook (s : St) (who : Nat) (s' : St) (hc : Consistent s)
    (h : comptroller s (.borrowHook who) = some s') : Consistent s' := by
  unfold comptroller at h
  dsimp only at h
  cases hm : updateCompBorrowIndex s with
  | none => simp [hm] at h
  | some s1 =>
    simp [hm] at h
    have hb := updBor_some s s1 hm
    have hs1 : s1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by
      have e := updBor_eq s hb
      rw [hm] at e
      simpa using e
    have hd := distBor_some s1 who s' h
    have heq := distBor_spec s1 who hd
    have e2 : s' = {s1 with accts := s1.accts.modify who fun a =>
      { a with
        borrowerIndex := s1.borrowState.index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index)
          s1.borrowState.index } } :=
      (Option.some_inj.mp (heq.symm.trans h)).symm
    rw [hs1] at e2
    dsimp only at e2
    have hsup : s'.supplyState.index = s.supplyState.index := by rw [e2]
    have hidx : s'.borrowState.index =
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [e2]
    have hsup_blk : s'.supplyState.block = s.supplyState.block := by rw [e2]
    have hnum : s'.blockNumber = s.blockNumber := by rw [e2]
    have hbor_blk : s'.borrowState.block = s.blockNumber := by rw [e2]; exact accrue_blk _ _ _
    have hac : s'.accts = s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } := by rw [e2]
    unfold Consistent
    refine ⟨?_, ?_, ?_⟩
    · rw [hsup_blk, hnum]
      exact hc.1
    · rw [hbor_blk, hnum]
      exact Nat.le_refl _
    · rw [hac]
      refine ProofForgeFin.DeFi.Rewards.forall_mem_modify ?_ ?_
      · intro a ha
        have h1 := (hc.2.2 a ha).1
        have h2 := (hc.2.2 a ha).2
        refine ⟨?_, ?_⟩
        · rw [hsup]
          exact h1
        · rw [hidx]
          exact Nat.le_trans h2 (accrue_ge _ _ _)
      · intro a ha
        have h1 := (hc.2.2 a ha).1
        refine ⟨?_, ?_⟩
        · rw [hsup]
          exact h1
        · rw [hidx]
          exact Nat.le_refl _

/-- A successful supply-speed change accrues at the old speed. -/
theorem setSupply_char (s : St) (a : Nat) (t : St) (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases hsa : s.supplyState.speed = a
  · simp [hsa] at h
    refine ⟨fun hne => absurd hsa hne, ?_⟩
    simpa [hsa] using h.symm
  · simp [hsa] at h
    obtain ⟨u, hu, rfl⟩ := h
    have hb := updSup_some s u hu
    have eu := updSup_eq s hb
    rw [hu] at eu
    have hu_eq : u = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by
      simpa using eu
    refine ⟨fun _ => hb, ?_⟩
    simp only [hsa, ↓reduceIte]
    rw [hu_eq]

/-- A successful borrow-speed change accrues at the old speed. -/
theorem setBor_char (s : St) (b : Nat) (t : St) (h : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases hsb : s.borrowState.speed = b
  · simp [hsb] at h
    refine ⟨fun hne => absurd hsb hne, ?_⟩
    simpa [hsb] using h.symm
  · simp [hsb] at h
    obtain ⟨u, hu, rfl⟩ := h
    have hb := updBor_some s u hu
    have eu := updBor_eq s hb
    rw [hu] at eu
    have hu_eq : u = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by
      simpa using eu
    refine ⟨fun _ => hb, ?_⟩
    simp only [hsb, ↓reduceIte]
    rw [hu_eq]

/-- The payment matches the specified `grant`. -/
theorem grant_eq (s : St) (who : Nat) :
    grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  dsimp only
  simp only [gt_iff_lt]
  by_cases hc : 0 < (s.accts.getD who noAcct).accrued ∧ (s.accts.getD who noAcct).accrued ≤ s.reserve
  · simp only [hc, ↓reduceIte]
    have hac : s.accts.modify who (fun a => {a with accrued := (0 : Nat), wallet := a.wallet + (s.accts.getD who noAcct).accrued}) = s.accts.modify who (fun a => {a with accrued := (0 : Nat), wallet := a.wallet + a.accrued}) := modify_congr _ _ _ _ noAcct rfl
    rw [hac]
  · simp only [hc, ↓reduceIte]

/-- A supply update and distribution is a settlement on side one. -/
theorem settle_supply (s : St) (who : Nat) (s' s1 : St)
    (hm : updateCompSupplyIndex s = some s1) (hd : distributeSupplierComp s1 who = some s') :
    M.Settle₁ who s s' := by
  have hb := updSup_some s s1 hm
  have hs1 : s1 = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by
    have e := updSup_eq s hb
    rw [hm] at e
    simpa using e
  have hle := distSup_some s1 who s' hd
  have heq := distSup_spec s1 who hle
  have e2 : s' = {s1 with accts := s1.accts.modify who fun a =>
    { a with
      supplierIndex := s1.supplyState.index,
      accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index)
        s1.supplyState.index } } :=
    (Option.some_inj.mp (heq.symm.trans hd)).symm
  rw [hs1] at e2
  dsimp only at e2
  have hidx' : (M.clock s').index₁ =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    have hidx : s'.supplyState.index =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [e2]
    exact hidx
  refine ⟨?_, fun a =>
    { a with
      supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
      accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }, ?_, ?_⟩
  · rw [e2]
    unfold M ProofForgeFin.Accumulator.Clock.catchUp₁ ProofForgeFin.Accumulator.Market.total₁ totalSupply
    dsimp only
    rw [accrue_idx, accrue_blk, accrue_spd]
  · rw [e2]
    rfl
  · rw [hidx']
    intro a
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · show (a.accrued + creditFor a.supply (accrualStart a.supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) + a.wallet ≤
        (a.accrued + a.wallet) + a.supply *
          ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
            ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale
      rw [accrualStart_eq_firstStart]
      unfold creditFor
      omega

/-- A borrow hook is a settlement on side two. -/
theorem settle_borrow (s : St) (who : Nat) (s' s1 : St)
    (hm : updateCompBorrowIndex s = some s1) (hd : distributeBorrowerComp s1 who = some s') :
    M.Settle₂ who s s' := by
  have hb := updBor_some s s1 hm
  have hs1 : s1 = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by
    have e := updBor_eq s hb
    rw [hm] at e
    simpa using e
  have hle := distBor_some s1 who s' hd
  have heq := distBor_spec s1 who hle
  have e2 : s' = {s1 with accts := s1.accts.modify who fun a =>
    { a with
      borrowerIndex := s1.borrowState.index,
      accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index)
        s1.borrowState.index } } :=
    (Option.some_inj.mp (heq.symm.trans hd)).symm
  rw [hs1] at e2
  dsimp only at e2
  have hidx' : (M.clock s').index₂ =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    have hidx : s'.borrowState.index =
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [e2]
    exact hidx
  refine ⟨?_, fun a =>
    { a with
      borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
      accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }, ?_, ?_⟩
    · rw [e2]
      unfold M ProofForgeFin.Accumulator.Clock.catchUp₂ ProofForgeFin.Accumulator.Market.total₂ totalBorrows
      dsimp only
      rw [accrue_idx, accrue_blk, accrue_spd]
    · rw [e2]
      rfl
    · rw [hidx']
      intro a
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · rfl
      · rfl
      · show (a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) + a.wallet ≤
          (a.accrued + a.wallet) + a.borrow *
            ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
              ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale
        rw [accrualStart_eq_firstStart]
        unfold creditFor
        omega

/-- A supply hook is a settlement on side one. -/
theorem settle_supply_hook (s : St) (who : Nat) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') : M.Settle₁ who s s' := by
  unfold comptroller at h
  dsimp only at h
  cases hm : updateCompSupplyIndex s with
  | none => simp [hm] at h
  | some s1 =>
    simp [hm] at h
    exact settle_supply s who s' s1 hm h

/-- A borrow hook is a settlement on side two. -/
theorem settle_borrow_hook (s : St) (who : Nat) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') : M.Settle₂ who s s' := by
  unfold comptroller at h
  dsimp only at h
  cases hm : updateCompBorrowIndex s with
  | none => simp [hm] at h
  | some s1 =>
    simp [hm] at h
    exact settle_borrow s who s' s1 hm h

/-- Every operation is a market action. -/
theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (a : Op) :
    M.Act sp s (nextSpeeds sp a) (emittedBy sp a) (exec comptroller s a) := by
  cases a with
  | mint who x =>
    unfold exec
    dsimp only
    split
    · rename_i hlen
      split
      · rename_i hhook
        refine Act.moves (Settle₁.then_adjust (settle_supply_hook _ _ _ hhook) rfl rfl ?_ ?_)
        · intro b
          exact ⟨Nat.le_refl _, rfl, rfl⟩
        · intro b
          rfl
      · rename_i hhook
        exact Act.moves (Reach.refl s)
    · rename_i hlen
      exact Act.moves (Reach.refl s)
  | redeem who x =>
    unfold exec
    dsimp only
    split
    · rename_i hlen
      split
      · rename_i hhook
        split
        · rename_i hle
          refine Act.moves (Settle₁.then_adjust (settle_supply_hook _ _ _ hhook) rfl rfl ?_ ?_)
          · intro b
            exact ⟨Nat.le_refl _, rfl, rfl⟩
          · intro b
            rfl
        · rename_i hle
          exact Act.moves (Reach.refl s)
      · rename_i hhook
        exact Act.moves (Reach.refl s)
    · rename_i hlen
      exact Act.moves (Reach.refl s)
  | transfer src dst x =>
    unfold exec
    dsimp only
    split
    · rename_i hlen
      split
      · rename_i h1
        split
        · rename_i h2
          split
          · rename_i hle
            refine Act.moves (Settle₁.transfer (settle_supply_hook _ _ _ h1)
              (settle_supply_hook _ _ _ h2) rfl rfl ?_ ?_ ?_ ?_)
            · intro b
              exact ⟨Nat.le_refl _, rfl, rfl⟩
            · intro b
              exact ⟨Nat.le_refl _, rfl, rfl⟩
            · intro b
              rfl
            · intro b
              rfl
          · rename_i hle
            exact Act.moves (Reach.refl s)
        · rename_i h2
          exact Act.moves (Reach.refl s)
      · rename_i h1
        exact Act.moves (Reach.refl s)
    · rename_i hlen
      exact Act.moves (Reach.refl s)
  | borrow who x =>
    unfold exec
    dsimp only
    split
    · rename_i hlen
      split
      · rename_i hhook
        refine Act.moves (Settle₂.then_adjust (settle_borrow_hook _ _ _ hhook) rfl rfl ?_ ?_)
        · intro b
          exact ⟨Nat.le_refl _, rfl, rfl⟩
        · intro b
          rfl
      · rename_i hhook
        exact Act.moves (Reach.refl s)
    · rename_i hlen
      exact Act.moves (Reach.refl s)
  | repay who x =>
    unfold exec
    dsimp only
    split
    · rename_i hlen
      split
      · rename_i hhook
        split
        · rename_i hle
          refine Act.moves (Settle₂.then_adjust (settle_borrow_hook _ _ _ hhook) rfl rfl ?_ ?_)
          · intro b
            exact ⟨Nat.le_refl _, rfl, rfl⟩
          · intro b
            rfl
        · rename_i hle
          exact Act.moves (Reach.refl s)
      · rename_i hhook
        exact Act.moves (Reach.refl s)
    · rename_i hlen
      exact Act.moves (Reach.refl s)
  | claim who => sorry
  | setSpeeds a b => sorry
  | advance k => sorry
  | drip x => sorry

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  cases c with
  | supplyHook who =>
    have e1 := updSup_eq s hc.1
    have hstart := supStart_le (s.acct who).supplierIndex s.supplyState.index
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
      (supRec_le s who hc) (accrue_ge _ _ _)
    have e2 := distSup_eq ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) who hstart
    obtain ⟨m, hm⟩ : ∃ m, distributeSupplierComp _ who = some m := ⟨_, e2⟩
    have hdone : comptroller s (.supplyHook who) = some m := by
      unfold comptroller
      dsimp only
      simp [e1, hm]
    rw [hdone]
    rfl
  | borrowHook who =>
    have e1 := updBor_eq s hc.2.1
    have hstart := borStart_le (s.acct who).borrowerIndex s.borrowState.index
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
      (borRec_le s who hc) (accrue_ge _ _ _)
    have e2 := distBor_eq ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) who hstart
    obtain ⟨m, hm⟩ : ∃ m, distributeBorrowerComp _ who = some m := ⟨_, e2⟩
    have hdone : comptroller s (.borrowHook who) = some m := by
      unfold comptroller
      dsimp only
      simp [e1, hm]
    rw [hdone]
    rfl
  | claim who =>
    have eB1 := updBor_eq s hc.2.1
    have hstartB := borStart_le (s.acct who).borrowerIndex s.borrowState.index
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
      (borRec_le s who hc) (accrue_ge _ _ _)
    have eB2 := distBor_eq ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) who hstartB
    obtain ⟨m1, hm1⟩ : ∃ m1, distributeBorrowerComp _ who = some m1 := ⟨_, eB2⟩
    have hbor : comptroller s (.borrowHook who) = some m1 := by
      unfold comptroller
      dsimp only
      simp [eB1, hm1]
    have hc1 : Consistent m1 := consistent_borrowHook s who m1 hc hbor
    have eS1 := updSup_eq m1 hc1.1
    have hstartS := supStart_le (m1.acct who).supplierIndex m1.supplyState.index
      (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index
      (supRec_le m1 who hc1) (accrue_ge _ _ _)
    have eS2 := distSup_eq ({ m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } : St) who hstartS
    obtain ⟨m2, hm2⟩ : ∃ m2, distributeSupplierComp _ who = some m2 := ⟨_, eS2⟩
    have hsup : comptroller m1 (.supplyHook who) = some m2 := by
      unfold comptroller
      dsimp only
      simp [eS1, hm2]
    have hcl : comptroller s (.claim who) = some (grant m2 who) := by
      unfold comptroller claimComp
      dsimp only
      simp [eB1, hm1, eS1, hm2, grant_eq]
    rw [hcl]
    rfl
  | setSpeeds a b =>
    obtain ⟨t, ht⟩ : ∃ t, setSupplySpeed s a = some t := by
      by_cases hsa : s.supplyState.speed = a
      · exact ⟨s, by unfold setSupplySpeed; simp [hsa]⟩
      · have e := updSup_eq s hc.1
        exact ⟨_, by unfold setSupplySpeed; simp [hsa, e]; rfl⟩
    have ct := setSupply_char s a t ht
    have htb : t.borrowState.block ≤ t.blockNumber := by
      have e1 : t.borrowState.block = s.borrowState.block := by rw [ct.2]
      have e2 : t.blockNumber = s.blockNumber := by rw [ct.2]
      rw [e1, e2]
      exact hc.2.1
    obtain ⟨s', hs'⟩ : ∃ s', setBorrowSpeed t b = some s' := by
      by_cases hsb : t.borrowState.speed = b
      · exact ⟨t, by unfold setBorrowSpeed; simp [hsb]⟩
      · have e := updBor_eq t htb
        exact ⟨_, by unfold setBorrowSpeed; simp [hsb, e]; rfl⟩
    have hdone : comptroller s (.setSpeeds a b) = some s' := by
      unfold comptroller setCompSpeedInternal
      dsimp only
      simp [ht, hs']
    rw [hdone]
    rfl
theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  dsimp only at h
  cases hm : updateCompSupplyIndex s with
  | none => simp [hm] at h
  | some s1 =>
    simp [hm] at h
    have hb := updSup_some s s1 hm
    have hs1 : s1 =
        ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St) := by
      have e := updSup_eq s hb
      rw [hm] at e
      simpa using e
    have hd := distSup_some s1 who s' h
    have heq := distSup_spec s1 who hd
    have e2 : s' = {s1 with accts := s1.accts.modify who fun a =>
      { a with
        supplierIndex := s1.supplyState.index,
        accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s1.supplyState.index)
          s1.supplyState.index } } :=
      (Option.some_inj.mp (heq.symm.trans h)).symm
    rw [hs1] at hd e2
    dsimp only at hd e2
    simp only [St.acct] at hd e2
    unfold SupplyDistributed
    exact ⟨hb, hd, e2⟩
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  dsimp only at h
  cases hm : updateCompBorrowIndex s with
  | none => simp [hm] at h
  | some s1 =>
    simp [hm] at h
    have hb := updBor_some s s1 hm
    have hs1 : s1 =
        ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St) := by
      have e := updBor_eq s hb
      rw [hm] at e
      simpa using e
    have hd := distBor_some s1 who s' h
    have heq := distBor_spec s1 who hd
    have e2 : s' = {s1 with accts := s1.accts.modify who fun a =>
      { a with
        borrowerIndex := s1.borrowState.index,
        accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s1.borrowState.index)
          s1.borrowState.index } } :=
      (Option.some_inj.mp (heq.symm.trans h)).symm
    rw [hs1] at hd e2
    dsimp only at hd e2
    simp only [St.acct] at hd e2
    unfold BorrowDistributed
    exact ⟨hb, hd, e2⟩
theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  dsimp only at h
  cases huB : updateCompBorrowIndex s with
  | none => simp [huB] at h
  | some t1 =>
    simp [huB] at h
    cases hdB : distributeBorrowerComp t1 who with
    | none => simp [hdB] at h
    | some m1 =>
      simp [hdB] at h
      cases huS : updateCompSupplyIndex m1 with
      | none => simp [huS] at h
      | some t2 =>
        simp [huS] at h
        cases hdS : distributeSupplierComp t2 who with
        | none => simp [hdS] at h
        | some m2 =>
          simp [hdS] at h
          have hbor : comptroller s (.borrowHook who) = some m1 := by
            unfold comptroller
            dsimp only
            simp [huB, hdB]
          have hsup : comptroller m1 (.supplyHook who) = some m2 := by
            unfold comptroller
            dsimp only
            simp [huS, hdS]
          have hg : s' = grant m2 who := by
            have he : grantCompInternal m2 who = grant m2 who := grant_eq m2 who
            rw [he] at h
            exact h.symm
          exact ⟨m1, m2, req_borrow_hook s who m1 hbor, req_supply_hook m1 who m2 hsup, hg⟩
theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  dsimp only at h
  cases h1 : setSupplySpeed s a with
  | none => simp [h1] at h
  | some t =>
    simp [h1] at h
    have cs := setSupply_char s a t h1
    have cb := setBor_char t b s' h
    have htb : t.borrowState = s.borrowState := by rw [cs.2]
    have htblk : t.blockNumber = s.blockNumber := by rw [cs.2]
    unfold SpeedsSet
    refine ⟨cs.1, ?_, ?_⟩
    · intro hne
      have hne' : t.borrowState.speed ≠ b := by rw [htb]; exact hne
      have hle := cb.1 hne'
      rw [htb, htblk] at hle
      exact hle
    · have e := cb.2
      rw [cs.2] at e
      dsimp only at e
      simp only [totalBorrows] at e
      exact e
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
