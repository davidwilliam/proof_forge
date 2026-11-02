import CompRewards.Spec
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Seq
import ProofForgeFin.Ledger
import ProofForgeFin.Rounding
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

theorem modify_congr_aux {α : Type} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at h
      simp only [List.modify_zero_cons, h]
    | succ i =>
      simp only [List.getD_cons_succ] at h
      simp only [List.modify_succ_cons, ih _ h]

theorem start_sup_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)
    = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0
  · simp only [hr, true_and]
    by_cases hi : compInitialIndex ≤ s.supplyState.index <;> simp [hi]
  · simp [hr]

theorem start_bor_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)
    = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0
  · simp only [hr, true_and]
    by_cases hi : compInitialIndex ≤ s.borrowState.index <;> simp [hi]
  · simp [hr]

theorem updSup_eq (s : St) :
    s.supplyState.block ≤ s.blockNumber →
    updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  intro hb
  cases s with
  | mk bn sup bor res accts =>
    simp only at hb ⊢
    unfold updateCompSupplyIndex subChecked accrueSide totalSupply fraction
    simp [hb]
    cases sup with
    | mk idx blk spd =>
      simp only at hb ⊢
      by_cases hdelta : 0 < bn - blk ∧ 0 < spd
      · simp [hdelta]
        by_cases htot : 0 < (List.map Acct.supply accts).sum
        · simp [htot]
        · simp [htot, Nat.add_zero]
      · simp [hdelta]
        by_cases hpos : 0 < bn - blk
        · have hspd : ¬ 0 < spd := fun hs => hdelta ⟨hpos, hs⟩
          simp [hpos, hspd]
        · simp [hpos]
          have heq : blk = bn := by omega
          subst heq
          rfl

theorem updBor_eq (s : St) :
    s.borrowState.block ≤ s.blockNumber →
    updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  intro hb
  cases s with
  | mk bn sup bor res accts =>
    simp only at hb ⊢
    unfold updateCompBorrowIndex subChecked accrueSide totalBorrows fraction
    simp [hb]
    cases bor with
    | mk idx blk spd =>
      simp only at hb ⊢
      by_cases hdelta : 0 < bn - blk ∧ 0 < spd
      · simp [hdelta]
        by_cases htot : 0 < (List.map Acct.borrow accts).sum
        · simp [htot]
        · simp [htot, Nat.add_zero]
      · simp [hdelta]
        by_cases hpos : 0 < bn - blk
        · have hspd : ¬ 0 < spd := fun hs => hdelta ⟨hpos, hs⟩
          simp [hpos, hspd]
        · simp [hpos]
          have heq : blk = bn := by omega
          subst heq
          rfl

theorem updSup_some_block (s : St) (mid : St) (h : updateCompSupplyIndex s = some mid) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · simp [hb] at h

theorem updBor_some_block (s : St) (mid : St) (h : updateCompBorrowIndex s = some mid) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · exact hb
  · simp [hb] at h

theorem accrualStart_le (rec idx : Nat) (h : rec ≤ idx) :
    accrualStart rec idx ≤ idx := by
  unfold accrualStart
  by_cases hr : rec = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi]
    · simp [hi]
  · simp [hr, h]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp [h]
    have hFG : (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) (s.accts.getD who noAcct)
      = (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) (s.accts.getD who noAcct) := rfl
    exact modify_congr_aux s.accts who (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + (s.acct who).accrued } : Acct)) (fun a : Acct => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct)) noAcct hFG
  · simp [h]
theorem distSup_char (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart := start_sup_eq s who
  unfold distributeSupplierComp subChecked at h
  simp only [hstart] at h
  by_cases hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    have hFG : (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).supply (s.supplyState.index - accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) } : Acct)) (s.accts.getD who noAcct)
      = (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) (s.accts.getD who noAcct) := rfl
    have hmod : s.accts.modify who (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).supply (s.supplyState.index - accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) } : Acct))
      = s.accts.modify who (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) :=
      modify_congr_aux s.accts who _ _ noAcct hFG
    unfold St.withAcct St.acct at h
    have h2 : s.accts.getD who noAcct = s.acct who := rfl
    rw [h2] at hFG
    have h3 : s' =
      { blockNumber := s.blockNumber, supplyState := s.supplyState, borrowState := s.borrowState, reserve := s.reserve,
        accts := s.accts.modify who fun a =>
          ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).supply (s.supplyState.index - accrualStart (s.accts.getD who noAcct).supplierIndex s.supplyState.index) } : Acct) } := Option.some_inj.mp h.symm
    rw [h3, hmod]
  · simp [hle] at h

theorem distBor_char (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart := start_bor_eq s who
  unfold distributeBorrowerComp subChecked at h
  simp only [hstart] at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    have hFG : (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).borrow (s.borrowState.index - accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) } : Acct)) (s.accts.getD who noAcct)
      = (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) (s.accts.getD who noAcct) := rfl
    have hmod : s.accts.modify who (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).borrow (s.borrowState.index - accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) } : Acct))
      = s.accts.modify who (fun a : Acct => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) :=
      modify_congr_aux s.accts who _ _ noAcct hFG
    unfold St.withAcct St.acct at h
    have h2 : s.accts.getD who noAcct = s.acct who := rfl
    rw [h2] at hFG
    have h3 : s' =
      { blockNumber := s.blockNumber, supplyState := s.supplyState, borrowState := s.borrowState, reserve := s.reserve,
        accts := s.accts.modify who fun a =>
          ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.accts.getD who noAcct).borrow (s.borrowState.index - accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) } : Acct) } := Option.some_inj.mp h.symm
    rw [h3, hmod]
  · simp [hle] at h

theorem accrueSupply_mono (s : St) : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [h]
  · simp [h]
theorem accrueBorrow_mono (s : St) : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  by_cases h : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s
  · simp [h]
  · simp [h]
theorem distSup_some (s : St) (who : Account) (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by
  have hstart := start_sup_eq s who
  unfold distributeSupplierComp subChecked
  simp only [hstart]
  simp [hle]
theorem distBor_some (s : St) (who : Account) (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by
  have hstart := start_bor_eq s who
  unfold distributeBorrowerComp subChecked
  simp only [hstart]
  simp [hle]
theorem getD_mem_or (l : List Acct) (who : Nat) : l.getD who noAcct ∈ l ∨ l.getD who noAcct = noAcct := by
  induction l generalizing who with
  | nil => simp
  | cons a l ih =>
    cases who with
    | zero => simp
    | succ n =>
      simp only [List.getD_cons_succ]
      rcases ih n with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
theorem acct_sup_le (s : St) (who : Account) (hc : Consistent s) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  have hmem : s.acct who ∈ s.accts ∨ s.acct who = noAcct := by
    have h := getD_mem_or s.accts who
    simp only [St.acct] at h ⊢
    exact h
  by_cases hm : s.acct who ∈ s.accts
  · exact (hc.2.2 _ hm).1
  · have heq : s.acct who = noAcct := by
      rcases hmem with h | h
      · simp [hm] at h
      · exact h
    simp [heq, noAcct]
theorem acct_bor_le (s : St) (who : Account) (hc : Consistent s) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  have hmem : s.acct who ∈ s.accts ∨ s.acct who = noAcct := by
    have h := getD_mem_or s.accts who
    simp only [St.acct] at h ⊢
    exact h
  by_cases hm : s.acct who ∈ s.accts
  · exact (hc.2.2 _ hm).2
  · have heq : s.acct who = noAcct := by
      rcases hmem with h | h
      · simp [hm] at h
      · exact h
    simp [heq, noAcct]
theorem distBor_pres_sup (s : St) (who : Account) (s' : St) (h : distributeBorrowerComp s who = some s') :
    (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by
  have hD := distBor_char s who s' h
  obtain ⟨_, heq⟩ := hD
  simp only [St.acct] at *
  rw [heq]
  simp only [ProofForgeFin.Ledger.getD_modify]
  by_cases hm : who < s.accts.length
  · simp [hm]
  · simp [hm]
theorem distSup_pres_bor (s : St) (who : Account) (s' : St) (h : distributeSupplierComp s who = some s') :
    (s'.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
  have hD := distSup_char s who s' h
  obtain ⟨_, heq⟩ := hD
  simp only [St.acct] at *
  rw [heq]
  simp only [ProofForgeFin.Ledger.getD_modify]
  by_cases hm : who < s.accts.length
  · simp [hm]
  · simp [hm]
theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  have hSupBlk : s.supplyState.block ≤ s.blockNumber := hc.1
  have hBorBlk : s.borrowState.block ≤ s.blockNumber := hc.2.1
  cases c with
  | supplyHook who =>
    let mid0 : St := { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
    have hUeq := updSup_eq s hSupBlk
    have hC : comptroller s (.supplyHook who) = distributeSupplierComp mid0 who := by
      unfold comptroller
      show (Option.bind _ _) = _
      rw [hUeq]
      rfl
    have hrec := acct_sup_le s who hc
    have hmono := accrueSupply_mono s
    have h1 : (mid0.acct who).supplierIndex = (s.acct who).supplierIndex := rfl
    have h2 : mid0.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := rfl
    have hmid_rec : (mid0.acct who).supplierIndex ≤ mid0.supplyState.index := by
      rw [h1, h2]
      exact Nat.le_trans hrec hmono
    have hle := accrualStart_le _ _ hmid_rec
    obtain ⟨s', hs'⟩ := distSup_some mid0 who hle
    have hCeq : comptroller s (.supplyHook who) = some s' := by rw [hC, hs']
    simp [hCeq]
  | borrowHook who =>
    let mid0 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hUeq := updBor_eq s hBorBlk
    have hC : comptroller s (.borrowHook who) = distributeBorrowerComp mid0 who := by
      unfold comptroller
      show (Option.bind _ _) = _
      rw [hUeq]
      rfl
    have hrec := acct_bor_le s who hc
    have hmono := accrueBorrow_mono s
    have h1 : (mid0.acct who).borrowerIndex = (s.acct who).borrowerIndex := rfl
    have h2 : mid0.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := rfl
    have hmid_rec : (mid0.acct who).borrowerIndex ≤ mid0.borrowState.index := by
      rw [h1, h2]
      exact Nat.le_trans hrec hmono
    have hle := accrualStart_le _ _ hmid_rec
    obtain ⟨s', hs'⟩ := distBor_some mid0 who hle
    have hCeq : comptroller s (.borrowHook who) = some s' := by rw [hC, hs']
    simp [hCeq]
  | claim who =>
    have hU1 := updBor_eq s hBorBlk
    have hrecB := acct_bor_le s who hc
    have hmonoB := accrueBorrow_mono s
    have hmidB_rec : (s.acct who).borrowerIndex ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans hrecB hmonoB
    have hleB := accrualStart_le _ _ hmidB_rec
    obtain ⟨m1, hm1⟩ := distBor_some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who hleB
    have hm1_sup : m1.supplyState = s.supplyState := by
      have hD := distBor_char { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who m1 hm1
      obtain ⟨_, heq⟩ := hD
      simp at heq
      rw [heq]
    have hm1_blk : m1.blockNumber = s.blockNumber := by
      have hD := distBor_char { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who m1 hm1
      obtain ⟨_, heq⟩ := hD
      simp at heq
      rw [heq]
    have hm1_supBlk : m1.supplyState.block ≤ m1.blockNumber := by rw [hm1_sup, hm1_blk]; exact hSupBlk
    have hU2 := updSup_eq m1 hm1_supBlk
    have hpres : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have hps := distBor_pres_sup { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who m1 hm1
      exact hps
    have hrecS := acct_sup_le s who hc
    have hm1_recS : (m1.acct who).supplierIndex ≤ m1.supplyState.index := by
      rw [hpres, hm1_sup]
      exact hrecS
    have hmonoS := accrueSupply_mono m1
    have hmidS_rec : (m1.acct who).supplierIndex ≤ (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index :=
      Nat.le_trans hm1_recS hmonoS
    have hleS := accrualStart_le _ _ hmidS_rec
    obtain ⟨m2, hm2⟩ := distSup_some { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } who hleS
    have hC : comptroller s (.claim who) = some (grantCompInternal m2 who) := by
      unfold comptroller claimComp
      simp [hU1, hm1, hU2, hm2]
    simp [hC]
  | setSpeeds a b =>
    have hSup : ∃ s1, setSupplySpeed s a = some s1 := by
      by_cases hs : s.supplyState.speed = a
      · exact ⟨s, by simp [setSupplySpeed, hs]⟩
      · exact ⟨{ s with supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }, by simp [setSupplySpeed, hs, updSup_eq s hSupBlk]⟩
    obtain ⟨s1, hS1⟩ := hSup
    have hs1_blk : s1.blockNumber = s.blockNumber := by
      unfold setSupplySpeed at hS1
      by_cases hs : s.supplyState.speed = a
      · simp [hs] at hS1
        subst hS1
        rfl
      · simp [hs] at hS1
        have heq := updSup_eq s hSupBlk
        rw [heq] at hS1
        simp at hS1
        subst hS1
        rfl
    have hs1_bor : s1.borrowState = s.borrowState := by
      unfold setSupplySpeed at hS1
      by_cases hs : s.supplyState.speed = a
      · simp [hs] at hS1
        subst hS1
        rfl
      · simp [hs] at hS1
        have heq := updSup_eq s hSupBlk
        rw [heq] at hS1
        simp at hS1
        subst hS1
        rfl
    have hs1_borBlk : s1.borrowState.block ≤ s1.blockNumber := by rw [hs1_bor, hs1_blk]; exact hBorBlk
    have hBor : ∃ s2, setBorrowSpeed s1 b = some s2 := by
      by_cases hs : s1.borrowState.speed = b
      · exact ⟨s1, by simp [setBorrowSpeed, hs]⟩
      · exact ⟨{ s1 with borrowState := { accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) with speed := b } }, by simp [setBorrowSpeed, hs, updBor_eq s1 hs1_borBlk]⟩
    obtain ⟨s2, hS2⟩ := hBor
    have hC : comptroller s (.setSpeeds a b) = some s2 := by
      unfold comptroller setCompSpeedInternal
      simp [hS1, hS2]
    simp [hC]

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    simp [hU] at h
  | some mid =>
    simp [hU] at h
    have hmid : mid = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      have hb := updSup_some_block s mid hU
      have heq := updSup_eq s hb
      rw [hU] at heq
      exact Option.some_inj.mp heq
    have hD := distSup_char mid who s' h
    obtain ⟨hle2, heq2⟩ := hD
    have hb := updSup_some_block s mid hU
    refine ⟨hb, ?_, ?_⟩
    · have hmid_acct : (mid.acct who).supplierIndex = (s.acct who).supplierIndex := by
        rw [hmid]
        rfl
      have hmid_idx : mid.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
        rw [hmid]
      rw [hmid_acct, hmid_idx] at hle2
      exact hle2
    · rw [hmid] at heq2
      simp at heq2
      exact heq2
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    simp [hU] at h
  | some mid =>
    simp [hU] at h
    have hmid : mid = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have hb := updBor_some_block s mid hU
      have heq := updBor_eq s hb
      rw [hU] at heq
      exact Option.some_inj.mp heq
    have hD := distBor_char mid who s' h
    obtain ⟨hle2, heq2⟩ := hD
    have hb := updBor_some_block s mid hU
    refine ⟨hb, ?_, ?_⟩
    · have hmid_acct : (mid.acct who).borrowerIndex = (s.acct who).borrowerIndex := by
        rw [hmid]
        rfl
      have hmid_idx : mid.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        rw [hmid]
      rw [hmid_acct, hmid_idx] at hle2
      exact hle2
    · rw [hmid] at heq2
      simp at heq2
      exact heq2
theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  -- borrow update
  cases hU1 : updateCompBorrowIndex s with
  | none =>
    simp [hU1] at h
  | some u1 =>
    simp [hU1] at h
    have hmid1 : u1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      have hb := updBor_some_block s u1 hU1
      have heq := updBor_eq s hb
      rw [hU1] at heq
      exact Option.some_inj.mp heq
    -- borrow distribute
    cases hD1 : distributeBorrowerComp u1 who with
    | none =>
      simp [hD1] at h
    | some m1 =>
      simp [hD1] at h
      have hBor := distBor_char u1 who m1 hD1
      obtain ⟨hleB, heqB⟩ := hBor
      have hb1 := updBor_some_block s u1 hU1
      -- supply update on m1
      cases hU2 : updateCompSupplyIndex m1 with
      | none =>
        simp [hU2] at h
      | some u2 =>
        simp [hU2] at h
        have hmid2 : u2 = { m1 with supplyState := accrueSide m1.supplyState m1.blockNumber (totalSupply m1) } := by
          have hb := updSup_some_block m1 u2 hU2
          have heq := updSup_eq m1 hb
          rw [hU2] at heq
          exact Option.some_inj.mp heq
        cases hD2 : distributeSupplierComp u2 who with
        | none =>
          simp [hD2] at h
        | some m2 =>
          simp [hD2] at h
          have hSup := distSup_char u2 who m2 hD2
          obtain ⟨hleS, heqS⟩ := hSup
          have hb2 := updSup_some_block m1 u2 hU2
          -- h : grantCompInternal m2 who = s'
          have hgrant : grant m2 who = s' := by
            rw [← grant_eq m2 who] at *
            exact h
          refine ⟨m1, m2, ?_, ?_, ?_⟩
          · -- BorrowDistributed s who m1
            have hmid1_acct : (u1.acct who).borrowerIndex = (s.acct who).borrowerIndex := by simp [hmid1, St.acct]
            have hmid1_idx : u1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hmid1]
            rw [hmid1] at heqB
            simp at heqB
            refine ⟨hb1, ?_, ?_⟩
            · rw [hmid1_acct, hmid1_idx] at hleB
              exact hleB
            · exact heqB
          · -- SupplyDistributed m1 who m2
            have hmid2_acct : (u2.acct who).supplierIndex = (m1.acct who).supplierIndex := by simp [hmid2, St.acct]
            have hmid2_idx : u2.supplyState.index = (accrueSide m1.supplyState m1.blockNumber (totalSupply m1)).index := by simp [hmid2]
            rw [hmid2] at heqS
            simp at heqS
            refine ⟨hb2, ?_, ?_⟩
            · rw [hmid2_acct, hmid2_idx] at hleS
              exact hleS
            · exact heqS
          · exact hgrant.symm
theorem setSup_char (s : St) (a : Nat) (s1 : St) (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1 = { s with supplyState := if s.supplyState.speed = a then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases hs : s.supplyState.speed = a
  · simp [hs] at h
    subst h
    refine ⟨fun hne => absurd hs hne, ?_⟩
    simp [hs]
  · simp [hs] at h
    have hb : s.supplyState.block ≤ s.blockNumber := by
      by_cases hbb : s.supplyState.block ≤ s.blockNumber
      · exact hbb
      · have hnone : updateCompSupplyIndex s = none := by
          unfold updateCompSupplyIndex subChecked
          simp [hbb]
        simp [hnone] at h
    have heq := updSup_eq s hb
    rw [heq] at h
    simp at h
    subst h
    refine ⟨fun _ => hb, ?_⟩
    simp [hs]
theorem setBor_char (s : St) (b : Nat) (s2 : St) (h : setBorrowSpeed s b = some s2) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s2 = { s with borrowState := if s.borrowState.speed = b then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases hs : s.borrowState.speed = b
  · simp [hs] at h
    subst h
    refine ⟨fun hne => absurd hs hne, ?_⟩
    simp [hs]
  · simp [hs] at h
    have hb : s.borrowState.block ≤ s.blockNumber := by
      by_cases hbb : s.borrowState.block ≤ s.blockNumber
      · exact hbb
      · have hnone : updateCompBorrowIndex s = none := by
          unfold updateCompBorrowIndex subChecked
          simp [hbb]
        simp [hnone] at h
    have heq := updBor_eq s hb
    rw [heq] at h
    simp at h
    subst h
    refine ⟨fun _ => hb, ?_⟩
    simp [hs]
theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  cases hS : setSupplySpeed s a with
  | none =>
    simp [hS] at h
  | some s1 =>
    simp [hS] at h
    cases hB : setBorrowSpeed s1 b with
    | none =>
      simp [hB] at h
    | some s2 =>
      simp [hB] at h
      subst h
      have hSup := setSup_char s a s1 hS
      have hBor := setBor_char s1 b s2 hB
      obtain ⟨hSupBlk, hSupEq⟩ := hSup
      obtain ⟨hBorBlk, hBorEq⟩ := hBor
      -- s1 differs from s only in supplyState, so borrow parts transfer
      have hs1_bor : s1.borrowState = s.borrowState := by rw [hSupEq]
      have hs1_blk : s1.blockNumber = s.blockNumber := by rw [hSupEq]
      have hs1_totBor : totalBorrows s1 = totalBorrows s := by simp [hSupEq, totalBorrows]
      refine ⟨?_, ?_, ?_⟩
      · intro hne
        exact hSupBlk hne
      · intro hne
        have hne1 : s1.borrowState.speed ≠ b := by
          rw [hs1_bor] at *
          exact hne
        have := hBorBlk hne1
        rw [hs1_blk] at this
        -- s.blockNumber = s1.blockNumber, s.borrowState.block = s1.borrowState.block?
        have hbor_blk : s.borrowState.block = s1.borrowState.block := by rw [hs1_bor]
        omega
      · -- s' equation from hSupEq and hBorEq, matching SpeedsSet
        rw [hSupEq] at hBorEq
        simp [totalBorrows] at hBorEq
        simpa [totalBorrows] using hBorEq
def sumPendSup (s : St) : Nat :=
  (s.accts.map fun a => a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index)).sum
def sumPendBor (s : St) : Nat :=
  (s.accts.map fun a => a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)).sum
def unindexedSup (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed
def unindexedBor (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed
def pot (s : St) : Nat :=
  (s.accts.map fun a => a.accrued + a.wallet).sum * doubleScale + sumPendSup s + sumPendBor s + (unindexedSup s + unindexedBor s) * doubleScale
def potTo (s : St) (who : Account) : Nat :=
  ((s.acct who).accrued + (s.acct who).wallet) * doubleScale
    + (s.acct who).supply * (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index)
    + (s.acct who).borrow * (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index)
    + (if 0 < (s.acct who).supply then unindexedSup s * doubleScale else 0)
    + (if 0 < (s.acct who).borrow then unindexedBor s * doubleScale else 0)
theorem upgrade_consistent (L : Legacy) (h : L.WellFormed) : Consistent (upgrade L) := by
  unfold Legacy.WellFormed at h
  obtain ⟨hSupStart, hSupLe, hBorStart, hBorLe, hSupBlk, hBorBlk, hIdx⟩ := h
  unfold Consistent upgrade initSide
  refine ⟨?_, ?_, ?_⟩
  · by_cases hs : L.supplyIndex = 0
    · simp [hs]
    · simp [hs]
      exact hSupBlk
  · by_cases hb : L.borrowIndex = 0
    · simp [hb]
    · simp [hb]
      exact hBorBlk
  · intro a ha
    have hle := hIdx a ha
    obtain ⟨hsup, hbor⟩ := hle
    constructor
    · by_cases hs : L.supplyIndex = 0
      · simp [hs]
        have hsup0 : a.supplierIndex ≤ L.supplyIndex := hsup
        omega
      · simp [hs]
        exact hsup
    · by_cases hb : L.borrowIndex = 0
      · simp [hb]
        have hbor0 : a.borrowerIndex ≤ L.borrowIndex := hbor
        omega
      · simp [hb]
        exact hbor
theorem pot_supply_hook_le (s s' : St) (who : Account) (h : SupplyDistributed s who s') : pot s' ≤ pot s := by
  obtain ⟨hBlk, hle, heq⟩ := h
  -- borrow parts unchanged, supply index monotonic
  have hmono : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrueSupply_mono s
  have hBorPend : sumPendBor s' = sumPendBor s := by
    rw [heq]
    unfold sumPendBor
    dsimp only
    exact ProofForgeFin.Ledger.sum_map_modify_eq _ _ _ _ noAcct (fun _ => rfl)
  have hBorU : unindexedBor s' = unindexedBor s := by
    rw [heq]
    unfold unindexedBor
    dsimp only
  have hSupU' : unindexedSup s' = 0 := by
    rw [heq]
    unfold unindexedSup accrueSide
    dsimp only
    by_cases h : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
    · simp [h, Nat.sub_self]
    · simp [h, Nat.sub_self]
  -- supply-side bound via pot_accrue_settle_le
  let tSup : Nat → Acct → Nat := fun i a => (a.accrued + a.wallet) * doubleScale + a.supply * (i - accrualStart a.supplierIndex i)
  let uSup : Acct → Nat := fun a => a.supply
  have htSup : ∀ a ∈ s.accts, tSup (accrueSide s.supplyState s.blockNumber (totalSupply s)).index a ≤ tSup s.supplyState.index a + uSup a * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := sorry
  have hUSup : (s.accts.map uSup).sum * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) + doubleScale * 0 ≤ doubleScale * unindexedSup s := sorry
  have hfSup : who < s.accts.length → tSup (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ((fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) (s.accts.getD who noAcct)) ≤ tSup (accrueSide s.supplyState s.blockNumber (totalSupply s)).index (s.accts.getD who noAcct) := sorry
  have hSupply : ((s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }).map (tSup (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)).sum + doubleScale * 0 ≤ (s.accts.map (tSup s.supplyState.index)).sum + doubleScale * unindexedSup s :=
    ProofForgeFin.Accumulator.pot_accrue_settle_le _ _ _ _ _ _ htSup hUSup hfSup
  sorry
theorem pot_borrow_hook_le (s s' : St) (who : Account) (h : BorrowDistributed s who s') : pot s' ≤ pot s := sorry
theorem pot_claim_le (s s' : St) (who : Account) (h : Claimed s who s') : pot s' ≤ pot s := sorry
theorem pot_setSpeeds_le (s s' : St) (a b : Nat) (h : SpeedsSet s a b s') : pot s' ≤ pot s := sorry
theorem pot_advance_eq (s : St) (k : Nat) (hSup : s.supplyState.block ≤ s.blockNumber) (hBor : s.borrowState.block ≤ s.blockNumber) : pot { s with blockNumber := s.blockNumber + k } = pot s + (k * (s.supplyState.speed + s.borrowState.speed)) * doubleScale := by
  unfold pot sumPendSup sumPendBor unindexedSup unindexedBor
  simp only
  have h1 : (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed = (s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed :=
    ProofForgeFin.DeFi.Rewards.elapsed_add_mul k s.supplyState.speed hSup
  have h2 : (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed = (s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed :=
    ProofForgeFin.DeFi.Rewards.elapsed_add_mul k s.borrowState.speed hBor
  rw [h1, h2]
  grind
theorem pot_drip_eq (s : St) (x : Nat) : pot { s with reserve := s.reserve + x } = pot s := by
  unfold pot sumPendSup sumPendBor unindexedSup unindexedBor
  simp
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
