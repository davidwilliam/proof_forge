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

open ProofForgeFin.Accumulator ProofForgeFin.DeFi.Rewards in
theorem start_eq_aux (rec idx : Nat) :
    (if rec = 0 ∧ compInitialIndex ≤ idx then compInitialIndex else rec) =
    accrualStart rec idx := by
  unfold accrualStart
  grind

theorem updSupply_full (s : St) (t : St) (h : updateCompSupplyIndex s = some t) :
    t.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) ∧
    t.borrowState = s.borrowState ∧ t.blockNumber = s.blockNumber ∧
    t.reserve = s.reserve ∧ t.accts = s.accts := by
  have hb : s.supplyState.block ≤ s.blockNumber := by
    unfold updateCompSupplyIndex subChecked at h
    by_cases hb : s.supplyState.block ≤ s.blockNumber
    · exact hb
    · simp [hb] at h
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked; simp [hb]
  unfold updateCompSupplyIndex at h
  rw [hsub] at h
  simp only at h
  simp only [GT.gt] at h
  unfold accrueSide
  by_cases hd : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
  · simp only [hd] at h ⊢
    simp at h ⊢
    by_cases ht : 0 < totalSupply s
    · simp [ht, fraction] at h ⊢
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp [ht] at h ⊢
      subst h
      simp at ⊢
  · simp only [hd] at h ⊢
    simp at h ⊢
    by_cases hd0 : 0 < s.blockNumber - s.supplyState.block
    · have hs : ¬ 0 < s.supplyState.speed := by
        by_cases hs : 0 < s.supplyState.speed
        · exact absurd ⟨hd0, hs⟩ hd
        · exact hs
      simp [hd0, hs] at h ⊢
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp [hd0] at h ⊢
      subst h
      have heq : s.supplyState.block = s.blockNumber := by omega
      refine ⟨?_, rfl, rfl, rfl, rfl⟩
      cases h1 : s.supplyState with
      | mk i b sp =>
        simp [h1] at heq ⊢
        subst heq
        rfl

theorem modify_congr_acct (l : List Acct) (who : Nat) (f f' : Acct → Acct)
    (h : f (l.getD who noAcct) = f' (l.getD who noAcct)) :
    l.modify who f = l.modify who f' := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp
    | succ n => simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp
      simp at h
      rw [h]
    | succ n =>
      simp
      simp at h
      exact ih n h

theorem le_accrueSide_index (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · simp
  · simp

theorem accrualStart_le (rec idx : Nat) (h : rec ≤ idx) : accrualStart rec idx ≤ idx := by
  unfold accrualStart
  grind

theorem acct_supply_le (s : St) (who : Nat) (hc : Consistent s) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at hc
  obtain ⟨h1, h2, h3⟩ := hc
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (h3 _ hm).1
  · rw [hm]
    unfold noAcct
    simp

theorem acct_borrow_le (s : St) (who : Nat) (hc : Consistent s) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  obtain ⟨h1, h2, h3⟩ := hc
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact (h3 _ hm).2
  · rw [hm]
    unfold noAcct
    simp

theorem grant_eq_state (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [hc, ↓reduceIte]
    have hmod : s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + (s.acct who).accrued }) = s.accts.modify who (fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }) := by
      apply modify_congr_acct
      rfl
    rw [hmod]
  · simp [hc]

theorem updBorrow_full (s : St) (t : St) (h : updateCompBorrowIndex s = some t) :
    t.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) ∧
    t.supplyState = s.supplyState ∧ t.blockNumber = s.blockNumber ∧
    t.reserve = s.reserve ∧ t.accts = s.accts := by
  have hb : s.borrowState.block ≤ s.blockNumber := by
    unfold updateCompBorrowIndex subChecked at h
    by_cases hb : s.borrowState.block ≤ s.blockNumber
    · exact hb
    · simp [hb] at h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [hb]
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  simp only [GT.gt] at h
  unfold accrueSide
  by_cases hd : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
  · simp only [hd] at h ⊢
    simp at h ⊢
    by_cases ht : 0 < totalBorrows s
    · simp [ht, fraction] at h ⊢
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp [ht] at h ⊢
      subst h
      simp at ⊢
  · simp only [hd] at h ⊢
    simp at h ⊢
    by_cases hd0 : 0 < s.blockNumber - s.borrowState.block
    · have hs : ¬ 0 < s.borrowState.speed := by
        by_cases hs : 0 < s.borrowState.speed
        · exact absurd ⟨hd0, hs⟩ hd
        · exact hs
      simp [hd0, hs] at h ⊢
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp [hd0] at h ⊢
      subst h
      have heq : s.borrowState.block = s.blockNumber := by omega
      refine ⟨?_, rfl, rfl, rfl, rfl⟩
      cases h1 : s.borrowState with
      | mk i b sp =>
        simp [h1] at heq ⊢
        subst heq
        rfl

theorem upd_supply_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) : (updateCompSupplyIndex s).isSome = true := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by unfold subChecked; simp [h]
  unfold updateCompSupplyIndex
  rw [hsub]
  simp only
  split
  · rfl
  · split
    · rfl
    · rfl

theorem upd_borrow_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) : (updateCompBorrowIndex s).isSome = true := by
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by unfold subChecked; simp [h]
  unfold updateCompBorrowIndex
  rw [hsub]
  simp only
  split
  · rfl
  · split
    · rfl
    · rfl

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsb, hbb, hrec⟩ := hc
  cases c with
  | supplyHook who =>
    unfold comptroller
    simp only
    cases hupd : updateCompSupplyIndex s with
    | none =>
      have hs := upd_supply_some s hsb
      rw [hupd] at hs
      simp at hs
    | some mid =>
      simp [hupd]
      have hupd_full := updSupply_full s mid hupd
      obtain ⟨hmid_sup, hmid_bor, hmid_blk, hmid_res, hmid_acct⟩ := hupd_full
      have hrec_s : (s.acct who).supplierIndex ≤ s.supplyState.index := acct_supply_le s who ⟨hsb, hbb, hrec⟩
      have hle : s.supplyState.index ≤ mid.supplyState.index := by rw [hmid_sup]; exact le_accrueSide_index s.supplyState s.blockNumber (totalSupply s)
      have hac : mid.acct who = s.acct who := by unfold St.acct; rw [hmid_acct]
      have hrec_mid : (mid.acct who).supplierIndex ≤ mid.supplyState.index := by rw [hac]; exact Nat.le_trans hrec_s hle
      have hstart_le : accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤ mid.supplyState.index := accrualStart_le _ _ hrec_mid
      have hstart_eq : (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) = accrualStart (mid.acct who).supplierIndex mid.supplyState.index := start_eq_aux _ _
      have hc_le : (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) ≤ mid.supplyState.index := by rw [hstart_eq]; exact hstart_le
      unfold distributeSupplierComp subChecked
      simp only
      simp [hc_le]
  | borrowHook who =>
    unfold comptroller
    simp only
    cases hupd : updateCompBorrowIndex s with
    | none =>
      have hs := upd_borrow_some s hbb
      rw [hupd] at hs
      simp at hs
    | some mid =>
      simp [hupd]
      have hupd_full := updBorrow_full s mid hupd
      obtain ⟨hmid_bor, hmid_sup, hmid_blk, hmid_res, hmid_acct⟩ := hupd_full
      have hrec_s : (s.acct who).borrowerIndex ≤ s.borrowState.index := acct_borrow_le s who ⟨hsb, hbb, hrec⟩
      have hle : s.borrowState.index ≤ mid.borrowState.index := by rw [hmid_bor]; exact le_accrueSide_index s.borrowState s.blockNumber (totalBorrows s)
      have hac : mid.acct who = s.acct who := by unfold St.acct; rw [hmid_acct]
      have hrec_mid : (mid.acct who).borrowerIndex ≤ mid.borrowState.index := by rw [hac]; exact Nat.le_trans hrec_s hle
      have hstart_le : accrualStart (mid.acct who).borrowerIndex mid.borrowState.index ≤ mid.borrowState.index := accrualStart_le _ _ hrec_mid
      have hstart_eq : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) = accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := start_eq_aux _ _
      have hc_le : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) ≤ mid.borrowState.index := by rw [hstart_eq]; exact hstart_le
      unfold distributeBorrowerComp subChecked
      simp only
      simp [hc_le]
  | claim who =>
    unfold comptroller claimComp
    simp only
    cases hb1 : updateCompBorrowIndex s with
    | none =>
      have hs := upd_borrow_some s hbb
      rw [hb1] at hs
      simp at hs
    | some t1 =>
      simp
      have hupd_b := updBorrow_full s t1 hb1
      obtain ⟨hmid_bor, hmid_sup, hmid_blk, hmid_res, hmid_acct⟩ := hupd_b
      have hrec_s_b : (s.acct who).borrowerIndex ≤ s.borrowState.index := acct_borrow_le s who ⟨hsb, hbb, hrec⟩
      have hle_b : s.borrowState.index ≤ t1.borrowState.index := by rw [hmid_bor]; exact le_accrueSide_index s.borrowState s.blockNumber (totalBorrows s)
      have hac_b : t1.acct who = s.acct who := by unfold St.acct; rw [hmid_acct]
      have hrec_t1 : (t1.acct who).borrowerIndex ≤ t1.borrowState.index := by rw [hac_b]; exact Nat.le_trans hrec_s_b hle_b
      have hstart_b : accrualStart (t1.acct who).borrowerIndex t1.borrowState.index ≤ t1.borrowState.index := accrualStart_le _ _ hrec_t1
      have heq_b : (if (t1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t1.borrowState.index then compInitialIndex else (t1.acct who).borrowerIndex) = accrualStart (t1.acct who).borrowerIndex t1.borrowState.index := start_eq_aux _ _
      have hc_b : (if (t1.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t1.borrowState.index then compInitialIndex else (t1.acct who).borrowerIndex) ≤ t1.borrowState.index := by rw [heq_b]; exact hstart_b
      cases hd1 : distributeBorrowerComp t1 who with
      | none =>
        unfold distributeBorrowerComp subChecked at hd1
        simp only at hd1
        simp [hc_b] at hd1
      | some m1 =>
        simp
        sorry
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal setSupplySpeed setBorrowSpeed
    simp only
    sorry
theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hmid : updateCompSupplyIndex s with
  | none => simp [hmid] at h
  | some mid =>
    simp [hmid] at h
    have hdist : distributeSupplierComp mid who = some s' := h
    have hupd := updSupply_full s mid hmid
    obtain ⟨hmid_sup, hmid_bor, hmid_blk, hmid_res, hmid_acct⟩ := hupd
    have hb : s.supplyState.block ≤ s.blockNumber := by unfold updateCompSupplyIndex subChecked at hmid; by_cases hb : s.supplyState.block ≤ s.blockNumber; exact hb; simp [hb] at hmid
    have hstart_eq : (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) = accrualStart (mid.acct who).supplierIndex mid.supplyState.index := start_eq_aux _ _
    have hacct_mid : mid.acct who = s.acct who := by unfold St.acct; rw [hmid_acct]
    unfold distributeSupplierComp subChecked at hdist
    simp only at hdist
    by_cases hc : (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) ≤ mid.supplyState.index
    · simp [hc] at hdist
      have hc2 : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [← hmid_sup, ← hacct_mid, ← hstart_eq]; exact hc
      refine ⟨hb, hc2, ?_⟩
      have hac : mid.acct who = s.accts.getD who noAcct := by unfold St.acct; rw [hmid_acct]
      have hsup : mid.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hmid_sup]
      have h1 : (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex) = accrualStart (s.accts.getD who noAcct).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [← hsup, ← hac]; exact hstart_eq
      have h2 : (mid.acct who).supply = (s.accts.getD who noAcct).supply := by rw [hac]
      have hmod : mid.accts.modify who (fun a => { a with supplierIndex := mid.supplyState.index, accrued := a.accrued + mulDouble (mid.acct who).supply (mid.supplyState.index - (if (mid.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ mid.supplyState.index then compInitialIndex else (mid.acct who).supplierIndex)) }) = s.accts.modify who (fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) := by rw [hmid_acct]; apply modify_congr_acct; rw [h1, hsup, h2]; rfl
      rw [← hdist]
      unfold St.withAcct
      rw [hmod, hmid_sup, hmid_bor, hmid_blk, hmid_res]
    · simp [hc] at hdist
theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  simp only at h
  cases hmid : updateCompBorrowIndex s with
  | none => simp [hmid] at h
  | some mid =>
    simp [hmid] at h
    have hdist : distributeBorrowerComp mid who = some s' := h
    have hupd := updBorrow_full s mid hmid
    obtain ⟨hmid_bor, hmid_sup, hmid_blk, hmid_res, hmid_acct⟩ := hupd
    have hb : s.borrowState.block ≤ s.blockNumber := by unfold updateCompBorrowIndex subChecked at hmid; by_cases hb : s.borrowState.block ≤ s.blockNumber; exact hb; simp [hb] at hmid
    have hstart_eq : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) = accrualStart (mid.acct who).borrowerIndex mid.borrowState.index := start_eq_aux _ _
    have hacct_mid : mid.acct who = s.acct who := by unfold St.acct; rw [hmid_acct]
    unfold distributeBorrowerComp subChecked at hdist
    simp only at hdist
    by_cases hc : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) ≤ mid.borrowState.index
    · simp [hc] at hdist
      have hc2 : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [← hmid_bor, ← hacct_mid, ← hstart_eq]; exact hc
      refine ⟨hb, hc2, ?_⟩
      have hac : mid.acct who = s.accts.getD who noAcct := by unfold St.acct; rw [hmid_acct]
      have hsup : mid.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hmid_bor]
      have h1 : (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex) = accrualStart (s.accts.getD who noAcct).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [← hsup, ← hac]; exact hstart_eq
      have h2 : (mid.acct who).borrow = (s.accts.getD who noAcct).borrow := by rw [hac]
      have hmod : mid.accts.modify who (fun a => { a with borrowerIndex := mid.borrowState.index, accrued := a.accrued + mulDouble (mid.acct who).borrow (mid.borrowState.index - (if (mid.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ mid.borrowState.index then compInitialIndex else (mid.acct who).borrowerIndex)) }) = s.accts.modify who (fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) := by rw [hmid_acct]; apply modify_congr_acct; rw [h1, hsup, h2]; rfl
      rw [← hdist]
      unfold St.withAcct
      rw [hmod, hmid_bor, hmid_sup, hmid_blk, hmid_res]
    · simp [hc] at hdist
theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  simp only at h
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
          have hclaim : grantCompInternal m2 who = s' := h
          have hbhook : comptroller s (.borrowHook who) = some m1 := by unfold comptroller; simp [hb1, hd1]
          have hshook : comptroller m1 (.supplyHook who) = some m2 := by unfold comptroller; simp [hs1, hd2]
          have hbdist := req_borrow_hook s who m1 hbhook
          have hsdist := req_supply_hook m1 who m2 hshook
          refine ⟨m1, m2, hbdist, hsdist, ?_⟩
          rw [← hclaim, grant_eq_state]
theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
