import CompRewards.Spec
import ProofForgeFin.Ledger
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Seq
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
    if (s.acct supplier).supplierIndex = 0 ∧ supplyIndex ≥ compInitialIndex then compInitialIndex
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
    if (s.acct borrower).borrowerIndex = 0 ∧ borrowIndex ≥ compInitialIndex then compInitialIndex
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

def td0_unindexedSupply (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed

def td0_unindexedBorrow (s : St) : Nat :=
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def td0_pendingScaled (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def td0_owed (s : St) : Nat :=
  (s.accts.map (td0_pendingScaled s)).sum / doubleScale +
    td0_unindexedSupply s + td0_unindexedBorrow s

def td0_owedTo (s : St) (who : Account) : Nat :=
  td0_pendingScaled s (s.acct who) / doubleScale +
    (if 0 < (s.acct who).supply then td0_unindexedSupply s else 0) +
    (if 0 < (s.acct who).borrow then td0_unindexedBorrow s else 0)

def td0_Inv (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

theorem td0_supplyHook_some (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.supplyHook who)).isSome := by sorry

theorem td0_borrowHook_some (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.borrowHook who)).isSome := by sorry

theorem td0_claim_some (s : St) (who : Account) (hs : Consistent s) :
    (comptroller s (.claim who)).isSome := by sorry

theorem td0_setSpeeds_some (s : St) (a b : Nat) (hs : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome := by sorry





theorem td0_claim_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.claim who) = some s') :
    Claimed s who s' := by sorry

theorem td0_setSpeeds_effect (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    SpeedsSet s a b s' := by sorry







theorem td0_run_inv (sp : Nat × Nat) (s : St) (ops : List Op) (h : td0_Inv sp s) :
    td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by sorry





theorem td0_inv_upgrade (L : Legacy) (hWF : L.WellFormed) :
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  unfold td0_Inv Consistent upgrade at *
  obtain ⟨hs0, hs_le, hb0, hb_le, hsblk, hbblk, haccts⟩ := hWF
  simp only [initSide]
  refine ⟨⟨?h1, ?h2, ?h3⟩, ?s1, ?s2⟩
  · by_cases h : L.supplyIndex = 0
    · simp [h]
    · simp [h]; exact hsblk
  · by_cases h : L.borrowIndex = 0
    · simp [h]
    · simp [h]; exact hbblk
  · intro a ha
    have ha0 := haccts a ha
    obtain ⟨hsa, hba⟩ := ha0
    by_cases hs : L.supplyIndex = 0 <;> by_cases hb : L.borrowIndex = 0
    · simp [hs, hb]
      have hs0a : a.supplierIndex = 0 := Nat.le_zero.mp (by simpa [hs] using hsa)
      have hb0a : a.borrowerIndex = 0 := Nat.le_zero.mp (by simpa [hb] using hba)
      constructor
      · rw [hs0a]; exact Nat.zero_le _
      · rw [hb0a]; exact Nat.zero_le _
    · simp [hs, hb]
      have hs0a : a.supplierIndex = 0 := Nat.le_zero.mp (by simpa [hs] using hsa)
      constructor
      · rw [hs0a]; exact Nat.zero_le _
      · exact hba
    · simp [hs, hb]
      have hb0a : a.borrowerIndex = 0 := Nat.le_zero.mp (by simpa [hb] using hba)
      constructor
      · exact hsa
      · rw [hb0a]; exact Nat.zero_le _
    · simp [hs, hb]
      exact ⟨hsa, hba⟩
  · by_cases h : L.supplyIndex = 0 <;> simp [h]
  · by_cases h : L.borrowIndex = 0 <;> simp [h]






theorem td0_owedTo_of_noPosition (s : St) (who : Account) (h : NoPosition s who) :
    td0_owedTo s who = 0 := by sorry

open CompRewards in def foo : Nat := 1

def bar : Nat := 2

theorem plan0_supplyHook_potential (s s' : St) (actor who : Account)
    (h : comptroller s (.supplyHook actor) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_borrowHook_potential (s s' : St) (actor who : Account)
    (h : comptroller s (.borrowHook actor) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_claim_potential (s s' : St) (actor who : Account)
    (h : comptroller s (.claim actor) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_setSpeeds_potential (s s' : St) (a b who : Account)
    (h : comptroller s (.setSpeeds a b) = some s') :
    s'.creditedTo who + td0_owedTo s' who ≤
      s.creditedTo who + td0_owedTo s who := by sorry

theorem plan0_exec_potential (sp : Nat × Nat) (s : St) (op : Op) (who : Account)
    (h : td0_Inv sp s) :
    (exec comptroller s op).creditedTo who +
        td0_owedTo (exec comptroller s op) who ≤
      s.creditedTo who + td0_owedTo s who + emittedBy sp op := by sorry



theorem tmp_check_modify (s : St) (who : Account) :
    (s.withAcct who id).accts = s.accts := by simp [St.withAcct]

theorem tmp_ledger_check (l : List Acct) (i j : Nat) (f : Acct → Acct) :
    (l.modify i f).getD j noAcct = if i = j ∧ j < l.length then f (l.getD j noAcct) else l.getD j noAcct :=
  ProofForgeFin.Ledger.getD_modify l i j f noAcct

def auxTestFoo2 : Nat := 1

def auxTestFoo3 : Nat := 2

def auxBorrowArith1 : Nat := 3

def auxBorrowTestA : Nat := 4

def auxBorrowTestB : Nat := 5

def auxArithA : Nat := 6

def auxScalePos : Nat := doubleScale

def myTestLem : Nat := 1

theorem myTestThm1 : 1 + 1 = 2 := by rfl

theorem auxGetDZero : ([].getD (0 : Nat) noAcct) = noAcct := by simp

theorem auxTotalNil : (([] : List Acct).map Acct.supply).sum = 0 := by simp

theorem aux_creditedTo_other (s : St) (actor who : Account) (f : Acct → Acct)
    (hne : actor ≠ who) :
    (s.withAcct actor f).creditedTo who = s.creditedTo who := by
  unfold St.creditedTo St.acct St.withAcct
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts actor who f noAcct
  rw [hmod]
  simp [hne]

theorem aux_creditedTo_pres4 (s : St) (actor who : Account) (f : Acct → Acct)
    (hacc : ∀ a, (f a).accrued = a.accrued ∧ (f a).wallet = a.wallet) :
    (s.withAcct actor f).creditedTo who = s.creditedTo who := by
  unfold St.creditedTo St.acct St.withAcct
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts actor who f noAcct
  rw [hmod]
  by_cases h : actor = who ∧ who < s.accts.length
  · simp only [if_pos h]
    have h2 := hacc (List.getD s.accts who noAcct)
    have e1 : (f (List.getD s.accts who noAcct)).accrued = (List.getD s.accts who noAcct).accrued := h2.1
    have e2 : (f (List.getD s.accts who noAcct)).wallet = (List.getD s.accts who noAcct).wallet := h2.2
    rw [e1, e2]
  · simp only [if_neg h]

theorem aux_acct_withAcct_same (s : St) (actor who : Account) (f : Acct → Acct)
    (hne : actor ≠ who) :
    (s.withAcct actor f).acct who = s.acct who := by
  unfold St.acct St.withAcct
  have hmod := ProofForgeFin.Ledger.getD_modify s.accts actor who f noAcct
  rw [hmod]
  simp [hne]

theorem aux_accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]

theorem plan0_run_potential_induct (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account)
    (h : td0_Inv sp s) :
    (run comptroller s ops).creditedTo who +
        td0_owedTo (run comptroller s ops) who ≤
      s.creditedTo who + td0_owedTo s who + emitted sp ops := by
  induction ops generalizing sp s with
  | nil => simp [run, emitted]
  | cons op rest ih =>
    have hStep := plan0_exec_potential sp s op who h
    have h0 := td0_run_inv sp s [op] h
    have eRun : run comptroller s [op] = exec comptroller s op := rfl
    have eSp : speedsAfter sp [op] = nextSpeeds sp op := rfl
    rw [eRun] at h0
    rw [eSp] at h0
    have hTail := ih (nextSpeeds sp op) (exec comptroller s op) h0
    have eRun2 : run comptroller s (op :: rest) = run comptroller (exec comptroller s op) rest := rfl
    have eEm : emitted sp (op :: rest) = emittedBy sp op + emitted (nextSpeeds sp op) rest := rfl
    rw [eRun2, eEm]
    omega

theorem plan0_run_potential_helperX (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account)
    (h : td0_Inv sp s) :
    (run comptroller s ops).creditedTo who +
        td0_owedTo (run comptroller s ops) who ≤
      s.creditedTo who + td0_owedTo s who + emitted sp ops := by
  induction ops generalizing sp s with
  | nil => simp [run, emitted]
  | cons op rest ih =>
    have hStep := plan0_exec_potential sp s op who h
    have h0 : td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by
      have h0a := td0_run_inv sp s [op] h
      have eRun : run comptroller s [op] = exec comptroller s op := rfl
      have eSp : speedsAfter sp [op] = nextSpeeds sp op := rfl
      rw [eRun] at h0a
      rw [eSp] at h0a
      exact h0a
    have hTail := ih (nextSpeeds sp op) (exec comptroller s op) h0
    have eRun2 : run comptroller s (op :: rest) = run comptroller (exec comptroller s op) rest := rfl
    have eEm : emitted sp (op :: rest) = emittedBy sp op + emitted (nextSpeeds sp op) rest := rfl
    rw [eRun2, eEm]
    omega

theorem plan0_run_potential (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account)
    (h : td0_Inv sp s) :
    (run comptroller s ops).creditedTo who +
        td0_owedTo (run comptroller s ops) who ≤
      s.creditedTo who + td0_owedTo s who + emitted sp ops :=
  plan0_run_potential_helperX sp s ops who h

theorem td0_run_creditedTo_bound (sp : Nat × Nat) (s : St) (ops : List Op) (h : td0_Inv sp s)
    (who : Account) :
    (run comptroller s ops).creditedTo who ≤
      s.creditedTo who + td0_owedTo s who + emitted sp ops := by
  have hP := plan0_run_potential sp s ops who h
  omega

open CompRewards in theorem tmp_scale_pos : 0 < doubleScale := by unfold doubleScale; decide
#check ProofForgeFin.DeFi.Rewards.settle_le
#check ProofForgeFin.DeFi.Rewards.pending_le_add
#check ProofForgeFin.DeFi.Rewards.sum_pending_le_add
#check ProofForgeFin.DeFi.Rewards.credit_mul_le

theorem plan1_supplyHook_global_potential (s s' : St) (who : Account)
    (h : comptroller s (.supplyHook who) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_borrowHook_global_potential (s s' : St) (who : Account)
    (h : comptroller s (.borrowHook who) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_claim_global_potential (s s' : St) (who : Account)
    (h : comptroller s (.claim who) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_setSpeeds_global_potential (s s' : St) (a b : Nat)
    (h : comptroller s (.setSpeeds a b) = some s') :
    s'.credited + td0_owed s' ≤ s.credited + td0_owed s := by sorry

theorem plan1_exec_global_potential (sp : Nat × Nat) (s : St) (op : Op)
    (h : td0_Inv sp s) :
    (exec comptroller s op).credited + td0_owed (exec comptroller s op) ≤
      s.credited + td0_owed s + emittedBy sp op := by sorry

theorem plan1_run_global_potential (sp : Nat × Nat) (s : St) (ops : List Op)
    (h : td0_Inv sp s) :
    (run comptroller s ops).credited + td0_owed (run comptroller s ops) ≤
      s.credited + td0_owed s + emitted sp ops := by
  induction ops generalizing sp s with
  | nil => simp [run, emitted]
  | cons op rest ih =>
    have hStep := plan1_exec_global_potential sp s op h
    have h0 : td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by
      have h0a := td0_run_inv sp s [op] h
      have eRun : run comptroller s [op] = exec comptroller s op := rfl
      have eSp : speedsAfter sp [op] = nextSpeeds sp op := rfl
      rw [eRun] at h0a
      rw [eSp] at h0a
      exact h0a
    have hTail := ih (nextSpeeds sp op) (exec comptroller s op) h0
    have eRun2 : run comptroller s (op :: rest) = run comptroller (exec comptroller s op) rest := rfl
    have eEm : emitted sp (op :: rest) = emittedBy sp op + emitted (nextSpeeds sp op) rest := rfl
    rw [eRun2, eEm]
    omega


theorem tmp_rewards_sig : True := trivial

open ProofForgeFin.DeFi.Rewards in theorem probe_pending_def (u s i : Nat) : pending u s i = u * (i - s) := by rfl

open ProofForgeFin.DeFi.Rewards in theorem probe2 (o u s i : Nat) : credit o u s i = u * (i - s) / o := by rfl

open ProofForgeFin.DeFi.Rewards in theorem probe_first2 (i r x : Nat) : firstStart i r x = if r = 0 then (if i ≤ x then i else 0) else r := by rfl

theorem aux_grant_credited_ok (s : St) (who : Account) :
    (grant s who).credited = s.credited := by
  unfold grant St.credited
  by_cases h : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [if_pos h]
    exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who
      (fun a => ({ a with accrued := 0, wallet := a.wallet + a.accrued } : Acct))
      (fun a => a.accrued + a.wallet) noAcct (by intro _; simp only; omega)
  · simp only [if_neg h]

theorem plan1_setSpeeds_global_potential_aux1 (s : St) :
    totalSupply s = totalSupply { s with supplyState := { s.supplyState with block := s.blockNumber } } := by
  simp [totalSupply]

theorem aux_DS_pos : 0 < doubleScale := by unfold doubleScale; decide

theorem aux_pending_mono_helper {idx0 idx1 st0 st1 : Nat}
    (hle : idx0 ≤ idx1) (hst : st0 ≤ st1) :
    idx1 - st1 ≤ (idx0 - st0) + (idx1 - idx0) := by
  omega

theorem aux_credited_withAcct_supply2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with supply := a.supply + x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_credited_withAcct_supply_sub2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with supply := a.supply - x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_credited_withAcct_borrow_add2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with borrow := a.borrow + x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_credited_withAcct_borrow_sub2 (s : St) (who x : Nat) :
    (s.withAcct who fun a => ({ a with borrow := a.borrow - x } : Acct)).credited = s.credited := by
  unfold St.credited St.withAcct
  exact ProofForgeFin.Ledger.sum_map_modify_eq s.accts who _ _ noAcct (by intro h; rfl)

theorem aux_unindexed_withAcct2 (s : St) (who : Account) (f : Acct → Acct) :
    td0_unindexedSupply (s.withAcct who f) = td0_unindexedSupply s := by
  simp [td0_unindexedSupply, St.withAcct]

theorem aux_unindexedB_withAcct2 (s : St) (who : Account) (f : Acct → Acct) :
    td0_unindexedBorrow (s.withAcct who f) = td0_unindexedBorrow s := by
  simp [td0_unindexedBorrow, St.withAcct]

theorem aux_compInit_pos : 0 < compInitialIndex := by
  unfold compInitialIndex
  decide

theorem aux_compInit_le_double : compInitialIndex ≤ doubleScale := by
  unfold compInitialIndex doubleScale
  simp

theorem aux_probe_acc1 (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem aux_accrue_index_ge5 (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [if_pos h]
    exact Nat.le_add_right sd.index _
  · simp only [if_neg h]
    exact Nat.le_refl _

theorem aux_probe_subst (s : St) (who : Account) (s' : St)
    (h : SupplyDistributed s who s') : s'.blockNumber = s.blockNumber := by
  obtain ⟨hblk, hle, heq⟩ := h
  subst heq
  rfl

theorem auxAccStartSelf (idx : Nat) : accrualStart idx idx = idx := by
  unfold accrualStart
  by_cases h : idx = 0
  · subst h
    simp only
    have hci : ¬ compInitialIndex ≤ 0 := by unfold compInitialIndex; omega
    simp [hci]
  · simp [h]

theorem auxPendingSettledSupply (s : St) (a : Acct) (x : Nat)
    (hset : accrualStart a.supplierIndex s.supplyState.index = s.supplyState.index) :
    td0_pendingScaled s ({ a with supply := a.supply + x }) = td0_pendingScaled s a := by
  unfold td0_pendingScaled
  rw [hset]
  simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add]

theorem auxPendWithAcctEq (s : St) (who : Account) (f : Acct → Acct) (a : Acct) :
    td0_pendingScaled (s.withAcct who f) a = td0_pendingScaled s a := by
  unfold td0_pendingScaled St.withAcct
  simp only

theorem td0_run_credited_bound (sp : Nat × Nat) (s : St) (ops : List Op) (h : td0_Inv sp s) :
    (run comptroller s ops).credited ≤ s.credited + td0_owed s + emitted sp ops := by
  have hP := plan1_run_global_potential sp s ops h
  omega

theorem aux_CI_ne_zero : compInitialIndex ≠ 0 := by
  unfold compInitialIndex
  omega

theorem aux_CI_pos : 0 < compInitialIndex := by
  unfold compInitialIndex
  decide

theorem aux_up_supply_index (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_supply_block (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_borrow_index (L : Legacy) :
    (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem aux_up_borrow_block (L : Legacy) :
    (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
  unfold upgrade initSide
  simp only
  by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem aux_up_speeds (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed ∧ (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h1 : L.supplyIndex = 0 <;> by_cases h2 : L.borrowIndex = 0 <;> simp [h1, h2]

theorem aux_up_accts (L : Legacy) : (upgrade L).accts = L.accts := by
  unfold upgrade; simp only

theorem aux_up_blockNum (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade; simp only

theorem aux_accStart_zero (idx : Nat) :
    accrualStart 0 idx = (if compInitialIndex ≤ idx then compInitialIndex else 0) := by
  unfold accrualStart
  simp

theorem aux_accStart_nz (r idx : Nat) (h : r ≠ 0) :
    accrualStart r idx = r := by
  unfold accrualStart
  simp [h]

theorem aux_legStart_zero (S : Nat) :
    legacyStart S 0 = S := by
  unfold legacyStart
  simp

theorem aux_legStart_nz (S r : Nat) (h : r ≠ 0) :
    legacyStart S r = r := by
  unfold legacyStart
  simp [h]

theorem aux_start_diff_le4 (S r I : Nat)
    (hS : S = 0 ∨ S = compInitialIndex) (hSI : S ≤ I) (hr : r ≤ I) :
    (if I = 0 then compInitialIndex else I) -
      accrualStart r (if I = 0 then compInitialIndex else I) ≤
    I - legacyStart S r := by
  by_cases hI : I = 0
  · subst hI
    have hr0 : r = 0 := Nat.le_zero.mp hr
    have hS0 : S = 0 := by
      rcases hS with h | h
      · exact h
      · subst h
        have hpos : 0 < compInitialIndex := aux_CI_pos
        omega
    subst hr0; subst hS0
    have hJ : (if (0 : Nat) = 0 then compInitialIndex else 0) = compInitialIndex := by simp
    rw [hJ, aux_legStart_zero, aux_accStart_zero]
    have h1 : compInitialIndex ≤ compInitialIndex := Nat.le_refl _
    have h2 : (if compInitialIndex ≤ compInitialIndex then compInitialIndex else 0) = compInitialIndex := if_pos h1
    rw [h2]
    simp
  · have hIf : (if I = 0 then compInitialIndex else I) = I := if_neg hI
    rw [hIf]
    by_cases hr0 : r = 0
    · subst hr0
      rw [aux_legStart_zero, aux_accStart_zero]
      by_cases hle : compInitialIndex ≤ I
      · rw [if_pos hle]
        rcases hS with h | h
        · subst h; simp
        · subst h; simp
      · rw [if_neg hle]
        have hS0 : S = 0 := by
          rcases hS with h | h
          · exact h
          · exfalso; subst h; omega
        subst hS0; simp
    · rw [aux_accStart_nz _ _ hr0, aux_legStart_nz _ _ hr0]
      exact Nat.le_refl _

theorem aux_pend_up_le (L : Legacy) (hWF : L.WellFormed) (a : Acct) (ha : a ∈ L.accts) :
    td0_pendingScaled (upgrade L) a ≤ Legacy.pendingScaled L a := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs0, hs_le, hb0, hb_le, hsblk, hbblk, haccts⟩ := hWF
  have hacct := haccts a ha
  obtain ⟨hsa, hba⟩ := hacct
  have hsup := aux_up_supply_index L
  have hbor := aux_up_borrow_index L
  unfold td0_pendingScaled Legacy.pendingScaled
  rw [hsup, hbor]
  have h1 : a.supply * ((if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) -
      accrualStart a.supplierIndex (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex)) ≤
    a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
    apply Nat.mul_le_mul_left
    exact aux_start_diff_le4 L.supplyStart a.supplierIndex L.supplyIndex hs0 hs_le hsa
  have h2 : a.borrow * ((if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) -
      accrualStart a.borrowerIndex (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex)) ≤
    a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
    apply Nat.mul_le_mul_left
    exact aux_start_diff_le4 L.borrowStart a.borrowerIndex L.borrowIndex hb0 hb_le hba
  omega

theorem aux_sum_map_mono (l : List Acct) (f g : Acct → Nat)
    (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hhd : f hd ≤ g hd := h hd (by simp)
    have htl : ∀ a ∈ tl, f a ≤ g a := fun a ha => h a (List.mem_cons_of_mem hd ha)
    have iht := ih htl
    omega

theorem plan2_start_diff_le (S r I : Nat)
    (hS : S = 0 ∨ S = compInitialIndex) (hSI : S ≤ I) (hrI : r ≤ I) :
    (if I = 0 then compInitialIndex else I) -
        accrualStart r (if I = 0 then compInitialIndex else I) ≤
      I - legacyStart S r :=
  aux_start_diff_le4 S r I hS hSI hrI


theorem plan2_pending_upgrade_le (L : Legacy) (hWF : L.WellFormed)
    (a : Acct) (ha : a ∈ L.accts) :
    td0_pendingScaled (upgrade L) a ≤ Legacy.pendingScaled L a :=
  aux_pend_up_le L hWF a ha


theorem plan2_unindexedSupply_upgrade_le (L : Legacy) :
    td0_unindexedSupply (upgrade L) ≤ L.unindexedSupply := by
  unfold td0_unindexedSupply upgrade initSide Legacy.unindexedSupply
  simp only
  by_cases h : L.supplyIndex = 0
  · simp [h]
  · simp [h]


theorem plan2_unindexedBorrow_upgrade_le (L : Legacy) :
    td0_unindexedBorrow (upgrade L) ≤ L.unindexedBorrow := by
  unfold td0_unindexedBorrow upgrade initSide Legacy.unindexedBorrow
  simp only
  by_cases h : L.borrowIndex = 0
  · simp [h]
  · simp [h]


theorem plan2_sum_pending_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    ((upgrade L).accts.map (td0_pendingScaled (upgrade L))).sum ≤
      (L.accts.map L.pendingScaled).sum := by
  have hAccts : (upgrade L).accts = L.accts := aux_up_accts L
  rw [hAccts]
  apply aux_sum_map_mono _ _ _
  intro a ha
  exact plan2_pending_upgrade_le L hWF a ha


theorem plan2_owed_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed := by
  unfold td0_owed Legacy.owed
  have hSum := plan2_sum_pending_upgrade_le L hWF
  have hS := plan2_unindexedSupply_upgrade_le L
  have hB := plan2_unindexedBorrow_upgrade_le L
  have hDiv : ((upgrade L).accts.map (td0_pendingScaled (upgrade L))).sum / doubleScale ≤
      (L.accts.map L.pendingScaled).sum / doubleScale :=
    Nat.div_le_div_right hSum
  omega


theorem plan2_unindexedBorrow_upgrade_le_aux_tmp : True := trivial

theorem plan2_unindexedBorrow_upgrade_le_check (L : Legacy) :
    td0_unindexedBorrow (upgrade L) ≤ L.unindexedBorrow := by
  unfold td0_unindexedBorrow upgrade initSide Legacy.unindexedBorrow
  simp only
  by_cases h : L.borrowIndex = 0
  · simp [h]
  · simp [h]

theorem plan2_sum_pending_upgrade_le_aux (L : Legacy) (hWF : L.WellFormed) :
    ((upgrade L).accts.map (td0_pendingScaled (upgrade L))).sum ≤
      (L.accts.map L.pendingScaled).sum := by
  have hAccts : (upgrade L).accts = L.accts := aux_up_accts L
  rw [hAccts]
  apply aux_sum_map_mono _ _ _
  intro a ha
  exact plan2_pending_upgrade_le L hWF a ha

theorem td0_owed_upgrade_le_fix (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed :=
  plan2_owed_upgrade_le L hWF

theorem td0_owed_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed :=
  plan2_owed_upgrade_le L hWF

theorem aux_ping : 1 = 1 := rfl

theorem td0_owedTo_upgrade_le (L : Legacy) (hWF : L.WellFormed) (who : Account) :
    td0_owedTo (upgrade L) who ≤ L.owedTo who := by
  have hAccts : (upgrade L).accts = L.accts := aux_up_accts L
  have hAcctEq : (upgrade L).acct who = L.accts.getD who noAcct := by
    unfold St.acct
    rw [hAccts]
  have hMemOr := ProofForgeFin.Ledger.getD_mem_or L.accts who noAcct
  have hPend : td0_pendingScaled (upgrade L) (L.accts.getD who noAcct) ≤
      Legacy.pendingScaled L (L.accts.getD who noAcct) := by
    cases hMemOr with
    | inl hmem =>
      exact aux_pend_up_le L hWF _ hmem
    | inr heq =>
      rw [heq]
      unfold td0_pendingScaled Legacy.pendingScaled noAcct
      simp
  have hSupUn : td0_unindexedSupply (upgrade L) ≤ L.unindexedSupply :=
    plan2_unindexedSupply_upgrade_le L
  have hBorUn : td0_unindexedBorrow (upgrade L) ≤ L.unindexedBorrow :=
    plan2_unindexedBorrow_upgrade_le L
  have hDiv : td0_pendingScaled (upgrade L) (L.accts.getD who noAcct) / doubleScale ≤
      Legacy.pendingScaled L (L.accts.getD who noAcct) / doubleScale :=
    Nat.div_le_div_right hPend
  have hS : (if 0 < (L.accts.getD who noAcct).supply then td0_unindexedSupply (upgrade L) else 0) ≤
      (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) := by
    by_cases h0 : 0 < (L.accts.getD who noAcct).supply
    · simp only [if_pos h0]
      exact hSupUn
    · simp only [if_neg h0, Nat.le_refl]
  have hB : (if 0 < (L.accts.getD who noAcct).borrow then td0_unindexedBorrow (upgrade L) else 0) ≤
      (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0) := by
    by_cases h0 : 0 < (L.accts.getD who noAcct).borrow
    · simp only [if_pos h0]
      exact hBorUn
    · simp only [if_neg h0, Nat.le_refl]
  unfold td0_owedTo Legacy.owedTo
  rw [hAcctEq]
  omega

theorem aux_subChecked_eq (a b : Nat) :
    subChecked a b = if b ≤ a then some (a - b) else none := by rfl

theorem aux_updS1 (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    (if s.supplyState.block ≤ s.blockNumber then (1:Nat) else 2) = 1 := by simp [hle]

theorem aux_sub_le (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [hle]

theorem aux_sub_nle (s : St) (hle : ¬ s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = none := by
  unfold subChecked
  simp [hle]

theorem aux_updSupply_rw (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      (let deltaBlocks := s.blockNumber - s.supplyState.block;
      if deltaBlocks > 0 ∧ s.supplyState.speed > 0 then
        let supplyTokens := totalSupply s
        let compAccrued := deltaBlocks * s.supplyState.speed
        let ratio := if supplyTokens > 0 then fraction compAccrued supplyTokens else 0
        some ({ s with supplyState := { s.supplyState with index := s.supplyState.index + ratio, block := s.blockNumber } } : St)
      else if deltaBlocks > 0 then
        some ({ s with supplyState := { s.supplyState with block := s.blockNumber } } : St)
      else (some s : Option St)) := by
  unfold updateCompSupplyIndex
  rw [aux_sub_le s hle]

theorem aux_updSupply_some2 (s t : St) (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · exact hle
  · rw [aux_sub_nle s hle] at h
    simp at h

theorem aux_opt_some_eq {α : Type} (x y : α) (h : (some x : Option α) = some y) : x = y := by cases h; rfl









theorem plan3_setCompSpeedInternal_spec (s : St) (a b : Nat) (t : St)
    (h : setCompSpeedInternal s a b = some t) :
    SpeedsSet s a b t := by sorry

theorem tmp_side_eta (sd : Side) (n : Nat) (h : sd.block = n) :
    ({ sd with block := n } : Side) = sd := by
  cases sd with
  | mk idx blk spd =>
    simp only at h ⊢
    rw [h]

theorem plan3_updateSupplyIndex_accrue (s : St) (t : St)
    (h : updateCompSupplyIndex s = some t) :
    t = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hle : s.supplyState.block ≤ s.blockNumber := aux_updSupply_some2 s t h
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := aux_sub_le s hle
  unfold updateCompSupplyIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide
  by_cases hd : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [if_pos hd] at h
    by_cases hpos : 0 < totalSupply s
    · simp only [if_pos hpos] at h
      have hTT : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s := ⟨hd.1, hd.2, hpos⟩
      rw [if_pos hTT]
      cases h
      rfl
    · have hnpos : ¬ 0 < totalSupply s := by omega
      simp only [if_neg hnpos] at h
      have hFF : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      rw [if_neg hFF]
      cases h
      rfl
  · simp only [if_neg hd] at h
    by_cases hd2 : s.blockNumber - s.supplyState.block > 0
    · simp only [if_pos hd2] at h
      have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      rw [if_neg hneg]
      cases h
      rfl
    · have hnd : ¬ s.blockNumber - s.supplyState.block > 0 := by omega
      simp only [if_neg hnd] at h
      have hneg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      rw [if_neg hneg]
      cases h
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      have hS : ({ s.supplyState with block := s.blockNumber } : Side) = s.supplyState :=
        tmp_side_eta s.supplyState s.blockNumber hbeq
      cases s with
      | mk bn sup bor res ac =>
        simp only at hS hbeq ⊢
        simp only [hS]

theorem plan3_updateBorrowIndex_accrue_aux : True := trivial

theorem aux_borrow_block_le (s t : St) (h : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex at h
  unfold subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem aux_borrow_eta (sd : Side) (n : Nat) (h : sd.block = n) :
    ({ sd with block := n } : Side) = sd := by
  cases sd with
  | mk idx blk spd => simp only at h ⊢; rw [h]

theorem plan3_updateBorrowIndex_accrue (s : St) (t : St)
    (h : updateCompBorrowIndex s = some t) :
    t = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hle : s.borrowState.block ≤ s.blockNumber := aux_borrow_block_le s t h
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [hle]
  unfold updateCompBorrowIndex at h
  rw [hsub] at h
  simp only at h
  unfold accrueSide
  by_cases hd : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [if_pos hd] at h
    by_cases hpos : 0 < totalBorrows s
    · simp only [if_pos hpos] at h
      have hTT : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s := ⟨hd.1, hd.2, hpos⟩
      rw [if_pos hTT]
      cases h
      rfl
    · have hnpos : ¬ 0 < totalBorrows s := by omega
      simp only [if_neg hnpos] at h
      have hFF : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      rw [if_neg hFF]
      cases h
      rfl
  · simp only [if_neg hd] at h
    by_cases hd2 : s.blockNumber - s.borrowState.block > 0
    · simp only [if_pos hd2] at h
      have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      rw [if_neg hneg]
      cases h
      rfl
    · have hnd : ¬ s.blockNumber - s.borrowState.block > 0 := by omega
      simp only [if_neg hnd] at h
      have hneg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      rw [if_neg hneg]
      cases h
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      have hS : ({ s.borrowState with block := s.blockNumber } : Side) = s.borrowState :=
        aux_borrow_eta s.borrowState s.blockNumber hbeq
      cases s with
      | mk bn sup bor res ac =>
        simp only at hS hbeq ⊢
        simp only [hS]

theorem plan3_setSupplySpeed_spec (s : St) (sup : Nat) (t : St)
    (h : setSupplySpeed s sup = some t) :
    (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = sup
  · have hcond : ¬ s.supplyState.speed ≠ sup := by simp [heq]
    rw [if_neg hcond] at h
    have ht : s = t := by cases h; rfl
    subst ht
    constructor
    · intro hne; exact absurd hne hcond
    · simp [heq]
  · have hcond : s.supplyState.speed ≠ sup := heq
    rw [if_pos hcond] at h
    cases hU : updateCompSupplyIndex s with
    | none =>
      rw [hU] at h
      simp at h
    | some s1 =>
      rw [hU] at h
      simp only [Option.map_some] at h
      have hle : s.supplyState.block ≤ s.blockNumber :=
        aux_updSupply_some2 s s1 hU
      have hs1 : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
        plan3_updateSupplyIndex_accrue s s1 hU
      cases h
      rw [hs1]
      constructor
      · intro _; exact hle
      · simp only [if_neg heq]

theorem plan3_setBorrowSpeed_spec_proof (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = bor
  · have hcond : ¬ s.borrowState.speed ≠ bor := by simp [heq]
    rw [if_neg hcond] at h
    have ht : s = t := by cases h; rfl
    subst ht
    constructor
    · intro hne; exact absurd hne hcond
    · simp [heq]
  · have hcond : s.borrowState.speed ≠ bor := heq
    rw [if_pos hcond] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      rw [hU] at h
      simp at h
    | some s1 =>
      rw [hU] at h
      simp only [Option.map_some] at h
      have hle : s.borrowState.block ≤ s.blockNumber :=
        aux_borrow_block_le s s1 hU
      have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        plan3_updateBorrowIndex_accrue s s1 hU
      cases h
      rw [hs1]
      constructor
      · intro _; exact hle
      · simp only [if_neg heq]

theorem plan3_setBorrowSpeed_spec_aux_use (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } :=
  plan3_setBorrowSpeed_spec_proof s bor t h

theorem plan3_setBorrowSpeed_spec_alt (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } :=
  plan3_setBorrowSpeed_spec_proof s bor t h

theorem plan3_setBorrowSpeed_spec (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = bor
  · have hcond : ¬ s.borrowState.speed ≠ bor := by simp [heq]
    rw [if_neg hcond] at h
    have ht : s = t := by cases h; rfl
    subst ht
    constructor
    · intro hne; exact absurd hne hcond
    · simp [heq]
  · have hcond : s.borrowState.speed ≠ bor := heq
    rw [if_pos hcond] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      rw [hU] at h
      simp at h
    | some s1 =>
      rw [hU] at h
      simp only [Option.map_some] at h
      have hle : s.borrowState.block ≤ s.blockNumber :=
        aux_borrow_block_le s s1 hU
      have hs1 : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        plan3_updateBorrowIndex_accrue s s1 hU
      cases h
      rw [hs1]
      constructor
      · intro _; exact hle
      · simp only [if_neg heq]

theorem plan3_compose_with_test (s : St) (X : Side) (Y : Side) :
    ({ ({ s with supplyState := X } : St) with borrowState := Y } : St) =
    ({ s with supplyState := X, borrowState := Y } : St) := by
  cases s <;> rfl

theorem plan3_mid_projs (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    mid.borrowState = s.borrowState := by
  rw [hmidEq]

theorem plan3_compose_gen3 (s : St) (X Y : Side) :
    ({ ({ s with supplyState := X } : St) with borrowState := Y } : St) =
    ({ s with supplyState := X, borrowState := Y } : St) := by
  cases s with
  | mk bn sup bor res ac => rfl

theorem plan3_mid_block (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    mid.blockNumber = s.blockNumber := by
  rw [hmidEq]

theorem plan3_mid_accts (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    mid.accts = s.accts := by
  rw [hmidEq]

theorem plan3_mid_borrows (s mid : St) (a : Nat)
    (hmidEq : mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) :
    totalBorrows mid = totalBorrows s := by
  have hac : mid.accts = s.accts := plan3_mid_accts s mid a hmidEq
  unfold totalBorrows
  rw [hac]

theorem td0_setSpeeds_effect_aux_tmp : True := trivial

theorem req_set_speeds_check_tmp : SpeedsSet (St.mk 0 ⟨0,0,0⟩ ⟨0,0,0⟩ 0 []) 0 0 (St.mk 0 ⟨0,0,0⟩ ⟨0,0,0⟩ 0 []) := by
  unfold SpeedsSet
  simp

theorem tmp_do_bind (s : St) (who : Account) :
    (do let s1 ← updateCompSupplyIndex s
        distributeSupplierComp s1 who) =
      Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) := by
  rfl

theorem tmp_comp_eq (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      Option.bind (updateCompSupplyIndex s) (fun s1 => distributeSupplierComp s1 who) := by
  unfold comptroller
  rfl

theorem tmp_list_modify_unfold (l : List Acct) (f : Acct → Acct) :
    l.modify 0 f = match l with | [] => [] | hd :: tl => f hd :: tl := by
  cases l <;> rfl

theorem tmp_list_modify_succ (hd : Acct) (tl : List Acct) (n : Nat) (f : Acct → Acct) :
    (hd :: tl).modify (n+1) f = hd :: tl.modify n f := by
  rfl

#check List.modify

theorem aux_modify_congr2 (l : List Acct) (i : Nat) (f g : Acct → Acct)
    (hfg : f (l.getD i noAcct) = g (l.getD i noAcct)) :
    l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hfg
      show (f hd :: tl) = (g hd :: tl)
      rw [hfg]
    | succ n =>
      simp only [List.getD_cons_succ] at hfg
      show hd :: tl.modify n f = hd :: tl.modify n g
      rw [ih n hfg]

theorem tmp_bind_none_contra (s : St) (who : Account) (s' : St)
    (hU : updateCompSupplyIndex s = none)
    (h : comptroller s (.supplyHook who) = some s') : False := by
  have hComp := tmp_comp_eq s who
  rw [hComp, hU] at h
  simp at h

theorem tmp_bind_reduce2 (s : St) (who : Account) (s' s1 : St)
    (hU : updateCompSupplyIndex s = some s1)
    (h : comptroller s (.supplyHook who) = some s') :
    distributeSupplierComp s1 who = some s' := by
  have hComp := tmp_comp_eq s who
  rw [hComp, hU] at h
  simpa using h



theorem plan4_updateCompSupplyIndex_spec (s s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ∧
    s1.accts = s.accts := by
  have hle : s.supplyState.block ≤ s.blockNumber := aux_updSupply_some2 s s1 h
  have heq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    plan3_updateSupplyIndex_accrue s s1 h
  refine ⟨hle, heq, ?_⟩
  rw [heq]


theorem plan4_distributeSupplierComp_spec (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
        s.supplyState.index ∧
    s' = s.withAcct who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s.supplyState.index)
          s.supplyState.index } := by sorry

theorem plan4_supplyDistributed_of_steps (s s1 s' : St) (who : Account)
    (hU : updateCompSupplyIndex s = some s1)
    (hD : distributeSupplierComp s1 who = some s') :
    SupplyDistributed s who s' := by sorry

theorem plan4_test_ge (index : Nat) :
    (index ≥ compInitialIndex) = (compInitialIndex ≤ index) := by rfl

theorem plan4_accrualStart_eq2 (recorded index : Nat) :
    (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases hrec : recorded = 0
  · simp [hrec]
  · simp [hrec]

theorem plan4_accrualStart_eq (recorded index : Nat) :
    (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) =
      accrualStart recorded index := plan4_accrualStart_eq2 recorded index

theorem plan4_updateCompSupplyIndex_spec_check (s s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ∧
    s1.accts = s.accts := by
  have hle : s.supplyState.block ≤ s.blockNumber := aux_updSupply_some2 s s1 h
  have heq : s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
    plan3_updateSupplyIndex_accrue s s1 h
  refine ⟨hle, heq, ?_⟩
  rw [heq]

theorem plan4_distributeSupplierComp_spec_aux1 (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  rw [plan4_accrualStart_eq2]

theorem tmp_parse_test (s : St) (who : Account) :
    s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index } : Acct)) = s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index } : Acct)) := by
  rfl

theorem tmp_FG_eq2 (s : St) (a : Acct) :
    ({ a with supplierIndex := s.supplyState.index } : Acct) = ({ a with supplierIndex := s.supplyState.index } : Acct) := by
  rfl

theorem tmp_twofield (s : St) (a : Acct) (x : Nat) :
    ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + x } : Acct) =
    ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + x } : Acct) := by
  rfl

theorem tmp_FG_eq3 (s : St) (who : Account) :
    (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + 1 } : Acct)) (List.getD s.accts who noAcct) = (fun a : Acct => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + 1 } : Acct)) (List.getD s.accts who noAcct) := by
  rfl

theorem plan4_impl_eq_spec_at (s : St) (who : Account) : (({ List.getD s.accts who noAcct with supplierIndex := s.supplyState.index, accrued := (List.getD s.accts who noAcct).accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) = (({ List.getD s.accts who noAcct with supplierIndex := s.supplyState.index, accrued := (List.getD s.accts who noAcct).accrued + creditFor (List.getD s.accts who noAcct).supply (accrualStart (List.getD s.accts who noAcct).supplierIndex s.supplyState.index) s.supplyState.index } : Acct)) := by
  have e1 : (List.getD s.accts who noAcct).supply = (s.acct who).supply := rfl
  have e2 : (List.getD s.accts who noAcct).supplierIndex = (s.acct who).supplierIndex := rfl
  rw [e1, e2]
  rfl

theorem plan4_supplyDistributed_of_steps_aux_tmp2 : True := trivial

theorem aux_withAcct_after_supply (s : St) (X : Side) (who : Account) (f : Acct → Acct) :
    (({ s with supplyState := X } : St).withAcct who f) =
    ({ s with supplyState := X, accts := s.accts.modify who f } : St) := by
  cases s with
  | mk bn sup bor res ac =>
    rfl

theorem plan4_supplyDistributed_of_steps_try3 (s s1 s' : St) (who : Account)
    (hU : updateCompSupplyIndex s = some s1)
    (hD : distributeSupplierComp s1 who = some s') :
    SupplyDistributed s who s' := by
  have hUspec := plan4_updateCompSupplyIndex_spec s s1 hU
  obtain ⟨hblk, hs1eq, haccts⟩ := hUspec
  have hDspec := plan4_distributeSupplierComp_spec s1 who s' hD
  obtain ⟨hle1, heq1⟩ := hDspec
  have hIdx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [hs1eq]
  have hAcctEq : s1.acct who = s.acct who := by
    unfold St.acct
    rw [haccts]
  have hle2 : accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [← hIdx, ← hAcctEq]
    exact hle1
  refine ⟨hblk, hle2, ?_⟩
  subst hs1eq
  rw [heq1]
  simp only [St.withAcct]

theorem myDist_supply (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
        s.supplyState.index ∧
    s' = s.withAcct who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s.supplyState.index)
          s.supplyState.index } := by
  unfold distributeSupplierComp at h
  simp only at h
  have hAcc : (if (s.acct who).supplierIndex = 0 ∧ s.supplyState.index ≥ compInitialIndex then compInitialIndex
      else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := by
    rw [plan4_accrualStart_eq2]
  rw [hAcc] at h
  cases hSub : subChecked s.supplyState.index (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none =>
    rw [hSub] at h
    simp at h
  | some delta =>
    rw [hSub] at h
    have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by
      unfold subChecked at hSub
      by_cases hc : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
      · exact hc
      · simp [hc] at hSub
    have hdelta : delta = s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index := by
      unfold subChecked at hSub
      simp [hle] at hSub
      exact hSub.symm
    simp only [Option.some_inj] at h
    subst h
    rw [hdelta]
    constructor
    · exact hle
    · unfold St.withAcct
      congr 1
      apply aux_modify_congr2
      show ({ List.getD s.accts who noAcct with supplierIndex := s.supplyState.index, accrued := (List.getD s.accts who noAcct).accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct) = _
      have e1 : (List.getD s.accts who noAcct).supply = (s.acct who).supply := rfl
      have e2 : (List.getD s.accts who noAcct).supplierIndex = (s.acct who).supplierIndex := rfl
      rw [e1, e2]
      unfold mulDouble creditFor
      rfl

theorem td0_supplyHook_effect_proof (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' := by
  have hComp := tmp_comp_eq s who
  rw [hComp] at h
  unfold Option.bind at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    rw [hU] at h
    simp at h
  | some s1 =>
    rw [hU] at h
    simp only at h
    have hD : distributeSupplierComp s1 who = some s' := h
    have hUspec := plan4_updateCompSupplyIndex_spec s s1 hU
    obtain ⟨hblk, hs1eq, haccts⟩ := hUspec
    have hDspec := myDist_supply s1 who s' hD
    obtain ⟨hle1, heq1⟩ := hDspec
    have hIdx : s1.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hs1eq]
    have hAcctEq : s1.acct who = s.acct who := by
      unfold St.acct
      rw [haccts]
    have hle2 : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [← hIdx, ← hAcctEq]
      exact hle1
    refine ⟨hblk, hle2, ?_⟩
    subst hs1eq
    rw [heq1]
    simp only [St.withAcct]

theorem td0_supplyHook_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' :=
  td0_supplyHook_effect_proof s who s' h

theorem myDist_borrow (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
        s.borrowState.index ∧
    s' = s.withAcct who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index)
          s.borrowState.index } := by
  unfold distributeBorrowerComp at h
  simp only at h
  have hAcc : (if (s.acct who).borrowerIndex = 0 ∧ s.borrowState.index ≥ compInitialIndex then compInitialIndex
      else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
    rw [plan4_accrualStart_eq2]
  rw [hAcc] at h
  cases hSub : subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none =>
    rw [hSub] at h
    simp at h
  | some delta =>
    rw [hSub] at h
    have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index := by
      unfold subChecked at hSub
      by_cases hc : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
      · exact hc
      · simp [hc] at hSub
    have hdelta : delta = s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
      unfold subChecked at hSub
      simp [hle] at hSub
      exact hSub.symm
    simp only [Option.some_inj] at h
    subst h
    rw [hdelta]
    constructor
    · exact hle
    · unfold St.withAcct
      congr 1
      apply aux_modify_congr2
      show ({ List.getD s.accts who noAcct with borrowerIndex := s.borrowState.index, accrued := (List.getD s.accts who noAcct).accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct) = _
      have e1 : (List.getD s.accts who noAcct).borrow = (s.acct who).borrow := rfl
      have e2 : (List.getD s.accts who noAcct).borrowerIndex = (s.acct who).borrowerIndex := rfl
      rw [e1, e2]
      unfold mulDouble creditFor
      rfl

theorem plan4_updateCompBorrowIndex_spec (s s1 : St)
    (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1 = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ∧
    s1.accts = s.accts := by
  have hle : s.borrowState.block ≤ s.blockNumber := aux_borrow_block_le s s1 h
  have heq : s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
    plan3_updateBorrowIndex_accrue s s1 h
  refine ⟨hle, heq, ?_⟩
  rw [heq]

theorem td0_borrowHook_effect_proved (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    BorrowDistributed s who s' := by
  have hComp : comptroller s (.borrowHook who) =
      Option.bind (updateCompBorrowIndex s) (fun s1 => distributeBorrowerComp s1 who) := rfl
  rw [hComp] at h
  unfold Option.bind at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    rw [hU] at h
    simp at h
  | some s1 =>
    rw [hU] at h
    simp only at h
    have hD : distributeBorrowerComp s1 who = some s' := h
    have hUspec := plan4_updateCompBorrowIndex_spec s s1 hU
    obtain ⟨hblk, hs1eq, haccts⟩ := hUspec
    have hDspec := myDist_borrow s1 who s' hD
    obtain ⟨hle1, heq1⟩ := hDspec
    have hIdx : s1.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hs1eq]
    have hAcctEq : s1.acct who = s.acct who := by
      unfold St.acct
      rw [haccts]
    have hle2 : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [← hIdx, ← hAcctEq]
      exact hle1
    refine ⟨hblk, hle2, ?_⟩
    subst hs1eq
    rw [heq1]
    simp only [St.withAcct]

theorem td0_borrowHook_effect (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    BorrowDistributed s who s' :=
  td0_borrowHook_effect_proved s who s' h

theorem td0_setSpeeds_some_auxA (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := aux_sub_le s hle
  unfold updateCompSupplyIndex
  rw [hsub]
  by_cases h1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · simp only [if_pos h1, Option.isSome_some]
  · simp only [if_neg h1]
    by_cases h2 : s.blockNumber - s.supplyState.block > 0
    · simp only [if_pos h2, Option.isSome_some]
    · simp only [if_neg h2, Option.isSome_some]

theorem td0_setSpeeds_some_auxB (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [hle]
  unfold updateCompBorrowIndex
  rw [hsub]
  by_cases h1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · simp only [if_pos h1, Option.isSome_some]
  · simp only [if_neg h1]
    by_cases h2 : s.blockNumber - s.borrowState.block > 0
    · simp only [if_pos h2, Option.isSome_some]
    · simp only [if_neg h2, Option.isSome_some]

theorem td0_setSpeeds_some_clean2 (s : St) (a b : Nat) (hs : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome = true := by
  have hsSup : s.supplyState.block ≤ s.blockNumber := hs.1
  have hsBor : s.borrowState.block ≤ s.blockNumber := hs.2.1
  have hSup : (setSupplySpeed s a).isSome = true := by
    unfold setSupplySpeed
    by_cases heq : s.supplyState.speed ≠ a
    · rw [if_pos heq]
      have hU := td0_setSpeeds_some_auxA s hsSup
      cases hU' : updateCompSupplyIndex s
      · rw [hU'] at hU
        contradiction
      · rfl
    · rw [if_neg heq]
      rfl
  obtain ⟨mid, hMid⟩ : ∃ mid, setSupplySpeed s a = some mid := Option.isSome_iff_exists.mp hSup
  have hspec := plan3_setSupplySpeed_spec s a mid hMid
  obtain ⟨_, hmidEq⟩ := hspec
  have hMidBlock : mid.blockNumber = s.blockNumber := plan3_mid_block s mid a hmidEq
  have hMidBorSt : mid.borrowState = s.borrowState := plan3_mid_projs s mid a hmidEq
  have hMidBor : mid.borrowState.block ≤ mid.blockNumber := by
    rw [hMidBorSt, hMidBlock]
    exact hsBor
  have hBorSome : (setBorrowSpeed mid b).isSome = true := by
    unfold setBorrowSpeed
    by_cases heq2 : mid.borrowState.speed ≠ b
    · rw [if_pos heq2]
      have hU2 := td0_setSpeeds_some_auxB mid hMidBor
      cases hU2' : updateCompBorrowIndex mid
      · rw [hU2'] at hU2
        contradiction
      · rfl
    · rw [if_neg heq2]
      rfl
  have hComp : comptroller s (.setSpeeds a b) =
      Option.bind (setSupplySpeed s a) (fun m => setBorrowSpeed m b) := rfl
  rw [hComp, hMid]
  exact hBorSome

theorem plan5_updateSupply_some (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by
  exact td0_setSpeeds_some_auxA s h


theorem plan5_updateBorrow_some (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := td0_setSpeeds_some_auxB s h


theorem plan5_updateSupply_preserve (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState := by
  have heq := plan3_updateSupplyIndex_accrue s t h
  rw [heq]
  exact ⟨rfl, rfl⟩


theorem plan5_setSupply_some (s : St) (a : Nat)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (setSupplySpeed s a).isSome = true := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed ≠ a
  · rw [if_pos heq]
    have hU := plan5_updateSupply_some s h
    cases hE : updateCompSupplyIndex s with
    | none =>
      have hF : (updateCompSupplyIndex s).isSome = false := by rw [hE]; rfl
      rw [hF] at hU
      contradiction
    | some s1 =>
      rfl
  · rw [if_neg heq]; rfl


theorem plan5_setSupply_preserve (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    mid.blockNumber = s.blockNumber ∧ mid.borrowState = s.borrowState := by
  have hspec := plan3_setSupplySpeed_spec s a mid h
  obtain ⟨_, hmidEq⟩ := hspec
  rw [hmidEq]
  exact ⟨rfl, rfl⟩


theorem plan5_setBorrow_some (s : St) (b : Nat)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (setBorrowSpeed s b).isSome = true := by
  unfold setBorrowSpeed
  by_cases heq : s.borrowState.speed ≠ b
  · rw [if_pos heq]
    have hU := plan5_updateBorrow_some s h
    cases hE : updateCompBorrowIndex s with
    | none =>
      have hF : (updateCompBorrowIndex s).isSome = false := by rw [hE]; rfl
      rw [hF] at hU
      contradiction
    | some s1 =>
      rfl
  · rw [if_neg heq]; rfl


theorem plan5_updateSupply_preserve_proof3 (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState := by
  have heq := plan3_updateSupplyIndex_accrue s t h
  rw [heq]
  exact ⟨rfl, rfl⟩

theorem plan5_preserve_inline_test (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState := by
  have heq := plan3_updateSupplyIndex_accrue s t h
  rw [heq]
  exact ⟨rfl, rfl⟩

theorem plan5_setSupply_some_proof (s : St) (a : Nat)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (setSupplySpeed s a).isSome = true := by
  unfold setSupplySpeed
  by_cases heq : s.supplyState.speed ≠ a
  · rw [if_pos heq]
    have hU := plan5_updateSupply_some s h
    cases hE : updateCompSupplyIndex s with
    | none =>
      have hF : (updateCompSupplyIndex s).isSome = false := by rw [hE]; rfl
      rw [hF] at hU
      contradiction
    | some s1 =>
      rfl
  · rw [if_neg heq]; rfl

theorem plan5_setSupply_preserve2 (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    mid.blockNumber = s.blockNumber ∧ mid.borrowState = s.borrowState := by
  have hspec := plan3_setSupplySpeed_spec s a mid h
  obtain ⟨_, hmidEq⟩ := hspec
  rw [hmidEq]
  exact ⟨rfl, rfl⟩

theorem plan5_setSupply_preserve_inline (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    mid.blockNumber = s.blockNumber ∧ mid.borrowState = s.borrowState := by
  have hspec := plan3_setSupplySpeed_spec s a mid h
  obtain ⟨_, hmidEq⟩ := hspec
  rw [hmidEq]
  exact ⟨rfl, rfl⟩

theorem td0_setSpeeds_some_proof (s : St) (a b : Nat) (hs : Consistent s) :
    (comptroller s (.setSpeeds a b)).isSome := by
  exact td0_setSpeeds_some_clean2 s a b hs

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hs
  cases c with
  | supplyHook who => exact td0_supplyHook_some s who hs
  | borrowHook who => exact td0_borrowHook_some s who hs
  | claim who => exact td0_claim_some s who hs
  | setSpeeds a b => exact td0_setSpeeds_some s a b hs

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  exact td0_supplyHook_effect s who s' h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  exact td0_borrowHook_effect s who s' h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  exact td0_claim_effect s who s' h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact td0_setSpeeds_effect s a b s' h

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hWF
  have hrun := td0_run_credited_bound (L.compSpeed, L.compSpeed) (upgrade L) ops
    (td0_inv_upgrade L hWF)
  have howed := td0_owed_upgrade_le L hWF
  omega

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hWF
  have hrun := td0_run_creditedTo_bound (L.compSpeed, L.compSpeed) (upgrade L) ops
    (td0_inv_upgrade L hWF) who
  have howed := td0_owedTo_upgrade_le L hWF who
  omega

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hWF hNo
  have hinv := td0_run_inv (L.compSpeed, L.compSpeed) (upgrade L) history
    (td0_inv_upgrade L hWF)
  have hrun := td0_run_creditedTo_bound (speedsAfter (L.compSpeed, L.compSpeed) history)
    (run comptroller (upgrade L) history) ops hinv who
  have hzero := td0_owedTo_of_noPosition (run comptroller (upgrade L) history) who hNo
  omega

end CompRewards
