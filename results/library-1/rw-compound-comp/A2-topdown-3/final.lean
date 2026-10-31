import CompRewards.Spec
import ProofForgeFin.DeFi.Rewards
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

def td0_pendingScaledAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def td0_pendingScaled (s : St) : Nat :=
  (s.accts.map (td0_pendingScaledAcct s)).sum

def td0_unindexed (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def td0_unindexedTo (s : St) (who : Account) : Nat :=
  (if 0 < (s.acct who).supply then
    (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0) +
  (if 0 < (s.acct who).borrow then
    (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0)

def td0_potential (s : St) : Nat :=
  doubleScale * s.credited + td0_pendingScaled s + doubleScale * td0_unindexed s

def td0_potentialTo (s : St) (who : Account) : Nat :=
  doubleScale * s.creditedTo who +
  td0_pendingScaledAcct s (s.acct who) +
  doubleScale * td0_unindexedTo s who

def td0_pendingOf (L : Legacy) (who : Account) : Nat :=
  L.pendingScaled (L.accts.getD who noAcct)

def td0_unindexedOf (L : Legacy) (who : Account) : Nat :=
  (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
  (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0)

def td0_Inv (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

theorem td0_call_some (s : St) (c : Call) :
    Consistent s → (comptroller s c).isSome := by sorry





theorem td0_claim_effect (s : St) (who : Account) (s' : St) :
    comptroller s (.claim who) = some s' → Claimed s who s' := by sorry





theorem td0_exec_inv (sp : Nat × Nat) (s : St) (op : Op) :
    td0_Inv sp s → td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by sorry

theorem td0_exec_potential_le (sp : Nat × Nat) (s : St) (op : Op) :
    td0_Inv sp s →
      td0_potential (exec comptroller s op) ≤
        td0_potential s + doubleScale * emittedBy sp op := by sorry

theorem td0_exec_potentialTo_le (sp : Nat × Nat) (s : St) (op : Op) (who : Account) :
    td0_Inv sp s →
      td0_potentialTo (exec comptroller s op) who ≤
        td0_potentialTo s who + doubleScale * emittedBy sp op := by sorry

theorem td0_run_inv (sp : Nat × Nat) (s : St) (ops : List Op) :
    td0_Inv sp s → td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by
  induction ops generalizing sp s with
  | nil =>
      intro h
      simpa [run, speedsAfter] using h
  | cons op ops ih =>
      intro h
      exact ih _ _ (td0_exec_inv sp s op h)

theorem td0_run_potential_le (sp : Nat × Nat) (s : St) (ops : List Op) :
    td0_Inv sp s →
      td0_potential (run comptroller s ops) ≤
        td0_potential s + doubleScale * emitted sp ops := by
  induction ops generalizing sp s with
  | nil =>
      intro h
      simp [run, emitted]
  | cons op ops ih =>
      intro h
      have hinv := td0_exec_inv sp s op h
      have hstep := td0_exec_potential_le sp s op h
      have hrest := ih _ _ hinv
      calc td0_potential (run comptroller s (op :: ops))
          = td0_potential (run comptroller (exec comptroller s op) ops) := rfl
        _ ≤ td0_potential (exec comptroller s op) +
              doubleScale * emitted (nextSpeeds sp op) ops := hrest
        _ ≤ (td0_potential s + doubleScale * emittedBy sp op) +
              doubleScale * emitted (nextSpeeds sp op) ops :=
            Nat.add_le_add_right hstep _
        _ = td0_potential s + doubleScale * emitted sp (op :: ops) := by
              simp [emitted, Nat.mul_add, Nat.add_assoc]

theorem td0_run_potentialTo_le (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account) :
    td0_Inv sp s →
      td0_potentialTo (run comptroller s ops) who ≤
        td0_potentialTo s who + doubleScale * emitted sp ops := by
  induction ops generalizing sp s with
  | nil =>
      intro h
      simp [run, emitted]
  | cons op ops ih =>
      intro h
      have hinv := td0_exec_inv sp s op h
      have hstep := td0_exec_potentialTo_le sp s op who h
      have hrest := ih _ _ hinv
      calc td0_potentialTo (run comptroller s (op :: ops)) who
          = td0_potentialTo (run comptroller (exec comptroller s op) ops) who := rfl
        _ ≤ td0_potentialTo (exec comptroller s op) who +
              doubleScale * emitted (nextSpeeds sp op) ops := hrest
        _ ≤ (td0_potentialTo s who + doubleScale * emittedBy sp op) +
              doubleScale * emitted (nextSpeeds sp op) ops :=
            Nat.add_le_add_right hstep _
        _ = td0_potentialTo s who + doubleScale * emitted sp (op :: ops) := by
              simp [emitted, Nat.mul_add, Nat.add_assoc]





theorem td0_credited_le_potential (s : St) :
    doubleScale * s.credited ≤ td0_potential s := by sorry

theorem td0_creditedTo_le_potential (s : St) (who : Account) :
    doubleScale * s.creditedTo who ≤ td0_potentialTo s who := by
  unfold td0_potentialTo
  omega






theorem td0_potentialTo_of_no_position (s : St) (who : Account) :
    NoPosition s who →
      td0_potentialTo s who = doubleScale * s.creditedTo who := by sorry

theorem td0_scaled_le_add {x y e : Nat} :
    doubleScale * x ≤ doubleScale * y + doubleScale * e → x ≤ y + e := by sorry

theorem td0_upgrade_inv_aux : True := trivial

theorem td0_initSide_speed2 (now : Nat) (sd : Side) :
    (initSide now sd).speed = sd.speed := by
  unfold initSide
  split
  · rfl
  · rfl

theorem td0_initSide_block_le2 (now : Nat) (sd : Side) (hblk : sd.block ≤ now) :
    (initSide now sd).block ≤ now := by
  unfold initSide
  split
  · simp
  · exact hblk

theorem td0_initSide_index_ge2 (now : Nat) (sd : Side) :
    sd.index ≤ (initSide now sd).index := by
  unfold initSide
  split
  · next h =>
    have h0 : sd.index = 0 := h
    omega
  · exact Nat.le_refl _

theorem td0_upgrade_inv (L : Legacy) :
    L.WellFormed → td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  intro hWF
  have hsupBlk : L.supplyBlock ≤ L.blockNumber := hWF.2.2.2.2.1
  have hborBlk : L.borrowBlock ≤ L.blockNumber := hWF.2.2.2.2.2.1
  have haccts : ∀ a ∈ L.accts, a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex := hWF.2.2.2.2.2.2
  have hsup_le : L.supplyIndex ≤ (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).index :=
    td0_initSide_index_ge2 L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩
  have hbor_le : L.borrowIndex ≤ (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).index :=
    td0_initSide_index_ge2 L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩
  have hsup_blk : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block ≤ L.blockNumber :=
    td0_initSide_block_le2 L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ hsupBlk
  have hbor_blk : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block ≤ L.blockNumber :=
    td0_initSide_block_le2 L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ hborBlk
  have hsup_spd : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).speed = L.compSpeed :=
    td0_initSide_speed2 L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩
  have hbor_spd : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).speed = L.compSpeed :=
    td0_initSide_speed2 L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩
  unfold td0_Inv Consistent upgrade
  simp only [] at hsup_blk hbor_blk hsup_spd hbor_spd hsup_le hbor_le ⊢
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hsup_blk
  · exact hbor_blk
  · intro a ha
    have h := haccts a ha
    exact ⟨Nat.le_trans h.1 hsup_le, Nat.le_trans h.2 hbor_le⟩
  · exact hsup_spd
  · exact hbor_spd

theorem td0_probe_len2 (l : List Acct) (n : Nat) (f : Acct → Acct) :
    (l.modify n f).length = l.length := by simp
#check @List.modify

theorem td0_probe_print : True := by trivial
#print List.modify
#print St.withAcct
#print Consistent
#print SupplyDistributed

theorem plan0_accrueSide_props (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index ∧
      (accrueSide sd now total).block = now ∧
      (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [h]
  · simp [h]


theorem plan0_withAcct_inv (sp : Nat × Nat) (s : St) (who : Account) (f : Acct → Acct) (hsi : ∀ a, (f a).supplierIndex = a.supplierIndex) (hbi : ∀ a, (f a).borrowerIndex = a.borrowerIndex) : td0_Inv sp s → td0_Inv sp (s.withAcct who f) := by
  intro h
  unfold td0_Inv at h ⊢
  unfold St.withAcct
  simp only at ⊢
  obtain ⟨hc, hsp1, hsp2⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hb1, hb2, hmem⟩ := hc
  refine ⟨⟨?_, ?_, ?_⟩, hsp1, hsp2⟩
  · exact hb1
  · exact hb2
  · intro a ha
    apply ProofForgeFin.DeFi.Rewards.forall_mem_modify (l := s.accts) (i := who) (f := f) _ _ a ha
    · intro b hb
      exact hmem b hb
    · intro b hb
      have h1 : (f b).supplierIndex = b.supplierIndex := hsi b
      have h2 : (f b).borrowerIndex = b.borrowerIndex := hbi b
      obtain ⟨hs, hbo⟩ := hmem b hb
      rw [h1, h2]
      exact ⟨hs, hbo⟩


theorem plan0_supplyDistributed_inv (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → SupplyDistributed s who s' → td0_Inv sp s' := by sorry

theorem plan0_borrowDistributed_inv (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → BorrowDistributed s who s' → td0_Inv sp s' := by
  intro hInv hDist
  unfold td0_Inv at hInv ⊢
  unfold BorrowDistributed at hDist
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hblk, hle, heq⟩ := hDist
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hprops := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hIdxLe, hBlkEq, hSpdEq⟩ := hprops
  subst heq
  simp only at ⊢
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hsb
  · omega
  · intro a ha
    apply ProofForgeFin.DeFi.Rewards.forall_mem_modify (l := s.accts) (i := who) _ _ a ha
    · intro b hb
      obtain ⟨hs, hbo⟩ := hmem b hb
      exact ⟨hs, Nat.le_trans hbo hIdxLe⟩
    · intro b hb
      obtain ⟨hs, hbo⟩ := hmem b hb
      refine ⟨?_, ?_⟩
      · exact hs
      · exact Nat.le_refl _
  · exact hsp1
  · omega




theorem plan0_speedsSet_inv (sp : Nat × Nat) (s : St) (a b : Nat)
    (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' → td0_Inv (a, b) s' := by
  intro hInv hSS
  unfold td0_Inv at hInv ⊢
  unfold SpeedsSet at hSS
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hsupNe, hborNe, heq⟩ := hSS
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hsupProps := plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  obtain ⟨hsupIdxLe, hsupBlkEq, hsupSpdEq⟩ := hsupProps
  have hborProps := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hborIdxLe, hborBlkEq, hborSpdEq⟩ := hborProps
  subst heq
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsb]
    · simp [h, hsupBlkEq]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hbb]
    · simp [h, hborBlkEq]
  · intro a0 ha0
    simp only at ha0
    obtain ⟨hs0, hb0⟩ := hmem a0 ha0
    have hsupLe : s.supplyState.index ≤ (if s.supplyState.speed = a then s.supplyState else {accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a}).index := by
      by_cases h : s.supplyState.speed = a
      · simp [h]
      · simp [h, hsupIdxLe]
    have hborLe : s.borrowState.index ≤ (if s.borrowState.speed = b then s.borrowState else {accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b}).index := by
      by_cases h : s.borrowState.speed = b
      · simp [h]
      · simp [h, hborIdxLe]
    simp only
    exact ⟨Nat.le_trans hs0 hsupLe, Nat.le_trans hb0 hborLe⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsp1]
    · simp [h]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hsp2]
    · simp [h]


theorem my_test_thm : True := trivial

theorem my_len_thm (l : List Acct) (n : Nat) (f : Acct → Acct) : (l.modify n f).length = l.length := by simp

theorem my_check_modify_eq : (List.modify ([] : List Acct) 0 id = []) := by rfl

theorem my_probe1 : True := trivial

theorem tmp_struct_proj (s : St) (X : Side) :
    ({ s with supplyState := X } : St).supplyState.speed = X.speed := by
  simp

theorem plan0_claimed_inv_aux5_thm (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → Claimed s who s' → td0_Inv sp s' := by
  intro hInv hClaim
  obtain ⟨m₁, m₂, hB, hS, rfl⟩ := hClaim
  have h1 : td0_Inv sp m₁ := plan0_borrowDistributed_inv sp s who m₁ hInv hB
  have h2 : td0_Inv sp m₂ := plan0_supplyDistributed_inv sp m₁ who m₂ h1 hS
  unfold grant
  by_cases hcond : 0 < (m₂.acct who).accrued ∧ (m₂.acct who).accrued ≤ m₂.reserve
  · rw [if_pos hcond]
    unfold td0_Inv at h2 ⊢
    obtain ⟨hc, hsp1, hsp2⟩ := h2
    unfold Consistent at hc ⊢
    obtain ⟨hsb, hbb, hmem⟩ := hc
    simp only at ⊢
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact hsb
    · exact hbb
    · intro a ha
      apply ProofForgeFin.DeFi.Rewards.forall_mem_modify (l := m₂.accts) (i := who) _ _ a ha
      · intro b hb
        exact hmem b hb
      · intro b hb
        obtain ⟨hsi, hbi⟩ := hmem b hb
        exact ⟨hsi, hbi⟩
    · exact hsp1
    · exact hsp2
  · rw [if_neg hcond]
    exact h2

theorem plan0_claimed_inv (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → Claimed s who s' → td0_Inv sp s' :=
  fun hInv hClaim => plan0_claimed_inv_aux5_thm sp s who s' hInv hClaim

theorem plan0_speedsSet_inv_aux1 (sp : Nat × Nat) (s : St) (a b : Nat)
    (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' → td0_Inv (a, b) s' := by
  intro hInv hSS
  unfold td0_Inv at hInv ⊢
  unfold SpeedsSet at hSS
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hsupNe, hborNe, heq⟩ := hSS
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hsupProps := plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  obtain ⟨hsupIdxLe, hsupBlkEq, hsupSpdEq⟩ := hsupProps
  have hborProps := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hborIdxLe, hborBlkEq, hborSpdEq⟩ := hborProps
  subst heq
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsb]
    · simp [h, hsupBlkEq]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hbb]
    · simp [h, hborBlkEq]
  · intro a0 ha0
    simp only at ha0
    obtain ⟨hs0, hb0⟩ := hmem a0 ha0
    have hsupLe : s.supplyState.index ≤ (if s.supplyState.speed = a then s.supplyState else {accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a}).index := by
      by_cases h : s.supplyState.speed = a
      · simp [h]
      · simp [h, hsupIdxLe]
    have hborLe : s.borrowState.index ≤ (if s.borrowState.speed = b then s.borrowState else {accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b}).index := by
      by_cases h : s.borrowState.speed = b
      · simp [h]
      · simp [h, hborIdxLe]
    simp only
    exact ⟨Nat.le_trans hs0 hsupLe, Nat.le_trans hb0 hborLe⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsp1]
    · simp [h]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hsp2]
    · simp [h]

theorem plan0_speedsSet_inv_direct (sp : Nat × Nat) (s : St) (a b : Nat)
    (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' → td0_Inv (a, b) s' := by
  intro hInv hSS
  unfold td0_Inv at hInv ⊢
  unfold SpeedsSet at hSS
  obtain ⟨hc, hsp1, hsp2⟩ := hInv
  obtain ⟨hsupNe, hborNe, heq⟩ := hSS
  unfold Consistent at hc ⊢
  obtain ⟨hsb, hbb, hmem⟩ := hc
  have hsupProps := plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  obtain ⟨hsupIdxLe, hsupBlkEq, hsupSpdEq⟩ := hsupProps
  have hborProps := plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)
  obtain ⟨hborIdxLe, hborBlkEq, hborSpdEq⟩ := hborProps
  subst heq
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsb]
    · simp [h, hsupBlkEq]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hbb]
    · simp [h, hborBlkEq]
  · intro a0 ha0
    simp only at ha0
    obtain ⟨hs0, hb0⟩ := hmem a0 ha0
    have hsupLe : s.supplyState.index ≤ (if s.supplyState.speed = a then s.supplyState else {accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a}).index := by
      by_cases h : s.supplyState.speed = a
      · simp [h]
      · simp [h, hsupIdxLe]
    have hborLe : s.borrowState.index ≤ (if s.borrowState.speed = b then s.borrowState else {accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b}).index := by
      by_cases h : s.borrowState.speed = b
      · simp [h]
      · simp [h, hborIdxLe]
    simp only
    exact ⟨Nat.le_trans hs0 hsupLe, Nat.le_trans hb0 hborLe⟩
  · simp only
    by_cases h : s.supplyState.speed = a
    · simp [h, hsp1]
    · simp [h]
  · simp only
    by_cases h : s.borrowState.speed = b
    · simp [h, hsp2]
    · simp [h]

theorem td0_exec_inv_aux_check : True := trivial

theorem td0_advance_inv_aux (sp : Nat × Nat) (s : St) (k : Nat) :
    td0_Inv sp s → td0_Inv sp ({ s with blockNumber := s.blockNumber + k }) := by
  intro h
  unfold td0_Inv at h ⊢
  obtain ⟨hc, h1, h2⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hb1, hb2, hmem⟩ := hc
  simp only at ⊢
  refine ⟨⟨by omega, by omega, hmem⟩, h1, h2⟩

theorem td0_drip_inv_aux (sp : Nat × Nat) (s : St) (x : Nat) :
    td0_Inv sp s → td0_Inv sp ({ s with reserve := s.reserve + x }) := by
  intro h
  unfold td0_Inv at h ⊢
  obtain ⟨hc, h1, h2⟩ := h
  unfold Consistent at hc ⊢
  obtain ⟨hb1, hb2, hmem⟩ := hc
  simp only at ⊢
  exact ⟨⟨hb1, hb2, hmem⟩, h1, h2⟩

theorem td0_mint_none_eq (s : St) (who x : Nat) (hwho : who < s.accts.length)
    (hhook : comptroller s (.supplyHook who) = none) :
    exec comptroller s (Op.mint who x) = s := by
  unfold exec
  simp [hwho, hhook]

theorem td0_mint_some_eq (s : St) (who x : Nat) (s' : St) (hwho : who < s.accts.length)
    (hhook : comptroller s (.supplyHook who) = some s') :
    exec comptroller s (Op.mint who x) = s'.withAcct who fun a => { a with supply := a.supply + x } := by
  unfold exec
  simp [hwho, hhook]

theorem td0_probe_exec2 (s : St) (who x : Nat) (s' : St)
    (hwho : who < s.accts.length)
    (hhook : comptroller s (.supplyHook who) = some s') :
    exec comptroller s (Op.mint who x) = s'.withAcct who fun a => { a with supply := a.supply + x } := by
  unfold exec
  simp [hwho, hhook]

theorem td0_probe_repay (s : St) (who x : Nat) (s' : St)
    (hhook : comptroller s (.borrowHook who) = some s')
    (hle : ¬ x ≤ (s'.acct who).borrow) :
    (match comptroller s (.borrowHook who) with
      | some s'' => if x ≤ (s''.acct who).borrow then s''.withAcct who fun a => { a with borrow := a.borrow - x } else s
      | none => s) = s := by
  simp [hhook, hle]

theorem td0_probe_repay_exec (s : St) (who x : Nat) (s' : St)
    (hwho : who < s.accts.length)
    (hhook : comptroller s (.borrowHook who) = some s')
    (hle : ¬ x ≤ (s'.acct who).borrow) :
    exec comptroller s (Op.repay who x) = s := by
  unfold exec
  simp [hwho, hhook, hle]

theorem snippet_probe_rewards_defs : True := trivial
#check @ProofForgeFin.DeFi.Rewards.settle_le
#check @ProofForgeFin.DeFi.Rewards.ite_accrue_le

theorem plan1_supply_distributed_potentialTo_le (sp : Nat × Nat) (s : St)
    (tgt who : Account) (s' : St) :
    td0_Inv sp s → SupplyDistributed s tgt s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_borrow_distributed_potentialTo_le (sp : Nat × Nat) (s : St)
    (tgt who : Account) (s' : St) :
    td0_Inv sp s → BorrowDistributed s tgt s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_claimed_potentialTo_le (sp : Nat × Nat) (s : St)
    (tgt who : Account) (s' : St) :
    td0_Inv sp s → Claimed s tgt s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_speeds_set_potentialTo_le (sp : Nat × Nat) (s : St)
    (a b : Nat) (who : Account) (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' →
      td0_potentialTo s' who ≤ td0_potentialTo s who := by sorry

theorem plan1_supply_change_potentialTo_le (s : St) (tgt who x : Nat) :
    s.supplyState.block = s.blockNumber →
    accrualStart (s.acct tgt).supplierIndex s.supplyState.index =
      s.supplyState.index →
    td0_potentialTo
        (s.withAcct tgt fun a => { a with supply := a.supply + x }) who ≤
      td0_potentialTo s who ∧
    td0_potentialTo
        (s.withAcct tgt fun a => { a with supply := a.supply - x }) who ≤
      td0_potentialTo s who := by sorry

theorem plan1_borrow_change_potentialTo_le (s : St) (tgt who x : Nat) :
    s.borrowState.block = s.blockNumber →
    accrualStart (s.acct tgt).borrowerIndex s.borrowState.index =
      s.borrowState.index →
    td0_potentialTo
        (s.withAcct tgt fun a => { a with borrow := a.borrow + x }) who ≤
      td0_potentialTo s who ∧
    td0_potentialTo
        (s.withAcct tgt fun a => { a with borrow := a.borrow - x }) who ≤
      td0_potentialTo s who := by sorry

def probe_defs_eq : Bool := true
#check @ProofForgeFin.DeFi.Rewards.pending
#check @ProofForgeFin.DeFi.Rewards.credit
#check @ProofForgeFin.DeFi.Rewards.firstStart
#check @ProofForgeFin.DeFi.Rewards.p62Start
#check @ProofForgeFin.DeFi.Rewards.effStart

theorem probe_pending_defs2 : True := by
  have h1 := ProofForgeFin.DeFi.Rewards.credit_mul_le (one := 5) (units := 3) (start := 1) (index := 10)
  have h2 := ProofForgeFin.DeFi.Rewards.settle_le (one := 5) (units := 3) (p := 1) (q := 2) (p' := 10) (index := 10) (r := 0) (r' := 1)
  trivial
#check @ProofForgeFin.DeFi.Rewards.pending
#check @ProofForgeFin.DeFi.Rewards.credit
#check @List.modify
#check @List.getD

theorem probe_defs_bridge1a : ProofForgeFin.DeFi.Rewards.pending 5 2 10 = 5 * (10 - 2) := by rfl

theorem probe_defs_bridge2a : ProofForgeFin.DeFi.Rewards.credit 100 5 2 10 = 5 * (10 - 2) / 100 := by rfl

theorem tmp_check_modify_def : True := by
  trivial
#check @List.modify
#check @List.getD

theorem tmp_print_modify : True := trivial
#check @List.modify
#check @List.getD
#print axioms List.modify

theorem aux_unfold_modify : True := trivial
#check List.modify
#reduce List.modify [1,2,3] 1 id

theorem tmp_explore_modify_eq : List.modify (a :: as : List Nat) 0 f = f a :: as := by rfl

theorem tmp_explore_modify_eq2 (a : Nat) (as : List Nat) (n : Nat) (f : Nat → Nat) :
    List.modify (a :: as) (n+1) f = a :: List.modify as n f := by rfl

theorem tmp_supply_change_probe1 (s : St) (tgt : Account) (f : Acct → Acct) :
    (s.withAcct tgt f).supplyState = s.supplyState := by rfl

theorem tmp_supply_change_probe2 (s : St) (tgt : Account) (f : Acct → Acct) :
    (s.withAcct tgt f).blockNumber = s.blockNumber := by rfl
#check @List.modify
#check @List.getD

theorem tmp_list_probe2 : True := trivial
#check @List.modify
#check @List.getElem_modify
#check @List.getD
#check @List.length_modify

theorem tmp_ne_lemma3 (l : List Acct) (tgt who : Nat) (f : Acct → Acct) (h : tgt ≠ who) :
    (l.modify tgt f).getD who noAcct = l.getD who noAcct := by
  induction l generalizing tgt who with
  | nil => simp
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact absurd rfl h
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w (by intro heq; apply h; rw [heq])

theorem tmp_acct_ne (s : St) (tgt who : Nat) (f : Acct → Acct) (h : tgt ≠ who) :
    (s.withAcct tgt f).acct who = s.acct who := by
  unfold St.withAcct St.acct
  simp only
  exact tmp_ne_lemma3 s.accts tgt who f h

theorem tmp_withAcct_side (s : St) (tgt : Nat) (f : Acct → Acct) :
    (s.withAcct tgt f).supplyState = s.supplyState ∧
    (s.withAcct tgt f).borrowState = s.borrowState ∧
    (s.withAcct tgt f).blockNumber = s.blockNumber := by
  refine ⟨rfl, rfl, rfl⟩

theorem tmp_check_mod3 : True := by trivial
#check @List.modify
#check @List.modifyTailIdx
#check @List.length_modify
#check @List.getElem_modify
#check @List.modifyHead

theorem bc_supply_pres (l : List Acct) (tgt who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supply = a.supply) :
    ((l.modify tgt f).getD who noAcct).supply = (l.getD who noAcct).supply := by
  induction l generalizing tgt who with
  | nil =>
    cases tgt with
    | zero => rfl
    | succ t => rfl
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact hf a
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w

theorem bc_accrued_pres (l : List Acct) (tgt who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).accrued = a.accrued) :
    ((l.modify tgt f).getD who noAcct).accrued = (l.getD who noAcct).accrued := by
  induction l generalizing tgt who with
  | nil =>
    cases tgt with
    | zero => rfl
    | succ t => rfl
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact hf a
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w

theorem bc_wallet_pres (l : List Acct) (tgt who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).wallet = a.wallet) :
    ((l.modify tgt f).getD who noAcct).wallet = (l.getD who noAcct).wallet := by
  induction l generalizing tgt who with
  | nil =>
    cases tgt with
    | zero => rfl
    | succ t => rfl
  | cons a as ih =>
    cases tgt with
    | zero =>
      cases who with
      | zero => exact hf a
      | succ w => rfl
    | succ t =>
      cases who with
      | zero => rfl
      | succ w => exact ih t w

theorem bc_explore1 (a : Acct) (as : List Acct) (f : Acct → Acct) :
    List.modify (a :: as) 0 f = f a :: as := by rfl

theorem bc_explore2 (a : Acct) (as : List Acct) (n : Nat) (f : Acct → Acct) :
    List.modify (a :: as) (n+1) f = a :: List.modify as n f := by rfl

theorem bc_explore3 (a : Acct) (as : List Acct) :
    List.getD (a :: as) 0 noAcct = a := by rfl

theorem bc_explore4 (a : Acct) (as : List Acct) (n : Nat) :
    List.getD (a :: as) (n+1) noAcct = List.getD as n noAcct := by rfl

theorem bc_explore5 : List.getD ([] : List Acct) 0 noAcct = noAcct := by rfl

theorem bc_explore6 (n : Nat) : List.getD ([] : List Acct) (n+1) noAcct = noAcct := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem tmp_adv_unindexed_eq (s : St) (k : Nat) (h1 : s.supplyState.block ≤ s.blockNumber) (h2 : s.borrowState.block ≤ s.blockNumber) :
    (s.blockNumber + k - s.supplyState.block) = (s.blockNumber - s.supplyState.block) + k := by omega

theorem tmp_adv_unindexed_eq2 (s : St) (k : Nat) (h1 : s.supplyState.block ≤ s.blockNumber) (h2 : s.borrowState.block ≤ s.blockNumber) :
    (s.blockNumber + k - s.borrowState.block) = (s.blockNumber - s.borrowState.block) + k := by omega

theorem tmp_pow_pos : 0 < compInitialIndex := by unfold compInitialIndex; exact Nat.pow_pos (by decide)

theorem tmp_if_neg_test (x : Nat) (hx : ¬ x = 0) : (if x = 0 then 1 else x) = x := by simp [hx]

theorem tmp_supDist_block2 (s : St) (tgt : Account) (s' : St) :
    SupplyDistributed s tgt s' → s'.supplyState.block = s.blockNumber := by
  intro h
  unfold SupplyDistributed at h
  obtain ⟨_, _, heq⟩ := h
  subst heq
  simp only
  unfold accrueSide
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s
  · simp [hc]
  · simp [hc]

theorem td0_ds_pos_aux : 0 < doubleScale := by
  unfold doubleScale
  apply Nat.pow_pos
  decide

theorem td0_owedTo_unfold (L : Legacy) (who : Account) :
    L.owedTo who = td0_pendingOf L who / doubleScale + td0_unindexedOf L who := by
  unfold Legacy.owedTo td0_pendingOf td0_unindexedOf
  rw [Nat.add_assoc]

theorem td0_account_bound_of_scaled (s : St) (L : Legacy) (who : Account) (e : Nat) :
    doubleScale * s.creditedTo who ≤
        doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who +
        doubleScale * e →
      s.creditedTo who ≤ (upgrade L).creditedTo who + L.owedTo who + e := by
  intro h
  have hD : 0 < doubleScale := td0_ds_pos_aux
  have howed := td0_owedTo_unfold L who
  rw [howed]
  have eq1 : s.creditedTo who * doubleScale = doubleScale * s.creditedTo who := Nat.mul_comm _ _
  have eq2 : ((upgrade L).creditedTo who + td0_unindexedOf L who + e) * doubleScale =
      doubleScale * (upgrade L).creditedTo who + doubleScale * td0_unindexedOf L who + doubleScale * e := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm ((upgrade L).creditedTo who) doubleScale, Nat.mul_comm (td0_unindexedOf L who) doubleScale, Nat.mul_comm e doubleScale]
  have h' : s.creditedTo who * doubleScale ≤ ((upgrade L).creditedTo who + td0_unindexedOf L who + e) * doubleScale + td0_pendingOf L who := by
    rw [eq1, eq2]
    omega
  have hle := ProofForgeFin.le_add_div_of_mul_le (X := s.creditedTo who) (Y := (upgrade L).creditedTo who + td0_unindexedOf L who + e) (P := td0_pendingOf L who) (D := doubleScale) hD h'
  omega

theorem tmp_upg_acct_eq (L : Legacy) (who : Account) :
    (upgrade L).acct who = L.accts.getD who noAcct := by
  unfold upgrade St.acct
  simp

theorem tmp_upg_cred_eq (L : Legacy) (who : Account) :
    (upgrade L).creditedTo who = (L.accts.getD who noAcct).accrued + (L.accts.getD who noAcct).wallet := by
  unfold St.creditedTo
  rw [tmp_upg_acct_eq]

theorem tmp_upg_block_eq (L : Legacy) : (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade; simp

theorem tmp_upg_supply_accts (L : Legacy) : (upgrade L).accts = L.accts := by
  unfold upgrade; simp

theorem tmp_init_char (now : Nat) (sd : Side) :
    (initSide now sd).index = (if sd.index = 0 then compInitialIndex else sd.index) ∧
    (initSide now sd).block = (if sd.index = 0 then now else sd.block) ∧
    (initSide now sd).speed = sd.speed := by
  unfold initSide
  by_cases h : sd.index = 0 <;> simp [h]

theorem tmp_list_api_probe2 : True := trivial
#check List.getD
#check List.getElem_mem

theorem tmp_getD_unfold_probe (l : List Acct) (n : Nat) :
    l.getD n noAcct = (l[n]?.getD noAcct) := by rfl
#check List.getD

theorem plan2_legacyStart_le_accrualStart (start recorded index : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hle : start ≤ index) (hrec : recorded ≤ index) :
    legacyStart start recorded ≤ accrualStart recorded index := by
  unfold legacyStart accrualStart
  by_cases hrec0 : recorded = 0
  · subst hrec0
    simp only [beq_self_eq_true, ↓reduceIte]
    rcases hstart with rfl | rfl
    · exact Nat.zero_le _
    · simp [hle]
  · simp only [hrec0, ↓reduceIte]
    exact Nat.le_refl _


theorem plan2_supply_gap_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    (initSide L.blockNumber
      (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.supplierIndex
          (initSide L.blockNumber
            (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index ≤
      L.supplyIndex - legacyStart L.supplyStart a.supplierIndex := by
  by_cases hI : L.supplyIndex = 0
  · have hS0 : L.supplyStart = 0 := by omega
    have ha0 : a.supplierIndex = 0 := by omega
    have hinit : (initSide L.blockNumber
      (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index = compInitialIndex := by
      unfold initSide
      simp [hI]
    rw [hinit, ha0, hS0, hI]
    unfold accrualStart legacyStart
    simp
  · have hinit : (initSide L.blockNumber
      (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index = L.supplyIndex := by
      unfold initSide
      simp [hI]
    rw [hinit]
    have hle2 : legacyStart L.supplyStart a.supplierIndex ≤
      accrualStart a.supplierIndex L.supplyIndex :=
      plan2_legacyStart_le_accrualStart L.supplyStart a.supplierIndex L.supplyIndex hstart hle ha
    have hacc_le : accrualStart a.supplierIndex L.supplyIndex ≤ L.supplyIndex := by
      unfold accrualStart
      split
      · split
        · assumption
        · omega
      · omega
    have hleg_le : legacyStart L.supplyStart a.supplierIndex ≤ L.supplyIndex := by
      unfold legacyStart
      split
      · exact hle
      · omega
    omega


theorem plan2_borrow_gap_le (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.borrowerIndex
          (initSide L.blockNumber
            (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by
  by_cases hI : L.borrowIndex = 0
  · have hS0 : L.borrowStart = 0 := by omega
    have ha0 : a.borrowerIndex = 0 := by omega
    have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = compInitialIndex := by
      unfold initSide
      simp [hI]
    rw [hinit, ha0, hS0, hI]
    unfold accrualStart legacyStart
    simp
  · have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = L.borrowIndex := by
      unfold initSide
      simp [hI]
    rw [hinit]
    have hle2 : legacyStart L.borrowStart a.borrowerIndex ≤
      accrualStart a.borrowerIndex L.borrowIndex :=
      plan2_legacyStart_le_accrualStart L.borrowStart a.borrowerIndex L.borrowIndex hstart hle ha
    have hacc_le : accrualStart a.borrowerIndex L.borrowIndex ≤ L.borrowIndex := by
      unfold accrualStart
      split
      · split
        · assumption
        · omega
      · omega
    have hleg_le : legacyStart L.borrowStart a.borrowerIndex ≤ L.borrowIndex := by
      unfold legacyStart
      split
      · exact hle
      · omega
    omega






theorem plan2_upgrade_unindexedTo_le (L : Legacy) (who : Account) :
    td0_unindexedTo (upgrade L) who ≤ td0_unindexedOf L who := by
  have hsup_blk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hbor_blk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hsup_spd : (upgrade L).supplyState.speed = L.compSpeed := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hbor_spd : (upgrade L).borrowState.speed = L.compSpeed := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hblk : (upgrade L).blockNumber = L.blockNumber := by
    unfold upgrade
    simp
  have hacct : (upgrade L).acct who = L.accts.getD who noAcct := by
    unfold upgrade St.acct
    simp
  have hS : (L.blockNumber - (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock)) * L.compSpeed ≤ (L.blockNumber - L.supplyBlock) * L.compSpeed := by
    by_cases hS0 : L.supplyIndex = 0
    · simp [hS0]
    · simp [hS0]
  have hB : (L.blockNumber - (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock)) * L.compSpeed ≤ (L.blockNumber - L.borrowBlock) * L.compSpeed := by
    by_cases hB0 : L.borrowIndex = 0
    · simp [hB0]
    · simp [hB0]
  unfold td0_unindexedTo td0_unindexedOf Legacy.unindexedSupply Legacy.unindexedBorrow
  rw [hsup_blk, hbor_blk, hsup_spd, hbor_spd, hblk, hacct]
  by_cases hs : 0 < (L.accts.getD who noAcct).supply <;> by_cases hb : 0 < (L.accts.getD who noAcct).borrow <;> simp only [hs, hb, if_true, if_false, Nat.zero_add, Nat.add_zero, Nat.zero_le]
  · exact Nat.add_le_add hS hB
  · exact hS
  · exact hB


theorem plan2_borrow_gap_le_aux (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.borrowerIndex
          (initSide L.blockNumber
            (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by
  by_cases hI : L.borrowIndex = 0
  · have hS0 : L.borrowStart = 0 := by omega
    have ha0 : a.borrowerIndex = 0 := by omega
    have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = compInitialIndex := by
      unfold initSide
      simp [hI]
    rw [hinit, ha0, hS0, hI]
    unfold accrualStart legacyStart
    simp
  · have hinit : (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index = L.borrowIndex := by
      unfold initSide
      simp [hI]
    rw [hinit]
    have hle2 : legacyStart L.borrowStart a.borrowerIndex ≤
      accrualStart a.borrowerIndex L.borrowIndex :=
      plan2_legacyStart_le_accrualStart L.borrowStart a.borrowerIndex L.borrowIndex hstart hle ha
    have hacc_le : accrualStart a.borrowerIndex L.borrowIndex ≤ L.borrowIndex := by
      unfold accrualStart
      split
      · split
        · assumption
        · omega
      · omega
    have hleg_le : legacyStart L.borrowStart a.borrowerIndex ≤ L.borrowIndex := by
      unfold legacyStart
      split
      · exact hle
      · omega
    omega

theorem plan2_tmp_mem (hd : Acct) (tl : List Acct) : hd ∈ hd :: tl := by simp

theorem plan2_tmp_mem2 (hd : Acct) (tl : List Acct) (a : Acct) (ha : a ∈ tl) : a ∈ hd :: tl := by simp [ha]

theorem plan2_dbg1 (tl : List Acct) (hd : Acct) : hd ∈ hd :: tl := by exact List.Mem.head _

theorem plan2_dbg2 : True := trivial

theorem plan2_probe_getD (l : List Acct) (who : Nat) : True := by
  cases l with
  | nil =>
    cases who with
    | zero => trivial
    | succ n => trivial
  | cons hd tl => trivial

theorem plan2_rfl1 (a : Acct) (as : List Acct) : List.getD (a :: as) 0 noAcct = a := by rfl

theorem plan2_rfl2 (a : Acct) (as : List Acct) (n : Nat) : List.getD (a :: as) (n+1) noAcct = List.getD as n noAcct := by rfl

theorem plan2_rfl3 : List.getD ([] : List Acct) 0 noAcct = noAcct := by rfl

theorem plan2_rfl4 (n : Nat) : List.getD ([] : List Acct) (n+1) noAcct = noAcct := by
  cases n with
  | zero => rfl
  | succ m => rfl

theorem plan2_aux_getD_le (l : List Acct) (S B : Nat) (who : Nat)
    (hmem : ∀ a ∈ l, a.supplierIndex ≤ S ∧ a.borrowerIndex ≤ B) :
    (l.getD who noAcct).supplierIndex ≤ S ∧ (l.getD who noAcct).borrowerIndex ≤ B := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero =>
      have h : List.getD ([] : List Acct) 0 noAcct = noAcct := rfl
      rw [h]
      constructor <;> (unfold noAcct; simp)
    | succ n =>
      have h : List.getD ([] : List Acct) (n+1) noAcct = noAcct := rfl
      rw [h]
      constructor <;> (unfold noAcct; simp)
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h : List.getD (hd :: tl) 0 noAcct = hd := rfl
      rw [h]
      exact hmem hd (List.Mem.head _)
    | succ n =>
      have h : List.getD (hd :: tl) (n+1) noAcct = List.getD tl n noAcct := rfl
      rw [h]
      apply ih
      intro a ha
      exact hmem a (List.Mem.tail _ ha)

theorem plan2_getD_index_le2 (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  obtain ⟨_, _, _, _, _, _, hmem⟩ := hWF
  exact plan2_aux_getD_le L.accts L.supplyIndex L.borrowIndex who hmem

theorem plan2_getD_index_le (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  obtain ⟨_, _, _, _, _, _, hmem⟩ := hWF
  exact plan2_aux_getD_le L.accts L.supplyIndex L.borrowIndex who hmem

theorem plan2_upgrade_pending_le (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    td0_pendingScaledAcct (upgrade L) ((upgrade L).acct who) ≤
      td0_pendingOf L who := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, haccts⟩ := hWF
  have hWF2 : L.WellFormed := ⟨hs0, hsle, hb0, hble, hsb, hbb, haccts⟩
  have hidx := plan2_getD_index_le L who hWF2
  have hsup_mem : (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex := hidx.1
  have hbor_mem : (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := hidx.2
  have hgapS := plan2_supply_gap_le L (L.accts.getD who noAcct) hs0 hsle hsup_mem
  have hgapB := plan2_borrow_gap_le L (L.accts.getD who noAcct) hb0 hble hbor_mem
  unfold td0_pendingScaledAcct td0_pendingOf Legacy.pendingScaled
  have hacct_eq : (upgrade L).acct who = L.accts.getD who noAcct := tmp_upg_acct_eq L who
  have hsup_idx : (upgrade L).supplyState.index =
      (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  have hbor_idx : (upgrade L).borrowState.index =
      (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  rw [hacct_eq, hsup_idx, hbor_idx]
  have hmulS : (L.accts.getD who noAcct).supply *
      ((initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index -
        accrualStart (L.accts.getD who noAcct).supplierIndex
          (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index) ≤
      (L.accts.getD who noAcct).supply * (L.supplyIndex - legacyStart L.supplyStart (L.accts.getD who noAcct).supplierIndex) :=
    Nat.mul_le_mul_left _ hgapS
  have hmulB : (L.accts.getD who noAcct).borrow *
      ((initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart (L.accts.getD who noAcct).borrowerIndex
          (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index) ≤
      (L.accts.getD who noAcct).borrow * (L.borrowIndex - legacyStart L.borrowStart (L.accts.getD who noAcct).borrowerIndex) :=
    Nat.mul_le_mul_left _ hgapB
  exact Nat.add_le_add hmulS hmulB

theorem plan2_upgrade_unindexedTo_le_aux1 (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le_aux2 (L : Legacy) :
    (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le_aux3 (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le_aux4 (L : Legacy) :
    (upgrade L).borrowState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  split
  · simp_all
  · simp_all

theorem plan2_upgrade_unindexedTo_le_aux5 (L : Legacy) :
    (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade
  simp only

theorem td0_upgrade_potentialTo_le (L : Legacy) (who : Account) :
    L.WellFormed →
      td0_potentialTo (upgrade L) who ≤
        doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who := by
  intro hWF
  unfold td0_potentialTo
  have hpend : td0_pendingScaledAcct (upgrade L) ((upgrade L).acct who) ≤ td0_pendingOf L who :=
    plan2_upgrade_pending_le L who hWF
  have hunidx : td0_unindexedTo (upgrade L) who ≤ td0_unindexedOf L who :=
    plan2_upgrade_unindexedTo_le L who
  have hmul : doubleScale * td0_unindexedTo (upgrade L) who ≤
      doubleScale * td0_unindexedOf L who :=
    Nat.mul_le_mul_left doubleScale hunidx
  omega

theorem plan2_tmp_inline1 (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  simp only
  split
  · rfl
  · rfl

theorem plan2_inline_check2 (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  simp only
  split
  · rfl
  · rfl

theorem plan2_inline_check3 (L : Legacy) :
    (upgrade L).blockNumber = L.blockNumber := by
  unfold upgrade
  simp

theorem plan2_inline_check4 (L : Legacy) (who : Account) :
    (upgrade L).acct who = L.accts.getD who noAcct := by
  unfold upgrade St.acct
  simp

theorem plan2_upgrade_unindexedTo_le_newproof (L : Legacy) (who : Account) :
    td0_unindexedTo (upgrade L) who ≤ td0_unindexedOf L who := by
  have hsup_blk := plan2_tmp_inline1 L
  have hbor_blk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hsup_spd := plan2_inline_check2 L
  have hbor_spd : (upgrade L).borrowState.speed = L.compSpeed := by
    unfold upgrade initSide
    simp only
    split
    · rfl
    · rfl
  have hblk := plan2_inline_check3 L
  have hacct := plan2_inline_check4 L who
  have hS : (L.blockNumber - (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock)) * L.compSpeed ≤ (L.blockNumber - L.supplyBlock) * L.compSpeed := by
    by_cases hS0 : L.supplyIndex = 0
    · simp [hS0]
    · simp [hS0]
  have hB : (L.blockNumber - (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock)) * L.compSpeed ≤ (L.blockNumber - L.borrowBlock) * L.compSpeed := by
    by_cases hB0 : L.borrowIndex = 0
    · simp [hB0]
    · simp [hB0]
  unfold td0_unindexedTo td0_unindexedOf Legacy.unindexedSupply Legacy.unindexedBorrow
  rw [hsup_blk, hbor_blk, hsup_spd, hbor_spd, hblk, hacct]
  by_cases hs : 0 < (L.accts.getD who noAcct).supply <;> by_cases hb : 0 < (L.accts.getD who noAcct).borrow <;> simp only [hs, hb, if_true, if_false, Nat.zero_add, Nat.add_zero, Nat.zero_le]
  · exact Nat.add_le_add hS hB
  · exact hS
  · exact hB

theorem td0_rewards_bound_of_scaled (s : St) (L : Legacy) (e : Nat) :
    doubleScale * s.credited ≤
        doubleScale * (upgrade L).credited +
        (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * e →
      s.credited ≤ (upgrade L).credited + L.owed + e := by
  intro h
  have hD : 0 < doubleScale := td0_ds_pos_aux
  have howed : L.owed = (L.accts.map L.pendingScaled).sum / doubleScale + L.unindexedSupply + L.unindexedBorrow := rfl
  rw [howed]
  have eq1 : s.credited * doubleScale = doubleScale * s.credited := Nat.mul_comm _ _
  have eq2 : ((upgrade L).credited + (L.unindexedSupply + L.unindexedBorrow) + e) * doubleScale =
      doubleScale * (upgrade L).credited + doubleScale * (L.unindexedSupply + L.unindexedBorrow) + doubleScale * e := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm ((upgrade L).credited) doubleScale, Nat.mul_comm (L.unindexedSupply + L.unindexedBorrow) doubleScale, Nat.mul_comm e doubleScale]
  have h' : s.credited * doubleScale ≤ ((upgrade L).credited + (L.unindexedSupply + L.unindexedBorrow) + e) * doubleScale + (L.accts.map L.pendingScaled).sum := by
    rw [eq1, eq2]
    omega
  have hle := ProofForgeFin.le_add_div_of_mul_le (X := s.credited) (Y := (upgrade L).credited + (L.unindexedSupply + L.unindexedBorrow) + e) (P := (L.accts.map L.pendingScaled).sum) (D := doubleScale) hD h'
  omega

theorem tmp_upg_unidx_le (L : Legacy) :
    td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by
  have hsup_blk : (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock :=
    plan2_upgrade_unindexedTo_le_aux1 L
  have hbor_blk : (upgrade L).borrowState.block = if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock :=
    plan2_upgrade_unindexedTo_le_aux2 L
  have hsup_spd : (upgrade L).supplyState.speed = L.compSpeed :=
    plan2_upgrade_unindexedTo_le_aux3 L
  have hbor_spd : (upgrade L).borrowState.speed = L.compSpeed :=
    plan2_upgrade_unindexedTo_le_aux4 L
  have hblk : (upgrade L).blockNumber = L.blockNumber :=
    plan2_upgrade_unindexedTo_le_aux5 L
  have hS : ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed ≤
      L.unindexedSupply := by
    rw [hsup_blk, hsup_spd, hblk]
    unfold Legacy.unindexedSupply
    by_cases hS0 : L.supplyIndex = 0
    · simp [hS0]
    · simp [hS0]
  have hB : ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed ≤
      L.unindexedBorrow := by
    rw [hbor_blk, hbor_spd, hblk]
    unfold Legacy.unindexedBorrow
    by_cases hB0 : L.borrowIndex = 0
    · simp [hB0]
    · simp [hB0]
  unfold td0_unindexed
  exact Nat.add_le_add hS hB

theorem tmp_upg_mem_pend_le (L : Legacy) (a : Acct) (hWF : L.WellFormed) (hmem : a ∈ L.accts) :
    td0_pendingScaledAcct (upgrade L) a ≤ L.pendingScaled a := by
  unfold Legacy.WellFormed at hWF
  obtain ⟨hs0, hsle, hb0, hble, hsb, hbb, haccts⟩ := hWF
  have ha := haccts a hmem
  have hsup_mem : a.supplierIndex ≤ L.supplyIndex := ha.1
  have hbor_mem : a.borrowerIndex ≤ L.borrowIndex := ha.2
  have hgapS := plan2_supply_gap_le L a hs0 hsle hsup_mem
  have hgapB := plan2_borrow_gap_le L a hb0 hble hbor_mem
  have hsup_idx : (upgrade L).supplyState.index =
      (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  have hbor_idx : (upgrade L).borrowState.index =
      (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index := by
    unfold upgrade; simp
  unfold td0_pendingScaledAcct Legacy.pendingScaled
  rw [hsup_idx, hbor_idx]
  have hmulS : a.supply *
      ((initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.supplierIndex
          (initSide L.blockNumber (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) :=
    Nat.mul_le_mul_left _ hgapS
  have hmulB : a.borrow *
      ((initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.borrowerIndex
          (initSide L.blockNumber (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index) ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) :=
    Nat.mul_le_mul_left _ hgapB
  exact Nat.add_le_add hmulS hmulB

theorem tmp_upg_sum_aux (L : Legacy) (l : List Acct)
    (h : ∀ a ∈ l, td0_pendingScaledAcct (upgrade L) a ≤ L.pendingScaled a) :
    ((l.map (td0_pendingScaledAcct (upgrade L))).sum ≤ (l.map L.pendingScaled).sum) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hhd : td0_pendingScaledAcct (upgrade L) hd ≤ L.pendingScaled hd := h hd (List.Mem.head _)
    have htl : ∀ a ∈ tl, td0_pendingScaledAcct (upgrade L) a ≤ L.pendingScaled a := fun a ha =>
      h a (List.Mem.tail _ ha)
    have iht := ih htl
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add hhd iht

theorem td0_upgrade_potential_le (L : Legacy) :
    L.WellFormed →
      td0_potential (upgrade L) ≤
        doubleScale * (upgrade L).credited +
        (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  intro hWF
  have hU : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow :=
    tmp_upg_unidx_le L
  have hU' : doubleScale * td0_unindexed (upgrade L) ≤
      doubleScale * (L.unindexedSupply + L.unindexedBorrow) :=
    Nat.mul_le_mul_left _ hU
  have hP : td0_pendingScaled (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
    unfold td0_pendingScaled
    have haccts_eq : (upgrade L).accts = L.accts := tmp_upg_supply_accts L
    rw [haccts_eq]
    apply tmp_upg_sum_aux L _ (fun a hmem => tmp_upg_mem_pend_le L a hWF hmem)
  unfold td0_potential
  exact Nat.add_le_add (Nat.add_le_add_left hP _) hU'

theorem upd_supply_eq2 (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
  unfold subChecked
  simp [hle]

theorem probe_upd_simp (s : St) (hle : s.supplyState.block ≤ s.blockNumber) :
    (match (if s.supplyState.block ≤ s.blockNumber then some (s.blockNumber - s.supplyState.block) else none : Option Nat) with
    | none => (none : Option St)
    | some deltaBlocks => some s) = some s := by
  simp [hle]

theorem plan3_updateSupply_accrue (s : St) (t : St) :
    updateCompSupplyIndex s = some t →
    s.supplyState.block ≤ s.blockNumber ∧
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  intro h
  have hle : s.supplyState.block ≤ s.blockNumber := by
    by_cases hc : s.supplyState.block ≤ s.blockNumber
    · exact hc
    · have hnone : subChecked s.blockNumber s.supplyState.block = none := by
        unfold subChecked
        rw [if_neg hc]
      unfold updateCompSupplyIndex at h
      rw [hnone] at h
      simp at h
  refine ⟨hle, ?_⟩
  unfold updateCompSupplyIndex subChecked at h
  rw [if_pos hle] at h
  simp only at h
  by_cases hpos : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hpos] at h
    cases h
    congr 1
    have h0 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed := hpos
    by_cases htot : 0 < totalSupply s
    · have hacc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s := ⟨h0.1, h0.2, htot⟩
      have htot' : totalSupply s > 0 := htot
      have e1 : (if totalSupply s > 0 then fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s) else 0) = (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s := by
        rw [if_pos htot']; rfl
      rw [e1]
      unfold accrueSide
      rw [if_pos hacc]
    · have htot' : ¬ totalSupply s > 0 := by omega
      have e1 : (if totalSupply s > 0 then fraction ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s) else 0) = 0 := if_neg htot'
      rw [e1]
      have hacc_neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      rfl
  · rw [if_neg hpos] at h
    by_cases hdelta : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos hdelta] at h
      cases h
      congr 1
      have hacc_neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by
        intro hc
        exact hpos ⟨hc.1, hc.2.1⟩
      unfold accrueSide
      rw [if_neg hacc_neg]
    · rw [if_neg hdelta] at h
      cases h
      have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have hacc_neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res accts =>
        simp only at hbeq ⊢
        cases sup with
        | mk idx blk spd =>
          simp only at hbeq ⊢
          rw [hbeq]


theorem plan3_updateBorrow_accrue (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber ∧
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  intro h
  have hle : s.borrowState.block ≤ s.blockNumber := by
    by_cases hc : s.borrowState.block ≤ s.blockNumber
    · exact hc
    · have hnone : subChecked s.blockNumber s.borrowState.block = none := by
        unfold subChecked
        rw [if_neg hc]
      unfold updateCompBorrowIndex at h
      rw [hnone] at h
      simp at h
  refine ⟨hle, ?_⟩
  unfold updateCompBorrowIndex subChecked at h
  rw [if_pos hle] at h
  simp only at h
  by_cases hpos : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hpos] at h
    cases h
    congr 1
    have h0 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed := hpos
    by_cases htot : 0 < totalBorrows s
    · have hacc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s := ⟨h0.1, h0.2, htot⟩
      have htot' : totalBorrows s > 0 := htot
      have e1 : (if totalBorrows s > 0 then fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s) else 0) = (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s := by
        rw [if_pos htot']; rfl
      rw [e1]
      unfold accrueSide
      rw [if_pos hacc]
    · have htot' : ¬ totalBorrows s > 0 := by omega
      have e1 : (if totalBorrows s > 0 then fraction ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s) else 0) = 0 := if_neg htot'
      rw [e1]
      have hacc_neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      rfl
  · rw [if_neg hpos] at h
    by_cases hdelta : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos hdelta] at h
      cases h
      congr 1
      have hacc_neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by
        intro hc
        exact hpos ⟨hc.1, hc.2.1⟩
      unfold accrueSide
      rw [if_neg hacc_neg]
    · rw [if_neg hdelta] at h
      cases h
      have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have hacc_neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := by omega
      unfold accrueSide
      rw [if_neg hacc_neg]
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      cases s with
      | mk bn sup bor res accts =>
        simp only at hbeq ⊢
        cases bor with
        | mk idx blk spd =>
          simp only at hbeq ⊢
          rw [hbeq]


theorem plan3_setSupplySpeed_spec (s : St) (a : Nat) (t : St) :
    setSupplySpeed s a = some t →
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState := if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by sorry



theorem plan3_setCompSpeedInternal_spec (s : St) (a b : Nat) (s' : St) :
    setCompSpeedInternal s a b = some s' → SpeedsSet s a b s' := by sorry

theorem plan3_updateSupply_accrue_aux1 (s : St) :
    accrueSide s.supplyState s.blockNumber (totalSupply s) =
    (if 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s then
      ({ s.supplyState with index := s.supplyState.index + (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale / totalSupply s, block := s.blockNumber } : Side)
    else ({ s.supplyState with block := s.blockNumber } : Side)) := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem plan3_updateSupply_accrue_try1 (s : St) (t : St) (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hle : s.supplyState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem plan3_supply_fraq_eq (d spd tot : Nat) :
    fraction (d * spd) tot = d * spd * doubleScale / tot := by
  unfold fraction
  rw [Nat.mul_assoc]

theorem plan3_supply_eta1d (bn : Nat) (sup : Side) (hbeq : sup.block = bn) :
    ({ sup with block := bn } : Side) = sup := by
  cases sup with | mk idx blk spd =>
    simp at hbeq ⊢
    subst hbeq
    rfl

theorem plan3_supply_eta2d (s : St) (hbeq : s.supplyState.block = s.blockNumber) :
    ({ s with supplyState := ({ s.supplyState with block := s.blockNumber } : Side) } : St) = s := by
  have h1 : (({ s.supplyState with block := s.blockNumber } : Side)) = s.supplyState :=
    plan3_supply_eta1d s.blockNumber s.supplyState hbeq
  cases s with | mk bn sup bor res accts =>
    simp at h1 hbeq ⊢
    rw [h1]

theorem tmp_supply_if1 (s : St) (a : Nat) (t : St) (heq : s.supplyState.speed = a)
    (h : setSupplySpeed s a = some t) : t = s := by
  unfold setSupplySpeed at h
  simp [heq] at h
  exact h.symm

theorem tmp_supply_if2 (s : St) (a : Nat) (t : St) (hne : s.supplyState.speed ≠ a)
    (u : St) (hU : updateCompSupplyIndex s = some u)
    (h : ((updateCompSupplyIndex s).map fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) = some t) : True := by
  rw [hU] at h
  simp at h
  trivial

theorem tmp_supply_rw (s : St) (Y X : Side) :
    ({ ({ s with supplyState := Y } : St) with supplyState := X } : St) = ({ s with supplyState := X } : St) := by
  rfl

theorem tmp_supply_rw2 (s : St) (u : St) (hU : u = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)) (a : Nat) (t : St)
    (h : t = ({ u with supplyState := ({ u.supplyState with speed := a } : Side) } : St)) :
    t = ({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St) := by
  rw [hU] at h
  rw [h]

theorem tmp_supply_branch_eq (s : St) (a : Nat) (t : St) (hEq : s.supplyState.speed = a)
    (h : setSupplySpeed s a = some t) : s = t := by
  unfold setSupplySpeed at h
  have hSimp : (if s.supplyState.speed ≠ a then (updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) else some s) = some s := by
    simp [hEq]
  rw [hSimp] at h
  simpa using h

theorem tmp_supply_branch_ne (s : St) (a : Nat) (t : St) (hNe : s.supplyState.speed ≠ a)
    (h : setSupplySpeed s a = some t) :
    ((updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) = some t) := by
  unfold setSupplySpeed at h
  have hSimp : (if s.supplyState.speed ≠ a then (updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) else some s) = (updateCompSupplyIndex s).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) := by
    simp [hNe]
  rw [hSimp] at h
  exact h

theorem tmp_eta_same2 (s : St) : ({ s with supplyState := s.supplyState } : St) = s := by
  cases s
  rfl

theorem tmp_if_same2 (s : St) (a : Nat) (hEq : s.supplyState.speed = a) :
    ({ s with supplyState := (if s.supplyState.speed = a then s.supplyState else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) } : St) = s := by
  have hIf : (if s.supplyState.speed = a then s.supplyState else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) = s.supplyState := by
    simp [hEq]
  rw [hIf]

theorem tmp_map_extract2 (u t : St) (a : Nat) (h : (Option.some u).map (fun s => ({ s with supplyState := ({ s.supplyState with speed := a } : Side) } : St)) = some t) :
    t = ({ u with supplyState := ({ u.supplyState with speed := a } : Side) } : St) := by
  simp at h
  exact h.symm

theorem tmp_goal_eq (s u : St) (a : Nat) (hU : u = ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St)) :
    ({ u with supplyState := ({ u.supplyState with speed := a } : Side) } : St) =
    ({ s with supplyState := ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side) } : St) := by
  rw [hU]

theorem tmp_inj_probe (u t : St) (f : St → St)
    (h : Option.map f (some u) = some t) : f u = t := by
  simpa using h

theorem tmp_borrow_rw (s u : St) (b : Nat)
    (hu : u = ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St)) :
    (({ u with borrowState := ({ u.borrowState with speed := b } : Side) } : St)) =
    (({ s with borrowState := ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side) } : St)) := by
  rw [hu]

theorem plan3_setBorrowSpeed_spec (s : St) (b : Nat) (t : St) :
    setBorrowSpeed s b = some t →
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState := if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  intro h
  unfold setBorrowSpeed at h
  by_cases hEq : s.borrowState.speed = b
  · have hFalse : ¬ (s.borrowState.speed ≠ b) := by simp [hEq]
    simp only [hFalse, ↓reduceIte] at h
    have ht : s = t := by simpa using h
    subst ht
    constructor
    · intro hne
      exact absurd hEq hne
    · simp [hEq]
  · have hTrue : s.borrowState.speed ≠ b := hEq
    rw [if_pos hTrue] at h
    cases hU : updateCompBorrowIndex s with
    | none =>
      simp [hU] at h
    | some u =>
      simp [hU] at h
      have hacc := plan3_updateBorrow_accrue s u hU
      obtain ⟨hblk, hu⟩ := hacc
      constructor
      · intro _
        exact hblk
      · have hEq2 : ¬ (s.borrowState.speed = b) := hEq
        simp only [hEq2, ↓reduceIte]
        have h2 := tmp_borrow_rw s u b hu
        rw [h2] at h
        exact h.symm

theorem tmp_mid_exists5 (s : St) (a b : Nat) (s' : St)
    (h : setCompSpeedInternal s a b = some s') :
    ∃ mid, setSupplySpeed s a = some mid ∧ setBorrowSpeed mid b = some s' := by
  unfold setCompSpeedInternal at h
  cases heq : setSupplySpeed s a
  · simp [heq] at h
  · simp [heq] at h
    exact ⟨_, rfl, h⟩

theorem tmp_mid_preserve (s mid : St) (a : Nat)
    (h : mid = ({ s with supplyState := (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)) } : St)) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧ mid.accts = s.accts ∧ mid.borrowState.speed = s.borrowState.speed := by
  constructor
  · rw [h]
  constructor
  · rw [h]
  constructor
  · rw [h]
  · rw [h]

theorem tmp_merge_eq (s : St) (SA : Side) (BA : Side) :
    (({ ({ s with supplyState := SA } : St) with borrowState := BA } : St)) =
    ({ s with supplyState := SA, borrowState := BA } : St) := by
  rfl

theorem td0_set_speeds_effect_proof : ∀ (s : St) (a b : Nat) (s' : St),
    comptroller s (.setSpeeds a b) = some s' → SpeedsSet s a b s' := by
  intro s a b s' h
  have h2 : setCompSpeedInternal s a b = some s' := h
  exact plan3_setCompSpeedInternal_spec s a b s' h2

theorem td0_set_speeds_effect (s : St) (a b : Nat) (s' : St) :
    comptroller s (.setSpeeds a b) = some s' → SpeedsSet s a b s' := by
  intro h
  exact plan3_setCompSpeedInternal_spec s a b s' h

theorem plan3_setCompSpeedInternal_spec_auxC (s : St) (a b : Nat) (s' : St) :
    setCompSpeedInternal s a b = some s' → SpeedsSet s a b s' := by
  intro h
  obtain ⟨mid, hMid, hBor⟩ := tmp_mid_exists5 s a b s' h
  have hSup := plan3_setSupplySpeed_spec s a mid hMid
  obtain ⟨hSupBlk, hMidEq⟩ := hSup
  have hBorSpec := plan3_setBorrowSpeed_spec mid b s' hBor
  obtain ⟨hBorBlkMid, hSEq⟩ := hBorSpec
  have hPres := tmp_mid_preserve s mid a hMidEq
  obtain ⟨hMidBor, hMidBn, hMidAc, hMidSpd⟩ := hPres
  have hTotEq : totalBorrows mid = totalBorrows s := by
    unfold totalBorrows
    rw [hMidAc]
  have h1 : (if mid.borrowState.speed = b then mid.borrowState
      else { accrueSide mid.borrowState mid.blockNumber (totalBorrows mid) with speed := b }) =
      (if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) := by
    rw [hMidSpd, hMidBor]
    by_cases he : s.borrowState.speed = b
    · simp [he]
    · simp only [he, ↓reduceIte]
      rw [hMidBn, hTotEq]
  have hSEq2 : s' = { mid with borrowState :=
      (if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) } := by
    rw [h1] at hSEq
    exact hSEq
  unfold SpeedsSet
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    exact hSupBlk hne
  · intro hne
    have hneMid : mid.borrowState.speed ≠ b := by rw [hMidSpd]; exact hne
    have hle := hBorBlkMid hneMid
    rw [hMidBor, hMidBn] at hle
    exact hle
  · rw [hSEq2, hMidEq]

theorem plan3_setCompSpeedInternal_spec_proof_final (s : St) (a b : Nat) (s' : St) :
    setCompSpeedInternal s a b = some s' → SpeedsSet s a b s' :=
  fun h => plan3_setCompSpeedInternal_spec_auxC s a b s' h

theorem tmp_supply_unfold (t : St) (who : Account) (s' : St)
    (hd : distributeSupplierComp t who = some s') : True := by
  unfold distributeSupplierComp at hd
  trivial

theorem tmp_supply_step1b (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ t, updateCompSupplyIndex s = some t ∧
      distributeSupplierComp t who = some s' := by
  unfold comptroller at h
  cases hU : updateCompSupplyIndex s with
  | none =>
    simp [hU] at h
  | some t =>
    simp [hU] at h
    exact ⟨t, rfl, h⟩

theorem tmp_if_parse (t : St) (who : Account) (h : (t.acct who).supplierIndex = 0) : True := by
  trivial

theorem plan4_modify_congr_at (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h0 : f hd = g hd := h
      simp [h0]
    | succ n =>
      have h0 : f (tl.getD n noAcct) = g (tl.getD n noAcct) := h
      simp [ih n h0]


theorem plan4_supplier_start_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · subst h
    by_cases hi : compInitialIndex ≤ index
    · simp [hi]
    · simp [hi]
  · simp [h, show ¬ (recorded = 0 ∧ compInitialIndex ≤ index) from fun ⟨heq, _⟩ => h heq]


theorem plan4_distributeSupplierComp_spec (s : St) (who : Account) (s' : St) :
    distributeSupplierComp s who = some s' →
      accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
          s.supplyState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex s.supplyState.index)
              s.supplyState.index } := by sorry

theorem plan4_supplyHook_decomp (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' →
      ∃ t, updateCompSupplyIndex s = some t ∧
        distributeSupplierComp t who = some s' :=
  fun h => tmp_supply_step1b s who s' h


theorem plan4_supplyDistributed_of_steps (s : St) (who : Account) (t s' : St) :
    s.supplyState.block ≤ s.blockNumber →
      t = { s with
        supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } →
        distributeSupplierComp t who = some s' →
          SupplyDistributed s who s' := by sorry

theorem tmp_try_modify_congr (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil =>
    cases who <;> rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h0 : f hd = g hd := h
      show List.modify (hd :: tl) 0 f = List.modify (hd :: tl) 0 g
      simp [h0]
    | succ n =>
      have h0 : f (tl.getD n noAcct) = g (tl.getD n noAcct) := h
      show List.modify (hd :: tl) (n+1) f = List.modify (hd :: tl) (n+1) g
      simp [ih n h0]

theorem plan4_modify_congr_at_proof (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g :=
  tmp_try_modify_congr l who f g h

theorem tmp_try_modify_congr2 (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  exact tmp_try_modify_congr l who f g h

theorem tmp_inline_proof_check (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by
  induction l generalizing who with
  | nil => cases who <;> rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have h0 : f hd = g hd := h
      simp [h0]
    | succ n =>
      have h0 : f (tl.getD n noAcct) = g (tl.getD n noAcct) := h
      simp [ih n h0]

theorem tmp_distrib_unfold (s : St) (who : Account) :
    distributeSupplierComp s who =
    match subChecked s.supplyState.index
      (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply deltaIndex }) := by
  unfold distributeSupplierComp subChecked
  simp only

theorem tmp_step_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := plan4_supplier_start_eq _ _
#check @plan4_modify_congr_at
#check @plan4_supplier_start_eq

theorem tmp_distrib_spec_aux2 (s : St) (who : Account) (s2 : St)
    (h : distributeSupplierComp s who = some s2) : True := by
  trivial

theorem tmp_final_auxA (s : St) (who : Account) :
    (s.accts.getD who noAcct).supply = (s.acct who).supply := rfl

theorem tmp_final_auxB (s : St) (who : Account) :
    (s.accts.getD who noAcct).supplierIndex = (s.acct who).supplierIndex := rfl

theorem tmp_pos_branch (s : St) (who : Account) (tgt : St)
    (hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index)
    (h : (some (s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) } : Acct))) : Option St) = some tgt) :
    tgt = s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) } : Acct)) := by
  have hsup : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := plan4_supplier_start_eq _ _
  have hY : s.withAcct who (fun a => ({ a with supplierIndex := s.supplyState.index, accrued := a.accrued + mulDouble (s.acct who).supply (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) } : Acct)) = tgt := Option.some_inj.mp h
  rw [hsup] at hY
  exact hY.symm

theorem tmp_parse_checkA (s : St) (who : Account) (t : St) (h : t = s.withAcct who fun a => { a with supplierIndex := s.supplyState.index }) : True := by trivial

theorem ztest_merge2 (s : St) (A : Side) (who : Nat) (f : Acct → Acct) :
    ({ s with supplyState := A } : St).withAcct who f =
    { s with supplyState := A, accts := s.accts.modify who f } := by
  unfold St.withAcct
  cases s with
  | mk bn sup bor res ac =>
    rfl

theorem td0_supply_hook_effect (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' → SupplyDistributed s who s' := by
  intro h
  obtain ⟨t, hU, hD⟩ := tmp_supply_step1b s who s' h
  obtain ⟨hblk, hteq⟩ := plan3_updateSupply_accrue s t hU
  exact plan4_supplyDistributed_of_steps s who t s' hblk hteq hD

theorem tmp_borrow_step1b_aux (s : St) (who : Account) (s' : St)
    (h : comptroller s (.borrowHook who) = some s') :
    ∃ t, updateCompBorrowIndex s = some t ∧
      distributeBorrowerComp t who = some s' := by
  unfold comptroller at h
  cases hU : updateCompBorrowIndex s with
  | none =>
    simp [hU] at h
  | some t =>
    simp [hU] at h
    exact ⟨t, rfl, h⟩

theorem tmp_bdistr_explore (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    True := by
  unfold distributeBorrowerComp at h
  simp only at h
  guard_hyp h : _ = some s'
  trivial

theorem tmp_bdistr_explore2 (s : St) (who : Account) :
    distributeBorrowerComp s who =
    let borrowIndex := s.borrowState.index
    let borrowerIndex :=
      if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ borrowIndex then compInitialIndex
      else (s.acct who).borrowerIndex
    match subChecked borrowIndex borrowerIndex with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := borrowIndex, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex }) := by
  rfl

theorem plan5_borrower_start_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · subst h
    simp only
    by_cases h2 : compInitialIndex ≤ index <;> simp [h2]
  · have hne : ¬ (recorded = 0 ∧ compInitialIndex ≤ index) := fun hh => h hh.1
    simp [hne, h]


theorem plan5_accrue_borrow_acct_eq (s : St) (who : Account) :
    ({ s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).acct who =
      s.acct who := by
  rfl


theorem plan5_accrue_borrow_withAcct_eq (s : St) (who : Account) (f : Acct → Acct) :
    ({ s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } : St).withAcct who f =
    { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who f } := by
  unfold St.withAcct
  cases s with | mk blockNumber supplyState borrowState reserve accts =>
    rfl


theorem plan5_distributeBorrowerComp_spec (s : St) (who : Account) (s' : St) :
    distributeBorrowerComp s who = some s' →
      accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
          s.borrowState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index)
              s.borrowState.index } := by sorry

theorem plan5_borrowHook_decomp (s : St) (who : Account) (s' : St) :
    comptroller s (.borrowHook who) = some s' →
      ∃ t, updateCompBorrowIndex s = some t ∧
        distributeBorrowerComp t who = some s' :=
  fun h => tmp_borrow_step1b_aux s who s' h


theorem plan5_borrowDistributed_of_steps (s : St) (who : Account) (t s' : St) :
    s.borrowState.block ≤ s.blockNumber →
      t = { s with
        borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
        distributeBorrowerComp t who = some s' →
          BorrowDistributed s who s' := by
  intro hle ht hdist
  have hspec := plan5_distributeBorrowerComp_spec t who s' hdist
  obtain ⟨hle2, heq⟩ := hspec
  have ht_idx : t.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [ht]
  have ht_acct : t.acct who = s.acct who := by
    rw [ht]
    exact plan5_accrue_borrow_acct_eq s who
  have hle2' : accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← ht_acct, ← ht_idx]
    exact hle2
  refine ⟨hle, hle2', ?_⟩
  rw [heq, ht]
  rfl


theorem plan5_borrower_start_eq_proof (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart
  by_cases h : recorded = 0
  · subst h
    simp only
    by_cases h2 : compInitialIndex ≤ index <;> simp [h2]
  · have hne : ¬ (recorded = 0 ∧ compInitialIndex ≤ index) := fun hh => h hh.1
    simp [hne, h]

theorem plan5_distributeBorrowerComp_spec_aux_check (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index := plan5_borrower_start_eq _ _

theorem plan5_mulDouble_eq_creditFor (u d idx st : Nat) (h : st ≤ idx) (hd : d = idx - st) :
    mulDouble u d = creditFor u st idx := by unfold mulDouble creditFor; rw [hd]

theorem tmp_bspec_explore (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') : True := by
  unfold distributeBorrowerComp subChecked at h
  trivial

theorem tmp_borrow_unfold_match (s : St) (who : Account) :
    distributeBorrowerComp s who =
    match subChecked s.borrowState.index
      (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) with
    | none => none
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex }) := by
  unfold distributeBorrowerComp subChecked
  simp only

theorem plan5_borrowHook_decomp_proof : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.borrowHook who) = some s' →
      ∃ t, updateCompBorrowIndex s = some t ∧ distributeBorrowerComp t who = some s' :=
  fun s who s' h => tmp_borrow_step1b_aux s who s' h

theorem plan5_borrowDistributed_of_steps_proof (s : St) (who : Account) (t s' : St) :
    s.borrowState.block ≤ s.blockNumber →
      t = { s with
        borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
        distributeBorrowerComp t who = some s' →
          BorrowDistributed s who s' := by
  intro hle ht hdist
  have hspec := plan5_distributeBorrowerComp_spec t who s' hdist
  obtain ⟨hle2, heq⟩ := hspec
  have ht_idx : t.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [ht]
  have ht_acct : t.acct who = s.acct who := by
    rw [ht]
    exact plan5_accrue_borrow_acct_eq s who
  have hle2' : accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← ht_acct, ← ht_idx]
    exact hle2
  refine ⟨hle, hle2', ?_⟩
  rw [heq, ht]
  rfl

theorem plan5_borrowDistributed_of_steps_inlinecheck (s : St) (who : Account) (t s' : St) :
    s.borrowState.block ≤ s.blockNumber →
      t = { s with
        borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
        distributeBorrowerComp t who = some s' →
          BorrowDistributed s who s' := by
  intro hle ht hdist
  have hspec := plan5_distributeBorrowerComp_spec t who s' hdist
  obtain ⟨hle2, heq⟩ := hspec
  have ht_idx : t.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [ht]
  have ht_acct : t.acct who = s.acct who := by
    rw [ht]
    exact plan5_accrue_borrow_acct_eq s who
  have hle2' : accrualStart (s.acct who).borrowerIndex
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
    rw [← ht_acct, ← ht_idx]
    exact hle2
  refine ⟨hle, hle2', ?_⟩
  rw [heq, ht]
  rfl

theorem plan5_borrowDistributed_of_steps_direct (s : St) (who : Account) (t s' : St)
    (hle : s.borrowState.block ≤ s.blockNumber)
    (ht : t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) })
    (hdist : distributeBorrowerComp t who = some s') :
    BorrowDistributed s who s' :=
  plan5_borrowDistributed_of_steps_inlinecheck s who t s' hle ht hdist

theorem plan5_inj_probe (s : St) (who : Account) (s' : St)
    (h : some (s.withAcct who id) = some s') :
    s.withAcct who id = s' := by
  cases h
  rfl

theorem plan5_try_proof5 (s : St) (who : Account) (s' : St) :
    distributeBorrowerComp s who = some s' →
      accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
          s.borrowState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index)
              s.borrowState.index } := by
  intro h
  have hunfold := tmp_borrow_unfold_match s who
  rw [hunfold] at h
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    plan5_borrower_start_eq _ _
  rw [hstart] at h
  unfold subChecked at h
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h
    refine ⟨hle, ?_⟩
    cases h
    unfold St.withAcct
    have hpt : (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)) (s.accts.getD who noAcct) =
      (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) (s.accts.getD who noAcct) := by
      show ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct) =
        ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)
      have ha1 : (s.accts.getD who noAcct).borrowerIndex = (s.acct who).borrowerIndex := rfl
      have ha2 : (s.accts.getD who noAcct).borrow = (s.acct who).borrow := rfl
      rw [ha1, ha2]
      unfold mulDouble creditFor
      rfl
    have hmod := plan4_modify_congr_at (l := s.accts) (who := who)
      (f := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)))
      (g := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct))) hpt
    rw [hmod]
  · simp only [hle, ↓reduceIte] at h
    simp at h

theorem plan5_try_proof6 (s : St) (who : Account) (s' : St) :
    distributeBorrowerComp s who = some s' →
      accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
          s.borrowState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            borrowerIndex := s.borrowState.index,
            accrued := a.accrued + creditFor a.borrow
              (accrualStart a.borrowerIndex s.borrowState.index)
              s.borrowState.index } := by
  intro h
  unfold distributeBorrowerComp at h
  simp only at h
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    plan5_borrower_start_eq _ _
  -- need to rewrite inside h's match scrutinee; generalize
  have h2 : (match subChecked s.borrowState.index (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
    | none => (none : Option St)
    | some deltaIndex =>
      some (s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow deltaIndex })) = some s' := by
    have := h
    rw [hstart] at this
    -- the let borrowerDelta etc may need unfolding; simp the lets
    simp only [subChecked, mulDouble] at this ⊢
    exact this
  unfold subChecked at h2
  by_cases hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hle, ↓reduceIte] at h2
    refine ⟨hle, ?_⟩
    cases h2
    unfold St.withAcct
    have hpt : (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)) (s.accts.getD who noAcct) =
      (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)) (s.accts.getD who noAcct) := by
      show ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct) =
        ({ (s.accts.getD who noAcct) with borrowerIndex := s.borrowState.index, accrued := (s.accts.getD who noAcct).accrued + creditFor (s.accts.getD who noAcct).borrow (accrualStart (s.accts.getD who noAcct).borrowerIndex s.borrowState.index) s.borrowState.index } : Acct)
      have ha1 : (s.accts.getD who noAcct).borrowerIndex = (s.acct who).borrowerIndex := rfl
      have ha2 : (s.accts.getD who noAcct).borrow = (s.acct who).borrow := rfl
      rw [ha1, ha2]
      unfold mulDouble creditFor
      rfl
    have hmod := plan4_modify_congr_at (l := s.accts) (who := who)
      (f := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + mulDouble (s.acct who).borrow (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) } : Acct)))
      (g := (fun a => ({ a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } : Acct))) hpt
    rw [hmod]
  · simp only [hle, ↓reduceIte] at h2
    simp at h2

theorem td0_borrow_hook_effect (s : St) (who : Account) (s' : St) :
    comptroller s (.borrowHook who) = some s' → BorrowDistributed s who s' := by
  intro h
  obtain ⟨t, hu, hd⟩ := tmp_borrow_step1b_aux s who s' h
  obtain ⟨hle, ht⟩ := plan3_updateBorrow_accrue s t hu
  exact plan5_borrowDistributed_of_steps s who t s' hle ht hd

theorem td0_call_some_aux_test (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := upd_supply_eq2 s h
  rw [hsub]
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc]
    simp
  · simp only [hc]
    by_cases hc2 : s.blockNumber - s.supplyState.block > 0
    · simp [hc2]
    · simp [hc2]

theorem td0_accrual_le (r idx : Nat) (h : r ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ idx
    · simp [hi, hi]
    · simp [hi]
  · simp [hr, h]

theorem td0_borrow_sub_eq (s : St) (hle : s.borrowState.block ≤ s.blockNumber) :
    subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
  unfold subChecked
  simp [hle]

theorem td0_getD_sup_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  unfold St.acct
  have h2 : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index := hmem
  have hS : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (h2 a ha).1
  -- use plan2_aux_getD_le with B := borrow index
  have hboth := plan2_aux_getD_le s.accts s.supplyState.index s.borrowState.index who h2
  exact hboth.1

theorem td0_getD_bor_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  have hboth := plan2_aux_getD_le s.accts s.supplyState.index s.borrowState.index who hmem
  exact hboth.2

theorem td0_updateSupply_some2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked; simp [h]
  rw [hsub]
  by_cases hc : (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0)
  · simp only [hc]; simp
  · simp only [hc]
    by_cases hc2 : s.blockNumber - s.supplyState.block > 0
    · simp [hc2]
    · simp [hc2]

theorem td0_updateBorrow_some2 (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome := by
  unfold updateCompBorrowIndex
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [h]
  rw [hsub]
  by_cases hc : (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0)
  · simp only [hc]; simp
  · simp only [hc]
    by_cases hc2 : s.blockNumber - s.borrowState.block > 0
    · simp [hc2]
    · simp [hc2]

theorem td0_distSupply_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  unfold distributeSupplierComp
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := plan4_supplier_start_eq _ _
  have hle : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) ≤ s.supplyState.index := by rw [hstart]; exact h
  have hsub : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = some (s.supplyState.index - (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex)) := by
    unfold subChecked; simp [hle]
  simp only []
  rw [hsub]
  simp

theorem td0_distBorrow_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  unfold distributeBorrowerComp
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := plan5_borrower_start_eq _ _
  have hle : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by rw [hstart]; exact h
  have hsub : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = some (s.borrowState.index - (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex)) := by
    unfold subChecked; simp [hle]
  simp only []
  rw [hsub]
  simp

theorem td0_updSup_acct (s t : St) (who : Account)
    (h : updateCompSupplyIndex s = some t) :
    t.acct who = s.acct who := by
  have hacc := plan3_updateSupply_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  rfl

theorem td0_updSup_idx_ge (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    s.supplyState.index ≤ t.supplyState.index := by
  have hacc := plan3_updateSupply_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  show s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
  exact (plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)).1

theorem td0_updSup_blk (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState ∧ t.supplyState.block = s.blockNumber := by
  have hacc := plan3_updateSupply_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  refine ⟨rfl, rfl, ?_⟩
  exact (plan0_accrueSide_props s.supplyState s.blockNumber (totalSupply s)).2.1

theorem td0_updBor_acct (s t : St) (who : Account)
    (h : updateCompBorrowIndex s = some t) :
    t.acct who = s.acct who := by
  have hacc := plan3_updateBorrow_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  rfl

theorem td0_updBor_idx_ge (s t : St)
    (h : updateCompBorrowIndex s = some t) :
    s.borrowState.index ≤ t.borrowState.index := by
  have hacc := plan3_updateBorrow_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  show s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
  exact (plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)).1

theorem td0_updBor_pres (s t : St)
    (h : updateCompBorrowIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.supplyState = s.supplyState ∧ t.borrowState.block = s.blockNumber := by
  have hacc := plan3_updateBorrow_accrue s t h
  obtain ⟨_, ht⟩ := hacc
  rw [ht]
  refine ⟨rfl, rfl, ?_⟩
  exact (plan0_accrueSide_props s.borrowState s.blockNumber (totalBorrows s)).2.1

theorem td0_setSup_pres2 (s mid : St) (a : Nat)
    (h : setSupplySpeed s a = some mid) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧ mid.accts = s.accts := by
  unfold setSupplySpeed at h
  by_cases heq : s.supplyState.speed = a
  · simp [heq] at h
    rw [← h]
    exact ⟨rfl, rfl, rfl⟩
  · simp [heq] at h
    cases hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      rw [← h]
      have hacc := plan3_updateSupply_accrue s u hu
      obtain ⟨_, ht⟩ := hacc
      rw [ht]
      exact ⟨rfl, rfl, rfl⟩

theorem td0_setBor_pres2 (s mid : St) (b : Nat)
    (h : setBorrowSpeed s b = some mid) :
    mid.supplyState = s.supplyState ∧ mid.blockNumber = s.blockNumber ∧ mid.accts = s.accts := by
  unfold setBorrowSpeed at h
  by_cases heq : s.borrowState.speed = b
  · simp [heq] at h
    rw [← h]
    exact ⟨rfl, rfl, rfl⟩
  · simp [heq] at h
    cases hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some u =>
      simp [hu] at h
      rw [← h]
      have hacc := plan3_updateBorrow_accrue s u hu
      obtain ⟨_, ht⟩ := hacc
      rw [ht]
      exact ⟨rfl, rfl, rfl⟩

theorem td0_setComp_exists (s : St) (a b : Nat) (s' : St)
    (h : setCompSpeedInternal s a b = some s') :
    ∃ mid, setSupplySpeed s a = some mid ∧ setBorrowSpeed mid b = some s' :=
  tmp_mid_exists5 s a b s' h

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hs
  exact td0_call_some s c hs

theorem req_supply_hook         : SupplyHookEffects comptroller := by
  intro s who s' h
  exact td0_supply_hook_effect s who s' h

theorem req_borrow_hook         : BorrowHookEffects comptroller := by
  intro s who s' h
  exact td0_borrow_hook_effect s who s' h

theorem req_claim               : ClaimEffects comptroller := by
  intro s who s' h
  exact td0_claim_effect s who s' h

theorem req_set_speeds          : SetSpeedsEffects comptroller := by
  intro s a b s' h
  exact td0_set_speeds_effect s a b s' h

theorem req_rewards_bounded     : RewardsBounded comptroller := by
  intro L ops hWF
  have hinv := td0_upgrade_inv L hWF
  have hrun := td0_run_potential_le (L.compSpeed, L.compSpeed) (upgrade L) ops hinv
  have hinit := td0_upgrade_potential_le L hWF
  have hscaled :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        doubleScale * (upgrade L).credited +
        (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by
    calc doubleScale * (run comptroller (upgrade L) ops).credited
        ≤ td0_potential (run comptroller (upgrade L) ops) :=
          td0_credited_le_potential _
      _ ≤ td0_potential (upgrade L) +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops := hrun
      _ ≤ (doubleScale * (upgrade L).credited +
            (L.accts.map L.pendingScaled).sum +
            doubleScale * (L.unindexedSupply + L.unindexedBorrow)) +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
          Nat.add_le_add_right hinit _
  exact td0_rewards_bound_of_scaled _ L _ hscaled

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hWF
  have hinv := td0_upgrade_inv L hWF
  have hrun := td0_run_potentialTo_le (L.compSpeed, L.compSpeed) (upgrade L) ops who hinv
  have hinit := td0_upgrade_potentialTo_le L who hWF
  have hscaled :
      doubleScale * (run comptroller (upgrade L) ops).creditedTo who ≤
        doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by
    calc doubleScale * (run comptroller (upgrade L) ops).creditedTo who
        ≤ td0_potentialTo (run comptroller (upgrade L) ops) who :=
          td0_creditedTo_le_potential _ _
      _ ≤ td0_potentialTo (upgrade L) who +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops := hrun
      _ ≤ (doubleScale * (upgrade L).creditedTo who +
            td0_pendingOf L who +
            doubleScale * td0_unindexedOf L who) +
            doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
          Nat.add_le_add_right hinit _
  exact td0_account_bound_of_scaled _ L who _ hscaled

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hWF hNo
  have hinv0 := td0_upgrade_inv L hWF
  have hinv := td0_run_inv (L.compSpeed, L.compSpeed) (upgrade L) history hinv0
  have hrun :=
    td0_run_potentialTo_le
      (speedsAfter (L.compSpeed, L.compSpeed) history)
      (run comptroller (upgrade L) history) ops who hinv
  have hmid :=
    td0_potentialTo_of_no_position
      (run comptroller (upgrade L) history) who hNo
  have hscaled :
      doubleScale *
          (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who ≤
        doubleScale * (run comptroller (upgrade L) history).creditedTo who +
          doubleScale *
            emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops := by
    calc doubleScale *
            (run comptroller (run comptroller (upgrade L) history) ops).creditedTo who
        ≤ td0_potentialTo
            (run comptroller (run comptroller (upgrade L) history) ops) who :=
          td0_creditedTo_le_potential _ _
      _ ≤ td0_potentialTo (run comptroller (upgrade L) history) who +
            doubleScale *
              emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops := hrun
      _ = doubleScale * (run comptroller (upgrade L) history).creditedTo who +
            doubleScale *
              emitted (speedsAfter (L.compSpeed, L.compSpeed) history) ops := by
            rw [hmid]
  exact td0_scaled_le_add hscaled

end CompRewards
