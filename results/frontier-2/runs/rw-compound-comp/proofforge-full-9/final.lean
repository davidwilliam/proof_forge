import CompRewards.Spec
import ProofForgeFin.Ledger
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Accumulator.Runs

open ProofForgeFin.Accumulator ProofForgeFin.DeFi.Rewards ProofForgeFin.Ledger
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

/-- `updateCompSupplyIndex(cToken)`: bring the supply index up to date
(`accrueSide`); reverts (`sub_` underflow) when the side's block lies ahead of the
current block. -/
def updateCompSupplyIndex (s : St) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
  else none

/-- `updateCompBorrowIndex(cToken, marketBorrowIndex)`. -/
def updateCompBorrowIndex (s : St) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
  else none

/-- `distributeSupplierComp(cToken, supplier)`: credit from `accrualStart`
(`>= compInitialIndex`, the Proposal 64 fix), rounded down via `creditFor`;
reverts (`sub_` underflow) when the start lies above the index. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  if accrualStart (s.acct supplier).supplierIndex s.supplyState.index ≤ s.supplyState.index then
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })
  else none

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  if accrualStart (s.acct borrower).borrowerIndex s.borrowState.index ≤ s.borrowState.index then
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })
  else none

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  if 0 < (s.acct user).accrued ∧ (s.acct user).accrued ≤ s.reserve then
    { s with reserve := s.reserve - (s.acct user).accrued,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
  else s

/-- `claimComp([holder], [market], true, true)`. -/
def claimComp (s : St) (holder : Account) : Option St :=
  match updateCompBorrowIndex s with
  | none => none
  | some s =>
    match distributeBorrowerComp s holder with
    | none => none
    | some s =>
      match updateCompSupplyIndex s with
      | none => none
      | some s =>
        match distributeSupplierComp s holder with
        | none => none
        | some s => some (grantCompInternal s holder)

/-- The supply branch of `setCompSpeedInternal`: when the supply speed changes, accrue at the
old speed, then store the new one. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    match updateCompSupplyIndex s with
    | none => none
    | some s => some { s with supplyState := { s.supplyState with speed := supplySpeed } }
  else some s

/-- The borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    match updateCompBorrowIndex s with
    | none => none
    | some s => some { s with borrowState := { s.borrowState with speed := borrowSpeed } }
  else some s

/-- `setCompSpeedInternal(cToken, supplySpeed, borrowSpeed)`: the supply branch, then the borrow
branch. -/
def setCompSpeedInternal (s : St) (supplySpeed borrowSpeed : Nat) : Option St :=
  match setSupplySpeed s supplySpeed with
  | none => none
  | some s => setBorrowSpeed s borrowSpeed

/-- Inversion for `updateCompSupplyIndex`: success records the block bound and the result. -/
theorem updS_inv (s s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
      s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  split at h
  · next hle =>
    cases h
    exact ⟨hle, rfl⟩
  · next hle =>
    cases h

/-- Inversion for `updateCompBorrowIndex`. -/
theorem updB_inv (s s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
      s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  split at h
  · next hle =>
    cases h
    exact ⟨hle, rfl⟩
  · next hle =>
    cases h

/-- Inversion for `distributeSupplierComp`. -/
theorem distS_inv (s s' : St) (who : Account) (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
      s' = s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } := by
  unfold distributeSupplierComp at h
  split at h
  · next hle =>
    cases h
    exact ⟨hle, rfl⟩
  · next hle =>
    cases h

/-- Inversion for `distributeBorrowerComp`. -/
theorem distB_inv (s s' : St) (who : Account) (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
      s' = s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } := by
  unfold distributeBorrowerComp at h
  split at h
  · next hle =>
    cases h
    exact ⟨hle, rfl⟩
  · next hle =>
    cases h

/-- `accrualStart` never lies above the index when the recorded checkpoint does not. -/
theorem accrualStart_le (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp only [hr, ↓reduceIte]
    by_cases hi : compInitialIndex ≤ index
    · simp only [hi, ↓reduceIte]
    · simp only [hi, ↓reduceIte]
      exact Nat.zero_le _
  · simp only [hr, ↓reduceIte]
    exact h

/-- An update never lowers the index. -/
theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos hc]
    exact Nat.le_add_right _ _
  · rw [if_neg hc]
    exact Nat.le_refl _

/-- An update brings the side up to date. -/
theorem accrueSide_block_eq (sd : Side) (now total : Nat)
    (h : sd.block ≤ now) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos hc]
  · rw [if_neg hc]

/-- Success equations for the updates and distributions. -/
theorem updS_ok (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex
  rw [if_pos h]

theorem updB_ok (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex
  rw [if_pos h]

theorem distS_ok (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold distributeSupplierComp
  rw [if_pos h]

theorem distB_ok (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold distributeBorrowerComp
  rw [if_pos h]

/-- Our payment is `grant`. -/
theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  rfl

/-- In a state whose recorded indices are all below the market's, so is account `who`'s. -/
theorem acct_supplier_le (s : St) (who : Account)
    (h : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact h _ hm
  · rw [hm]
    show (0 : Nat) ≤ s.supplyState.index
    exact Nat.zero_le _

theorem acct_borrower_le (s : St) (who : Account)
    (h : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
  · exact h _ hm
  · rw [hm]
    show (0 : Nat) ≤ s.borrowState.index
    exact Nat.zero_le _

/-- A borrow distribution does not touch the account's supply checkpoint. -/
theorem withAcct_supplier (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  unfold St.withAcct St.acct
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases hc : who = who ∧ who < s.accts.length
  · rw [if_pos hc, hf]
  · rw [if_neg hc]

/-- A supply distribution does not touch the account's borrow checkpoint. -/
theorem withAcct_borrower (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((s.withAcct who f).acct who).borrowerIndex = (s.acct who).borrowerIndex := by
  unfold St.withAcct St.acct
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases hc : who = who ∧ who < s.accts.length
  · rw [if_pos hc, hf]
  · rw [if_neg hc]

/-- A borrow distribution preserves the account's supply checkpoint readback. -/
theorem distB_supplier (t1 t2 : St) (who : Account)
    (h : distributeBorrowerComp t1 who = some t2) :
    (t2.acct who).supplierIndex = (t1.acct who).supplierIndex := by
  obtain ⟨_, r⟩ := distB_inv t1 t2 who h
  rw [r]
  exact withAcct_supplier _ _ _ (fun a => rfl)

/-- A supply distribution preserves the account's borrow checkpoint readback. -/
theorem distS_borrower (t1 t2 : St) (who : Account)
    (h : distributeSupplierComp t1 who = some t2) :
    (t2.acct who).borrowerIndex = (t1.acct who).borrowerIndex := by
  obtain ⟨_, r⟩ := distS_inv t1 t2 who h
  rw [r]
  exact withAcct_borrower _ _ _ (fun a => rfl)

/-- Forward success for `setSupplySpeed`. -/
theorem setS_ok (s : St) (a : Nat)
    (h : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) :
    ∃ t, setSupplySpeed s a = some t := by
  unfold setSupplySpeed
  split
  · next hne =>
    have eu := updS_ok s (h hne)
    rw [eu]
    exact ⟨_, rfl⟩
  · next hn =>
    exact ⟨s, rfl⟩

/-- Forward success for `setBorrowSpeed`. -/
theorem setB_ok (s : St) (b : Nat)
    (h : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :
    ∃ t, setBorrowSpeed s b = some t := by
  unfold setBorrowSpeed
  split
  · next hne =>
    have eu := updB_ok s (h hne)
    rw [eu]
    exact ⟨_, rfl⟩
  · next hn =>
    exact ⟨s, rfl⟩

/-- Inversion for `setSupplySpeed`. -/
theorem setS_inv (s t : St) (a : Nat) (h : setSupplySpeed s a = some t) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState := if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  split at h
  · next hne =>
    cases eu : updateCompSupplyIndex s with
    | none =>
      simp only [eu] at h
      cases h
    | some u =>
      simp only [eu] at h
      cases h
      obtain ⟨hsb, ru⟩ := updS_inv s u eu
      subst ru
      refine ⟨fun _ => hsb, ?_⟩
      rw [if_neg hne]
      try rfl
  · next hn =>
    cases h
    refine ⟨fun hne => (hn hne).elim, ?_⟩
    have hb : s.supplyState.speed = a := Classical.byContradiction (fun hc => hn hc)
    rw [if_pos hb]

/-- Inversion for `setBorrowSpeed`. -/
theorem setB_inv (s t : St) (b : Nat) (h : setBorrowSpeed s b = some t) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState := if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  split at h
  · next hne =>
    cases eu : updateCompBorrowIndex s with
    | none =>
      simp only [eu] at h
      cases h
    | some u =>
      simp only [eu] at h
      cases h
      obtain ⟨hbb, ru⟩ := updB_inv s u eu
      subst ru
      refine ⟨fun _ => hbb, ?_⟩
      rw [if_neg hne]
      try rfl
  · next hn =>
    cases h
    refine ⟨fun hne => (hn hne).elim, ?_⟩
    have hb : s.borrowState.speed = b := Classical.byContradiction (fun hc => hn hc)
    rw [if_pos hb]

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who =>
    match updateCompSupplyIndex s with
    | none => none
    | some s => distributeSupplierComp s who
  | .borrowHook who =>
    match updateCompBorrowIndex s with
    | none => none
    | some s => distributeBorrowerComp s who
  | .claim who => claimComp s who
  | .setSpeeds a b => setCompSpeedInternal s a b

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases e1 : updateCompSupplyIndex s with
  | none =>
    simp only [e1] at h
    cases h
  | some s1 =>
    simp only [e1] at h
    cases e2 : distributeSupplierComp s1 who with
    | none =>
      simp only [e2] at h
      cases h
    | some s2 =>
      simp only [e2] at h
      cases h
      obtain ⟨hb, r1⟩ := updS_inv s s1 e1
      obtain ⟨hs, r2⟩ := distS_inv s1 s' who e2
      subst r1
      exact ⟨hb, hs, r2⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases e1 : updateCompBorrowIndex s with
  | none =>
    simp only [e1] at h
    cases h
  | some s1 =>
    simp only [e1] at h
    cases e2 : distributeBorrowerComp s1 who with
    | none =>
      simp only [e2] at h
      cases h
    | some s2 =>
      simp only [e2] at h
      cases h
      obtain ⟨hb, r1⟩ := updB_inv s s1 e1
      obtain ⟨hs, r2⟩ := distB_inv s1 s' who e2
      subst r1
      exact ⟨hb, hs, r2⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  cases e1 : updateCompBorrowIndex s with
  | none =>
    simp only [e1] at h
    cases h
  | some t1 =>
    simp only [e1] at h
    cases e2 : distributeBorrowerComp t1 who with
    | none =>
      simp only [e2] at h
      cases h
    | some t2 =>
      simp only [e2] at h
      cases e3 : updateCompSupplyIndex t2 with
      | none =>
        simp only [e3] at h
        cases h
      | some t3 =>
        simp only [e3] at h
        cases e4 : distributeSupplierComp t3 who with
        | none =>
          simp only [e4] at h
          cases h
        | some t4 =>
          simp only [e4] at h
          cases h
          obtain ⟨hb1, r1⟩ := updB_inv s t1 e1
          obtain ⟨hs2, r2⟩ := distB_inv t1 t2 who e2
          obtain ⟨hb3, r3⟩ := updS_inv t2 t3 e3
          obtain ⟨hs4, r4⟩ := distS_inv t3 t4 who e4
          rw [grant_eq]
          refine ⟨t2, t4, ⟨hb1, ?_, ?_⟩, ⟨hb3, ?_, ?_⟩, rfl⟩
          · rw [r1] at hs2
            exact hs2
          · rw [r1] at r2
            exact r2
          · rw [r3] at hs4
            exact hs4
          · rw [r3] at r4
            exact r4

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller, setCompSpeedInternal] at h
  cases e1 : setSupplySpeed s a with
  | none =>
    simp only [e1] at h
    cases h
  | some t1 =>
    simp only [e1] at h
    cases e2 : setBorrowSpeed t1 b with
    | none =>
      simp only [e2] at h
      cases h
    | some t2 =>
      simp only [e2] at h
      have hs' : t2 = s' := by
        cases h
        rfl
      rw [← hs'] at h ⊢
      obtain ⟨hs1, r1⟩ := setS_inv s t1 a e1
      obtain ⟨hs2, r2⟩ := setB_inv t1 t2 b e2
      refine ⟨hs1, ?_, ?_⟩
      · intro hne
        have hne2 : t1.borrowState.speed ≠ b := by
          rw [r1]
          exact hne
        have hle := hs2 hne2
        rw [r1] at hle
        exact hle
      · by_cases ha : s.supplyState.speed = a
        · by_cases hb : s.borrowState.speed = b
          · have hb2 : t1.borrowState.speed = b := by
              rw [r1]
              exact hb
            rw [if_pos hb2] at r2
            rw [if_pos ha]
            rw [if_pos hb]
            rw [r1] at r2
            rw [if_pos ha] at r2
            exact r2
          · have hnb2 : t1.borrowState.speed ≠ b := by
              rw [r1]
              exact hb
            rw [if_neg hnb2] at r2
            rw [if_pos ha]
            rw [if_neg hb]
            rw [r1] at r2
            rw [if_pos ha] at r2
            exact r2
        · have hna : s.supplyState.speed ≠ a := ha
          by_cases hb : s.borrowState.speed = b
          · have hb2 : t1.borrowState.speed = b := by
              rw [r1]
              exact hb
            rw [if_pos hb2] at r2
            rw [if_neg hna]
            rw [if_pos hb]
            rw [r1] at r2
            rw [if_neg hna] at r2
            exact r2
          · have hnb2 : t1.borrowState.speed ≠ b := by
              rw [r1]
              exact hb
            rw [if_neg hnb2] at r2
            rw [if_neg hna]
            rw [if_neg hb]
            rw [r1] at r2
            rw [if_neg hna] at r2
            exact r2

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hSb, hBb, hIdx⟩ := hc
  have hs1 : ∀ who : Account, (s.acct who).supplierIndex ≤ s.supplyState.index :=
    fun who => acct_supplier_le s who (fun a ha => (hIdx a ha).1)
  have hb1 : ∀ who : Account, (s.acct who).borrowerIndex ≤ s.borrowState.index :=
    fun who => acct_borrower_le s who (fun a ha => (hIdx a ha).2)
  cases c with
  | supplyHook who =>
    obtain ⟨t1, e1⟩ : ∃ t, updateCompSupplyIndex s = some t := ⟨_, updS_ok s hSb⟩
    obtain ⟨_, r1⟩ := updS_inv s t1 e1
    have hd : accrualStart (t1.acct who).supplierIndex (t1.supplyState).index ≤
        (t1.supplyState).index := by
      rw [r1]
      exact accrualStart_le _ _ (Nat.le_trans (hs1 who) (accrueSide_index_ge _ _ _))
    obtain ⟨t2, e2⟩ : ∃ t, distributeSupplierComp t1 who = some t := ⟨_, distS_ok t1 who hd⟩
    exact Option.isSome_iff_exists.mpr ⟨t2, by simp only [comptroller, e1, e2]⟩
  | borrowHook who =>
    obtain ⟨t1, e1⟩ : ∃ t, updateCompBorrowIndex s = some t := ⟨_, updB_ok s hBb⟩
    obtain ⟨_, r1⟩ := updB_inv s t1 e1
    have hd : accrualStart (t1.acct who).borrowerIndex (t1.borrowState).index ≤
        (t1.borrowState).index := by
      rw [r1]
      exact accrualStart_le _ _ (Nat.le_trans (hb1 who) (accrueSide_index_ge _ _ _))
    obtain ⟨t2, e2⟩ : ∃ t, distributeBorrowerComp t1 who = some t := ⟨_, distB_ok t1 who hd⟩
    exact Option.isSome_iff_exists.mpr ⟨t2, by simp only [comptroller, e1, e2]⟩
  | claim who =>
    obtain ⟨t1, e1⟩ : ∃ t, updateCompBorrowIndex s = some t := ⟨_, updB_ok s hBb⟩
    obtain ⟨_, r1⟩ := updB_inv s t1 e1
    have hdB : accrualStart (t1.acct who).borrowerIndex (t1.borrowState).index ≤
        (t1.borrowState).index := by
      rw [r1]
      exact accrualStart_le _ _ (Nat.le_trans (hb1 who) (accrueSide_index_ge _ _ _))
    obtain ⟨t2, e2⟩ : ∃ t, distributeBorrowerComp t1 who = some t := ⟨_, distB_ok t1 who hdB⟩
    obtain ⟨_, r2⟩ := distB_inv t1 t2 who e2
    have hSb2 : t2.supplyState.block ≤ t2.blockNumber := by
      rw [r2, r1]
      exact hSb
    obtain ⟨t3, e3⟩ : ∃ t, updateCompSupplyIndex t2 = some t := ⟨_, updS_ok t2 hSb2⟩
    obtain ⟨_, r3⟩ := updS_inv t2 t3 e3
    have hdS : accrualStart (t3.acct who).supplierIndex (t3.supplyState).index ≤
        (t3.supplyState).index := by
      have e31 : (t3.acct who).supplierIndex = (t2.acct who).supplierIndex := by
        rw [r3]
        try rfl
      rw [e31, distB_supplier t1 t2 who e2, r3, r2, r1]
      exact accrualStart_le _ _ (Nat.le_trans (hs1 who) (accrueSide_index_ge _ _ _))
    obtain ⟨t4, e4⟩ : ∃ t, distributeSupplierComp t3 who = some t := ⟨_, distS_ok t3 who hdS⟩
    exact Option.isSome_iff_exists.mpr
      ⟨grantCompInternal t4 who, by simp only [comptroller, claimComp, e1, e2, e3, e4]⟩
  | setSpeeds a b =>
    obtain ⟨t1, e1⟩ : ∃ t, setSupplySpeed s a = some t := setS_ok s a (fun _ => hSb)
    obtain ⟨_, r1⟩ := setS_inv s t1 a e1
    obtain ⟨t2, e2⟩ : ∃ t, setBorrowSpeed t1 b = some t :=
      setB_ok t1 b (fun _ => by rw [r1]; exact hBb)
    have hfin : comptroller s (.setSpeeds a b) = some t2 := by
      simp only [comptroller, setCompSpeedInternal, e1]
      exact e2
    exact Option.isSome_iff_exists.mpr ⟨t2, hfin⟩
/-! ## Potentials for the boundedness requirements -/

/-- Scaled supply rewards owed to `a` at the current index. -/
def owedSup (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - firstStart compInitialIndex a.supplierIndex s.supplyState.index)

/-- Scaled borrow rewards owed to `a` at the current index. -/
def owedBor (s : St) (a : Acct) : Nat :=
  a.borrow * (s.borrowState.index - firstStart compInitialIndex a.borrowerIndex s.borrowState.index)

/-- Supply emission not yet in the index. -/
def unidxSup (s : St) : Nat := (s.blockNumber - s.supplyState.block) * s.supplyState.speed

/-- Borrow emission not yet in the index. -/
def unidxBor (s : St) : Nat := (s.blockNumber - s.borrowState.block) * s.borrowState.speed

/-- Global potential: credited COMP at index scale, plus what is owed, plus the
unindexed emission at index scale. No interaction raises it; time passing raises
it by exactly the emission. -/
def Phi (s : St) : Nat :=
  (s.accts.map fun a => (a.accrued + a.wallet) * doubleScale + owedSup s a + owedBor s a).sum +
    doubleScale * (unidxSup s + unidxBor s)

/-- Our checkpoint rule is the safe one. -/
theorem accrualStart_firstStart (rec idx : Nat) :
    accrualStart rec idx = firstStart compInitialIndex rec idx := rfl

theorem one_pos : 0 < doubleScale := by
  unfold doubleScale
  decide

/-- An update always brings the side up to date. -/
theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos hc]
  · rw [if_neg hc]

/-- An update distributes at most the unindexed emission. -/
theorem covered_accrueSide (s : St) :
    Covered (totalSupply s) (doubleScale * unidxSup s)
      s.supplyState.index (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  refine ⟨accrueSide_index_ge _ _ _, ?_⟩
  unfold accrueSide unidxSup
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < totalSupply s
  · rw [if_pos hc]
    simp only []
    rw [Nat.add_sub_cancel_left]
    have h := total_mul_indexDelta_le doubleScale
      ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) (totalSupply s)
    simp only [indexDelta] at h
    rw [Nat.mul_comm doubleScale _]
    exact h
  · rw [if_neg hc]
    simp only [Nat.sub_self, Nat.mul_zero]
    exact Nat.zero_le _

/-- The borrow-side twin. -/
theorem covered_accrueSide_bor (s : St) :
    Covered (totalBorrows s) (doubleScale * unidxBor s)
      s.borrowState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  refine ⟨accrueSide_index_ge _ _ _, ?_⟩
  unfold accrueSide unidxBor
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < totalBorrows s
  · rw [if_pos hc]
    simp only []
    rw [Nat.add_sub_cancel_left]
    have h := total_mul_indexDelta_le doubleScale
      ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) (totalBorrows s)
    simp only [indexDelta] at h
    rw [Nat.mul_comm doubleScale _]
    exact h
  · rw [if_neg hc]
    simp only [Nat.sub_self, Nat.mul_zero]
    exact Nat.zero_le _

/-- A supply hook (update + settle) does not raise the potential. -/
theorem Phi_supplyHook (s s' : St) (who : Account) (h : SupplyDistributed s who s') :
    Phi s' ≤ Phi s := by
  obtain ⟨hb, hs, rsd⟩ := h
  rw [rsd]
  have hI : s.supplyState.index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_index_ge _ _ _
  have hcov : Covered (totalSupply s) (doubleScale * unidxSup s) s.supplyState.index
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    covered_accrueSide s
  have hU : (s.accts.map fun a => a.supply).sum *
        ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) +
        doubleScale * (0 + unidxBor s) ≤ doubleScale * (unidxSup s + unidxBor s) :=
    accrue_budget hcov
  have ht : ∀ a ∈ s.accts,
      ((a.accrued + a.wallet) * doubleScale +
        a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          firstStart compInitialIndex a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) +
        (a.borrow * (s.borrowState.index -
          firstStart compInitialIndex a.borrowerIndex s.borrowState.index))) ≤
      ((a.accrued + a.wallet) * doubleScale + owedSup s a + owedBor s a) +
      a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
        s.supplyState.index) := by
    intro a ha
    have h1 : a.supply *
          ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          firstStart compInitialIndex a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) ≤
        owedSup s a + a.supply *
          ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          s.supplyState.index) := by
      simp only [owedSup]
      exact owed_le_add (firstStart_mono compInitialIndex a.supplierIndex hI)
    have hb : owedBor s a = a.borrow * (s.borrowState.index -
        firstStart compInitialIndex a.borrowerIndex s.borrowState.index) := rfl
    omega
  have hf : ∀ a : Acct,
      (((a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) +
        a.wallet) * doubleScale +
        a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          firstStart compInitialIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) +
        (a.borrow * (s.borrowState.index -
          firstStart compInitialIndex a.borrowerIndex s.borrowState.index))) ≤
      (((a.accrued + a.wallet) * doubleScale +
        a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          firstStart compInitialIndex a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) +
        (a.borrow * (s.borrowState.index -
          firstStart compInitialIndex a.borrowerIndex s.borrowState.index)))) := by
    intro a
    have hset : (a.accrued + a.supply *
          ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          firstStart compInitialIndex a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale) *
          doubleScale +
        a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          firstStart compInitialIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) ≤
        a.accrued * doubleScale + a.supply *
          ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          firstStart compInitialIndex a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) :=
      settle_scaled_le
        (le_firstStart_self compInitialIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
    simp only [creditFor, accrualStart_firstStart, Nat.add_mul] at hset ⊢
    omega
  have hfall : who < s.accts.length →
      (fun (I : Nat) (a : Acct) => (a.accrued + a.wallet) * doubleScale +
        a.supply * (I - firstStart compInitialIndex a.supplierIndex I) +
        (a.borrow * (s.borrowState.index -
          firstStart compInitialIndex a.borrowerIndex s.borrowState.index)))
      ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      ((fun (a : Acct) =>
        { a with
          supplierIndex :=
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index })
        (s.accts.getD who noAcct)) ≤
      (fun (I : Nat) (a : Acct) => (a.accrued + a.wallet) * doubleScale +
        a.supply * (I - firstStart compInitialIndex a.supplierIndex I) +
        (a.borrow * (s.borrowState.index -
          firstStart compInitialIndex a.borrowerIndex s.borrowState.index)))
      ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
      (s.accts.getD who noAcct) := by
    intro _
    simp only []
    exact hf _
  have hU0 : unidxSup ({ s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }) = 0 := by
    simp only [unidxSup, accrueSide_block, Nat.sub_self, Nat.zero_mul]
  have hUb : unidxBor ({ s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }) =
      unidxBor s := rfl
  have hmod := pot_accrue_settle_le s.accts who
    (fun a =>
      { a with
        supplierIndex :=
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index })
    noAcct
    (fun I a => (a.accrued + a.wallet) * doubleScale +
      a.supply * (I - firstStart compInitialIndex a.supplierIndex I) +
      (a.borrow * (s.borrowState.index -
        firstStart compInitialIndex a.borrowerIndex s.borrowState.index)))
    (fun a => a.supply) ht hU hfall
  unfold Phi at ⊢
  rw [hU0, hUb] at ⊢
  simp only [owedSup, owedBor, unidxSup, unidxBor] at hmod ⊢
  omega

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
