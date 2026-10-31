import CompRewards.Spec
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

def td0_pendingAcct (s : St) (a : Acct) : Nat :=
  a.supply * (s.supplyState.index - accrualStart a.supplierIndex s.supplyState.index) +
  a.borrow * (s.borrowState.index - accrualStart a.borrowerIndex s.borrowState.index)

def td0_pending (s : St) : Nat := (s.accts.map (td0_pendingAcct s)).sum

def td0_unindexed (s : St) : Nat :=
  (s.blockNumber - s.supplyState.block) * s.supplyState.speed +
  (s.blockNumber - s.borrowState.block) * s.borrowState.speed

def td0_potential (s : St) : Nat :=
  doubleScale * s.credited + td0_pending s + doubleScale * td0_unindexed s

def td0_pendingTo (s : St) (who : Account) : Nat := td0_pendingAcct s (s.acct who)

def td0_unindexedTo (s : St) (who : Account) : Nat :=
  (if 0 < (s.acct who).supply then
     (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0) +
  (if 0 < (s.acct who).borrow then
     (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0)

def td0_potentialTo (s : St) (who : Account) : Nat :=
  doubleScale * s.creditedTo who + td0_pendingTo s who + doubleScale * td0_unindexedTo s who

def td0_Inv (sp : Nat × Nat) (s : St) : Prop :=
  Consistent s ∧ s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2

theorem plan15_updateSupply_pres (s : St) :
    Consistent s →
    ∃ t, updateCompSupplyIndex s = some t ∧ Consistent t := by
  sorry

theorem plan15_updateBorrow_pres (s : St) :
    Consistent s →
    ∃ t, updateCompBorrowIndex s = some t ∧ Consistent t := by
  intro hC
  obtain ⟨hSup, hBor, hIdx⟩ := hC
  have hsub : subChecked s.blockNumber s.borrowState.block =
    some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked
    simp [hBor]
  unfold updateCompBorrowIndex
  rw [hsub]
  by_cases h1 : (s.blockNumber - s.borrowState.block) > 0 ∧ s.borrowState.speed > 0
  · simp only [h1, ↓reduceIte]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · exact hSup
    · simp
    · intro a ha
      obtain ⟨hs, hb⟩ := hIdx a ha
      simp only
      constructor
      · exact hs
      · apply Nat.le_trans hb
        apply Nat.le_add_right
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (s.blockNumber - s.borrowState.block) > 0
    · simp only [h2, ↓reduceIte]
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · exact hSup
      · simp
      · intro a ha
        obtain ⟨hs, hb⟩ := hIdx a ha
        simp only
        constructor
        · exact hs
        · exact hb
    · have hzero : s.blockNumber - s.borrowState.block = 0 := by omega
      have heq : s.blockNumber = s.borrowState.block := by omega
      simp only [h2, ↓reduceIte]
      refine ⟨s, rfl, ?_, ?_, ?_⟩
      · exact hSup
      · omega
      · exact hIdx


theorem plan15_distributeSupplier_pres (s : St) (who : Account) :
    Consistent s →
    ∃ s', distributeSupplierComp s who = some s' ∧ Consistent s' := by
  sorry

theorem plan15_distributeBorrower_pres (s : St) (who : Account) :
    Consistent s →
    ∃ s', distributeBorrowerComp s who = some s' ∧ Consistent s' := by
  sorry

theorem plan15_setSpeeds_some (s : St) (a b : Nat) :
    Consistent s → (comptroller s (.setSpeeds a b)).isSome := by
  sorry

theorem td0_calls_some : ∀ (s : St) (c : Call), Consistent s → (comptroller s c).isSome := by
  intro s c hs
  cases c with
  | supplyHook who =>
      obtain ⟨t, ht, htCons⟩ := plan15_updateSupply_pres s hs
      obtain ⟨s', hs', _hsCons⟩ := plan15_distributeSupplier_pres t who htCons
      simp [comptroller, ht, hs']
  | borrowHook who =>
      obtain ⟨t, ht, htCons⟩ := plan15_updateBorrow_pres s hs
      obtain ⟨s', hs', _hsCons⟩ := plan15_distributeBorrower_pres t who htCons
      simp [comptroller, ht, hs']
  | claim who =>
      obtain ⟨t1, ht1, h1⟩ := plan15_updateBorrow_pres s hs
      obtain ⟨t2, ht2, h2⟩ := plan15_distributeBorrower_pres t1 who h1
      obtain ⟨t3, ht3, h3⟩ := plan15_updateSupply_pres t2 h2
      obtain ⟨t4, ht4, _h4⟩ := plan15_distributeSupplier_pres t3 who h3
      simp [comptroller, claimComp, ht1, ht2, ht3, ht4]
  | setSpeeds a b =>
      exact plan15_setSpeeds_some s a b hs


theorem plan12_bind_some {α β : Type} (m : Option α) (f : α → Option β) (y : β) :
    m.bind f = some y → ∃ x, m = some x ∧ f x = some y := by
  intro h
  cases m with
  | none => simp at h
  | some x => exact ⟨x, rfl, h⟩

theorem plan12_update_supply_spec (s : St) (t : St) :
    updateCompSupplyIndex s = some t →
    s.supplyState.block ≤ s.blockNumber ∧
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  sorry

theorem plan12_distribute_supply_spec (t : St) (who : Account) (s' : St) :
    distributeSupplierComp t who = some s' →
    accrualStart (t.acct who).supplierIndex t.supplyState.index ≤ t.supplyState.index ∧
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        supplierIndex := t.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex t.supplyState.index) t.supplyState.index } } := by
  sorry

theorem plan12_combine_supply (s t s' : St) (who : Account) :
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } →
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        supplierIndex := t.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex t.supplyState.index) t.supplyState.index } } →
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  intro ht hs'
  subst ht
  subst hs'
  rfl


theorem td0_supply_hook_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.supplyHook who) = some s' → SupplyDistributed s who s' := by
  intro s who s' h
  have hbind : (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) = some s' := h
  obtain ⟨t, ht_update, ht_dist⟩ := plan12_bind_some _ _ _ hbind
  obtain ⟨hblock, ht_eq⟩ := plan12_update_supply_spec s t ht_update
  obtain ⟨hstart, hs'_eq⟩ := plan12_distribute_supply_spec t who s' ht_dist
  have hstart' : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [ht_eq] at hstart
    exact hstart
  unfold SupplyDistributed
  exact ⟨hblock, hstart', plan12_combine_supply s t s' who ht_eq hs'_eq⟩


theorem plan14_block_le_of_update (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber := by sorry

theorem plan14_eq_of_pos (s : St) (t : St) :
    0 < s.blockNumber - s.borrowState.block →
    0 < s.borrowState.speed →
    0 < totalBorrows s →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan14_eq_of_zero_total (s : St) (t : St) :
    0 < s.blockNumber - s.borrowState.block →
    0 < s.borrowState.speed →
    totalBorrows s = 0 →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan14_eq_of_zero_speed (s : St) (t : St) :
    0 < s.blockNumber - s.borrowState.block →
    s.borrowState.speed = 0 →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan14_eq_of_zero_delta (s : St) (t : St) :
    s.blockNumber - s.borrowState.block = 0 →
    updateCompBorrowIndex s = some t →
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan13_update_borrow_spec (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber ∧
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  intro h
  refine ⟨plan14_block_le_of_update s t h, ?_⟩
  by_cases hd : 0 < s.blockNumber - s.borrowState.block
  · by_cases hs : 0 < s.borrowState.speed
    · by_cases ht : 0 < totalBorrows s
      · exact plan14_eq_of_pos s t hd hs ht h
      · have ht0 : totalBorrows s = 0 := by omega
        exact plan14_eq_of_zero_total s t hd hs ht0 h
    · have hs0 : s.borrowState.speed = 0 := by omega
      exact plan14_eq_of_zero_speed s t hd hs0 h
  · have hd0 : s.blockNumber - s.borrowState.block = 0 := by omega
    exact plan14_eq_of_zero_delta s t hd0 h


theorem plan13_distribute_borrow_spec (t : St) (who : Account) (s' : St) :
    distributeBorrowerComp t who = some s' →
    accrualStart (t.acct who).borrowerIndex t.borrowState.index ≤ t.borrowState.index ∧
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        borrowerIndex := t.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex t.borrowState.index) t.borrowState.index } } := by
  sorry

theorem plan13_start_le_of_update (s t : St) (who : Account) :
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
    accrualStart (t.acct who).borrowerIndex t.borrowState.index ≤ t.borrowState.index →
    accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  intro ht hle
  subst ht
  exact hle


theorem plan13_combine_borrow (s t s' : St) (who : Account) :
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } →
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        borrowerIndex := t.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex t.borrowState.index) t.borrowState.index } } →
    s' = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
      accts := s.accts.modify who fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } } := by
  intro ht hs'
  subst ht
  subst hs'
  rfl


theorem td0_borrow_hook_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.borrowHook who) = some s' → BorrowDistributed s who s' := by
  intro s who s' h
  have hb : (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) = some s' := h
  obtain ⟨t, ht, hd⟩ := plan12_bind_some _ _ _ hb
  obtain ⟨hblock, ht_eq⟩ := plan13_update_borrow_spec s t ht
  obtain ⟨hstart_t, hd_eq⟩ := plan13_distribute_borrow_spec t who s' hd
  have hstart := plan13_start_le_of_update s t who ht_eq hstart_t
  unfold BorrowDistributed
  exact ⟨hblock, hstart, plan13_combine_borrow s t s' who ht_eq hd_eq⟩


theorem plan17_borrow_hook_eq (s : St) (who : Account) :
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind fun t => distributeBorrowerComp t who := by
  sorry

theorem plan17_supply_hook_eq (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind fun t => distributeSupplierComp t who := by
  sorry

theorem plan17_claim_eq (s : St) (who : Account) :
    comptroller s (.claim who) =
      (updateCompBorrowIndex s).bind fun t =>
        (distributeBorrowerComp t who).bind fun m1 =>
          (updateCompSupplyIndex m1).bind fun u =>
            (distributeSupplierComp u who).bind fun m2 =>
              some (grantCompInternal m2 who) := by
  sorry

theorem plan16_claim_decomp (s : St) (who : Account) (s' : St) :
    comptroller s (.claim who) = some s' →
    ∃ m1 m2, comptroller s (.borrowHook who) = some m1 ∧
      comptroller m1 (.supplyHook who) = some m2 ∧
      s' = grantCompInternal m2 who := by
  intro h
  rw [plan17_claim_eq s who] at h
  obtain ⟨t, ht, h1⟩ := plan12_bind_some _ _ _ h
  obtain ⟨m1, hm1, h2⟩ := plan12_bind_some _ _ _ h1
  obtain ⟨u, hu, h3⟩ := plan12_bind_some _ _ _ h2
  obtain ⟨m2, hm2, h4⟩ := plan12_bind_some _ _ _ h3
  have hs' : s' = grantCompInternal m2 who := (Option.some.inj h4).symm
  refine ⟨m1, m2, ?_, ?_, hs'⟩
  · rw [plan17_borrow_hook_eq s who, ht]
    exact hm1
  · rw [plan17_supply_hook_eq m1 who, hu]
    exact hm2


theorem plan16_grant_eq (s : St) (who : Account) :
    grantCompInternal s who = grant s who := by sorry

theorem plan16_claimed_intro (s : St) (who : Account) (m1 m2 s' : St) :
    BorrowDistributed s who m1 → SupplyDistributed m1 who m2 →
    s' = grant m2 who → Claimed s who s' := by
  intro hb hs hg
  unfold Claimed
  exact ⟨m1, m2, hb, hs, hg⟩

theorem td0_claim_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.claim who) = some s' → Claimed s who s' := by
  intro s who s' h
  obtain ⟨m1, m2, hbHook, hsHook, hGrant⟩ := plan16_claim_decomp s who s' h
  have hb := td0_borrow_hook_effect s who m1 hbHook
  have hs := td0_supply_hook_effect m1 who m2 hsHook
  have hGrant' : s' = grant m2 who := hGrant.trans (plan16_grant_eq m2 who)
  exact plan16_claimed_intro s who m1 m2 s' hb hs hGrant'


theorem plan11_setSupply_spec (s : St) (a : Nat) (t : St) :
    setSupplySpeed s a = some t →
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState := if s.supplyState.speed = a then s.supplyState
          else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  sorry

theorem plan11_setBorrow_spec (s : St) (b : Nat) (t : St) :
    setBorrowSpeed s b = some t →
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState := if s.borrowState.speed = b then s.borrowState
          else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  sorry

theorem plan11_setSupply_preserves (s : St) (a : Nat) (t : St) :
    setSupplySpeed s a = some t →
    t.borrowState = s.borrowState ∧ t.blockNumber = s.blockNumber ∧ t.accts = s.accts := by
  sorry

theorem plan11_combine (s s1 s' : St) (a b : Nat) :
    s1 = { s with supplyState := if s.supplyState.speed = a then s.supplyState
           else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } →
    s' = { s1 with borrowState := if s1.borrowState.speed = b then s1.borrowState
           else { accrueSide s1.borrowState s1.blockNumber (totalBorrows s1) with speed := b } } →
    s1.borrowState = s.borrowState →
    s1.blockNumber = s.blockNumber →
    s1.accts = s.accts →
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  sorry

theorem td0_set_speeds_effect : ∀ (s : St) (a b : Nat) (s' : St),
    comptroller s (.setSpeeds a b) = some s' → SpeedsSet s a b s' := by
  intro s a b s' h
  have h1 : setCompSpeedInternal s a b = some s' := h
  unfold setCompSpeedInternal at h1
  cases hss : setSupplySpeed s a with
  | none =>
      simp [hss] at h1
  | some s1 =>
      have h2 : setBorrowSpeed s1 b = some s' := by
        simpa [hss] using h1
      obtain ⟨hsupBlock, hsupEq⟩ := plan11_setSupply_spec s a s1 hss
      obtain ⟨hborBlock0, hborEq⟩ := plan11_setBorrow_spec s1 b s' h2
      obtain ⟨hborState, hblk, haccts⟩ := plan11_setSupply_preserves s a s1 hss
      unfold SpeedsSet
      refine ⟨?_, ?_, ?_⟩
      · exact hsupBlock
      · intro hbne
        have hb1 : s1.borrowState.speed ≠ b := by
          rw [hborState]
          exact hbne
        have hb2 := hborBlock0 hb1
        rw [hborState, hblk] at hb2
        exact hb2
      · exact plan11_combine s s1 s' a b hsupEq hborEq hborState hblk haccts


theorem plan1_accrueSide_props (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index ∧
    (accrueSide sd now total).block = now ∧
    (accrueSide sd now total).speed = sd.speed := by
  sorry

theorem plan1_modify_mem_pred {l : List Acct} {who : Nat} {f : Acct → Acct}
    {P : Acct → Prop}
    (hP : ∀ a ∈ l, P a) (hf : ∀ a ∈ l, P (f a)) {a : Acct}
    (ha : a ∈ l.modify who f) : P a := by
  sorry

theorem plan0_supply_inv (sp : Nat × Nat) (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' → td0_Inv sp s → td0_Inv sp s' := by
  intro hCall hInv
  obtain ⟨_hBlk, _hStart, rfl⟩ := td0_supply_hook_effect s who s' hCall
  obtain ⟨hCons, hSupSpd, hBorSpd⟩ := hInv
  obtain ⟨_hSupBlk, hBorBlk, hAll⟩ := hCons
  obtain ⟨hIdxGe, hNewBlk, hNewSpd⟩ :=
    plan1_accrueSide_props s.supplyState s.blockNumber (totalSupply s)
  unfold td0_Inv Consistent
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block ≤ s.blockNumber
    rw [hNewBlk]
    exact Nat.le_refl _
  · exact hBorBlk
  · intro a ha
    apply plan1_modify_mem_pred _ _ ha
    · intro b hb
      exact ⟨Nat.le_trans (hAll b hb).1 hIdxGe, (hAll b hb).2⟩
    · intro b hb
      exact ⟨Nat.le_refl _, (hAll b hb).2⟩
  · show (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed = sp.1
    rw [hNewSpd]
    exact hSupSpd
  · exact hBorSpd


theorem plan0_borrow_inv (sp : Nat × Nat) (s : St) (who : Account) (s' : St) :
    comptroller s (.borrowHook who) = some s' → td0_Inv sp s → td0_Inv sp s' := by
  sorry

theorem plan0_claim_inv (sp : Nat × Nat) (s : St) (who : Account) (s' : St) :
    comptroller s (.claim who) = some s' → td0_Inv sp s → td0_Inv sp s' := by
  sorry

theorem plan0_setSpeeds_inv (s : St) (a b : Nat) (s' : St) :
    comptroller s (.setSpeeds a b) = some s' → Consistent s → td0_Inv (a, b) s' := by
  sorry

theorem plan0_withAcct_inv (sp : Nat × Nat) (s : St) (who : Account) (f : Acct → Acct) :
    td0_Inv sp s →
    (∀ a, (f a).supplierIndex = a.supplierIndex ∧ (f a).borrowerIndex = a.borrowerIndex) →
    td0_Inv sp (s.withAcct who f) := by
  sorry

theorem plan0_env_inv (sp : Nat × Nat) (s : St) (k x : Nat) :
    td0_Inv sp s →
    td0_Inv sp { s with blockNumber := s.blockNumber + k } ∧
    td0_Inv sp { s with reserve := s.reserve + x } := by
  intro h
  unfold td0_Inv Consistent at *
  obtain ⟨⟨hsup, hbor, haccts⟩, hsp1, hsp2⟩ := h
  constructor
  · refine ⟨⟨?_, ?_, ?_⟩, hsp1, hsp2⟩ <;> simp_all <;> omega
  · refine ⟨⟨?_, ?_, ?_⟩, hsp1, hsp2⟩ <;> simp_all


theorem td0_exec_inv : ∀ (sp : Nat × Nat) (s : St) (op : Op), td0_Inv sp s →
    td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by
  intro sp s op h
  cases op with
  | mint who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.supplyHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.supplyHook who) = some t := by
        cases hc : comptroller s (.supplyHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_supply_inv sp s who s' hs' h
      have heq : exec comptroller s (Op.mint who x) =
          s'.withAcct who (fun a => { a with supply := a.supply + x }) := by
        simp [exec, hlen, hs']
      rw [heq]
      exact plan0_withAcct_inv sp s' who
        (fun a => { a with supply := a.supply + x }) hinv (fun a => ⟨rfl, rfl⟩)
    · have heq : exec comptroller s (Op.mint who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | redeem who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.supplyHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.supplyHook who) = some t := by
        cases hc : comptroller s (.supplyHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_supply_inv sp s who s' hs' h
      by_cases hle : x ≤ (s'.acct who).supply
      · have heq : exec comptroller s (Op.redeem who x) =
            s'.withAcct who (fun a => { a with supply := a.supply - x }) := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact plan0_withAcct_inv sp s' who
          (fun a => { a with supply := a.supply - x }) hinv (fun a => ⟨rfl, rfl⟩)
      · have heq : exec comptroller s (Op.redeem who x) = s := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact h
    · have heq : exec comptroller s (Op.redeem who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | transfer src dst x =>
    by_cases hcond : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · have hsome := td0_calls_some s (.supplyHook src) h.1
      obtain ⟨s1, hs1⟩ : ∃ t, comptroller s (.supplyHook src) = some t := by
        cases hc : comptroller s (.supplyHook src) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv1 := plan0_supply_inv sp s src s1 hs1 h
      have hsome2 := td0_calls_some s1 (.supplyHook dst) hinv1.1
      obtain ⟨s2, hs2⟩ : ∃ t, comptroller s1 (.supplyHook dst) = some t := by
        cases hc : comptroller s1 (.supplyHook dst) with
        | none => simp [hc] at hsome2
        | some t => exact ⟨t, rfl⟩
      have hinv2 := plan0_supply_inv sp s1 dst s2 hs2 hinv1
      by_cases hle : x ≤ (s2.acct src).supply
      · have heq : exec comptroller s (Op.transfer src dst x) =
            (s2.withAcct src (fun a => { a with supply := a.supply - x })).withAcct dst
              (fun a => { a with supply := a.supply + x }) := by
          simp [exec, hcond, hs1, hs2, hle]
        rw [heq]
        have hinvSrc : td0_Inv sp
            (s2.withAcct src (fun a => { a with supply := a.supply - x })) :=
          plan0_withAcct_inv sp s2 src
            (fun a => { a with supply := a.supply - x }) hinv2 (fun a => ⟨rfl, rfl⟩)
        exact plan0_withAcct_inv sp
          (s2.withAcct src (fun a => { a with supply := a.supply - x })) dst
          (fun a => { a with supply := a.supply + x }) hinvSrc (fun a => ⟨rfl, rfl⟩)
      · have heq : exec comptroller s (Op.transfer src dst x) = s := by
          simp [exec, hcond, hs1, hs2, hle]
        rw [heq]
        exact h
    · have heq : exec comptroller s (Op.transfer src dst x) = s := by
        simp [exec, hcond]
      rw [heq]
      exact h
  | borrow who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.borrowHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.borrowHook who) = some t := by
        cases hc : comptroller s (.borrowHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_borrow_inv sp s who s' hs' h
      have heq : exec comptroller s (Op.borrow who x) =
          s'.withAcct who (fun a => { a with borrow := a.borrow + x }) := by
        simp [exec, hlen, hs']
      rw [heq]
      exact plan0_withAcct_inv sp s' who
        (fun a => { a with borrow := a.borrow + x }) hinv (fun a => ⟨rfl, rfl⟩)
    · have heq : exec comptroller s (Op.borrow who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | repay who x =>
    by_cases hlen : who < s.accts.length
    · have hsome := td0_calls_some s (.borrowHook who) h.1
      obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.borrowHook who) = some t := by
        cases hc : comptroller s (.borrowHook who) with
        | none => simp [hc] at hsome
        | some t => exact ⟨t, rfl⟩
      have hinv := plan0_borrow_inv sp s who s' hs' h
      by_cases hle : x ≤ (s'.acct who).borrow
      · have heq : exec comptroller s (Op.repay who x) =
            s'.withAcct who (fun a => { a with borrow := a.borrow - x }) := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact plan0_withAcct_inv sp s' who
          (fun a => { a with borrow := a.borrow - x }) hinv (fun a => ⟨rfl, rfl⟩)
      · have heq : exec comptroller s (Op.repay who x) = s := by
          simp [exec, hlen, hs', hle]
        rw [heq]
        exact h
    · have heq : exec comptroller s (Op.repay who x) = s := by
        simp [exec, hlen]
      rw [heq]
      exact h
  | claim who =>
    have hsome := td0_calls_some s (.claim who) h.1
    obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.claim who) = some t := by
      cases hc : comptroller s (.claim who) with
      | none => simp [hc] at hsome
      | some t => exact ⟨t, rfl⟩
    have heq : exec comptroller s (Op.claim who) = s' := by
      simp [exec, hs']
    rw [heq]
    exact plan0_claim_inv sp s who s' hs' h
  | setSpeeds a b =>
    have hsome := td0_calls_some s (.setSpeeds a b) h.1
    obtain ⟨s', hs'⟩ : ∃ t, comptroller s (.setSpeeds a b) = some t := by
      cases hc : comptroller s (.setSpeeds a b) with
      | none => simp [hc] at hsome
      | some t => exact ⟨t, rfl⟩
    have heq : exec comptroller s (Op.setSpeeds a b) = s' := by
      simp [exec, hs']
    rw [heq]
    exact plan0_setSpeeds_inv s a b s' hs' h.1
  | advance k =>
    exact (plan0_env_inv sp s k 0 h).1
  | drip x =>
    exact (plan0_env_inv sp s 0 x h).2


theorem td0_exec_potential_le : ∀ (sp : Nat × Nat) (s : St) (op : Op), td0_Inv sp s →
    td0_potential (exec comptroller s op) ≤
      td0_potential s + doubleScale * emittedBy sp op := by
  sorry

theorem plan3_supply_hook_potentialTo_le (sp : Nat × Nat) (s : St)
    (a who : Account) (s' : St) :
    td0_Inv sp s →
    comptroller s (.supplyHook a) = some s' →
    td0_potentialTo s' who ≤ td0_potentialTo s who := by
  sorry

theorem plan3_supply_hook_synced (s : St) (a : Account) (s' : St)
    (ha : a < s.accts.length) :
    comptroller s (.supplyHook a) = some s' →
    (s'.acct a).supplierIndex = s'.supplyState.index ∧
      s'.supplyState.block = s'.blockNumber := by
  sorry

theorem plan3_add_supply_potentialTo_le (s : St) (a who x : Nat) :
    (s.acct a).supplierIndex = s.supplyState.index →
    s.supplyState.block = s.blockNumber →
    td0_potentialTo
        (s.withAcct a fun acct => { acct with supply := acct.supply + x }) who ≤
      td0_potentialTo s who := by
  sorry

theorem plan3_sub_supply_potentialTo_le (s : St) (a who x : Nat) :
    (s.acct a).supplierIndex = s.supplyState.index →
    s.supplyState.block = s.blockNumber →
    td0_potentialTo
        (s.withAcct a fun acct => { acct with supply := acct.supply - x }) who ≤
      td0_potentialTo s who := by
  sorry

theorem plan3_transfer_move_potentialTo_le (s s1 s2 : St)
    (src dst who x : Nat) :
    src < s.accts.length →
    dst < s.accts.length →
    comptroller s (.supplyHook src) = some s1 →
    comptroller s1 (.supplyHook dst) = some s2 →
    td0_potentialTo
        ((s2.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst
          fun a => { a with supply := a.supply + x }) who ≤
      td0_potentialTo s2 who := by
  sorry

theorem plan2_potentialTo_supply_ops (sp : Nat × Nat) (s : St) (who : Account) :
    td0_Inv sp s →
    (∀ a x, td0_potentialTo (exec comptroller s (.mint a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.mint a x)) ∧
    (∀ a x, td0_potentialTo (exec comptroller s (.redeem a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.redeem a x)) ∧
    (∀ src dst x, td0_potentialTo (exec comptroller s (.transfer src dst x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.transfer src dst x)) := by
  intro hInv
  refine ⟨?_, ?_, ?_⟩
  · intro a x
    simp only [emittedBy, Nat.mul_zero, Nat.add_zero]
    by_cases ha : a < s.accts.length
    · cases hcall : comptroller s (.supplyHook a) with
      | none =>
          have key : exec comptroller s (.mint a x) = s := by
            simp [exec, ha, hcall]
          rw [key]
          exact Nat.le_refl _
      | some s' =>
          have key : exec comptroller s (.mint a x) =
              s'.withAcct a fun acct => { acct with supply := acct.supply + x } := by
            simp [exec, ha, hcall]
          rw [key]
          exact Nat.le_trans
            (plan3_add_supply_potentialTo_le s' a who x
              (plan3_supply_hook_synced s a s' ha hcall).1
              (plan3_supply_hook_synced s a s' ha hcall).2)
            (plan3_supply_hook_potentialTo_le sp s a who s' hInv hcall)
    · have key : exec comptroller s (.mint a x) = s := by
        simp [exec, ha]
      rw [key]
      exact Nat.le_refl _
  · intro a x
    simp only [emittedBy, Nat.mul_zero, Nat.add_zero]
    by_cases ha : a < s.accts.length
    · cases hcall : comptroller s (.supplyHook a) with
      | none =>
          have key : exec comptroller s (.redeem a x) = s := by
            simp [exec, ha, hcall]
          rw [key]
          exact Nat.le_refl _
      | some s' =>
          by_cases hx : x ≤ (s'.acct a).supply
          · have key : exec comptroller s (.redeem a x) =
                s'.withAcct a fun acct => { acct with supply := acct.supply - x } := by
              simp [exec, ha, hcall, hx]
            rw [key]
            exact Nat.le_trans
              (plan3_sub_supply_potentialTo_le s' a who x
                (plan3_supply_hook_synced s a s' ha hcall).1
                (plan3_supply_hook_synced s a s' ha hcall).2)
              (plan3_supply_hook_potentialTo_le sp s a who s' hInv hcall)
          · have key : exec comptroller s (.redeem a x) = s := by
              simp [exec, ha, hcall, hx]
            rw [key]
            exact Nat.le_refl _
    · have key : exec comptroller s (.redeem a x) = s := by
        simp [exec, ha]
      rw [key]
      exact Nat.le_refl _
  · intro src dst x
    simp only [emittedBy, Nat.mul_zero, Nat.add_zero]
    by_cases hg : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · cases hcall1 : comptroller s (.supplyHook src) with
      | none =>
          have key : exec comptroller s (.transfer src dst x) = s := by
            simp [exec, hg, hcall1]
          rw [key]
          exact Nat.le_refl _
      | some s1 =>
          have hInv1 : td0_Inv sp s1 :=
            plan0_supply_inv sp s src s1 hcall1 hInv
          cases hcall2 : comptroller s1 (.supplyHook dst) with
          | none =>
              have key : exec comptroller s (.transfer src dst x) = s := by
                simp [exec, hg, hcall1, hcall2]
              rw [key]
              exact Nat.le_refl _
          | some s2 =>
              by_cases hx : x ≤ (s2.acct src).supply
              · have key : exec comptroller s (.transfer src dst x) =
                    (s2.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst
                      fun a => { a with supply := a.supply + x } := by
                  simp [exec, hg, hcall1, hcall2, hx]
                rw [key]
                exact Nat.le_trans
                  (plan3_transfer_move_potentialTo_le s s1 s2 src dst who x
                    hg.1 hg.2.1 hcall1 hcall2)
                  (Nat.le_trans
                    (plan3_supply_hook_potentialTo_le sp s1 dst who s2 hInv1 hcall2)
                    (plan3_supply_hook_potentialTo_le sp s src who s1 hInv hcall1))
              · have key : exec comptroller s (.transfer src dst x) = s := by
                  simp [exec, hg, hcall1, hcall2, hx]
                rw [key]
                exact Nat.le_refl _
    · have key : exec comptroller s (.transfer src dst x) = s := by
        simp [exec, hg]
      rw [key]
      exact Nat.le_refl _


theorem plan2_potentialTo_borrow_ops (sp : Nat × Nat) (s : St) (who : Account) :
    td0_Inv sp s →
    (∀ a x, td0_potentialTo (exec comptroller s (.borrow a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.borrow a x)) ∧
    (∀ a x, td0_potentialTo (exec comptroller s (.repay a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.repay a x)) := by
  sorry

theorem plan2_potentialTo_claim (sp : Nat × Nat) (s : St) (a who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.claim a)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.claim a) := by
  sorry

theorem plan2_potentialTo_setSpeeds (sp : Nat × Nat) (s : St) (a b : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.setSpeeds a b)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.setSpeeds a b) := by
  sorry

theorem plan2_potentialTo_advance (sp : Nat × Nat) (s : St) (k : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.advance k)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.advance k) := by
  intro hInv
  obtain ⟨hCons, hSup, hBor⟩ := hInv
  have hSB : s.supplyState.block ≤ s.blockNumber := hCons.1
  have hBB : s.borrowState.block ≤ s.blockNumber := hCons.2.1
  have hexec : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } := by
    simp [exec]
  have hemit : emittedBy sp (.advance k) = k * (sp.1 + sp.2) := by simp [emittedBy]
  rw [hexec, hemit]
  have hsup_eq : s.supplyState.speed = sp.1 := hSup
  have hbor_eq : s.borrowState.speed = sp.2 := hBor
  have hSB' : s.blockNumber + k - s.supplyState.block = (s.blockNumber - s.supplyState.block) + k := by
    omega
  have hBB' : s.blockNumber + k - s.borrowState.block = (s.blockNumber - s.borrowState.block) + k := by
    omega
  have h1 : ((s.blockNumber - s.supplyState.block) + k) * sp.1 =
      (s.blockNumber - s.supplyState.block) * sp.1 + k * sp.1 := Nat.add_mul _ _ _
  have h2 : ((s.blockNumber - s.borrowState.block) + k) * sp.2 =
      (s.blockNumber - s.borrowState.block) * sp.2 + k * sp.2 := Nat.add_mul _ _ _
  have hdist : k * (sp.1 + sp.2) = k * sp.1 + k * sp.2 := Nat.mul_add k sp.1 sp.2
  unfold td0_potentialTo td0_pendingTo td0_unindexedTo St.creditedTo td0_pendingAcct St.acct
  simp only []
  rw [hSB', hBB', hsup_eq, hbor_eq, h1, h2]
  by_cases hs : 0 < (s.accts.getD who noAcct).supply
  · by_cases hb : 0 < (s.accts.getD who noAcct).borrow
    · simp only [hs, hb, ↓reduceIte]
      have e1 : doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 + k * sp.1 +
          ((s.blockNumber - s.borrowState.block) * sp.2 + k * sp.2)) =
        doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 +
          (s.blockNumber - s.borrowState.block) * sp.2) +
        (doubleScale * (k * sp.1) + doubleScale * (k * sp.2)) := by
        simp only [Nat.mul_add]
        ac_rfl
      have e2 : doubleScale * (k * (sp.1 + sp.2)) =
        doubleScale * (k * sp.1) + doubleScale * (k * sp.2) := by
        rw [hdist, Nat.mul_add]
      rw [e1, e2]
      omega
    · simp only [hs, show ¬ (0 < (s.accts.getD who noAcct).borrow) from hb, ↓reduceIte]
      have e1 : doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 + k * sp.1 + 0) =
        doubleScale * ((s.blockNumber - s.supplyState.block) * sp.1 + 0) +
        doubleScale * (k * sp.1) := by
        simp only [Nat.mul_add]
        ac_rfl
      have e2 : doubleScale * (k * (sp.1 + sp.2)) =
        doubleScale * (k * sp.1) + doubleScale * (k * sp.2) := by
        rw [hdist, Nat.mul_add]
      rw [e1, e2]
      omega
  · by_cases hb : 0 < (s.accts.getD who noAcct).borrow
    · simp only [show ¬ (0 < (s.accts.getD who noAcct).supply) from hs, hb, ↓reduceIte]
      have e1 : doubleScale * (0 + ((s.blockNumber - s.borrowState.block) * sp.2 + k * sp.2)) =
        doubleScale * (0 + (s.blockNumber - s.borrowState.block) * sp.2) +
        doubleScale * (k * sp.2) := by
        simp only [Nat.mul_add]
        ac_rfl
      have e2 : doubleScale * (k * (sp.1 + sp.2)) =
        doubleScale * (k * sp.1) + doubleScale * (k * sp.2) := by
        rw [hdist, Nat.mul_add]
      rw [e1, e2]
      omega
    · simp only [show ¬ (0 < (s.accts.getD who noAcct).supply) from hs,
        show ¬ (0 < (s.accts.getD who noAcct).borrow) from hb, ↓reduceIte]
      omega


theorem plan2_potentialTo_drip (sp : Nat × Nat) (s : St) (x : Nat)
    (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s (.drip x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.drip x) := by
  intro _
  have h1 : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := by
    simp [exec]
  have h2 : emittedBy sp (.drip x) = 0 := by simp [emittedBy]
  rw [h1, h2, Nat.mul_zero, Nat.add_zero]
  unfold td0_potentialTo td0_pendingTo td0_unindexedTo St.creditedTo td0_pendingAcct St.acct
  simp


theorem td0_exec_potentialTo_le : ∀ (sp : Nat × Nat) (s : St) (op : Op) (who : Account),
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s op) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp op := by
  intro sp s op who h
  cases op with
  | mint a x =>
      exact (plan2_potentialTo_supply_ops sp s who h).1 a x
  | redeem a x =>
      exact (plan2_potentialTo_supply_ops sp s who h).2.1 a x
  | transfer src dst x =>
      exact (plan2_potentialTo_supply_ops sp s who h).2.2 src dst x
  | borrow a x =>
      exact (plan2_potentialTo_borrow_ops sp s who h).1 a x
  | repay a x =>
      exact (plan2_potentialTo_borrow_ops sp s who h).2 a x
  | claim a =>
      exact plan2_potentialTo_claim sp s a who h
  | setSpeeds a b =>
      exact plan2_potentialTo_setSpeeds sp s a b who h
  | advance k =>
      exact plan2_potentialTo_advance sp s k who h
  | drip x =>
      exact plan2_potentialTo_drip sp s x who h


theorem td0_run_inv : ∀ (ops : List Op) (sp : Nat × Nat) (s : St), td0_Inv sp s →
    td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by
  intro ops
  induction ops with
  | nil =>
      intro sp s h
      exact h
  | cons op ops ih =>
      intro sp s h
      exact ih (nextSpeeds sp op) (exec comptroller s op) (td0_exec_inv sp s op h)

theorem td0_run_potential : ∀ (ops : List Op) (sp : Nat × Nat) (s : St), td0_Inv sp s →
    td0_potential (run comptroller s ops) ≤
      td0_potential s + doubleScale * emitted sp ops := by
  intro ops
  induction ops with
  | nil =>
      intro sp s h
      exact Nat.le_refl _
  | cons op ops ih =>
      intro sp s h
      have hstep := td0_exec_potential_le sp s op h
      have hinv := td0_exec_inv sp s op h
      have hrec := ih (nextSpeeds sp op) (exec comptroller s op) hinv
      have hsum := Nat.add_le_add hstep
        (Nat.le_refl (doubleScale * emitted (nextSpeeds sp op) ops))
      have htrans := Nat.le_trans hrec hsum
      have hem : emitted sp (op :: ops) =
          emittedBy sp op + emitted (nextSpeeds sp op) ops := rfl
      rw [hem, Nat.mul_add, ← Nat.add_assoc]
      exact htrans

theorem td0_run_potentialTo : ∀ (ops : List Op) (sp : Nat × Nat) (s : St) (who : Account),
    td0_Inv sp s →
    td0_potentialTo (run comptroller s ops) who ≤
      td0_potentialTo s who + doubleScale * emitted sp ops := by
  intro ops
  induction ops with
  | nil =>
      intro sp s who h
      exact Nat.le_refl _
  | cons op ops ih =>
      intro sp s who h
      have hstep := td0_exec_potentialTo_le sp s op who h
      have hinv := td0_exec_inv sp s op h
      have hrec := ih (nextSpeeds sp op) (exec comptroller s op) who hinv
      have hsum := Nat.add_le_add hstep
        (Nat.le_refl (doubleScale * emitted (nextSpeeds sp op) ops))
      have htrans := Nat.le_trans hrec hsum
      have hem : emitted sp (op :: ops) =
          emittedBy sp op + emitted (nextSpeeds sp op) ops := rfl
      rw [hem, Nat.mul_add, ← Nat.add_assoc]
      exact htrans



theorem plan10_upgrade_supply_index (L : Legacy) :
    (upgrade L).supplyState.index =
      if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]


theorem plan10_accrualStart_zero (st idx : Nat) :
    accrualStart 0 idx =
        (if compInitialIndex ≤ idx then compInitialIndex else 0) ∧
      legacyStart st 0 = st := by
  constructor
  · unfold accrualStart; simp
  · unfold legacyStart; simp


theorem plan10_accrualStart_pos {r : Nat} (hr : r ≠ 0) (st idx : Nat) :
    accrualStart r idx = r ∧ legacyStart st r = r := by
  unfold accrualStart legacyStart
  simp [hr]


theorem plan10_mul_le_mono (n x y : Nat) (h : x ≤ y) :
    n * x ≤ n * y := by exact Nat.mul_le_mul_left n h


theorem plan9_supply_pending_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  have hU := plan10_upgrade_supply_index L
  apply plan10_mul_le_mono
  by_cases hr : a.supplierIndex = 0
  · have hz :=
      plan10_accrualStart_zero L.supplyStart (upgrade L).supplyState.index
    rw [hr, hz.1, hz.2, hU]
    by_cases hi : L.supplyIndex = 0
    · rw [if_pos hi, if_pos (Nat.le_refl compInitialIndex)]
      cases hstart with
      | inl hst => rw [hst]; omega
      | inr hst => rw [hst]; omega
    · rw [if_neg hi]
      by_cases hc : compInitialIndex ≤ L.supplyIndex
      · rw [if_pos hc]
        cases hstart with
        | inl hst => rw [hst]; omega
        | inr hst => rw [hst]; omega
      · rw [if_neg hc]
        cases hstart with
        | inl hst => rw [hst]; omega
        | inr hst => rw [hst]; omega
  · have hp :=
      plan10_accrualStart_pos hr L.supplyStart (upgrade L).supplyState.index
    rw [hp.1, hp.2, hU]
    by_cases hi : L.supplyIndex = 0
    · rw [if_pos hi]; omega
    · rw [if_neg hi]; omega


theorem plan9_borrow_pending_le (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hstartle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
  sorry

theorem plan9_pending_sum_le (L : Legacy)
    (h : ∀ a ∈ L.accts, td0_pendingAcct (upgrade L) a ≤ L.pendingScaled a) :
    td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
  sorry

theorem plan9_supply_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed ≤
      L.unindexedSupply := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hsup : (upgrade L).supplyState = initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ := rfl
  rw [hbn, hsup]
  by_cases hidx : L.supplyIndex = 0
  · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.blockNumber := by
      unfold initSide
      simp only [hidx, if_true]
    rw [hblock, Nat.sub_self, Nat.zero_mul]
    exact Nat.zero_le _
  · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.supplyBlock := by
      unfold initSide
      simp only [hidx, if_false]
    have hspeed : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).speed = L.compSpeed := by
      unfold initSide
      simp only [hidx, if_false]
    rw [hblock, hspeed]
    unfold Legacy.unindexedSupply
    exact Nat.le_refl _


theorem plan9_borrow_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed ≤
      L.unindexedBorrow := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hbor : (upgrade L).borrowState = initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ := rfl
  rw [hbn, hbor]
  by_cases hidx : L.borrowIndex = 0
  · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.blockNumber := by
      unfold initSide
      simp only [hidx, if_true]
    rw [hblock, Nat.sub_self, Nat.zero_mul]
    exact Nat.zero_le _
  · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.borrowBlock := by
      unfold initSide
      simp only [hidx, if_false]
    have hspeed : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).speed = L.compSpeed := by
      unfold initSide
      simp only [hidx, if_false]
    rw [hblock, hspeed]
    unfold Legacy.unindexedBorrow
    exact Nat.le_refl _


theorem plan9_combine (L : Legacy)
    (hp : td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum)
    (hu : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow) :
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  show doubleScale * (upgrade L).credited + td0_pending (upgrade L) +
      doubleScale * td0_unindexed (upgrade L) ≤ _
  exact Nat.add_le_add (Nat.add_le_add_left hp _) (Nat.mul_le_mul_left _ hu)

theorem td0_upgrade_potential_le : ∀ (L : Legacy), L.WellFormed →
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  intro L hWF
  have hsStart := hWF.1
  have hsLe := hWF.2.1
  have hbStart := hWF.2.2.1
  have hbLe := hWF.2.2.2.1
  have hacct := hWF.2.2.2.2.2.2
  have hpoint : ∀ a ∈ L.accts, td0_pendingAcct (upgrade L) a ≤ L.pendingScaled a := by
    intro a ha
    have hbnd := hacct a ha
    have hs := plan9_supply_pending_le L a hsStart hsLe hbnd.1
    have hb := plan9_borrow_pending_le L a hbStart hbLe hbnd.2
    unfold td0_pendingAcct Legacy.pendingScaled
    exact Nat.add_le_add hs hb
  have hp := plan9_pending_sum_le L hpoint
  have hu : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by
    unfold td0_unindexed
    exact Nat.add_le_add (plan9_supply_unindexed_le L) (plan9_borrow_unindexed_le L)
  exact plan9_combine L hp hu


theorem plan7_getD_mem_or_default (l : List Acct) (who : Nat) :
    l.getD who noAcct ∈ l ∨ l.getD who noAcct = noAcct := by
  induction l generalizing who with
  | nil =>
    simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      exact Or.inl (List.Mem.head _)
    | succ n =>
      simp only [List.getD_cons_succ]
      rcases ih n with h | h
      · exact Or.inl (List.Mem.tail _ h)
      · exact Or.inr h


theorem plan7_wellformed_apply (L : Legacy) (a : Acct)
    (hWF : L.WellFormed) (ha : a ∈ L.accts) :
    a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex := by
  unfold Legacy.WellFormed at hWF
  exact hWF.2.2.2.2.2.2 _ ha


theorem plan7_noAcct_supplierIndex : noAcct.supplierIndex = 0 := rfl

theorem plan7_noAcct_borrowerIndex : noAcct.borrowerIndex = 0 := rfl

theorem plan6_acct_bounds (L : Legacy) (who : Account) (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  cases plan7_getD_mem_or_default L.accts who with
  | inl hmem =>
    exact plan7_wellformed_apply L (L.accts.getD who noAcct) hWF hmem
  | inr heq =>
    rw [heq]
    exact ⟨by rw [plan7_noAcct_supplierIndex]; exact Nat.zero_le _,
           by rw [plan7_noAcct_borrowerIndex]; exact Nat.zero_le _⟩


theorem plan8_upgrade_supply_index (L : Legacy) :
    (upgrade L).supplyState.index =
      if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  sorry

theorem plan8_start_zero (st idx : Nat) :
    accrualStart 0 idx =
        (if compInitialIndex ≤ idx then compInitialIndex else 0) ∧
      legacyStart st 0 = st := by
  sorry

theorem plan8_start_pos {r : Nat} (hr : r ≠ 0) (st idx : Nat) :
    accrualStart r idx = r ∧ legacyStart st r = r := by
  sorry

theorem plan8_compInitialIndex_pos : 0 < compInitialIndex := by
  sorry

theorem plan8_mul_le_mono (n x y : Nat) (h : x ≤ y) :
    n * x ≤ n * y := by
  sorry

theorem plan6_supply_pending_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  apply plan8_mul_le_mono
  have hU := plan8_upgrade_supply_index L
  have hpos := plan8_compInitialIndex_pos
  by_cases hr : a.supplierIndex = 0
  · obtain ⟨hacc, hleg⟩ :=
      plan8_start_zero L.supplyStart ((upgrade L).supplyState.index)
    rw [hr, hacc, hleg, hU]
    by_cases hI : L.supplyIndex = 0
    · simp [hI] <;> omega
    · by_cases hle : compInitialIndex ≤ L.supplyIndex
      · simp [hI, hle] <;> omega
      · simp [hI, hle] <;> omega
  · obtain ⟨hacc, hleg⟩ :=
      plan8_start_pos hr L.supplyStart ((upgrade L).supplyState.index)
    rw [hacc, hleg, hU]
    by_cases hI : L.supplyIndex = 0
    · simp [hI] <;> omega
    · simp [hI] <;> omega


theorem plan6_borrow_pending_le (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hstartle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
  sorry

theorem plan6_supply_unindexed_le (L : Legacy) (a : Acct) :
    (if 0 < a.supply then
       ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
         (upgrade L).supplyState.speed
     else 0) ≤
      (if 0 < a.supply then L.unindexedSupply else 0) := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hsup : (upgrade L).supplyState = initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ := rfl
  by_cases hpos : 0 < a.supply
  · have hifL : (if 0 < a.supply then ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed else 0)
      = ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed := by
      simp [hpos]
    have hifR : (if 0 < a.supply then L.unindexedSupply else 0) = L.unindexedSupply := by
      simp [hpos]
    rw [hifL, hifR, hbn, hsup]
    by_cases hidx : L.supplyIndex = 0
    · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.blockNumber := by
        unfold initSide
        simp only [hidx, if_true]
      rw [hblock, Nat.sub_self, Nat.zero_mul]
      exact Nat.zero_le _
    · have hblock : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).block = L.supplyBlock := by
        unfold initSide
        simp only [hidx, if_false]
      have hspeed : (initSide L.blockNumber ⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩).speed = L.compSpeed := by
        unfold initSide
        simp only [hidx, if_false]
      rw [hblock, hspeed]
      exact Nat.le_refl _
  · have hifL : (if 0 < a.supply then ((upgrade L).blockNumber - (upgrade L).supplyState.block) * (upgrade L).supplyState.speed else 0) = 0 := by
      simp [hpos]
    have hifR : (if 0 < a.supply then L.unindexedSupply else 0) = 0 := by
      simp [hpos]
    rw [hifL, hifR]
    exact Nat.le_refl _


theorem plan6_borrow_unindexed_le (L : Legacy) (a : Acct) :
    (if 0 < a.borrow then
       ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
         (upgrade L).borrowState.speed
     else 0) ≤
      (if 0 < a.borrow then L.unindexedBorrow else 0) := by
  have hbn : (upgrade L).blockNumber = L.blockNumber := rfl
  have hbor : (upgrade L).borrowState = initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ := rfl
  by_cases hpos : 0 < a.borrow
  · have hifL : (if 0 < a.borrow then ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed else 0)
      = ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed := by
      simp [hpos]
    have hifR : (if 0 < a.borrow then L.unindexedBorrow else 0) = L.unindexedBorrow := by
      simp [hpos]
    rw [hifL, hifR, hbn, hbor]
    by_cases hidx : L.borrowIndex = 0
    · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.blockNumber := by
        unfold initSide
        simp only [hidx, if_true]
      rw [hblock, Nat.sub_self, Nat.zero_mul]
      exact Nat.zero_le _
    · have hblock : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).block = L.borrowBlock := by
        unfold initSide
        simp only [hidx, if_false]
      have hspeed : (initSide L.blockNumber ⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩).speed = L.compSpeed := by
        unfold initSide
        simp only [hidx, if_false]
      rw [hblock, hspeed]
      exact Nat.le_refl _
  · have hifL : (if 0 < a.borrow then ((upgrade L).blockNumber - (upgrade L).borrowState.block) * (upgrade L).borrowState.speed else 0) = 0 := by
      simp [hpos]
    have hifR : (if 0 < a.borrow then L.unindexedBorrow else 0) = 0 := by
      simp [hpos]
    rw [hifL, hifR]
    exact Nat.le_refl _


theorem td0_upgrade_potentialTo_le : ∀ (L : Legacy) (who : Account), L.WellFormed →
    td0_potentialTo (upgrade L) who ≤
      doubleScale * (upgrade L).creditedTo who +
        L.pendingScaled (L.accts.getD who noAcct) +
        doubleScale * ((if 0 < (L.accts.getD who noAcct).supply
                        then L.unindexedSupply else 0) +
                       (if 0 < (L.accts.getD who noAcct).borrow
                        then L.unindexedBorrow else 0)) := by
  intro L who hWF
  obtain ⟨hsb, hbb⟩ := plan6_acct_bounds L who hWF
  have hsp := plan6_supply_pending_le L (L.accts.getD who noAcct)
    hWF.1 hWF.2.1 hsb
  have hbp := plan6_borrow_pending_le L (L.accts.getD who noAcct)
    hWF.2.2.1 hWF.2.2.2.1 hbb
  have hsu := plan6_supply_unindexed_le L (L.accts.getD who noAcct)
  have hbu := plan6_borrow_unindexed_le L (L.accts.getD who noAcct)
  have ha : (upgrade L).acct who = L.accts.getD who noAcct := rfl
  have hpend : td0_pendingTo (upgrade L) who ≤
      L.pendingScaled (L.accts.getD who noAcct) := by
    unfold td0_pendingTo td0_pendingAcct Legacy.pendingScaled
    rw [ha]
    exact Nat.add_le_add hsp hbp
  have hun : td0_unindexedTo (upgrade L) who ≤
      (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
      (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0) := by
    unfold td0_unindexedTo
    rw [ha]
    exact Nat.add_le_add hsu hbu
  unfold td0_potentialTo
  exact Nat.add_le_add (Nat.add_le_add_left hpend _)
    (Nat.mul_le_mul_left doubleScale hun)


theorem td0_potentialTo_of_noPosition : ∀ (s : St) (who : Account), NoPosition s who →
    td0_potentialTo s who = doubleScale * s.creditedTo who := by
  intro s who h
  unfold NoPosition at h
  unfold td0_potentialTo td0_pendingTo td0_unindexedTo td0_pendingAcct St.creditedTo
  obtain ⟨hsup, hbor⟩ := h
  have hsup' : (s.acct who).supply = 0 := hsup
  have hbor' : (s.acct who).borrow = 0 := hbor
  rw [hsup', hbor']
  simp


theorem plan4_credited_le_potential (s : St) :
    doubleScale * s.credited ≤ td0_potential s := by
  unfold td0_potential
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem plan4_owed_eq (L : Legacy) :
    L.owed = (L.accts.map L.pendingScaled).sum / doubleScale +
      (L.unindexedSupply + L.unindexedBorrow) := by
  unfold Legacy.owed
  rw [Nat.add_assoc]

theorem plan5_lt_div_mul_add (s : Nat) :
    s < doubleScale * (s / doubleScale) + doubleScale := by
  have hpos : 0 < doubleScale := by unfold doubleScale; exact Nat.pow_pos (by decide)
  have hmod : s % doubleScale < doubleScale := Nat.mod_lt _ hpos
  have hdiv : doubleScale * (s / doubleScale) + s % doubleScale = s := Nat.div_add_mod s doubleScale
  omega


theorem plan5_mul_target_succ (c0 s u e : Nat) :
    doubleScale * (c0 + (s / doubleScale + u) + e + 1) =
      doubleScale * c0 + doubleScale * (s / doubleScale) +
        doubleScale * u + doubleScale * e + doubleScale := by
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


theorem plan5_mul_mono (d a b : Nat) (h : a ≤ b) :
    d * a ≤ d * b := by
  exact Nat.mul_le_mul_left d h


theorem plan4_bound_of_scaled_le (c c0 s u e : Nat) :
    doubleScale * c ≤
        doubleScale * c0 + s + doubleScale * u + doubleScale * e →
    c ≤ c0 + (s / doubleScale + u) + e := by
  intro h
  have hlt := plan5_lt_div_mul_add s
  have hexp := plan5_mul_target_succ c0 s u e
  by_cases hc : c ≤ c0 + (s / doubleScale + u) + e
  · exact hc
  · exfalso
    have hsucc : c0 + (s / doubleScale + u) + e + 1 ≤ c := by omega
    have hmono := plan5_mul_mono doubleScale _ _ hsucc
    omega


theorem td0_rewards_conclude : ∀ (L : Legacy) (ops : List Op),
    td0_potential (run comptroller (upgrade L) ops) ≤
        td0_potential (upgrade L) + doubleScale * emitted (L.compSpeed, L.compSpeed) ops →
    td0_potential (upgrade L) ≤
        doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
          doubleScale * (L.unindexedSupply + L.unindexedBorrow) →
    (run comptroller (upgrade L) ops).credited ≤
      (upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops := by
  intro L ops h1 h2
  have hlow := plan4_credited_le_potential (run comptroller (upgrade L) ops)
  have htrans :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        td0_potential (upgrade L) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.le_trans hlow h1
  have hstep :
      td0_potential (upgrade L) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops ≤
        (doubleScale * (upgrade L).credited +
            (L.accts.map L.pendingScaled).sum +
            doubleScale * (L.unindexedSupply + L.unindexedBorrow)) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.add_le_add_right h2 _
  have hcomb :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        doubleScale * (upgrade L).credited +
          (L.accts.map L.pendingScaled).sum +
          doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.le_trans htrans hstep
  have hbound := plan4_bound_of_scaled_le _ _ _ _ _ hcomb
  rw [plan4_owed_eq L]
  exact hbound


theorem td0_account_conclude : ∀ (L : Legacy) (ops : List Op) (who : Account),
    td0_potentialTo (run comptroller (upgrade L) ops) who ≤
        td0_potentialTo (upgrade L) who +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops →
    td0_potentialTo (upgrade L) who ≤
        doubleScale * (upgrade L).creditedTo who +
          L.pendingScaled (L.accts.getD who noAcct) +
          doubleScale * ((if 0 < (L.accts.getD who noAcct).supply
                          then L.unindexedSupply else 0) +
                         (if 0 < (L.accts.getD who noAcct).borrow
                          then L.unindexedBorrow else 0)) →
    (run comptroller (upgrade L) ops).creditedTo who ≤
      (upgrade L).creditedTo who + L.owedTo who +
        emitted (L.compSpeed, L.compSpeed) ops := by
  sorry

theorem td0_no_backdated_conclude : ∀ (s : St) (sp : Nat × Nat) (ops : List Op)
    (who : Account),
    td0_potentialTo (run comptroller s ops) who ≤
        td0_potentialTo s who + doubleScale * emitted sp ops →
    td0_potentialTo s who = doubleScale * s.creditedTo who →
    (run comptroller s ops).creditedTo who ≤ s.creditedTo who + emitted sp ops := by
  intro s sp ops who hRun hInit
  have hLow : doubleScale * (run comptroller s ops).creditedTo who ≤
      td0_potentialTo (run comptroller s ops) who := by
    unfold td0_potentialTo
    omega
  rw [hInit] at hRun
  have hDS : 0 < doubleScale := by unfold doubleScale; omega
  have hComb : doubleScale * (run comptroller s ops).creditedTo who ≤
      doubleScale * (s.creditedTo who + emitted sp ops) := by
    calc doubleScale * (run comptroller s ops).creditedTo who
        ≤ td0_potentialTo (run comptroller s ops) who := hLow
      _ ≤ doubleScale * s.creditedTo who + doubleScale * emitted sp ops := hRun
      _ = doubleScale * (s.creditedTo who + emitted sp ops) := by rw [Nat.mul_add]
  exact Nat.le_of_mul_le_mul_left hComb hDS


theorem td0_upgrade_inv_aux : ∀ (L : Legacy), L.WellFormed →
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  intro L hW
  unfold td0_Inv upgrade Consistent initSide Legacy.WellFormed at *
  obtain ⟨hs0, hs_le, hb0, hb_le, hsblk, hbblk, haccts⟩ := hW
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · by_cases h : L.supplyIndex = 0 <;> simp [h] <;> omega
  · by_cases h : L.borrowIndex = 0 <;> simp [h] <;> omega
  · intro a ha
    have ha' := haccts a ha
    by_cases hs : L.supplyIndex = 0 <;> by_cases hb : L.borrowIndex = 0 <;> simp [hs, hb] <;> omega
  · by_cases h : L.supplyIndex = 0 <;> simp [h]
  · by_cases h : L.borrowIndex = 0 <;> simp [h]

theorem td0_upgrade_inv : ∀ (L : Legacy), L.WellFormed →
    td0_Inv (L.compSpeed, L.compSpeed) (upgrade L) := by
  intro L h
  exact td0_upgrade_inv_aux L h

def td0_check1 : 0 < doubleScale := by unfold doubleScale; omega
#check @Nat.le_of_mul_le_mul_left
#check @Nat.mul_left_cancel

def foo_test : Nat := 1

theorem aux_up_idx_supply (L : Legacy) :
    (upgrade L).supplyState.index = if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_blk_supply (L : Legacy) :
    (upgrade L).supplyState.block = if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_spd_supply2 (L : Legacy) :
    (upgrade L).supplyState.speed = L.compSpeed := by
  unfold upgrade initSide
  by_cases h : L.supplyIndex = 0 <;> simp [h]

theorem aux_up_accts2 (L : Legacy) : (upgrade L).accts = L.accts := by
  unfold upgrade; simp

theorem aux_sum_le_sum2 (f g : Acct → Nat) (l : List Acct) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp
    have hhd : f hd ≤ g hd := h hd (by simp)
    have htl : ∀ a ∈ tl, f a ≤ g a := fun a ha => h a (by simp [ha])
    have iht := ih htl
    omega

theorem my_test_thm : 1 + 1 = 2 := by rfl

theorem my_test2 : ∀ (s : St), s = s := by intro s; rfl

theorem td0_updSup_some2 (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex subChecked
  simp only [h, ite_true]
  split
  · simp
  · split
    · simp
    · simp

theorem td0_updSup_eq (s : St) :
    updateCompSupplyIndex s =
      match subChecked s.blockNumber s.supplyState.block with
      | none => none
      | some d =>
        if d > 0 ∧ s.supplyState.speed > 0 then
          let tot := totalSupply s
          let r := if tot > 0 then (d * s.supplyState.speed) * doubleScale / tot else 0
          some { s with supplyState :=
            { s.supplyState with index := s.supplyState.index + r, block := s.blockNumber } }
        else if d > 0 then
          some { s with supplyState := { s.supplyState with block := s.blockNumber } }
        else some s := by
  unfold updateCompSupplyIndex totalSupply fraction
  rfl

theorem td0_subChecked_eq (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]

def check_modify : Nat := 1
#check @List.modify
#check @List.getD

theorem tmp_check_modify (l : List Acct) (n : Nat) (f : Acct → Acct) :
    (l.modify n f).length = l.length := by
  simp

theorem chkLen (l : List Acct) (n : Nat) (f : Acct → Acct) : (l.modify n f).length = l.length := by simp

def dummyY : Nat := 2

theorem plan2_potentialTo_claim_aux_test (sp : Nat × Nat) (s : St) (a who : Account) (hInv : td0_Inv sp s) :
    emittedBy sp (.claim a) = 0 := by simp [emittedBy]

theorem chk_omega_test (a b : Nat) (h : ¬ a ≤ b) : b < a := by
  omega
#check @Nat.mul_le_mul_left
#check @Nat.le_of_mul_le_mul_left
#check @Nat.div_add_mod
#check @Nat.mod_lt
#check @Nat.succ_le_of_lt
#check @Classical.byContradiction

theorem plan5_test_aux (s : Nat) : s < doubleScale * (s / doubleScale) + doubleScale := by
  have hpos : 0 < doubleScale := by unfold doubleScale; exact Nat.pow_pos (by decide)
  have hmod : s % doubleScale < doubleScale := Nat.mod_lt _ hpos
  have hdiv : doubleScale * (s / doubleScale) + s % doubleScale = s := Nat.div_add_mod s doubleScale
  omega

theorem tmp_getD_unfold_test (l : List Acct) (n : Nat) : l.getD n noAcct = (l[n]?).getD noAcct := by rfl

theorem tmp_hUp_test (L : Legacy) :
    (upgrade L).borrowState.index = if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex := by
  unfold upgrade initSide
  simp only
  split
  · rfl
  · rfl

theorem tmp_pos_test : 0 < compInitialIndex := by
  unfold compInitialIndex
  omega

theorem plan7_tmp_proof (l : List Acct) (who : Nat) :
    l.getD who noAcct ∈ l ∨ l.getD who noAcct = noAcct := by
  induction l generalizing who with
  | nil =>
    simp
  | cons hd tl ih =>
    cases who with
    | zero =>
      exact Or.inl (List.Mem.head _)
    | succ n =>
      simp only [List.getD_cons_succ]
      rcases ih n with h | h
      · exact Or.inl (List.Mem.tail _ h)
      · exact Or.inr h

theorem plan9_supply_pending_le_proof2 (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) :=
  plan6_supply_pending_le L a hstart hstartle ha

theorem snippet_test_by_cases (s : St) : s.supplyState.block ≤ s.blockNumber ∨ ¬ s.supplyState.block ≤ s.blockNumber := by
  by_cases h : s.supplyState.block ≤ s.blockNumber
  · exact Or.inl h
  · exact Or.inr h

theorem plan13_update_borrow_spec_aux1 (s : St) :
    accrueSide s.borrowState s.blockNumber (totalBorrows s) =
    if 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s then
      { s.borrowState with index := s.borrowState.index + (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale / totalBorrows s, block := s.blockNumber }
    else { s.borrowState with block := s.blockNumber } := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem plan13_distribute_borrow_spec_aux_check :
    ∀ (t : St) (who : Account),
    (if (t.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ t.borrowState.index
      then compInitialIndex else (t.acct who).borrowerIndex) =
    accrualStart (t.acct who).borrowerIndex t.borrowState.index := by
  intro t who
  unfold accrualStart St.acct
  by_cases h : (t.accts.getD who noAcct).borrowerIndex = 0
  · simp only [h, ↓reduceIte]
    by_cases h2 : compInitialIndex ≤ t.borrowState.index <;> simp [h2, h]
  · simp only [h, ↓reduceIte]
    have : ¬ ((t.accts.getD who noAcct).borrowerIndex = 0 ∧
      compInitialIndex ≤ t.borrowState.index) := fun hh => h hh.1
    simp [this]

theorem plan14_block_le_of_update_aux_tmp : ∀ (s : St) (t : St),
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber := by
  intro s t h
  unfold updateCompBorrowIndex subChecked at h
  by_cases hle : s.borrowState.block ≤ s.blockNumber
  · exact hle
  · simp [hle] at h

theorem plan15_updateSupply_pres_aux_tmp2 (s : St) :
    Consistent s →
    ∃ t, updateCompSupplyIndex s = some t ∧ Consistent t := by
  intro hC
  obtain ⟨hSup, hBor, hIdx⟩ := hC
  have hsub : subChecked s.blockNumber s.supplyState.block =
    some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked
    simp [hSup]
  unfold updateCompSupplyIndex
  rw [hsub]
  by_cases h1 : (s.blockNumber - s.supplyState.block) > 0 ∧ s.supplyState.speed > 0
  · simp only [h1, ↓reduceIte]
    refine ⟨_, rfl, ?_, hBor, ?_⟩
    · simp
    · intro a ha
      obtain ⟨hs, hb⟩ := hIdx a ha
      simp only
      constructor
      · apply Nat.le_trans hs
        apply Nat.le_add_right
      · exact hb
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (s.blockNumber - s.supplyState.block) > 0
    · simp only [h2, ↓reduceIte]
      refine ⟨_, rfl, ?_, hBor, ?_⟩
      · simp
      · intro a ha
        obtain ⟨hs, hb⟩ := hIdx a ha
        simp only
        constructor
        · exact hs
        · exact hb
    · have hzero : s.blockNumber - s.supplyState.block = 0 := by omega
      have heq : s.blockNumber = s.supplyState.block := by omega
      simp only [h2, ↓reduceIte]
      refine ⟨s, rfl, ?_, ?_, ?_⟩
      · omega
      · exact hBor
      · exact hIdx

theorem plan16_claim_decomp_auxcheck : ∀ (s : St) (who : Account),
    comptroller s (.claim who) = claimComp s who := by
  intro s who; rfl

theorem plan16_claim_decomp_auxcheck2 : ∀ (s : St) (who : Account),
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun t => distributeBorrowerComp t who) := by
  intro s who; rfl

theorem plan16_claim_decomp_auxcheck3 : ∀ (s : St) (who : Account),
    comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) := by
  intro s who; rfl

theorem req_calls_succeed       : CallsSucceed comptroller := by
  intro s c hs
  exact td0_calls_some s c hs

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
  have hrun := td0_run_potential ops (L.compSpeed, L.compSpeed) (upgrade L) hinv
  have hinit := td0_upgrade_potential_le L hWF
  exact td0_rewards_conclude L ops hrun hinit

theorem req_account_bounded     : AccountBounded comptroller := by
  intro L ops who hWF
  have hinv := td0_upgrade_inv L hWF
  have hrun := td0_run_potentialTo ops (L.compSpeed, L.compSpeed) (upgrade L) who hinv
  have hinit := td0_upgrade_potentialTo_le L who hWF
  exact td0_account_conclude L ops who hrun hinit

theorem req_no_backdated        : NoBackdatedRewards comptroller := by
  intro L history ops who hWF hNo
  have hinv0 := td0_upgrade_inv L hWF
  have hinv := td0_run_inv history (L.compSpeed, L.compSpeed) (upgrade L) hinv0
  have hrun := td0_run_potentialTo ops
    (speedsAfter (L.compSpeed, L.compSpeed) history)
    (run comptroller (upgrade L) history) who hinv
  have hzero := td0_potentialTo_of_noPosition
    (run comptroller (upgrade L) history) who hNo
  exact td0_no_backdated_conclude (run comptroller (upgrade L) history)
    (speedsAfter (L.compSpeed, L.compSpeed) history) ops who hrun hzero

end CompRewards
