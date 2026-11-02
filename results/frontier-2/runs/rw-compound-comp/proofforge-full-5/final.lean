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
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := supplyIndex,
               accrued := a.accrued + mulDouble a.supply deltaIndex })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  let borrowIndex := s.borrowState.index
  let borrowerIndex :=
    if (s.acct borrower).borrowerIndex = 0 ∧ compInitialIndex ≤ borrowIndex then compInitialIndex
    else (s.acct borrower).borrowerIndex
  match subChecked borrowIndex borrowerIndex with
  | none => none
  | some deltaIndex =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := borrowIndex,
               accrued := a.accrued + mulDouble a.borrow deltaIndex })

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
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

theorem sub_some {a b d : Nat} (h : subChecked a b = some d) : b ≤ a ∧ d = a - b := by
  unfold subChecked at h
  split at h
  · next hb => simp at h; subst h; exact ⟨hb, rfl⟩
  · next hb => simp at h

theorem modify_congr (l : List Acct) (w : Nat) (f1 f2 : Acct → Acct)
    (h : f1 (l.getD w noAcct) = f2 (l.getD w noAcct)) : l.modify w f1 = l.modify w f2 := by
  induction l generalizing w with
  | nil => simp
  | cons a l ih =>
    cases w with
    | zero => simp at h ⊢; simp [h]
    | succ w =>
      simp at h ⊢
      exact ih w h

theorem start_supply_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex
     else (s.acct who).supplierIndex) =
    accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).supplierIndex = 0 <;> simp [hr]

theorem start_borrow_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex
     else (s.acct who).borrowerIndex) =
    accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases hr : (s.acct who).borrowerIndex = 0 <;> simp [hr]

theorem accrualStart_le {recorded index : Nat} (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · simp [hr]
    by_cases hi : compInitialIndex ≤ index
    · rw [if_pos hi]; exact hi
    · simp [hi]
  · simp [hr]; exact h

theorem accrueSupply_le (s : St) : s.supplyState.index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem accrueBorrow_le (s : St) : s.borrowState.index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem upd_supply_some (s : St) (s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  cases hs : subChecked s.blockNumber s.supplyState.block with
  | none => simp [hs] at h
  | some delta =>
    simp only [hs] at h
    have hsub := sub_some hs
    have hle : s.supplyState.block ≤ s.blockNumber := hsub.1
    have hdelta : delta = s.blockNumber - s.supplyState.block := hsub.2
    subst hdelta
    refine ⟨hle, ?_⟩
    simp only [fraction, doubleScale] at h
    simp only [accrueSide, doubleScale] at ⊢
    by_cases hc1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
    · by_cases hc2 : totalSupply s > 0
      · have g1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s := ⟨hc1.1, hc1.2, hc2⟩
        rw [if_pos hc1] at h
        rw [if_pos hc2] at h
        rw [if_pos g1] at ⊢
        simp only [Option.some_inj] at h ⊢
        rw [h]
      · have g1neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by
          intro hc; exact hc2 hc.2.2
        rw [if_pos hc1] at h
        rw [if_neg hc2] at h
        rw [if_neg g1neg] at ⊢
        simp only [Option.some_inj] at h ⊢
        subst h
        rfl
    · rw [if_neg hc1] at h
      have g1neg : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by
        intro hc; exact hc1 ⟨hc.1, hc.2.1⟩
      rw [if_neg g1neg] at ⊢
      by_cases hd : s.blockNumber - s.supplyState.block > 0
      · rw [if_pos hd] at h
        simp only [Option.some_inj] at h ⊢
        rw [h]
      · rw [if_neg hd] at h
        simp only [Option.some_inj] at h
        subst h
        have hbeq : s.supplyState.block = s.blockNumber := by omega
        cases s with
        | mk bn sup bor res ac =>
          cases sup with
          | mk ix bl sp =>
            simp only at hbeq ⊢
            subst hbeq
            rfl

theorem upd_borrow_some (s : St) (s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
    s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  cases hs : subChecked s.blockNumber s.borrowState.block with
  | none => simp [hs] at h
  | some delta =>
    simp only [hs] at h
    have hsub := sub_some hs
    have hle : s.borrowState.block ≤ s.blockNumber := hsub.1
    have hdelta : delta = s.blockNumber - s.borrowState.block := hsub.2
    subst hdelta
    refine ⟨hle, ?_⟩
    simp only [fraction, doubleScale] at h
    simp only [accrueSide, doubleScale] at ⊢
    by_cases hc1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
    · by_cases hc2 : totalBorrows s > 0
      · have g1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s := ⟨hc1.1, hc1.2, hc2⟩
        rw [if_pos hc1] at h
        rw [if_pos hc2] at h
        rw [if_pos g1] at ⊢
        simp only [Option.some_inj] at h ⊢
        rw [h]
      · have g1neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by
          intro hc; exact hc2 hc.2.2
        rw [if_pos hc1] at h
        rw [if_neg hc2] at h
        rw [if_neg g1neg] at ⊢
        simp only [Option.some_inj] at h ⊢
        subst h
        rfl
    · rw [if_neg hc1] at h
      have g1neg : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by
        intro hc; exact hc1 ⟨hc.1, hc.2.1⟩
      rw [if_neg g1neg] at ⊢
      by_cases hd : s.blockNumber - s.borrowState.block > 0
      · rw [if_pos hd] at h
        simp only [Option.some_inj] at h ⊢
        rw [h]
      · rw [if_neg hd] at h
        simp only [Option.some_inj] at h
        subst h
        have hbeq : s.borrowState.block = s.blockNumber := by omega
        cases s with
        | mk bn sup bor res ac =>
          cases bor with
          | mk ix bl sp =>
            simp only at hbeq ⊢
            subst hbeq
            rfl

theorem dist_supply_some (s : St) (who : Account) (s2 : St)
    (h : distributeSupplierComp s who = some s2) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s2 = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  have hstart := start_supply_eq s who
  unfold distributeSupplierComp at h
  simp only at h
  rw [hstart] at h
  cases hd : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none => simp [hd] at h
  | some delta =>
    simp only [hd] at h
    have hsub := sub_some hd
    have hle := hsub.1
    have hdelta : delta =
      s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index := hsub.2
    subst hdelta
    refine ⟨hle, ?_⟩
    simp only [Option.some_inj] at h
    subst h
    unfold St.withAcct mulDouble creditFor
    congr 1
    apply modify_congr
    show (_ : Acct) = _
    simp only [St.acct]

theorem dist_borrow_some (s : St) (who : Account) (s2 : St)
    (h : distributeBorrowerComp s who = some s2) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s2 = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  have hstart := start_borrow_eq s who
  unfold distributeBorrowerComp at h
  simp only at h
  rw [hstart] at h
  cases hd : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none => simp [hd] at h
  | some delta =>
    simp only [hd] at h
    have hsub := sub_some hd
    have hle := hsub.1
    have hdelta : delta =
      s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index := hsub.2
    subst hdelta
    refine ⟨hle, ?_⟩
    simp only [Option.some_inj] at h
    subst h
    unfold St.withAcct mulDouble creditFor
    congr 1
    apply modify_congr
    show (_ : Acct) = _
    simp only [St.acct]

theorem upd_supply_succeeds (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s1, updateCompSupplyIndex s = some s1 := by
  unfold updateCompSupplyIndex
  have hsub : subChecked s.blockNumber s.supplyState.block = some (s.blockNumber - s.supplyState.block) := by
    unfold subChecked; simp [h]
  rw [hsub]
  simp only
  by_cases hc1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hc1]
    exact ⟨_, rfl⟩
  · rw [if_neg hc1]
    by_cases hd : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos hd]
      exact ⟨_, rfl⟩
    · rw [if_neg hd]
      exact ⟨s, rfl⟩

theorem upd_borrow_succeeds (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s1, updateCompBorrowIndex s = some s1 := by
  unfold updateCompBorrowIndex
  have hsub : subChecked s.blockNumber s.borrowState.block = some (s.blockNumber - s.borrowState.block) := by
    unfold subChecked; simp [h]
  rw [hsub]
  simp only
  by_cases hc1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hc1]
    exact ⟨_, rfl⟩
  · rw [if_neg hc1]
    by_cases hd : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos hd]
      exact ⟨_, rfl⟩
    · rw [if_neg hd]
      exact ⟨s, rfl⟩

theorem dist_supply_succeeds (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s2, distributeSupplierComp s who = some s2 := by
  unfold distributeSupplierComp
  simp only
  have hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index :=
    accrualStart_le h
  have hstart := start_supply_eq s who
  rw [hstart]
  cases hs : subChecked s.supplyState.index
      (accrualStart (s.acct who).supplierIndex s.supplyState.index) with
  | none =>
    unfold subChecked at hs
    split at hs
    · next hb => simp [hb] at hs
    · next hb => exact absurd hle hb
  | some delta => exact ⟨_, rfl⟩

theorem dist_borrow_succeeds (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    ∃ s2, distributeBorrowerComp s who = some s2 := by
  unfold distributeBorrowerComp
  simp only
  have hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index :=
    accrualStart_le h
  have hstart := start_borrow_eq s who
  rw [hstart]
  cases hs : subChecked s.borrowState.index
      (accrualStart (s.acct who).borrowerIndex s.borrowState.index) with
  | none =>
    unfold subChecked at hs
    split at hs
    · next hb => simp [hb] at hs
    · next hb => exact absurd hle hb
  | some delta => exact ⟨_, rfl⟩

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hU : updateCompSupplyIndex s with
  | none => simp [hU] at h
  | some s1 =>
    simp [hU] at h
    cases hD : distributeSupplierComp s1 who with
    | none => simp [hD] at h
    | some s2 =>
      simp [hD] at h
      subst h
      have hU' := upd_supply_some s s1 hU
      have hD' := dist_supply_some s1 who s2 hD
      obtain ⟨hblock, hUeq⟩ := hU'
      obtain ⟨hstart1, hDeq⟩ := hD'
      subst hUeq
      subst hDeq
      exact ⟨hblock, hstart1, rfl⟩

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  unfold comptroller at h
  cases hU : updateCompBorrowIndex s with
  | none => simp [hU] at h
  | some s1 =>
    simp [hU] at h
    cases hD : distributeBorrowerComp s1 who with
    | none => simp [hD] at h
    | some s2 =>
      simp [hD] at h
      subst h
      have hU' := upd_borrow_some s s1 hU
      have hD' := dist_borrow_some s1 who s2 hD
      obtain ⟨hblock, hUeq⟩ := hU'
      obtain ⟨hstart1, hDeq⟩ := hD'
      subst hUeq
      subst hDeq
      exact ⟨hblock, hstart1, rfl⟩

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp at h
  cases hU1 : updateCompBorrowIndex s with
  | none => simp [hU1] at h
  | some t1 =>
    simp [hU1] at h
    cases hD1 : distributeBorrowerComp t1 who with
    | none => simp [hD1] at h
    | some m1 =>
      simp [hD1] at h
      cases hU2 : updateCompSupplyIndex m1 with
      | none => simp [hU2] at h
      | some t2 =>
        simp [hU2] at h
        cases hD2 : distributeSupplierComp t2 who with
        | none => simp [hD2] at h
        | some m2 =>
          simp [hD2] at h
          subst h
          have hU1' := upd_borrow_some s t1 hU1
          have hD1' := dist_borrow_some t1 who m1 hD1
          have hU2' := upd_supply_some m1 t2 hU2
          have hD2' := dist_supply_some t2 who m2 hD2
          obtain ⟨hb1, hU1eq⟩ := hU1'
          obtain ⟨hst1, hD1eq⟩ := hD1'
          obtain ⟨hb2, hU2eq⟩ := hU2'
          obtain ⟨hst2, hD2eq⟩ := hD2'
          subst hU1eq
          subst hD1eq
          subst hU2eq
          subst hD2eq
          exact ⟨_, _, ⟨hb1, hst1, rfl⟩, ⟨hb2, hst2, rfl⟩, rfl⟩

theorem set_supply_some (s : St) (a : Nat) (s1 : St)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1 = { s with supplyState := if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by
  unfold setSupplySpeed at h
  by_cases hs : s.supplyState.speed ≠ a
  · rw [if_pos hs] at h
    cases hU : updateCompSupplyIndex s with
    | none => simp [hU] at h
    | some t =>
      simp [hU] at h
      subst h
      have hUt := upd_supply_some s t hU
      obtain ⟨hblock, hUeq⟩ := hUt
      subst hUeq
      refine ⟨fun _ => hblock, ?_⟩
      simp [hs]
  · rw [if_neg hs] at h
    simp only [Option.some_inj] at h
    subst h
    have heq : s.supplyState.speed = a := by
      by_cases heq : s.supplyState.speed = a
      · exact heq
      · exact False.elim (hs heq)
    refine ⟨fun hc => absurd hc hs, ?_⟩
    simp [heq]

theorem set_borrow_some (s : St) (b : Nat) (s1 : St)
    (h : setBorrowSpeed s b = some s1) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s1 = { s with borrowState := if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  unfold setBorrowSpeed at h
  by_cases hs : s.borrowState.speed ≠ b
  · rw [if_pos hs] at h
    cases hU : updateCompBorrowIndex s with
    | none => simp [hU] at h
    | some t =>
      simp [hU] at h
      subst h
      have hUt := upd_borrow_some s t hU
      obtain ⟨hblock, hUeq⟩ := hUt
      subst hUeq
      refine ⟨fun _ => hblock, ?_⟩
      simp [hs]
  · rw [if_neg hs] at h
    simp only [Option.some_inj] at h
    subst h
    have heq : s.borrowState.speed = b := by
      by_cases heq : s.borrowState.speed = b
      · exact heq
      · exact False.elim (hs heq)
    refine ⟨fun hc => absurd hc hs, ?_⟩
    simp [heq]

theorem set_supply_succeeds (s : St) (a : Nat)
    (h : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) :
    ∃ s1, setSupplySpeed s a = some s1 := by
  unfold setSupplySpeed
  by_cases hs : s.supplyState.speed ≠ a
  · rw [if_pos hs]
    obtain ⟨t, ht⟩ := upd_supply_succeeds s (h hs)
    exact ⟨{ t with supplyState := { t.supplyState with speed := a } }, by simp [ht]⟩
  · rw [if_neg hs]
    exact ⟨_, rfl⟩

theorem set_borrow_succeeds (s : St) (b : Nat)
    (h : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) :
    ∃ s1, setBorrowSpeed s b = some s1 := by
  unfold setBorrowSpeed
  by_cases hs : s.borrowState.speed ≠ b
  · rw [if_pos hs]
    obtain ⟨t, ht⟩ := upd_borrow_succeeds s (h hs)
    exact ⟨{ t with borrowState := { t.borrowState with speed := b } }, by simp [ht]⟩
  · rw [if_neg hs]
    exact ⟨_, rfl⟩

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  cases h1 : setSupplySpeed s a with
  | none => simp [h1] at h
  | some s1 =>
    simp [h1] at h
    cases h2 : setBorrowSpeed s1 b with
    | none => simp [h2] at h
    | some s2 =>
      simp [h2] at h
      subst h
      have hS := set_supply_some s a s1 h1
      have hB := set_borrow_some s1 b s2 h2
      obtain ⟨hsblock, hSeq⟩ := hS
      obtain ⟨hbblock, hBeq⟩ := hB
      subst hSeq
      subst hBeq
      simp at hbblock ⊢
      refine ⟨hsblock, fun hc => hbblock hc, rfl⟩

theorem acct_supply_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | heq
  · have h1 := (hmem _ hm).1
    simpa [St.acct] using h1
  · have h2 : s.acct who = noAcct := heq
    rw [h2]
    exact Nat.zero_le _

theorem acct_borrow_le (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at h
  obtain ⟨_, _, hmem⟩ := h
  rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | heq
  · have h1 := (hmem _ hm).2
    simpa [St.acct] using h1
  · have h2 : s.acct who = noAcct := heq
    rw [h2]
    exact Nat.zero_le _

theorem dist_borrow_preserves_supplyIx (t1 : St) (who : Account) (m1 : St)
    (hD : distributeBorrowerComp t1 who = some m1) :
    (m1.acct who).supplierIndex = (t1.acct who).supplierIndex := by
  have hD' := dist_borrow_some t1 who m1 hD
  obtain ⟨_, hDeq⟩ := hD'
  rw [hDeq]
  unfold St.acct
  rw [ProofForgeFin.Ledger.getD_modify]
  split <;> rfl

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hsblock, hbblock, hmem⟩ := hc
  have hcon : Consistent s := ⟨hsblock, hbblock, hmem⟩
  cases c with
  | supplyHook who =>
    unfold comptroller
    obtain ⟨s1, hU⟩ := upd_supply_succeeds s hsblock
    simp only [hU]
    have hUeq := (upd_supply_some s s1 hU).2
    have hle1 := acct_supply_le s who hcon
    have hbound : (s1.acct who).supplierIndex ≤ s1.supplyState.index := by
      rw [hUeq]
      simp only [St.acct]
      exact Nat.le_trans hle1 (accrueSupply_le s)
    obtain ⟨s2, hD⟩ := dist_supply_succeeds s1 who hbound
    simp [hD]
  | borrowHook who =>
    unfold comptroller
    obtain ⟨s1, hU⟩ := upd_borrow_succeeds s hbblock
    simp only [hU]
    have hUeq := (upd_borrow_some s s1 hU).2
    have hle1 := acct_borrow_le s who hcon
    have hbound : (s1.acct who).borrowerIndex ≤ s1.borrowState.index := by
      rw [hUeq]
      simp only [St.acct]
      exact Nat.le_trans hle1 (accrueBorrow_le s)
    obtain ⟨s2, hD⟩ := dist_borrow_succeeds s1 who hbound
    simp [hD]
  | claim who =>
    unfold comptroller claimComp
    obtain ⟨t1, hU1⟩ := upd_borrow_succeeds s hbblock
    simp [hU1]
    have hU1eq := (upd_borrow_some s t1 hU1).2
    have hleB := acct_borrow_le s who hcon
    have hboundB : (t1.acct who).borrowerIndex ≤ t1.borrowState.index := by
      rw [hU1eq]
      simp only [St.acct]
      exact Nat.le_trans hleB (accrueBorrow_le s)
    obtain ⟨m1, hD1⟩ := dist_borrow_succeeds t1 who hboundB
    simp [hD1]
    have hD1eq := (dist_borrow_some t1 who m1 hD1).2
    have hblockS : m1.supplyState.block ≤ m1.blockNumber := by
      rw [hD1eq, hU1eq]
      exact hsblock
    obtain ⟨t2, hU2⟩ := upd_supply_succeeds m1 hblockS
    simp [hU2]
    have hU2eq := (upd_supply_some m1 t2 hU2).2
    have hpres : (m1.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have hp1 := dist_borrow_preserves_supplyIx t1 who m1 hD1
      have ht1acct : t1.acct who = s.acct who := by simp [hU1eq, St.acct]
      rw [hp1, ht1acct]
    have hleS := acct_supply_le s who hcon
    have hboundS : (t2.acct who).supplierIndex ≤ t2.supplyState.index := by
      have ht2acct : t2.acct who = m1.acct who := by simp [hU2eq, St.acct]
      rw [ht2acct, hpres]
      have h1 : (s.acct who).supplierIndex ≤ m1.supplyState.index := by
        rw [hD1eq, hU1eq]
        exact hleS
      have h2 : m1.supplyState.index ≤ t2.supplyState.index := by
        simp [hU2eq]
        exact accrueSupply_le m1
      exact Nat.le_trans h1 h2
    obtain ⟨m2, hD2⟩ := dist_supply_succeeds t2 who hboundS
    simp [hD2]
  | setSpeeds a b =>
    unfold comptroller setCompSpeedInternal
    have hsuc : ∃ s1, setSupplySpeed s a = some s1 := by
      unfold setSupplySpeed
      by_cases hs : s.supplyState.speed ≠ a
      · rw [if_pos hs]
        obtain ⟨t, ht⟩ := upd_supply_succeeds s hsblock
        exact ⟨{ t with supplyState := { t.supplyState with speed := a } }, by simp [ht]⟩
      · rw [if_neg hs]
        exact ⟨_, rfl⟩
    obtain ⟨s1, h1⟩ := hsuc
    simp [h1]
    have hSeq := (set_supply_some s a s1 h1).2
    have hsuc2 : ∃ s2, setBorrowSpeed s1 b = some s2 := by
      unfold setBorrowSpeed
      by_cases hs : s1.borrowState.speed ≠ b
      · rw [if_pos hs]
        have hblock : s1.borrowState.block ≤ s1.blockNumber := by
          rw [hSeq]
          exact hbblock
        obtain ⟨t, ht⟩ := upd_borrow_succeeds s1 hblock
        exact ⟨{ t with borrowState := { t.borrowState with speed := b } }, by simp [ht]⟩
      · rw [if_neg hs]
        exact ⟨_, rfl⟩
    obtain ⟨s2, h2⟩ := hsuc2
    simp [h2]
/-- Per-account potential term at indices `iS`, `iB`: credited COMP (scaled) plus
pending supply and borrow rewards counted from the protocol starts (`firstStart`). -/
def sterm (iS iB : Nat) (a : Acct) : Nat :=
  (a.accrued + a.wallet) * doubleScale +
  (ProofForgeFin.DeFi.Rewards.pending a.supply
    (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex iS) iS +
   ProofForgeFin.DeFi.Rewards.pending a.borrow
    (ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex iB) iB)

/-- Global potential: every account's term plus the scaled emission not yet in either index. -/
def pot (s : St) : Nat :=
  (s.accts.map (sterm s.supplyState.index s.borrowState.index)).sum +
  doubleScale * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed +
    (s.blockNumber - s.borrowState.block) * s.borrowState.speed)

/-- Per-account potential: `who`'s term plus the scaled unindexed emission of each side
counted only while `who` holds a position there. -/
def potTo (s : St) (who : Account) : Nat :=
  sterm s.supplyState.index s.borrowState.index (s.acct who) +
  doubleScale * ((if 0 < (s.acct who).supply
      then (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0) +
    (if 0 < (s.acct who).borrow
      then (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0))

/-- Run invariant with ghost speeds `g`: speeds match and no side block lies ahead. -/
def Inv (g : Nat × Nat) (s : St) : Prop :=
  s.supplyState.speed = g.1 ∧ s.borrowState.speed = g.2 ∧
  s.supplyState.block ≤ s.blockNumber ∧ s.borrowState.block ≤ s.blockNumber

theorem firstStart_bridge (r i : Nat) :
    accrualStart r i = ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex r i :=
  rfl

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split <;> rfl

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split <;> rfl

theorem supply_budget (s : St) :
    totalSupply s * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
      s.supplyState.index) ≤
    doubleScale * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) := by
  unfold accrueSide totalSupply doubleScale
  by_cases hc : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
    0 < (s.accts.map Acct.supply).sum
  · rw [if_pos hc]
    simp only
    rw [Nat.add_sub_cancel_left]
    have heq : (s.blockNumber - s.supplyState.block) * s.supplyState.speed * 10 ^ 36 =
        10 ^ 36 * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) := Nat.mul_comm _ _
    rw [heq]
    have hcomm : (s.accts.map Acct.supply).sum *
        (10 ^ 36 * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) /
          (s.accts.map Acct.supply).sum) =
        (10 ^ 36 * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed) /
          (s.accts.map Acct.supply).sum) * (s.accts.map Acct.supply).sum :=
      Nat.mul_comm _ _
    rw [hcomm]
    exact Nat.div_mul_le_self _ _
  · rw [if_neg hc]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_le]

theorem borrow_budget (s : St) :
    totalBorrows s * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
      s.borrowState.index) ≤
    doubleScale * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) := by
  unfold accrueSide totalBorrows doubleScale
  by_cases hc : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
    0 < (s.accts.map Acct.borrow).sum
  · rw [if_pos hc]
    simp only
    rw [Nat.add_sub_cancel_left]
    have heq : (s.blockNumber - s.borrowState.block) * s.borrowState.speed * 10 ^ 36 =
        10 ^ 36 * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) := Nat.mul_comm _ _
    rw [heq]
    have hcomm : (s.accts.map Acct.borrow).sum *
        (10 ^ 36 * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) /
          (s.accts.map Acct.borrow).sum) =
        (10 ^ 36 * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed) /
          (s.accts.map Acct.borrow).sum) * (s.accts.map Acct.borrow).sum :=
      Nat.mul_comm _ _
    rw [hcomm]
    exact Nat.div_mul_le_self _ _
  · rw [if_neg hc]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_le]

theorem sterm_settle_supply (iS iB : Nat) (a0 : Acct) :
    sterm iS iB ({ a0 with supplierIndex := iS, accrued := a0.accrued + creditFor a0.supply (accrualStart a0.supplierIndex iS) iS }) ≤
    sterm iS iB a0 := by
  have hbridge : accrualStart a0.supplierIndex iS =
      ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.supplierIndex iS :=
    firstStart_bridge _ _
  have hsettle := ProofForgeFin.Accumulator.settle_scaled_le_of_le
    (one := doubleScale) (c := a0.accrued + a0.wallet) (u := a0.supply) (i := iS)
    (p := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.supplierIndex iS)
    (q := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.supplierIndex iS)
    (q' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex iS iS)
    (Nat.le_refl _)
    (ProofForgeFin.Accumulator.le_firstStart_self compInitialIndex iS)
  rw [hbridge]
  unfold sterm creditFor ProofForgeFin.DeFi.Rewards.pending
  dsimp only
  have hrw : (a0.accrued + a0.supply * (iS - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.supplierIndex iS) / doubleScale) + a0.wallet = (a0.accrued + a0.wallet) + a0.supply * (iS - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.supplierIndex iS) / doubleScale := by omega
  rw [hrw]
  omega

theorem sterm_settle_borrow (iS iB : Nat) (a0 : Acct) :
    sterm iS iB ({ a0 with borrowerIndex := iB, accrued := a0.accrued + creditFor a0.borrow (accrualStart a0.borrowerIndex iB) iB }) ≤
    sterm iS iB a0 := by
  have hbridge : accrualStart a0.borrowerIndex iB =
      ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.borrowerIndex iB :=
    firstStart_bridge _ _
  have hsettle := ProofForgeFin.Accumulator.settle_scaled_le_of_le
    (one := doubleScale) (c := a0.accrued + a0.wallet) (u := a0.borrow) (i := iB)
    (p := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.borrowerIndex iB)
    (q := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.borrowerIndex iB)
    (q' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex iB iB)
    (Nat.le_refl _)
    (ProofForgeFin.Accumulator.le_firstStart_self compInitialIndex iB)
  rw [hbridge]
  unfold sterm creditFor ProofForgeFin.DeFi.Rewards.pending
  dsimp only
  have hrw : (a0.accrued + a0.borrow * (iB - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.borrowerIndex iB) / doubleScale) + a0.wallet = (a0.accrued + a0.wallet) + a0.borrow * (iB - ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a0.borrowerIndex iB) / doubleScale := by omega
  rw [hrw]
  omega

theorem sterm_accrue_supply_le (iS iS' iB : Nat) (hle : iS ≤ iS') (a : Acct) :
    sterm iS' iB a ≤ sterm iS iB a + a.supply * (iS' - iS) := by
  have hmono := ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.supplierIndex hle
  have hgrow := ProofForgeFin.Accumulator.owed_le_add (u := a.supply) (i := iS) (i' := iS')
    (s := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex iS)
    (s' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.supplierIndex iS') hmono
  unfold sterm ProofForgeFin.DeFi.Rewards.pending
  omega

theorem sterm_accrue_borrow_le (iS iB iB' : Nat) (hle : iB ≤ iB') (a : Acct) :
    sterm iS iB' a ≤ sterm iS iB a + a.borrow * (iB' - iB) := by
  have hmono := ProofForgeFin.Accumulator.firstStart_mono compInitialIndex a.borrowerIndex hle
  have hgrow := ProofForgeFin.Accumulator.owed_le_add (u := a.borrow) (i := iB) (i' := iB')
    (s := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex iB)
    (s' := ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex a.borrowerIndex iB') hmono
  unfold sterm ProofForgeFin.DeFi.Rewards.pending
  omega

theorem supplyHookStep (s s1 : St) (who : Account) (g : Nat × Nat)
    (hI : Inv g s) (hD : SupplyDistributed s who s1) :
    Inv g s1 ∧ pot s1 ≤ pot s := by
  obtain ⟨hblock, hstart, hSeq⟩ := hD
  obtain ⟨hgS, hgB, hgblockS, hgblockB⟩ := hI
  rw [hSeq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [accrueSide_speed]; exact hgS
  · exact hgB
  · rw [accrueSide_block]; exact Nat.le_refl _
  · exact hgblockB
  · have hle : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrueSupply_le s
    have e_sum := ProofForgeFin.DeFi.Rewards.sum_modify_index_le
      (l := s.accts) (i := who)
      (f := fun a => ({ a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct))
      (dflt := noAcct)
      (t := sterm s.supplyState.index s.borrowState.index)
      (t' := sterm (accrueSide s.supplyState s.blockNumber (totalSupply s)).index s.borrowState.index)
      (units := Acct.supply)
      (d := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)
      (E := doubleScale * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed))
      (fun _ => sterm_settle_supply _ _ _)
      (fun a _ => sterm_accrue_supply_le _ _ _ hle a)
      (supply_budget s)
    simp only [pot, accrueSide_block, accrueSide_speed, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mul_add]
    omega

theorem borrowHookStep (s s1 : St) (who : Account) (g : Nat × Nat)
    (hI : Inv g s) (hD : BorrowDistributed s who s1) :
    Inv g s1 ∧ pot s1 ≤ pot s := by
  obtain ⟨hblock, hstart, hSeq⟩ := hD
  obtain ⟨hgS, hgB, hgblockS, hgblockB⟩ := hI
  rw [hSeq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hgS
  · rw [accrueSide_speed]; exact hgB
  · exact hgblockS
  · rw [accrueSide_block]; exact Nat.le_refl _
  · have hle : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueBorrow_le s
    have e_sum := ProofForgeFin.DeFi.Rewards.sum_modify_index_le
      (l := s.accts) (i := who)
      (f := fun a => ({ a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } : Acct))
      (dflt := noAcct)
      (t := sterm s.supplyState.index s.borrowState.index)
      (t' := sterm s.supplyState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (units := Acct.borrow)
      (d := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index)
      (E := doubleScale * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed))
      (fun _ => sterm_settle_borrow _ _ _)
      (fun a _ => sterm_accrue_borrow_le _ _ _ hle a)
      (borrow_budget s)
    simp only [pot, accrueSide_block, accrueSide_speed, Nat.sub_self, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    rw [Nat.mul_add]
    omega

theorem sterm_supply_units_eq (iS iB : Nat) (a : Acct) (u' : Nat)
    (hset : a.supplierIndex = iS) :
    sterm iS iB ({ a with supply := u' }) = sterm iS iB a := by
  unfold sterm ProofForgeFin.DeFi.Rewards.pending
  rw [hset]
  simp

theorem sterm_borrow_units_eq (iS iB : Nat) (a : Acct) (u' : Nat)
    (hset : a.borrowerIndex = iB) :
    sterm iS iB ({ a with borrow := u' }) = sterm iS iB a := by
  unfold sterm ProofForgeFin.DeFi.Rewards.pending
  rw [hset]
  simp

theorem sterm_grant_eq (iS iB : Nat) (a0 : Acct) :
    sterm iS iB ({ a0 with accrued := 0, wallet := a0.wallet + a0.accrued }) =
    sterm iS iB a0 := by
  have hc : (0 : Nat) + (a0.wallet + a0.accrued) = a0.accrued + a0.wallet := by omega
  unfold sterm
  dsimp only
  rw [hc]

theorem hook_settles_supply (s s1 : St) (who : Account)
    (hD : SupplyDistributed s who s1) (hlen : who < s.accts.length) :
    (s1.acct who).supplierIndex = s1.supplyState.index := by
  obtain ⟨_, _, hSeq⟩ := hD
  rw [hSeq]
  unfold St.acct
  rw [ProofForgeFin.Ledger.getD_modify]
  rw [if_pos ⟨rfl, hlen⟩]

theorem hook_settles_borrow (s s1 : St) (who : Account)
    (hD : BorrowDistributed s who s1) (hlen : who < s.accts.length) :
    (s1.acct who).borrowerIndex = s1.borrowState.index := by
  obtain ⟨_, _, hSeq⟩ := hD
  rw [hSeq]
  unfold St.acct
  rw [ProofForgeFin.Ledger.getD_modify]
  rw [if_pos ⟨rfl, hlen⟩]

theorem supplyAccrueStep (s : St) (g : Nat × Nat) (hI : Inv g s)
    (s1 : St) (hU : updateCompSupplyIndex s = some s1) :
    Inv g s1 ∧ pot s1 ≤ pot s := by
  have hU' := upd_supply_some s s1 hU
  obtain ⟨hblock, hUeq⟩ := hU'
  obtain ⟨hgS, hgB, hgblockS, hgblockB⟩ := hI
  rw [hUeq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [accrueSide_speed]; exact hgS
  · exact hgB
  · rw [accrueSide_block]; exact Nat.le_refl _
  · exact hgblockB
  · have hle : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrueSupply_le s
    have e_sum := ProofForgeFin.DeFi.Rewards.sum_le_of_index_le
      (l := s.accts)
      (t := sterm s.supplyState.index s.borrowState.index)
      (t' := sterm (accrueSide s.supplyState s.blockNumber (totalSupply s)).index s.borrowState.index)
      (units := Acct.supply)
      (d := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index)
      (E := doubleScale * ((s.blockNumber - s.supplyState.block) * s.supplyState.speed))
      (fun a _ => sterm_accrue_supply_le _ _ _ hle a)
      (supply_budget s)
    simp only [pot, accrueSide_block, accrueSide_speed, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mul_add]
    omega

theorem borrowAccrueStep (s : St) (g : Nat × Nat) (hI : Inv g s)
    (s1 : St) (hU : updateCompBorrowIndex s = some s1) :
    Inv g s1 ∧ pot s1 ≤ pot s := by
  have hU' := upd_borrow_some s s1 hU
  obtain ⟨hblock, hUeq⟩ := hU'
  obtain ⟨hgS, hgB, hgblockS, hgblockB⟩ := hI
  rw [hUeq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hgS
  · rw [accrueSide_speed]; exact hgB
  · exact hgblockS
  · rw [accrueSide_block]; exact Nat.le_refl _
  · have hle : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueBorrow_le s
    have e_sum := ProofForgeFin.DeFi.Rewards.sum_le_of_index_le
      (l := s.accts)
      (t := sterm s.supplyState.index s.borrowState.index)
      (t' := sterm s.supplyState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
      (units := Acct.borrow)
      (d := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index)
      (E := doubleScale * ((s.blockNumber - s.borrowState.block) * s.borrowState.speed))
      (fun a _ => sterm_accrue_borrow_le _ _ _ hle a)
      (borrow_budget s)
    simp only [pot, accrueSide_block, accrueSide_speed, Nat.sub_self, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    rw [Nat.mul_add]
    omega

theorem mintStep (s : St) (who x : Nat) (g : Nat × Nat) (hI : Inv g s) :
    Inv g (exec comptroller s (.mint who x)) ∧
    pot (exec comptroller s (.mint who x)) ≤ pot s + doubleScale * emittedBy g (.mint who x) := by
  unfold exec
  by_cases hlen : who < s.accts.length
  · simp only [hlen, ↓reduceIte]
    cases hH : comptroller s (.supplyHook who) with
    | none =>
      dsimp only
      refine ⟨?_, ?_⟩
      · exact hI
      · show pot s ≤ pot s + doubleScale * 0
        exact Nat.le_add_right _ _
    | some s1 =>
      dsimp only
      have hDist := req_supply_hook s who s1 hH
      have hStep := supplyHookStep s s1 who g hI hDist
      obtain ⟨hI1, hP1⟩ := hStep
      have hSeq := hDist.2.2
      have hlen1 : who < s1.accts.length := by rw [hSeq]; simp [hlen]
      have hset : (s1.acct who).supplierIndex = s1.supplyState.index :=
        hook_settles_supply s s1 who hDist hlen
      have e_sum : ((s1.accts.modify who fun a => ({ a with supply := a.supply + x } : Acct)).map (sterm s1.supplyState.index s1.borrowState.index)).sum = ((s1.accts.map (sterm s1.supplyState.index s1.borrowState.index))).sum := by
        apply ProofForgeFin.Ledger.sum_map_modify_eq
        intro hwho
        exact sterm_supply_units_eq _ _ _ _ hset
      have eP : pot (s1.withAcct who fun a => ({ a with supply := a.supply + x } : Acct)) = pot s1 := by
        unfold pot St.withAcct
        simp only [e_sum]
      have hIfin : Inv g (s1.withAcct who fun a => ({ a with supply := a.supply + x } : Acct)) := hI1
      rw [eP]
      refine ⟨hIfin, ?_⟩
      show pot s1 ≤ pot s + doubleScale * 0
      exact Nat.le_trans hP1 (Nat.le_add_right _ _)
  · simp only [hlen, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · exact hI
    · show pot s ≤ pot s + doubleScale * 0
      exact Nat.le_add_right _ _

theorem redeemStep (s : St) (who x : Nat) (g : Nat × Nat) (hI : Inv g s) :
    Inv g (exec comptroller s (.redeem who x)) ∧
    pot (exec comptroller s (.redeem who x)) ≤ pot s + doubleScale * emittedBy g (.redeem who x) := by
  unfold exec
  by_cases hlen : who < s.accts.length
  · simp only [hlen, ↓reduceIte]
    cases hH : comptroller s (.supplyHook who) with
    | none =>
      dsimp only
      refine ⟨?_, ?_⟩
      · exact hI
      · show pot s ≤ pot s + doubleScale * 0
        exact Nat.le_add_right _ _
    | some s1 =>
      dsimp only
      have hDist := req_supply_hook s who s1 hH
      have hStep := supplyHookStep s s1 who g hI hDist
      obtain ⟨hI1, hP1⟩ := hStep
      have hSeq := hDist.2.2
      have hlen1 : who < s1.accts.length := by rw [hSeq]; simp [hlen]
      have hset : (s1.acct who).supplierIndex = s1.supplyState.index :=
        hook_settles_supply s s1 who hDist hlen
      by_cases hx : x ≤ (s1.acct who).supply
      · simp only [hx, ↓reduceIte]
        have e_sum : ((s1.accts.modify who fun a => ({ a with supply := a.supply - x } : Acct)).map (sterm s1.supplyState.index s1.borrowState.index)).sum = ((s1.accts.map (sterm s1.supplyState.index s1.borrowState.index))).sum := by
          apply ProofForgeFin.Ledger.sum_map_modify_eq
          intro hwho
          exact sterm_supply_units_eq _ _ _ _ hset
        have eP : pot (s1.withAcct who fun a => ({ a with supply := a.supply - x } : Acct)) = pot s1 := by
          unfold pot St.withAcct
          simp only [e_sum]
        have hIfin : Inv g (s1.withAcct who fun a => ({ a with supply := a.supply - x } : Acct)) := hI1
        rw [eP]
        refine ⟨hIfin, ?_⟩
        show pot s1 ≤ pot s + doubleScale * 0
        exact Nat.le_trans hP1 (Nat.le_add_right _ _)
      · simp only [hx, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · exact hI
        · show pot s ≤ pot s + doubleScale * 0
          exact Nat.le_add_right _ _
  · simp only [hlen, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · exact hI
    · show pot s ≤ pot s + doubleScale * 0
      exact Nat.le_add_right _ _

theorem borrowStep (s : St) (who x : Nat) (g : Nat × Nat) (hI : Inv g s) :
    Inv g (exec comptroller s (.borrow who x)) ∧
    pot (exec comptroller s (.borrow who x)) ≤ pot s + doubleScale * emittedBy g (.borrow who x) := by
  unfold exec
  by_cases hlen : who < s.accts.length
  · simp only [hlen, ↓reduceIte]
    cases hH : comptroller s (.borrowHook who) with
    | none =>
      dsimp only
      refine ⟨?_, ?_⟩
      · exact hI
      · show pot s ≤ pot s + doubleScale * 0
        exact Nat.le_add_right _ _
    | some s1 =>
      dsimp only
      have hDist := req_borrow_hook s who s1 hH
      have hStep := borrowHookStep s s1 who g hI hDist
      obtain ⟨hI1, hP1⟩ := hStep
      have hSeq := hDist.2.2
      have hlen1 : who < s1.accts.length := by rw [hSeq]; simp [hlen]
      have hset : (s1.acct who).borrowerIndex = s1.borrowState.index :=
        hook_settles_borrow s s1 who hDist hlen
      have e_sum : ((s1.accts.modify who fun a => ({ a with borrow := a.borrow + x } : Acct)).map (sterm s1.supplyState.index s1.borrowState.index)).sum = ((s1.accts.map (sterm s1.supplyState.index s1.borrowState.index))).sum := by
        apply ProofForgeFin.Ledger.sum_map_modify_eq
        intro hwho
        exact sterm_borrow_units_eq _ _ _ _ hset
      have eP : pot (s1.withAcct who fun a => ({ a with borrow := a.borrow + x } : Acct)) = pot s1 := by
        unfold pot St.withAcct
        simp only [e_sum]
      have hIfin : Inv g (s1.withAcct who fun a => ({ a with borrow := a.borrow + x } : Acct)) := hI1
      rw [eP]
      refine ⟨hIfin, ?_⟩
      show pot s1 ≤ pot s + doubleScale * 0
      exact Nat.le_trans hP1 (Nat.le_add_right _ _)
  · simp only [hlen, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · exact hI
    · show pot s ≤ pot s + doubleScale * 0
      exact Nat.le_add_right _ _

theorem repayStep (s : St) (who x : Nat) (g : Nat × Nat) (hI : Inv g s) :
    Inv g (exec comptroller s (.repay who x)) ∧
    pot (exec comptroller s (.repay who x)) ≤ pot s + doubleScale * emittedBy g (.repay who x) := by
  unfold exec
  by_cases hlen : who < s.accts.length
  · simp only [hlen, ↓reduceIte]
    cases hH : comptroller s (.borrowHook who) with
    | none =>
      dsimp only
      refine ⟨?_, ?_⟩
      · exact hI
      · show pot s ≤ pot s + doubleScale * 0
        exact Nat.le_add_right _ _
    | some s1 =>
      dsimp only
      have hDist := req_borrow_hook s who s1 hH
      have hStep := borrowHookStep s s1 who g hI hDist
      obtain ⟨hI1, hP1⟩ := hStep
      have hSeq := hDist.2.2
      have hlen1 : who < s1.accts.length := by rw [hSeq]; simp [hlen]
      have hset : (s1.acct who).borrowerIndex = s1.borrowState.index :=
        hook_settles_borrow s s1 who hDist hlen
      by_cases hx : x ≤ (s1.acct who).borrow
      · simp only [hx, ↓reduceIte]
        have e_sum : ((s1.accts.modify who fun a => ({ a with borrow := a.borrow - x } : Acct)).map (sterm s1.supplyState.index s1.borrowState.index)).sum = ((s1.accts.map (sterm s1.supplyState.index s1.borrowState.index))).sum := by
          apply ProofForgeFin.Ledger.sum_map_modify_eq
          intro hwho
          exact sterm_borrow_units_eq _ _ _ _ hset
        have eP : pot (s1.withAcct who fun a => ({ a with borrow := a.borrow - x } : Acct)) = pot s1 := by
          unfold pot St.withAcct
          simp only [e_sum]
        have hIfin : Inv g (s1.withAcct who fun a => ({ a with borrow := a.borrow - x } : Acct)) := hI1
        rw [eP]
        refine ⟨hIfin, ?_⟩
        show pot s1 ≤ pot s + doubleScale * 0
        exact Nat.le_trans hP1 (Nat.le_add_right _ _)
      · simp only [hx, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · exact hI
        · show pot s ≤ pot s + doubleScale * 0
          exact Nat.le_add_right _ _
  · simp only [hlen, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · exact hI
    · show pot s ≤ pot s + doubleScale * 0
      exact Nat.le_add_right _ _

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
