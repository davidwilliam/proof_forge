import CompRewards.Spec
import ProofForgeFin.Accumulator.Market
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

open ProofForgeFin.Accumulator in
/-- Reading the comptroller state as a two-sided reward market: supply is side 1,
borrow is side 2. The credited amount is accrued plus paid (wallet). -/
def M : ProofForgeFin.Accumulator.Market St Acct where
  one := doubleScale
  init := compInitialIndex
  clock s := ⟨s.blockNumber, s.supplyState.index, s.supplyState.block, s.supplyState.speed,
    s.borrowState.index, s.borrowState.block, s.borrowState.speed⟩
  accts s := s.accts
  dflt := noAcct
  units₁ a := a.supply
  units₂ a := a.borrow
  rec₁ a := a.supplierIndex
  rec₂ a := a.borrowerIndex
  credited a := a.accrued + a.wallet
  dflt_units₁ := rfl
  dflt_units₂ := rfl

/-- `accrueSide` brings the block up to date in both branches. -/
theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide; split <;> simp

/-- `accrueSide` never lowers the index. -/
theorem accrueSide_le_index (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide; split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- The fixed code computes `accrualStart`. -/
theorem start_eq_accrualStart (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by
  unfold accrualStart; by_cases h : recorded = 0 <;> simp [h]

/-- The fixed code computes `creditFor`. -/
theorem delta_eq_creditFor (units start index : Nat) :
    mulDouble units (index - start) = creditFor units start index := rfl

/-- `updateCompSupplyIndex` succeeds exactly when the side's block is not ahead, and
brings the supply side up to date per `accrueSide`. -/
theorem upd_supply_some (s s₁ : St) (h : updateCompSupplyIndex s = some s₁) :
    s.supplyState.block ≤ s.blockNumber ∧
    s₁ = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    refine ⟨hb, ?_⟩
    split at h
    · rename_i hC
      obtain ⟨h1, h2⟩ := hC
      by_cases ht : 0 < totalSupply s
      · have hS := Option.some_inj.mp h
        subst hS
        simp only [accrueSide, fraction, h1, h2, ht, and_true, ↓reduceIte]
      · have hS := Option.some_inj.mp h
        subst hS
        simp only [accrueSide, ht, and_false, Nat.add_zero, ↓reduceIte]
    · rename_i hC
      by_cases hd2 : s.blockNumber - s.supplyState.block > 0
      · simp only [hd2, ↓reduceIte] at h
        have hS := Option.some_inj.mp h
        subst hS
        have hd' : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
            0 < totalSupply s) := by omega
        simp only [accrueSide, hd', ↓reduceIte]
      · simp only [hd2, ↓reduceIte] at h
        have hS := Option.some_inj.mp h
        subst hS
        have heq : s.blockNumber = s.supplyState.block := by omega
        have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) = s.supplyState := by
          unfold accrueSide
          simp [heq]
        rw [hacc]
  · simp only [hb, ↓reduceIte] at h
    cases h

/-- `updateCompBorrowIndex` succeeds exactly when the side's block is not ahead, and
brings the borrow side up to date per `accrueSide`. -/
theorem upd_borrow_some (s s₁ : St) (h : updateCompBorrowIndex s = some s₁) :
    s.borrowState.block ≤ s.blockNumber ∧
    s₁ = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    refine ⟨hb, ?_⟩
    split at h
    · rename_i hC
      obtain ⟨h1, h2⟩ := hC
      by_cases ht : 0 < totalBorrows s
      · have hS := Option.some_inj.mp h
        subst hS
        simp only [accrueSide, fraction, h1, h2, ht, and_true, ↓reduceIte]
      · have hS := Option.some_inj.mp h
        subst hS
        simp only [accrueSide, ht, and_false, Nat.add_zero, ↓reduceIte]
    · rename_i hC
      by_cases hd2 : s.blockNumber - s.borrowState.block > 0
      · simp only [hd2, ↓reduceIte] at h
        have hS := Option.some_inj.mp h
        subst hS
        have hd' : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
            0 < totalBorrows s) := by omega
        simp only [accrueSide, hd', ↓reduceIte]
      · simp only [hd2, ↓reduceIte] at h
        have hS := Option.some_inj.mp h
        subst hS
        have heq : s.blockNumber = s.borrowState.block := by omega
        have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) = s.borrowState := by
          unfold accrueSide
          simp [heq]
        rw [hacc]
  · simp only [hb, ↓reduceIte] at h
    cases h

/-- `distributeSupplierComp` succeeds exactly when the account's start lies below the
index, and credits exactly `creditFor` for the supply held since `accrualStart`. -/
theorem dist_supply_some (s s₂ : St) (who : Nat)
    (h : distributeSupplierComp s who = some s₂) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s₂ = s.withAcct who (fun a => { a with
      supplierIndex := s.supplyState.index,
      accrued := a.accrued + creditFor a.supply
        (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex)
      = accrualStart (s.acct who).supplierIndex s.supplyState.index :=
    start_eq_accrualStart _ _
  unfold distributeSupplierComp at h
  dsimp only at h
  cases he : subChecked s.supplyState.index (if (s.acct who).supplierIndex = 0 ∧
    compInitialIndex ≤ s.supplyState.index then compInitialIndex
    else (s.acct who).supplierIndex) with
  | none =>
    rw [he] at h
    dsimp only at h
    cases h
  | some delta =>
    rw [he] at h
    dsimp only at h
    rw [hstart] at he
    unfold subChecked at he
    split at he
    · rename_i hC
      refine ⟨hC, ?_⟩
      have hDd : delta = s.supplyState.index -
          accrualStart (s.acct who).supplierIndex s.supplyState.index :=
        (Option.some_inj.mp he).symm
      have hS := Option.some_inj.mp h
      subst hS
      rw [hDd]
      unfold St.withAcct
      congr 1
      refine ProofForgeFin.Ledger.modify_congr _ _ noAcct ?_
      intro hlen
      simp only [St.acct, delta_eq_creditFor]
    · rename_i hn
      cases he

/-- `distributeBorrowerComp` succeeds exactly when the account's start lies below the
index, and credits exactly `creditFor` for the borrow held since `accrualStart`. -/
theorem dist_borrow_some (s s₂ : St) (who : Nat)
    (h : distributeBorrowerComp s who = some s₂) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    s₂ = s.withAcct who (fun a => { a with
      borrowerIndex := s.borrowState.index,
      accrued := a.accrued + creditFor a.borrow
        (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex)
      = accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
    start_eq_accrualStart _ _
  unfold distributeBorrowerComp at h
  dsimp only at h
  cases he : subChecked s.borrowState.index (if (s.acct who).borrowerIndex = 0 ∧
    compInitialIndex ≤ s.borrowState.index then compInitialIndex
    else (s.acct who).borrowerIndex) with
  | none =>
    rw [he] at h
    dsimp only at h
    cases h
  | some delta =>
    rw [he] at h
    dsimp only at h
    rw [hstart] at he
    unfold subChecked at he
    split at he
    · rename_i hC
      refine ⟨hC, ?_⟩
      have hDd : delta = s.borrowState.index -
          accrualStart (s.acct who).borrowerIndex s.borrowState.index :=
        (Option.some_inj.mp he).symm
      have hS := Option.some_inj.mp h
      subst hS
      rw [hDd]
      unfold St.withAcct
      congr 1
      refine ProofForgeFin.Ledger.modify_congr _ _ noAcct ?_
      intro hlen
      simp only [St.acct, delta_eq_creditFor]
    · rename_i hn
      cases he

/-- An account's start never lies above an index brought up to date past its recorded
index. -/
theorem start_le_accrued (sd : Side) (now total rec : Nat)
    (hrec : rec ≤ sd.index) :
    accrualStart rec (accrueSide sd now total).index ≤ (accrueSide sd now total).index := by
  have hmono : sd.index ≤ (accrueSide sd now total).index := accrueSide_le_index _ _ _
  unfold accrualStart
  by_cases hr : rec = 0
  · rw [if_pos hr]
    by_cases hi : compInitialIndex ≤ (accrueSide sd now total).index
    · rw [if_pos hi]
      exact hi
    · rw [if_neg hi]
      exact Nat.zero_le _
  · rw [if_neg hr]
    exact Nat.le_trans hrec hmono

/-- An account's start never lies above an index that already covers its recorded index. -/
theorem accrualStart_le_of_le (rec idx : Nat) (h : rec ≤ idx) :
    accrualStart rec idx ≤ idx := by
  unfold accrualStart
  by_cases hr : rec = 0
  · rw [if_pos hr]
    by_cases hi : compInitialIndex ≤ idx
    · rw [if_pos hi]
      exact hi
    · rw [if_neg hi]
      exact Nat.zero_le _
  · rw [if_neg hr]
    exact h

/-- A field that a change keeps reads the same on the changed account. -/
theorem withAcct_keeps (s : St) (who : Nat) (f : Acct → Acct) (p : Acct → Nat)
    (h : ∀ a, p (f a) = p a) : p ((s.withAcct who f).acct who) = p (s.acct who) := by
  unfold St.withAcct St.acct
  exact ProofForgeFin.Ledger.getD_modify_of_keeps _ _ _ _ _ h

/-- The updated supply index is the library's `catchUp`. -/
theorem upd_supply_index (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
    ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  split
  · rfl
  · rfl

/-- The updated borrow index is the library's `catchUp`. -/
theorem upd_borrow_index (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
    ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  split
  · rfl
  · rfl

/-- An update keeps the speed. -/
theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split
  · rfl
  · rfl

/-- The market's supply total is `totalSupply`. -/
theorem total_supply_eq (s : St) : M.total₁ s = totalSupply s := rfl

/-- The market's borrow total is `totalBorrows`. -/
theorem total_borrows_eq (s : St) : M.total₂ s = totalBorrows s := rfl

/-- The fixed start is the library's `firstStart`. -/
theorem start_eq_firstStart (rec idx : Nat) :
    ProofForgeFin.DeFi.Rewards.firstStart compInitialIndex rec idx = accrualStart rec idx := by
  unfold ProofForgeFin.DeFi.Rewards.firstStart accrualStart
  rfl

/-- The market's start value is the initial index. -/
theorem init_eq : M.init = compInitialIndex := rfl

/-- Peeling a successful bind. -/
theorem peel_some (t : St) (R : St → Option St) : ((some t >>= R)) = R t := rfl

/-- Peeling a failing bind. -/
theorem peel_none (R : St → Option St) : ((none >>= R)) = none := rfl

/-- A pure result. -/
theorem peel_pure (x : St) : (pure x : Option St) = some x := rfl

/-- Mapping a successful option. -/
theorem peel_map_some (x : St) (f : St → St) : (Option.map f (some x)) = some (f x) := rfl

/-- Mapping a failing option. -/
theorem peel_map_none (f : St → St) : (Option.map f none) = none := rfl

/-- Peeling a successful dot-notation bind. -/
theorem peel_obind_some (t : St) (R : St → Option St) : (Option.bind (some t) R) = R t := rfl

/-- Peeling a failing dot-notation bind. -/
theorem peel_obind_none (R : St → Option St) : (Option.bind none R) = none := rfl

/-- The code's grant is the spec's grant. -/
theorem grant_eq (s : St) (who : Nat) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant
  by_cases hc : (s.acct who).accrued > 0 ∧ (s.acct who).accrued ≤ s.reserve
  · simp only [hc, and_self, ↓reduceIte]
    congr 1
    refine ProofForgeFin.Ledger.modify_congr _ _ noAcct ?_
    intro hlen
    simp only [St.acct]
  · simp only [hc, ↓reduceIte]

/-- `updateCompSupplyIndex` in closed form under its precondition. -/
theorem upd_supply_eq_of (s : St) (hb : s.supplyState.block ≤ s.blockNumber) : updateCompSupplyIndex s = some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked
  simp only [hb, ↓reduceIte]
  by_cases hc : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0
  · rw [if_pos hc]
    have h1 := hc.1
    have h2 := hc.2
    by_cases ht : 0 < totalSupply s
    · simp only [accrueSide, fraction, h1, h2, ht, and_true, ↓reduceIte]
    · simp only [accrueSide, ht, and_false, Nat.add_zero, ↓reduceIte]
  · rw [if_neg hc]
    by_cases hd2 : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos hd2]
      have hd' : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧ 0 < totalSupply s) := fun h => hc ⟨h.1, h.2.1⟩
      simp only [accrueSide, hd', ↓reduceIte]
    · rw [if_neg hd2]
      have heq : s.blockNumber = s.supplyState.block := by omega
      have hacc : accrueSide s.supplyState s.blockNumber (totalSupply s) = s.supplyState := by
        unfold accrueSide
        simp [heq]
      rw [hacc]

/-- `updateCompBorrowIndex` in closed form under its precondition. -/
theorem upd_borrow_eq_of (s : St) (hb : s.borrowState.block ≤ s.blockNumber) : updateCompBorrowIndex s = some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked
  simp only [hb, ↓reduceIte]
  by_cases hc : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0
  · rw [if_pos hc]
    have h1 := hc.1
    have h2 := hc.2
    by_cases ht : 0 < totalBorrows s
    · simp only [accrueSide, fraction, h1, h2, ht, and_true, ↓reduceIte]
    · simp only [accrueSide, ht, and_false, Nat.add_zero, ↓reduceIte]
  · rw [if_neg hc]
    by_cases hd2 : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos hd2]
      have hd' : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧ 0 < totalBorrows s) := fun h => hc ⟨h.1, h.2.1⟩
      simp only [accrueSide, hd', ↓reduceIte]
    · rw [if_neg hd2]
      have heq : s.blockNumber = s.borrowState.block := by omega
      have hacc : accrueSide s.borrowState s.blockNumber (totalBorrows s) = s.borrowState := by
        unfold accrueSide
        simp [heq]
      rw [hacc]

/-- `distributeSupplierComp` in closed form under its precondition. -/
theorem dist_supply_eq_of (s : St) (who : Nat) (hle : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) : distributeSupplierComp s who = some (s.withAcct who (fun a => { a with supplierIndex := s.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })) := by
  have hstart : (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index then compInitialIndex else (s.acct who).supplierIndex) = accrualStart (s.acct who).supplierIndex s.supplyState.index := start_eq_accrualStart _ _
  unfold distributeSupplierComp subChecked
  dsimp only
  rw [hstart, if_pos hle]
  dsimp only
  unfold St.withAcct
  congr 1
  congr 1
  refine ProofForgeFin.Ledger.modify_congr _ _ noAcct ?_
  intro hlen
  simp only [St.acct, delta_eq_creditFor]

/-- `distributeBorrowerComp` in closed form under its precondition. -/
theorem dist_borrow_eq_of (s : St) (who : Nat) (hle : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) : distributeBorrowerComp s who = some (s.withAcct who (fun a => { a with borrowerIndex := s.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })) := by
  have hstart : (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index then compInitialIndex else (s.acct who).borrowerIndex) = accrualStart (s.acct who).borrowerIndex s.borrowState.index := start_eq_accrualStart _ _
  unfold distributeBorrowerComp subChecked
  dsimp only
  rw [hstart, if_pos hle]
  dsimp only
  unfold St.withAcct
  congr 1
  congr 1
  refine ProofForgeFin.Ledger.modify_congr _ _ noAcct ?_
  intro hlen
  simp only [St.acct, delta_eq_creditFor]

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hu : updateCompSupplyIndex s with
  | none =>
    simp only [hu] at h
    change none = some s' at h
    cases h
  | some s₁ =>
    rw [hu] at h
    change distributeSupplierComp s₁ who = some s' at h
    obtain ⟨hb, hSeq⟩ := upd_supply_some s s₁ hu
    obtain ⟨hle, hDeq⟩ := dist_supply_some s₁ s' who h
    have hacct : s₁.acct who = s.acct who := by
      rw [hSeq]
      rfl
    have hidx : s₁.supplyState.index = (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
      rw [hSeq]
    refine ⟨hb, ?_, ?_⟩
    · rw [hacct, hidx] at hle
      exact hle
    · rw [hSeq] at hDeq
      rw [hDeq]
      rfl

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  cases hu : updateCompBorrowIndex s with
  | none =>
    simp only [hu] at h
    change none = some s' at h
    cases h
  | some s₁ =>
    rw [hu] at h
    change distributeBorrowerComp s₁ who = some s' at h
    obtain ⟨hb, hSeq⟩ := upd_borrow_some s s₁ hu
    obtain ⟨hle, hDeq⟩ := dist_borrow_some s₁ s' who h
    have hacct : s₁.acct who = s.acct who := by
      rw [hSeq]
      rfl
    have hidx : s₁.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
      rw [hSeq]
    refine ⟨hb, ?_, ?_⟩
    · rw [hacct, hidx] at hle
      exact hle
    · rw [hSeq] at hDeq
      rw [hDeq]
      rfl

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller, claimComp] at h
  cases hu1 : updateCompBorrowIndex s with
  | none =>
    rw [hu1, peel_none] at h
    cases h
  | some t₁ =>
    rw [hu1, peel_some] at h
    cases hd1 : distributeBorrowerComp t₁ who with
    | none =>
      rw [hd1, peel_none] at h
      cases h
    | some t₂ =>
      rw [hd1, peel_some] at h
      cases hu2 : updateCompSupplyIndex t₂ with
      | none =>
        rw [hu2, peel_none] at h
        cases h
      | some t₃ =>
        rw [hu2, peel_some] at h
        cases hd2 : distributeSupplierComp t₃ who with
        | none =>
          rw [hd2, peel_none] at h
          cases h
        | some t₄ =>
          rw [hd2, peel_some, peel_pure] at h
          obtain ⟨hbb, hSeq1⟩ := upd_borrow_some s t₁ hu1
          obtain ⟨hle1, hDeq1⟩ := dist_borrow_some t₁ t₂ who hd1
          obtain ⟨hb2, hSeq2⟩ := upd_supply_some t₂ t₃ hu2
          obtain ⟨hle2, hDeq2⟩ := dist_supply_some t₃ t₄ who hd2
          have hX := Option.some_inj.mp h
          rw [grant_eq] at hX
          refine ⟨t₂, t₄, ?_, ?_, ?_⟩
          · refine ⟨hbb, ?_, ?_⟩
            · have hacct1 : t₁.acct who = s.acct who := by
                rw [hSeq1]
                rfl
              have hidx1 : t₁.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
                rw [hSeq1]
              rw [hacct1, hidx1] at hle1
              exact hle1
            · rw [hSeq1] at hDeq1
              rw [hDeq1]
              rfl
          · refine ⟨hb2, ?_, ?_⟩
            · have hacct2 : t₃.acct who = t₂.acct who := by
                rw [hSeq2]
                rfl
              have hidx2 : t₃.supplyState.index = (accrueSide t₂.supplyState t₂.blockNumber (totalSupply t₂)).index := by
                rw [hSeq2]
              rw [hacct2, hidx2] at hle2
              exact hle2
            · rw [hSeq2] at hDeq2
              rw [hDeq2]
              rfl
          · exact hX.symm

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller, setCompSpeedInternal] at h
  by_cases hs : s.supplyState.speed = a
  · have hne : ¬ s.supplyState.speed ≠ a := fun hne => hne hs
    unfold setSupplySpeed at h
    rw [if_neg hne, peel_obind_some] at h
    by_cases hsb : s.borrowState.speed = b
    · have hne2 : ¬ s.borrowState.speed ≠ b := fun hne => hne hsb
      unfold setBorrowSpeed at h
      rw [if_neg hne2] at h
      have hS : s = s' := Option.some_inj.mp h
      subst hS
      refine ⟨?_, ?_, ?_⟩
      · intro hneA
        exact (hneA hs).elim
      · intro hneB
        exact (hneB hsb).elim
      · rw [if_pos hs, if_pos hsb]
    · unfold setBorrowSpeed at h
      rw [if_pos hsb] at h
      cases hu : updateCompBorrowIndex s with
      | none =>
        rw [hu, peel_map_none] at h
        cases h
      | some t₁ =>
        rw [hu, peel_map_some] at h
        obtain ⟨hbb, hSeq⟩ := upd_borrow_some s t₁ hu
        refine ⟨?_, ?_, ?_⟩
        · intro hneA
          exact (hneA hs).elim
        · intro _
          exact hbb
        · have hS : (fun t => { t with borrowState := { t.borrowState with speed := b } }) t₁ = s' := Option.some_inj.mp h
          rw [hSeq] at hS
          rw [if_pos hs, if_neg hsb, ←hS]
  · have hpos : s.supplyState.speed ≠ a := fun heq => hs heq
    unfold setSupplySpeed at h
    rw [if_pos hpos] at h
    cases hu : updateCompSupplyIndex s with
    | none =>
      rw [hu, peel_map_none, peel_obind_none] at h
      cases h
    | some t₁ =>
      rw [hu, peel_map_some, peel_obind_some] at h
      obtain ⟨hbS, hSeq⟩ := upd_supply_some s t₁ hu
      have eBor : t₁.borrowState = s.borrowState := by
        rw [hSeq]
      have eBlk : t₁.blockNumber = s.blockNumber := by
        rw [hSeq]
      have eTot : totalBorrows t₁ = totalBorrows s := by
        rw [hSeq]
        rfl
      generalize hI : ({ t₁ with supplyState := { t₁.supplyState with speed := a } }) = mid at h
      have eBorM : mid.borrowState = s.borrowState := by
        rw [←hI]
        exact eBor
      have eBlkM : mid.blockNumber = s.blockNumber := by
        rw [←hI]
        exact eBlk
      have eTotM : totalBorrows mid = totalBorrows s := by
        rw [←hI]
        exact eTot
      unfold setBorrowSpeed at h
      by_cases hsb : mid.borrowState.speed ≠ b
      · rw [if_pos hsb] at h
        cases huB : updateCompBorrowIndex mid with
        | none =>
          rw [huB, peel_map_none] at h
          cases h
        | some u₁ =>
          rw [huB, peel_map_some] at h
          obtain ⟨hbbB, hSeqB⟩ := upd_borrow_some mid u₁ huB
          have hsbB : s.borrowState.speed ≠ b := by
            rw [←eBorM]
            exact hsb
          have hbbB' : s.borrowState.block ≤ s.blockNumber := by
            rw [←eBorM, ←eBlkM]
            exact hbbB
          have hS : (fun t => { t with borrowState := { t.borrowState with speed := b } }) u₁ = s' := Option.some_inj.mp h
          subst hS
          subst hSeqB
          subst hI
          subst hSeq
          refine ⟨?_, ?_, ?_⟩
          · intro _
            exact hbS
          · intro _
            exact hbbB'
          · rw [if_neg hs, if_neg hsbB]
            rfl
      · rw [if_neg hsb] at h
        have hS : mid = s' := Option.some_inj.mp h
        have hsbB : s.borrowState.speed = b := by
          by_cases he : s.borrowState.speed = b
          · exact he
          · rw [←eBorM] at he
            exact (hsb he).elim
        subst hS
        subst hI
        subst hSeq
        refine ⟨?_, ?_, ?_⟩
        · intro _
          exact hbS
        · intro hneB
          exact (hneB hsbB).elim
        · rw [if_neg hs, if_pos hsbB]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  obtain ⟨hbS, hbB, hrec⟩ := hc
  cases c with
  | supplyHook who =>
    have hrecS : (s.acct who).supplierIndex ≤ s.supplyState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).1
      · rw [hm]
        exact Nat.zero_le _
    have hle : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      start_le_accrued s.supplyState s.blockNumber (totalSupply s) _ hrecS
    have hXeq := upd_supply_eq_of s hbS
    have hleX : accrualStart (({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).acct who).supplierIndex ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState).index) ≤ ((({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }).supplyState).index) := hle
    simp only [comptroller, hXeq, peel_some, dist_supply_eq_of _ who hleX]
    rfl
  | borrowHook who =>
    have hrecB : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).2
      · rw [hm]
        exact Nat.zero_le _
    have hle : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      start_le_accrued s.borrowState s.blockNumber (totalBorrows s) _ hrecB
    have hXeq := upd_borrow_eq_of s hbB
    have hleX : accrualStart ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).acct who).borrowerIndex) ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState).index) ≤ ((({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }).borrowState).index) := hle
    simp only [comptroller, hXeq, peel_some, dist_borrow_eq_of _ who hleX]
    rfl
  | claim who =>
    have hrecS : (s.acct who).supplierIndex ≤ s.supplyState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).1
      · rw [hm]
        exact Nat.zero_le _
    have hrecB : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
      unfold St.acct
      rcases ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct with hm | hm
      · exact (hrec _ hm).2
      · rw [hm]
        exact Nat.zero_le _
    simp only [comptroller, claimComp]
    cases hu1 : updateCompBorrowIndex s with
    | none =>
      rw [upd_borrow_eq_of s hbB] at hu1
      cases hu1
    | some t₁ =>
      rw [peel_some]
      have hSeq1 : t₁ = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } :=
        Option.some_inj.mp (hu1.symm.trans (upd_borrow_eq_of s hbB))
      have e_acct1 : t₁.acct who = s.acct who := by
        rw [hSeq1]
        rfl
      have e_bidx1 : t₁.borrowState.index = (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
        rw [hSeq1]
      have hrecB1 : (t₁.acct who).borrowerIndex ≤ t₁.borrowState.index := by
        rw [e_acct1, e_bidx1]
        exact Nat.le_trans hrecB (accrueSide_le_index _ _ _)
      have hle1 : accrualStart (t₁.acct who).borrowerIndex t₁.borrowState.index ≤ t₁.borrowState.index :=
        accrualStart_le_of_le _ _ hrecB1
      cases hd1 : distributeBorrowerComp t₁ who with
      | none =>
        rw [dist_borrow_eq_of t₁ who hle1] at hd1
        cases hd1
      | some t₂ =>
        rw [peel_some]
        have hSeq2 : t₂ = t₁.withAcct who (fun a => { a with borrowerIndex := t₁.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex t₁.borrowState.index) t₁.borrowState.index }) :=
          Option.some_inj.mp (hd1.symm.trans (dist_borrow_eq_of t₁ who hle1))
        have e_sup2 : t₂.supplyState = s.supplyState := by
          rw [hSeq2, hSeq1]
          rfl
        have e_blk2 : t₂.blockNumber = s.blockNumber := by
          rw [hSeq2, hSeq1]
          rfl
        have hbS2 : t₂.supplyState.block ≤ t₂.blockNumber := by
          rw [hSeq2, hSeq1]
          exact hbS
        cases hu2 : updateCompSupplyIndex t₂ with
        | none =>
          rw [upd_supply_eq_of t₂ hbS2] at hu2
          cases hu2
        | some t₃ =>
          rw [peel_some]
          have hSeq3 : t₃ = { t₂ with supplyState := accrueSide t₂.supplyState t₂.blockNumber (totalSupply t₂) } :=
            Option.some_inj.mp (hu2.symm.trans (upd_supply_eq_of t₂ hbS2))
          have e_acct3 : t₃.acct who = t₂.acct who := by
            rw [hSeq3]
            rfl
          have e_sidx3 : t₃.supplyState.index = (accrueSide t₂.supplyState t₂.blockNumber (totalSupply t₂)).index := by
            rw [hSeq3]
          have k1 : (t₂.acct who).supplierIndex = (t₁.acct who).supplierIndex := by
            rw [hSeq2]
            apply withAcct_keeps
            intro a
            rfl
          have k2 : (t₁.acct who).supplierIndex = (s.acct who).supplierIndex := by
            rw [e_acct1]
          have hrecS3 : (t₃.acct who).supplierIndex ≤ t₃.supplyState.index := by
            have g1 : (t₃.acct who).supplierIndex = (s.acct who).supplierIndex := by
              rw [e_acct3, k1, k2]
            have g2 : s.supplyState.index ≤ t₃.supplyState.index := by
              rw [e_sidx3, e_sup2]
              exact accrueSide_le_index _ _ _
            rw [g1]
            exact Nat.le_trans hrecS g2
          have hle3 : accrualStart (t₃.acct who).supplierIndex t₃.supplyState.index ≤ t₃.supplyState.index :=
            accrualStart_le_of_le _ _ hrecS3
          cases hd2 : distributeSupplierComp t₃ who with
          | none =>
            rw [dist_supply_eq_of t₃ who hle3] at hd2
            cases hd2
          | some t₄ =>
            rw [peel_some, peel_pure]
            rfl
  | setSpeeds a b =>
    simp only [comptroller, setCompSpeedInternal]
    by_cases hs : s.supplyState.speed = a
    · have hne : ¬ s.supplyState.speed ≠ a := fun hne => hne hs
      unfold setSupplySpeed
      rw [if_neg hne, peel_obind_some]
      by_cases hsb : s.borrowState.speed = b
      · have hne2 : ¬ s.borrowState.speed ≠ b := fun hne => hne hsb
        unfold setBorrowSpeed
        rw [if_neg hne2]
        rfl
      · unfold setBorrowSpeed
        rw [if_pos hsb]
        cases hu : updateCompBorrowIndex s with
        | none =>
          rw [upd_borrow_eq_of s hbB] at hu
          cases hu
        | some t₁ =>
          rw [peel_map_some]
          rfl
    · have hpos : s.supplyState.speed ≠ a := fun heq => hs heq
      unfold setSupplySpeed
      rw [if_pos hpos]
      cases hu : updateCompSupplyIndex s with
      | none =>
        rw [upd_supply_eq_of s hbS] at hu
        cases hu
      | some t₁ =>
        rw [peel_map_some, peel_obind_some]
        have hSeq : t₁ = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } :=
          Option.some_inj.mp (hu.symm.trans (upd_supply_eq_of s hbS))
        have eBor : t₁.borrowState = s.borrowState := by
          rw [hSeq]
        have eBlk : t₁.blockNumber = s.blockNumber := by
          rw [hSeq]
        generalize hI : ({ t₁ with supplyState := { t₁.supplyState with speed := a } }) = mid
        have eBorM : mid.borrowState = s.borrowState := by
          rw [←hI]
          exact eBor
        have eBlkM : mid.blockNumber = s.blockNumber := by
          rw [←hI]
          exact eBlk
        have hbBM : mid.borrowState.block ≤ mid.blockNumber := by
          rw [eBorM, eBlkM]
          exact hbB
        unfold setBorrowSpeed
        by_cases hsb : mid.borrowState.speed ≠ b
        · rw [if_pos hsb]
          cases huB : updateCompBorrowIndex mid with
          | none =>
            rw [upd_borrow_eq_of mid hbBM] at huB
            cases huB
          | some u₁ =>
            rw [peel_map_some]
            rfl
        · rw [if_neg hsb]
          rfl
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
