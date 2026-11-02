import CompRewards.Spec
import ProofForgeFin.DeFi.Rewards
import ProofForgeFin.Accumulator.Index
import ProofForgeFin.Accumulator.Potential
import ProofForgeFin.Accumulator.Runs
import ProofForgeFin.Ledger
import ProofForgeFin.Seq
/-!
Fixed COMP distribution: Proposal 64 condition (`>= compInitialIndex`).
-/
namespace CompRewards

open ProofForgeFin ProofForgeFin.DeFi.Rewards ProofForgeFin.Accumulator ProofForgeFin.Ledger

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
      some { s with supplyState :=
        { s.supplyState with index := s.supplyState.index +
            (if totalSupply s > 0 then fraction (deltaBlocks * s.supplyState.speed)
              (totalSupply s) else 0), block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with supplyState := { s.supplyState with block := s.blockNumber } }
    else some s

/-- `updateCompBorrowIndex(cToken, marketBorrowIndex)`. -/
def updateCompBorrowIndex (s : St) : Option St :=
  match subChecked s.blockNumber s.borrowState.block with
  | none => none
  | some deltaBlocks =>
    if deltaBlocks > 0 ∧ s.borrowState.speed > 0 then
      some { s with borrowState :=
        { s.borrowState with index := s.borrowState.index +
            (if totalBorrows s > 0 then fraction (deltaBlocks * s.borrowState.speed)
              (totalBorrows s) else 0), block := s.blockNumber } }
    else if deltaBlocks > 0 then
      some { s with borrowState := { s.borrowState with block := s.blockNumber } }
    else some s

/-- `distributeSupplierComp(cToken, supplier)`. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  match subChecked s.supplyState.index
      (accrualStart (s.acct supplier).supplierIndex s.supplyState.index) with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  match subChecked s.borrowState.index
      (accrualStart (s.acct borrower).borrowerIndex s.borrowState.index) with
  | none => none
  | some _ =>
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })

/-- `compAccrued[user] = grantCompInternal(user, compAccrued[user])`. -/
def grantCompInternal (s : St) (user : Account) : St :=
  let amount := (s.acct user).accrued
  if amount > 0 ∧ amount ≤ s.reserve then
    { s with reserve := s.reserve - amount,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
  else s

/-- `claimComp([holder], [market], true, true)`. -/
def claimComp (s : St) (holder : Account) : Option St :=
  (updateCompBorrowIndex s).bind fun s =>
  (distributeBorrowerComp s holder).bind fun s =>
  (updateCompSupplyIndex s).bind fun s =>
  (distributeSupplierComp s holder).bind fun s =>
  some (grantCompInternal s holder)

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

theorem one_pos : 0 < doubleScale := by
  unfold doubleScale
  exact Nat.pow_pos (by decide)

theorem init_eq_one : compInitialIndex = doubleScale := rfl

theorem accrualStart_eq_firstStart (recorded index : Nat) :
    accrualStart recorded index = firstStart compInitialIndex recorded index := by
  unfold accrualStart firstStart
  rfl

theorem subChecked_some {a b : Nat} (h : b ≤ a) : subChecked a b = some (a - b) := by
  unfold subChecked
  simp [h]

theorem subChecked_none {a b : Nat} (h : ¬ b ≤ a) : subChecked a b = none := by
  unfold subChecked
  simp [h]

theorem accrueSide_index (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      sd.index + (if 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total then
        (now - sd.block) * sd.speed * doubleScale / total else 0) := by
  unfold accrueSide
  split
  · simp
  · simp

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split <;> simp

theorem accrueSide_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  rw [accrueSide_index]
  omega

theorem updateSupply_of_le (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  have hs : subChecked s.blockNumber s.supplyState.block =
      some (s.blockNumber - s.supplyState.block) := subChecked_some h
  unfold updateCompSupplyIndex
  rw [hs]
  simp only
  by_cases hd : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
  · have hd' : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 := hd
    rw [if_pos hd']
    by_cases ht : totalSupply s > 0
    · have ht2 : 0 < totalSupply s := ht
      rw [if_pos ht]
      have hspec : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < (s.accts.map Acct.supply).sum := ⟨hd.1, hd.2, ht2⟩
      unfold accrueSide totalSupply fraction
      rw [if_pos hspec]
    · have ht2 : ¬ 0 < totalSupply s := ht
      rw [if_neg ht]
      have hspec : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by omega
      unfold accrueSide
      rw [if_neg hspec]
      simp only [Nat.add_zero]
  · have hd2 : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := hd
    rw [if_neg hd2]
    by_cases hd3 : s.blockNumber - s.supplyState.block > 0
    · rw [if_pos hd3]
      have hspec : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by omega
      unfold accrueSide
      rw [if_neg hspec]
    · rw [if_neg hd3]
      have hbeq : s.supplyState.block = s.blockNumber := by omega
      have hspec : ¬ (0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
          0 < totalSupply s) := by omega
      unfold accrueSide
      rw [if_neg hspec]
      cases s with | mk bn sup bor res ac =>
      cases sup with | mk si sb ss =>
      have hsb : sb = bn := hbeq
      subst hsb
      rfl

theorem updateSupply_of_gt (s : St) (h : s.blockNumber < s.supplyState.block) :
    updateCompSupplyIndex s = none := by
  have hs : ¬ s.supplyState.block ≤ s.blockNumber := by omega
  have : subChecked s.blockNumber s.supplyState.block = none := subChecked_none hs
  unfold updateCompSupplyIndex
  rw [this]

theorem updateBorrow_of_le (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    updateCompBorrowIndex s =
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  have hs : subChecked s.blockNumber s.borrowState.block =
      some (s.blockNumber - s.borrowState.block) := subChecked_some h
  unfold updateCompBorrowIndex
  rw [hs]
  simp only
  by_cases hd : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
  · have hd' : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := hd
    rw [if_pos hd']
    by_cases ht : totalBorrows s > 0
    · have ht2 : 0 < totalBorrows s := ht
      rw [if_pos ht]
      have hspec : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < (s.accts.map Acct.borrow).sum := ⟨hd.1, hd.2, ht2⟩
      unfold accrueSide totalBorrows fraction
      rw [if_pos hspec]
    · have ht2 : ¬ 0 < totalBorrows s := ht
      rw [if_neg ht]
      have hspec : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by omega
      unfold accrueSide
      rw [if_neg hspec]
      simp only [Nat.add_zero]
  · have hd2 : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := hd
    rw [if_neg hd2]
    by_cases hd3 : s.blockNumber - s.borrowState.block > 0
    · rw [if_pos hd3]
      have hspec : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by omega
      unfold accrueSide
      rw [if_neg hspec]
    · rw [if_neg hd3]
      have hbeq : s.borrowState.block = s.blockNumber := by omega
      have hspec : ¬ (0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
          0 < totalBorrows s) := by omega
      unfold accrueSide
      rw [if_neg hspec]
      cases s with | mk bn sup bor res ac =>
      cases bor with | mk bi bb bs =>
      have hbb : bb = bn := hbeq
      subst hbb
      rfl

theorem updateBorrow_of_gt (s : St) (h : s.blockNumber < s.borrowState.block) :
    updateCompBorrowIndex s = none := by
  have hs : ¬ s.borrowState.block ≤ s.blockNumber := by omega
  have : subChecked s.blockNumber s.borrowState.block = none := subChecked_none hs
  unfold updateCompBorrowIndex
  rw [this]

theorem supplierStart_eq (s : St) (who : Account) :
    (if (s.acct who).supplierIndex = 0 ∧ compInitialIndex ≤ s.supplyState.index
      then compInitialIndex else (s.acct who).supplierIndex) =
      accrualStart (s.acct who).supplierIndex s.supplyState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).supplierIndex = 0
  · simp [h0]
  · simp [h0]

theorem borrowerStart_eq (s : St) (who : Account) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) =
      accrualStart (s.acct who).borrowerIndex s.borrowState.index := by
  unfold accrualStart
  by_cases h0 : (s.acct who).borrowerIndex = 0
  · simp [h0]
  · simp [h0]

theorem modify_congr {α : Type} (l : List α) (i : Nat) (f g : α → α) (d : α)
    (h : f (l.getD i d) = g (l.getD i d)) : l.modify i f = l.modify i g := by
  induction l generalizing i with
  | nil =>
    simp only [List.getD_nil] at h
    cases i with
    | zero => simp [h]
    | succ i => simp
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.modify_zero_cons, List.getD_cons_zero] at h ⊢
      rw [h]
    | succ i =>
      simp only [List.modify_succ_cons, List.getD_cons_succ] at h ⊢
      rw [ih _ h]

theorem distributeSupply_of_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who = some (s.withAcct who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index }) := by
  unfold distributeSupplierComp
  rw [subChecked_some h]

theorem distributeSupply_of_gt (s : St) (who : Account)
    (h : s.supplyState.index < accrualStart (s.acct who).supplierIndex s.supplyState.index) :
    distributeSupplierComp s who = none := by
  unfold distributeSupplierComp
  simp only [subChecked_none (by omega : ¬ accrualStart (s.acct who).supplierIndex
    s.supplyState.index ≤ s.supplyState.index)]

theorem distributeBorrow_of_le (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index) :
    distributeBorrowerComp s who = some (s.withAcct who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index }) := by
  unfold distributeBorrowerComp
  rw [subChecked_some h]

theorem distributeBorrow_of_gt (s : St) (who : Account)
    (h : s.borrowState.index < accrualStart (s.acct who).borrowerIndex s.borrowState.index) :
    distributeBorrowerComp s who = none := by
  unfold distributeBorrowerComp
  simp only [subChecked_none (by omega : ¬ accrualStart (s.acct who).borrowerIndex
    s.borrowState.index ≤ s.borrowState.index)]

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := by
  unfold grantCompInternal grant St.acct
  rfl

theorem withAcct_acct_of_lt (s : St) (who : Account) (f : Acct → Acct)
    (h : who < s.accts.length) :
    (s.withAcct who f).acct who = f (s.acct who) :=
  Ledger.getD_modify_self s.accts who f noAcct h

theorem withAcct_acct_of_ge (s : St) (who : Account) (f : Acct → Acct)
    (h : s.accts.length ≤ who) :
    (s.withAcct who f).acct who = s.acct who := by
  unfold St.withAcct St.acct
  rw [Ledger.modify_of_length_le _ _ h]

theorem withAcct_other_acct (s : St) (who v : Account) (f : Acct → Acct) (h : who ≠ v) :
    (s.withAcct who f).acct v = s.acct v := by
  unfold St.withAcct St.acct
  exact Ledger.getD_modify_ne s.accts f noAcct h

theorem withAcct_block (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).blockNumber = s.blockNumber := rfl

theorem withAcct_supplyState (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).supplyState = s.supplyState := rfl

theorem withAcct_borrowState (s : St) (who : Account) (f : Acct → Acct) :
    (s.withAcct who f).borrowState = s.borrowState := rfl

theorem hookSupply_eq (s : St) (who : Account) :
    comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind fun s => distributeSupplierComp s who := rfl

theorem hookBorrow_eq (s : St) (who : Account) :
    comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind fun s => distributeBorrowerComp s who := rfl

theorem hookClaim_eq (s : St) (who : Account) :
    comptroller s (.claim who) = claimComp s who := rfl

theorem hookSpeeds_eq (s : St) (a b : Nat) :
    comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' hs'
  rw [hookSupply_eq] at hs'
  cases hupd : updateCompSupplyIndex s with
  | none =>
    rw [hupd] at hs'
    simp at hs'
  | some s1 =>
    rw [hupd] at hs'
    simp only [Option.bind_some] at hs'
    have hb : s.supplyState.block ≤ s.blockNumber := by
      by_cases hbb : s.supplyState.block ≤ s.blockNumber
      · exact hbb
      · have hn : updateCompSupplyIndex s = none := updateSupply_of_gt s (by omega)
        rw [hn] at hupd
        simp at hupd
    rw [updateSupply_of_le s hb] at hupd
    by_cases hss : accrualStart (s1.acct who).supplierIndex (s1.supplyState.index) ≤
        s1.supplyState.index
    · rw [distributeSupply_of_le s1 who hss] at hs'
      cases hs'
      cases hupd
      have hstart : accrualStart (s.acct who).supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := hss
      exact ⟨hb, hstart, rfl⟩
    · have hn := distributeSupply_of_gt s1 who (by omega)
      rw [hn] at hs'
      simp at hs'

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' hs'
  rw [hookBorrow_eq] at hs'
  cases hupd : updateCompBorrowIndex s with
  | none =>
    rw [hupd] at hs'
    simp at hs'
  | some s1 =>
    rw [hupd] at hs'
    simp only [Option.bind_some] at hs'
    have hb : s.borrowState.block ≤ s.blockNumber := by
      by_cases hbb : s.borrowState.block ≤ s.blockNumber
      · exact hbb
      · have hn : updateCompBorrowIndex s = none := updateBorrow_of_gt s (by omega)
        rw [hn] at hupd
        simp at hupd
    rw [updateBorrow_of_le s hb] at hupd
    by_cases hss : accrualStart (s1.acct who).borrowerIndex (s1.borrowState.index) ≤
        s1.borrowState.index
    · rw [distributeBorrow_of_le s1 who hss] at hs'
      cases hs'
      cases hupd
      have hstart : accrualStart (s.acct who).borrowerIndex
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := hss
      exact ⟨hb, hstart, rfl⟩
    · have hn := distributeBorrow_of_gt s1 who (by omega)
      rw [hn] at hs'
      simp at hs'

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' hs'
  rw [hookClaim_eq] at hs'
  unfold claimComp at hs'
  cases hb1 : updateCompBorrowIndex s with
  | none =>
    rw [hb1] at hs'
    simp at hs'
  | some t0 =>
    rw [hb1] at hs'
    simp only [Option.bind_some] at hs'
    cases hd1 : distributeBorrowerComp t0 who with
    | none =>
      rw [hd1] at hs'
      simp at hs'
    | some d1 =>
      rw [hd1] at hs'
      simp only [Option.bind_some] at hs'
      cases hb2 : updateCompSupplyIndex d1 with
      | none =>
        rw [hb2] at hs'
        simp at hs'
      | some t1 =>
        rw [hb2] at hs'
        simp only [Option.bind_some] at hs'
        cases hd2 : distributeSupplierComp t1 who with
        | none =>
          rw [hd2] at hs'
          simp at hs'
        | some d2 =>
          rw [hd2] at hs'
          simp only [Option.bind_some] at hs'
          have hbB : s.borrowState.block ≤ s.blockNumber := by
            by_cases hbb : s.borrowState.block ≤ s.blockNumber
            · exact hbb
            · have hn : updateCompBorrowIndex s = none := updateBorrow_of_gt s (by omega)
              rw [hn] at hb1
              simp at hb1
          rw [updateBorrow_of_le s hbB] at hb1
          by_cases hssB : accrualStart (t0.acct who).borrowerIndex (t0.borrowState.index) ≤
              t0.borrowState.index
          · rw [distributeBorrow_of_le t0 who hssB] at hd1
            have hbS : d1.supplyState.block ≤ d1.blockNumber := by
              by_cases hbb : d1.supplyState.block ≤ d1.blockNumber
              · exact hbb
              · have hn : updateCompSupplyIndex d1 = none := updateSupply_of_gt d1 (by omega)
                rw [hn] at hb2
                simp at hb2
            rw [updateSupply_of_le d1 hbS] at hb2
            by_cases hssS : accrualStart (t1.acct who).supplierIndex (t1.supplyState.index) ≤
                t1.supplyState.index
            · rw [distributeSupply_of_le t1 who hssS] at hd2
              cases hb2
              have hsS : accrualStart (d1.acct who).supplierIndex
                  (accrueSide d1.supplyState d1.blockNumber (totalSupply d1)).index ≤
                  (accrueSide d1.supplyState d1.blockNumber (totalSupply d1)).index := hssS
              cases hd2
              cases hs'
              cases hd1
              cases hb1
              have hsB : accrualStart (s.acct who).borrowerIndex
                  (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
                  (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := hssB
              exact ⟨_, _, ⟨hbB, hsB, rfl⟩, ⟨hbS, hsS, rfl⟩, grant_eq _ _⟩
            · have hn := distributeSupply_of_gt t1 who (by omega)
              rw [hn] at hd2
              simp at hd2
          · have hn := distributeBorrow_of_gt t0 who (by omega)
            rw [hn] at hd1
            simp at hd1

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' hs'
  rw [hookSpeeds_eq] at hs'
  unfold setCompSpeedInternal at hs'
  cases hsup : setSupplySpeed s a with
  | none =>
    rw [hsup] at hs'
    simp at hs'
  | some t1 =>
    rw [hsup] at hs'
    simp only [Option.bind_some] at hs'
    cases hbor : setBorrowSpeed t1 b with
    | none =>
      rw [hbor] at hs'
      simp at hs'
    | some t2 =>
      rw [hbor] at hs'
      unfold setSupplySpeed at hsup
      unfold setBorrowSpeed at hbor
      by_cases heqS : s.supplyState.speed = a
      · have hcS : ¬ s.supplyState.speed ≠ a := fun hh => hh heqS
        rw [if_neg hcS] at hsup
        cases hsup
        by_cases heqB : s.borrowState.speed = b
        · have hcB : ¬ s.borrowState.speed ≠ b := fun hh => hh heqB
          rw [if_neg hcB] at hbor
          cases hbor
          cases hs'
          refine ⟨fun hh => absurd hh hcS, fun hh => absurd hh hcB, ?_⟩
          rw [if_pos heqS, if_pos heqB]
        · have hcB : s.borrowState.speed ≠ b := heqB
          rw [if_pos hcB] at hbor
          have hbB : s.borrowState.block ≤ s.blockNumber := by
            by_cases hbb : s.borrowState.block ≤ s.blockNumber
            · exact hbb
            · have hn : updateCompBorrowIndex s = none := updateBorrow_of_gt s (by omega)
              rw [hn] at hbor
              simp at hbor
          rw [updateBorrow_of_le s hbB] at hbor
          simp only [Option.map_some] at hbor
          cases hbor
          cases hs'
          refine ⟨fun hh => absurd hh hcS, fun _ => hbB, ?_⟩
          rw [if_pos heqS, if_neg hcB]
      · have hcS : s.supplyState.speed ≠ a := heqS
        rw [if_pos hcS] at hsup
        have hbS : s.supplyState.block ≤ s.blockNumber := by
          by_cases hbb : s.supplyState.block ≤ s.blockNumber
          · exact hbb
          · have hn : updateCompSupplyIndex s = none := updateSupply_of_gt s (by omega)
            rw [hn] at hsup
            simp at hsup
        rw [updateSupply_of_le s hbS] at hsup
        simp only [Option.map_some] at hsup
        by_cases heqB : t1.borrowState.speed = b
        · have hcB : ¬ t1.borrowState.speed ≠ b := fun hh => hh heqB
          rw [if_neg hcB] at hbor
          cases hbor
          cases hs'
          cases hsup
          have heqB' : s.borrowState.speed = b := heqB
          refine ⟨fun _ => hbS, fun hh => absurd heqB' hh, ?_⟩
          rw [if_neg hcS, if_pos heqB']
        · have hcB : t1.borrowState.speed ≠ b := heqB
          rw [if_pos hcB] at hbor
          have hbB : t1.borrowState.block ≤ t1.blockNumber := by
            by_cases hbb : t1.borrowState.block ≤ t1.blockNumber
            · exact hbb
            · have hn : updateCompBorrowIndex t1 = none := updateBorrow_of_gt t1 (by omega)
              rw [hn] at hbor
              simp at hbor
          rw [updateBorrow_of_le t1 hbB] at hbor
          simp only [Option.map_some] at hbor
          cases hbor
          cases hs'
          cases hsup
          have heqB' : s.borrowState.speed ≠ b := heqB
          have hbB' : s.borrowState.block ≤ s.blockNumber := hbB
          refine ⟨fun _ => hbS, fun _ => hbB', ?_⟩
          rw [if_neg hcS, if_neg heqB']
          rfl

theorem start_le_new (rec oldIdx newIdx : Nat) (hold : rec ≤ oldIdx) (hle : oldIdx ≤ newIdx) :
    accrualStart rec newIdx ≤ newIdx := by
  unfold accrualStart
  by_cases h0 : rec = 0
  · subst h0
    rw [if_pos rfl]
    by_cases hi : compInitialIndex ≤ newIdx
    · rw [if_pos hi]
      exact hi
    · rw [if_neg hi]
      exact Nat.zero_le _
  · rw [if_neg h0]
    omega

theorem getD_eq_default_of_ge (l : List Acct) (i : Nat) (h : l.length ≤ i) :
    l.getD i noAcct = noAcct := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      simp only [List.getD_cons_succ]
      have h2 : l.length ≤ i := by simpa using h
      exact ih i h2

theorem recorded_supply_le (s : St) (who : Account)
    (hcon : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  rcases Ledger.getD_mem_or s.accts who noAcct with hmem | hno
  · exact hcon _ hmem
  · have hN : s.acct who = noAcct := hno
    rw [hN]
    exact Nat.zero_le _

theorem recorded_borrow_le (s : St) (who : Account)
    (hcon : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  rcases Ledger.getD_mem_or s.accts who noAcct with hmem | hno
  · exact hcon _ hmem
  · have hN : s.acct who = noAcct := hno
    rw [hN]
    exact Nat.zero_le _

theorem withAcct_supplierIndex (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by
  by_cases hm : who < s.accts.length
  · rw [withAcct_acct_of_lt _ _ _ hm]
    exact hf _
  · have hmg : s.accts.length ≤ who := by
      have hmc := hm
      simp at hmc
      exact hmc
    rw [withAcct_acct_of_ge _ _ _ hmg]

/-- One account's potential term at supply index `si` and borrow index `bi`: credited COMP at
scale plus pending on both sides (from `firstStart`, the safe start). -/
def potTerm (si bi : Nat) (a : Acct) : Nat :=
  a.accrued * doubleScale + a.wallet * doubleScale + pending a.supply (firstStart compInitialIndex a.supplierIndex si) si + pending a.borrow (firstStart compInitialIndex a.borrowerIndex bi) bi

/-- Global potential: every account's term plus unindexed emission at scale. -/
def pot (s : St) : Nat :=
  (s.accts.map fun a => potTerm s.supplyState.index s.borrowState.index a).sum + doubleScale * (unindexed s.supplyState.block s.supplyState.speed s.blockNumber + unindexed s.borrowState.block s.borrowState.speed s.blockNumber)

/-- Per-account potential: its term plus unindexed emission where it holds a position. -/
def potTo (s : St) (who : Account) : Nat :=
  potTerm s.supplyState.index s.borrowState.index (s.acct who) + doubleScale * ((if 0 < (s.acct who).supply then unindexed s.supplyState.block s.supplyState.speed s.blockNumber else 0) + (if 0 < (s.acct who).borrow then unindexed s.borrowState.block s.borrowState.speed s.blockNumber else 0))

theorem creditFor_eq (units start index : Nat) :
    creditFor units start index = credit doubleScale units start index := rfl

theorem accrueSide_index_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      catchUp doubleScale sd.index sd.block sd.speed now total := by
  rw [accrueSide_index, catchUp_eq]

theorem legacyStart_eq_effStart (start recorded : Nat) :
    legacyStart start recorded = effStart start recorded := rfl

theorem accrueSide_speed_eq (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split <;> rfl

theorem supplyUpdate_pot_le (s : St) :
    pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ pot s := by
  have hle : s.supplyState.index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    accrueSide_le _ _ _
  have ht : ∀ a ∈ s.accts, potTerm ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index) s.borrowState.index a ≤ potTerm s.supplyState.index s.borrowState.index a + a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) := by
    intro a _
    have hmono := firstStart_mono compInitialIndex a.supplierIndex hle
    have h1 := owed_le_add (u := a.supply) (i := s.supplyState.index) (i' := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (s := firstStart compInitialIndex a.supplierIndex s.supplyState.index) (s' := firstStart compInitialIndex a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) hmono
    simp only [potTerm, pending]
    omega
  have hcov := covered_catchUp doubleScale s.supplyState.index s.supplyState.block s.supplyState.speed s.blockNumber (totalSupply s)
  rw [←accrueSide_index_eq] at hcov
  have hbud := accrue_budget (V := unindexed s.borrowState.block s.borrowState.speed s.blockNumber) hcov
  have hU : (s.accts.map Acct.supply).sum * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index - s.supplyState.index) + doubleScale * (0 + unindexed s.borrowState.block s.borrowState.speed s.blockNumber) ≤ doubleScale * (unindexed s.supplyState.block s.supplyState.speed s.blockNumber + unindexed s.borrowState.block s.borrowState.speed s.blockNumber) := hbud
  have hS := sum_le_of_index_le s.accts (fun a => potTerm s.supplyState.index s.borrowState.index a) (fun a => potTerm (accrueSide s.supplyState s.blockNumber (totalSupply s)).index s.borrowState.index a) Acct.supply ht (Nat.le_refl _)
  have eU : unindexed (accrueSide s.supplyState s.blockNumber (totalSupply s)).block (accrueSide s.supplyState s.blockNumber (totalSupply s)).speed s.blockNumber = 0 := by
    rw [accrueSide_block, accrueSide_speed_eq]
    exact unindexed_self _ _
  unfold pot
  dsimp only
  rw [eU]
  omega

theorem supplySettleTerm_le (a : Acct) (i b : Nat) :
    potTerm i b { a with supplierIndex := i, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex i) i } ≤ potTerm i b a := by
  have hq : accrualStart a.supplierIndex i = firstStart compInitialIndex a.supplierIndex i :=
    (accrualStart_eq_firstStart _ _).symm
  have hset := settle_scaled_le_of_le (one := doubleScale) (c := a.accrued + a.wallet) (u := a.supply) (i := i) (p := firstStart compInitialIndex a.supplierIndex i) (q := firstStart compInitialIndex a.supplierIndex i) (q' := firstStart compInitialIndex i i) (Nat.le_refl _) (le_firstStart_self compInitialIndex i)
  rw [hq]
  simp only [potTerm, pending, creditFor_eq, credit, Nat.add_mul] at hset ⊢
  omega

theorem supplySettle_pot_le (u : St) (who : Account) :
    pot (u.withAcct who fun a => { a with supplierIndex := u.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex u.supplyState.index) u.supplyState.index }) ≤ pot u := by
  have hsum : (((u.accts.modify who fun a => { a with supplierIndex := u.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex u.supplyState.index) u.supplyState.index }).map (potTerm u.supplyState.index u.borrowState.index)).sum ≤ (u.accts.map (potTerm u.supplyState.index u.borrowState.index)).sum) :=
    sum_map_modify_le u.accts who (fun a => { a with supplierIndex := u.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex u.supplyState.index) u.supplyState.index }) (potTerm u.supplyState.index u.borrowState.index) noAcct (fun _ => supplySettleTerm_le (u.accts.getD who noAcct) u.supplyState.index u.borrowState.index)
  have hpotW : pot (u.withAcct who fun a => { a with supplierIndex := u.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex u.supplyState.index) u.supplyState.index }) = ((((u.accts.modify who fun a => { a with supplierIndex := u.supplyState.index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex u.supplyState.index) u.supplyState.index }).map (potTerm u.supplyState.index u.borrowState.index)).sum + doubleScale * (unindexed u.supplyState.block u.supplyState.speed u.blockNumber + unindexed u.borrowState.block u.borrowState.speed u.blockNumber))) := by
    unfold pot St.withAcct
    dsimp only
  have hpotU : pot u = (((u.accts.map (potTerm u.supplyState.index u.borrowState.index)).sum + doubleScale * (unindexed u.supplyState.block u.supplyState.speed u.blockNumber + unindexed u.borrowState.block u.borrowState.speed u.blockNumber))) := rfl
  rw [hpotW, hpotU]
  exact Nat.add_le_add_right hsum _

theorem supplyHook_pot (s s' : St) (who : Account) (h : SupplyDistributed s who s') :
    pot s' ≤ pot s := by
  obtain ⟨hb, hstart, hs'⟩ := h
  have hUpd : pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ≤ pot s :=
    supplyUpdate_pot_le s
  have hSet : pot s' ≤ pot { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
    rw [hs']
    exact supplySettle_pot_le { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who
  exact Nat.le_trans hSet hUpd

theorem borrowUpdate_pot_le (s : St) :
    pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤ pot s := by
  have hle : s.borrowState.index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    accrueSide_le _ _ _
  have ht : ∀ a ∈ s.accts, potTerm s.supplyState.index ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) a ≤ potTerm s.supplyState.index s.borrowState.index a + a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) := by
    intro a _
    have hmono := firstStart_mono compInitialIndex a.borrowerIndex hle
    have h1 := owed_le_add (u := a.borrow) (i := s.borrowState.index) (i' := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (s := firstStart compInitialIndex a.borrowerIndex s.borrowState.index) (s' := firstStart compInitialIndex a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) hmono
    simp only [potTerm, pending]
    omega
  have hcov := covered_catchUp doubleScale s.borrowState.index s.borrowState.block s.borrowState.speed s.blockNumber (totalBorrows s)
  rw [←accrueSide_index_eq] at hcov
  have hbud := accrue_budget (V := unindexed s.supplyState.block s.supplyState.speed s.blockNumber) hcov
  have hU : (s.accts.map Acct.borrow).sum * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index - s.borrowState.index) + doubleScale * (0 + unindexed s.supplyState.block s.supplyState.speed s.blockNumber) ≤ doubleScale * (unindexed s.supplyState.block s.supplyState.speed s.blockNumber + unindexed s.borrowState.block s.borrowState.speed s.blockNumber) := by
    rw [Nat.add_comm (unindexed s.supplyState.block s.supplyState.speed s.blockNumber) (unindexed s.borrowState.block s.borrowState.speed s.blockNumber)]
    exact hbud
  have hS := sum_le_of_index_le s.accts (fun a => potTerm s.supplyState.index s.borrowState.index a) (fun a => potTerm s.supplyState.index (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index a) Acct.borrow ht (Nat.le_refl _)
  have eU : unindexed (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block (accrueSide s.borrowState s.blockNumber (totalBorrows s)).speed s.blockNumber = 0 := by
    rw [accrueSide_block, accrueSide_speed_eq]
    exact unindexed_self _ _
  unfold pot
  dsimp only
  rw [eU, Nat.add_comm (unindexed s.supplyState.block s.supplyState.speed s.blockNumber) 0]
  omega

theorem borrowSettleTerm_le (a : Acct) (i b : Nat) :
    potTerm b i { a with borrowerIndex := i, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex i) i } ≤ potTerm b i a := by
  have hq : accrualStart a.borrowerIndex i = firstStart compInitialIndex a.borrowerIndex i :=
    (accrualStart_eq_firstStart _ _).symm
  have hset := settle_scaled_le_of_le (one := doubleScale) (c := a.accrued + a.wallet) (u := a.borrow) (i := i) (p := firstStart compInitialIndex a.borrowerIndex i) (q := firstStart compInitialIndex a.borrowerIndex i) (q' := firstStart compInitialIndex i i) (Nat.le_refl _) (le_firstStart_self compInitialIndex i)
  rw [hq]
  simp only [potTerm, pending, creditFor_eq, credit, Nat.add_mul] at hset ⊢
  omega

theorem borrowSettle_pot_le (u : St) (who : Account) :
    pot (u.withAcct who fun a => { a with borrowerIndex := u.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex u.borrowState.index) u.borrowState.index }) ≤ pot u := by
  have hsum : (((u.accts.modify who fun a => { a with borrowerIndex := u.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex u.borrowState.index) u.borrowState.index }).map (potTerm u.supplyState.index u.borrowState.index)).sum ≤ (u.accts.map (potTerm u.supplyState.index u.borrowState.index)).sum) :=
    sum_map_modify_le u.accts who (fun a => { a with borrowerIndex := u.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex u.borrowState.index) u.borrowState.index }) (potTerm u.supplyState.index u.borrowState.index) noAcct (fun _ => borrowSettleTerm_le (u.accts.getD who noAcct) u.borrowState.index u.supplyState.index)
  have hpotW : pot (u.withAcct who fun a => { a with borrowerIndex := u.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex u.borrowState.index) u.borrowState.index }) = ((((u.accts.modify who fun a => { a with borrowerIndex := u.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex u.borrowState.index) u.borrowState.index }).map (potTerm u.supplyState.index u.borrowState.index)).sum + doubleScale * (unindexed u.supplyState.block u.supplyState.speed u.blockNumber + unindexed u.borrowState.block u.borrowState.speed u.blockNumber))) := by
    unfold pot St.withAcct
    dsimp only
  have hpotU : pot u = (((u.accts.map (potTerm u.supplyState.index u.borrowState.index)).sum + doubleScale * (unindexed u.supplyState.block u.supplyState.speed u.blockNumber + unindexed u.borrowState.block u.borrowState.speed u.blockNumber))) := rfl
  rw [hpotW, hpotU]
  exact Nat.add_le_add_right hsum _

theorem borrowHook_pot (s s' : St) (who : Account) (h : BorrowDistributed s who s') :
    pot s' ≤ pot s := by
  obtain ⟨hb, hstart, hs'⟩ := h
  have hUpd : pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } ≤ pot s :=
    borrowUpdate_pot_le s
  have hSet : pot s' ≤ pot { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
    rw [hs']
    exact borrowSettle_pot_le { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who
  exact Nat.le_trans hSet hUpd

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hbs, hbb, hcon⟩ := hc
  cases c with
  | supplyHook who =>
    have hold := recorded_supply_le s who (fun a ha => (hcon a ha).1)
    have hle := accrueSide_le s.supplyState s.blockNumber (totalSupply s)
    have hstart := start_le_new _ _ _ hold hle
    have hU := updateSupply_of_le s hbs
    have hD := distributeSupply_of_le
      { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who hstart
    simp [hookSupply_eq, hU, hD, Option.bind_some]
  | borrowHook who =>
    have hold := recorded_borrow_le s who (fun a ha => (hcon a ha).2)
    have hle := accrueSide_le s.borrowState s.blockNumber (totalBorrows s)
    have hstart := start_le_new _ _ _ hold hle
    have hU := updateBorrow_of_le s hbb
    have hD := distributeBorrow_of_le
      { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who hstart
    simp [hookBorrow_eq, hU, hD, Option.bind_some]
  | claim who =>
    have holdB := recorded_borrow_le s who (fun a ha => (hcon a ha).2)
    have hleB := accrueSide_le s.borrowState s.blockNumber (totalBorrows s)
    have hstartB := start_le_new _ _ _ holdB hleB
    let t0 : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
    have hU1 : updateCompBorrowIndex s = some t0 := updateBorrow_of_le s hbb
    have hstartB' : accrualStart (t0.acct who).borrowerIndex (t0.borrowState.index) ≤
        t0.borrowState.index := hstartB
    let d1 : St := t0.withAcct who fun a => { a with borrowerIndex := t0.borrowState.index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex t0.borrowState.index) t0.borrowState.index }
    have hD1 : distributeBorrowerComp t0 who = some d1 :=
      distributeBorrow_of_le t0 who hstartB'
    have hbS : d1.supplyState.block ≤ d1.blockNumber := hbs
    let t1 : St := { d1 with supplyState := accrueSide d1.supplyState d1.blockNumber (totalSupply d1) }
    have hU2 : updateCompSupplyIndex d1 = some t1 := updateSupply_of_le d1 hbS
    have hrec : (t1.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have e1 : (t1.acct who).supplierIndex = (d1.acct who).supplierIndex := rfl
      have e2 : (d1.acct who).supplierIndex = (s.acct who).supplierIndex :=
        withAcct_supplierIndex t0 who _ (fun a => rfl)
      omega
    have holdS := recorded_supply_le s who (fun a ha => (hcon a ha).1)
    have holdS' : (t1.acct who).supplierIndex ≤ d1.supplyState.index := by
      rw [hrec]
      exact holdS
    have hleS' : d1.supplyState.index ≤ t1.supplyState.index := accrueSide_le _ _ _
    have hstartS := start_le_new _ _ _ holdS' hleS'
    have hD2 := distributeSupply_of_le t1 who hstartS
    simp [hookClaim_eq, claimComp, hU1, hD1, hU2, hD2, Option.bind_some]
  | setSpeeds a b =>
    by_cases heqS : s.supplyState.speed = a
    · have eS : setSupplySpeed s a = some s := by
        unfold setSupplySpeed
        rw [if_neg (fun hh => hh heqS)]
      by_cases heqB : s.borrowState.speed = b
      · have eB : setBorrowSpeed s b = some s := by
          unfold setBorrowSpeed
          rw [if_neg (fun hh => hh heqB)]
        simp [hookSpeeds_eq, setCompSpeedInternal, eS, eB, Option.bind_some]
      · have hU := updateBorrow_of_le s hbb
        let u : St := { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
        have hU' : updateCompBorrowIndex s = some u := hU
        have eB : setBorrowSpeed s b =
            some { u with borrowState := { u.borrowState with speed := b } } := by
          unfold setBorrowSpeed
          rw [if_pos heqB, hU']
          rfl
        simp [hookSpeeds_eq, setCompSpeedInternal, eS, eB, Option.bind_some]
    · have hU := updateSupply_of_le s hbs
      let X : St := { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
      have hU' : updateCompSupplyIndex s = some X := hU
      let t1 : St := { X with supplyState := { X.supplyState with speed := a } }
      have eS : setSupplySpeed s a = some t1 := by
        unfold setSupplySpeed
        rw [if_pos heqS, hU']
        rfl
      by_cases heqB : t1.borrowState.speed = b
      · have eB : setBorrowSpeed t1 b = some t1 := by
          unfold setBorrowSpeed
          rw [if_neg (fun hh => hh heqB)]
        simp [hookSpeeds_eq, setCompSpeedInternal, eS, eB, Option.bind_some]
      · have hbB : t1.borrowState.block ≤ t1.blockNumber := hbb
        have hV := updateBorrow_of_le t1 hbB
        let u : St := { t1 with borrowState := accrueSide t1.borrowState t1.blockNumber (totalBorrows t1) }
        have hV' : updateCompBorrowIndex t1 = some u := hV
        have eB : setBorrowSpeed t1 b =
            some { u with borrowState := { u.borrowState with speed := b } } := by
          unfold setBorrowSpeed
          rw [if_pos heqB, hV']
          rfl
        simp [hookSpeeds_eq, setCompSpeedInternal, eS, eB, Option.bind_some]
