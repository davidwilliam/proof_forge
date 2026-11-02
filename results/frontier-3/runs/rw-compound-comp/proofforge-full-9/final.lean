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

/-- `distributeSupplierComp(cToken, supplier)`, with the Proposal 64 start (`>=`): an
account with no recorded index starts at `compInitialIndex` once the market index has reached
it, exactly `accrualStart`. -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  match subChecked s.supplyState.index
      (accrualStart (s.acct supplier).supplierIndex s.supplyState.index) with
  | none => none
  | some _ =>
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply
                  (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })

/-- `distributeBorrowerComp(cToken, borrower, marketBorrowIndex)`, with the Proposal 64 start. -/
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
  if 0 < (s.acct user).accrued ∧ (s.acct user).accrued ≤ s.reserve then
    { s with reserve := s.reserve - (s.acct user).accrued,
             accts := s.accts.modify user fun a => { a with accrued := 0, wallet := a.wallet + a.accrued } }
  else s

/-- `claimComp([holder], [market], true, true)`. -/
def claimComp (s : St) (holder : Account) : Option St :=
  (updateCompBorrowIndex s).bind fun a =>
    (distributeBorrowerComp a holder).bind fun b =>
      (updateCompSupplyIndex b).bind fun c =>
        (distributeSupplierComp c holder).bind fun d =>
          some (grantCompInternal d holder)

/-- The supply branch of `setCompSpeedInternal`: when the supply speed changes, accrue at the
old speed, then store the new one. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    match updateCompSupplyIndex s with
    | none => none
    | some t => some { s with supplyState := { t.supplyState with speed := supplySpeed } }
  else some s

/-- The borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    match updateCompBorrowIndex s with
    | none => none
    | some t => some { s with borrowState := { t.borrowState with speed := borrowSpeed } }
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

/-! ## Helpers: the code matches the specification -/

theorem modify_congr {α : Type} (l : List α) (w : Nat) (f g : α → α) (d : α)
    (h : f (l.getD w d) = g (l.getD w d)) : l.modify w f = l.modify w g := by
  induction l generalizing w with
  | nil =>
    have e1 := ProofForgeFin.Ledger.modify_of_length_le (α := α) [] f (Nat.zero_le w)
    have e2 := ProofForgeFin.Ledger.modify_of_length_le (α := α) [] g (Nat.zero_le w)
    rw [e1, e2]
  | cons a l ih =>
    cases w with
    | zero =>
      simp only [List.getD_cons_zero] at h
      simp only [List.modify_zero_cons, h]
    | succ w =>
      simp only [List.getD_cons_succ] at h
      simp only [List.modify_succ_cons]
      rw [ih w h]

theorem updSup_eq (s : St) (t : St) (h : updateCompSupplyIndex s = some t) :
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    unfold accrueSide at *
    unfold fraction at h
    by_cases hd : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed ∧
      0 < totalSupply s
    · have hc1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 :=
        ⟨hd.1, hd.2.1⟩
      have htc : totalSupply s > 0 := hd.2.2
      rw [if_pos hc1, if_pos htc] at h
      rw [if_pos hd]
      exact (Option.some_inj.mp h).symm
    · simp only [hd, ↓reduceIte] at h ⊢
      by_cases hd1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
      · have hc1 : s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0 := hd1
        rw [if_pos hc1] at h
        by_cases ht : 0 < totalSupply s
        · exact absurd ⟨hd1.1, hd1.2, ht⟩ hd
        · have htc : ¬ totalSupply s > 0 := ht
          rw [if_neg htc] at h
          exact (Option.some_inj.mp h).symm
      · have hc1 : ¬ (s.blockNumber - s.supplyState.block > 0 ∧ s.supplyState.speed > 0) := hd1
        rw [if_neg hc1] at h
        by_cases hd2 : 0 < s.blockNumber - s.supplyState.block
        · have hc2 : s.blockNumber - s.supplyState.block > 0 := hd2
          rw [if_pos hc2] at h
          exact (Option.some_inj.mp h).symm
        · have hc2 : ¬ s.blockNumber - s.supplyState.block > 0 := hd2
          rw [if_neg hc2] at h
          have ht2 : t = s := (Option.some_inj.mp h).symm
          have hbb : s.supplyState.block = s.blockNumber := by omega
          rw [ht2]
          cases s with
          | mk bn sup bor res ac =>
            cases sup with
            | mk ix bl sp =>
              simp only at hbb ⊢
              rw [hbb]
  · simp only [hb, ↓reduceIte] at h
    cases h

theorem updBor_eq (s : St) (t : St) (h : updateCompBorrowIndex s = some t) :
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    unfold accrueSide at *
    unfold fraction at h
    by_cases hd : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed ∧
      0 < totalBorrows s
    · have hc1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 :=
        ⟨hd.1, hd.2.1⟩
      have htc : totalBorrows s > 0 := hd.2.2
      rw [if_pos hc1, if_pos htc] at h
      rw [if_pos hd]
      exact (Option.some_inj.mp h).symm
    · simp only [hd, ↓reduceIte] at h ⊢
      by_cases hd1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
      · have hc1 : s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0 := hd1
        rw [if_pos hc1] at h
        by_cases ht : 0 < totalBorrows s
        · exact absurd ⟨hd1.1, hd1.2, ht⟩ hd
        · have htc : ¬ totalBorrows s > 0 := ht
          rw [if_neg htc] at h
          exact (Option.some_inj.mp h).symm
      · have hc1 : ¬ (s.blockNumber - s.borrowState.block > 0 ∧ s.borrowState.speed > 0) := hd1
        rw [if_neg hc1] at h
        by_cases hd2 : 0 < s.blockNumber - s.borrowState.block
        · have hc2 : s.blockNumber - s.borrowState.block > 0 := hd2
          rw [if_pos hc2] at h
          exact (Option.some_inj.mp h).symm
        · have hc2 : ¬ s.blockNumber - s.borrowState.block > 0 := hd2
          rw [if_neg hc2] at h
          have ht2 : t = s := (Option.some_inj.mp h).symm
          have hbb : s.borrowState.block = s.blockNumber := by omega
          rw [ht2]
          cases s with
          | mk bn sup bor res ac =>
            cases bor with
            | mk ix bl sp =>
              simp only at hbb ⊢
              rw [hbb]
  · simp only [hb, ↓reduceIte] at h
    cases h

theorem updSup_block (s : St) (t : St) (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber := by
  unfold updateCompSupplyIndex subChecked at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte] at h
    cases h

theorem updBor_block (s : St) (t : St) (h : updateCompBorrowIndex s = some t) :
    s.borrowState.block ≤ s.blockNumber := by
  unfold updateCompBorrowIndex subChecked at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · exact hb
  · simp only [hb, ↓reduceIte] at h
    cases h

theorem distSup_eq (s : St) (who : Account) (t : St)
    (h : distributeSupplierComp s who = some t) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    t = s.withAcct who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } := by
  unfold distributeSupplierComp subChecked at h
  by_cases hc : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
    s.supplyState.index
  · simp only [hc, ↓reduceIte] at h
    exact ⟨hc, (Option.some_inj.mp h).symm⟩
  · simp only [hc, ↓reduceIte] at h
    cases h

theorem distBor_eq (s : St) (who : Account) (t : St)
    (h : distributeBorrowerComp s who = some t) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    t = s.withAcct who fun a =>
      { a with
        borrowerIndex := s.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } := by
  unfold distributeBorrowerComp subChecked at h
  by_cases hc : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
    s.borrowState.index
  · simp only [hc, ↓reduceIte] at h
    exact ⟨hc, (Option.some_inj.mp h).symm⟩
  · simp only [hc, ↓reduceIte] at h
    cases h

theorem grant_eq (s : St) (who : Account) : grantCompInternal s who = grant s who := rfl

theorem distBor_keep_sup (s : St) (who w : Account) (v : St)
    (h : distributeBorrowerComp s who = some v) :
    (v.acct w).supplierIndex = (s.acct w).supplierIndex := by
  obtain ⟨_, heq⟩ := distBor_eq s who v h
  rw [heq]
  show (((s.accts.modify who (fun a =>
    { a with
      borrowerIndex := s.borrowState.index,
      accrued := a.accrued + creditFor a.borrow
        (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })).getD w noAcct).supplierIndex) = ((s.accts.getD w noAcct).supplierIndex)
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases hw : who = w ∧ w < s.accts.length
  · rw [if_pos hw]
  · rw [if_neg hw]

theorem distSup_keep_bor (s : St) (who w : Account) (v : St)
    (h : distributeSupplierComp s who = some v) :
    (v.acct w).borrowerIndex = (s.acct w).borrowerIndex := by
  obtain ⟨_, heq⟩ := distSup_eq s who v h
  rw [heq]
  show (((s.accts.modify who (fun a =>
    { a with
      supplierIndex := s.supplyState.index,
      accrued := a.accrued + creditFor a.supply
        (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })).getD w noAcct).borrowerIndex) = ((s.accts.getD w noAcct).borrowerIndex)
  rw [ProofForgeFin.Ledger.getD_modify]
  by_cases hw : who = w ∧ w < s.accts.length
  · rw [if_pos hw]
  · rw [if_neg hw]

theorem accrueSide_index_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [hc, ↓reduceIte]
    exact Nat.le_add_right _ _
  · simp only [hc, ↓reduceIte]
    exact Nat.le_refl _

theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem accrueSide_eq_catchUp (sd : Side) (now total : Nat) :
    (accrueSide sd now total).index =
      ProofForgeFin.Accumulator.catchUp doubleScale sd.index sd.block sd.speed now total := by
  unfold accrueSide ProofForgeFin.Accumulator.catchUp
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hc]
  · simp [hc]

theorem start_le_index (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  by_cases hr : recorded = 0
  · rw [if_pos hr]
    by_cases hi : compInitialIndex ≤ index
    · rw [if_pos hi]
      exact hi
    · rw [if_neg hi]
      exact Nat.zero_le _
  · rw [if_neg hr]
    exact h

theorem acct_rec_le (s : St)
    (h : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index ∧
      a.borrowerIndex ≤ s.borrowState.index) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  have hmem := ProofForgeFin.Ledger.getD_mem_or s.accts who noAcct
  show (s.accts.getD who noAcct).supplierIndex ≤ s.supplyState.index ∧
    (s.accts.getD who noAcct).borrowerIndex ≤ s.borrowState.index
  rcases hmem with hm | hm
  · exact h _ hm
  · rw [hm]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem updSup_some (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome := by
  unfold updateCompSupplyIndex subChecked
  simp only [h, ↓reduceIte]
  by_cases c1 : 0 < s.blockNumber - s.supplyState.block ∧ 0 < s.supplyState.speed
  · simp [c1]
  · simp only [c1, ↓reduceIte]
    by_cases c2 : 0 < s.blockNumber - s.supplyState.block
    · simp [c2]
    · simp [c2]

theorem updBor_some (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome := by
  unfold updateCompBorrowIndex subChecked
  simp only [h, ↓reduceIte]
  by_cases c1 : 0 < s.blockNumber - s.borrowState.block ∧ 0 < s.borrowState.speed
  · simp [c1]
  · simp only [c1, ↓reduceIte]
    by_cases c2 : 0 < s.blockNumber - s.borrowState.block
    · simp [c2]
    · simp [c2]

theorem distSup_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  unfold distributeSupplierComp subChecked
  simp [h]

theorem distBor_some (s : St) (who : Account)
    (h : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  unfold distributeBorrowerComp subChecked
  simp [h]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  unfold Consistent at hc
  obtain ⟨hbb1, hbb2, hrec⟩ := hc
  cases c with
  | supplyHook who =>
    have h2 : comptroller s (.supplyHook who) =
        (updateCompSupplyIndex s).bind (fun s => distributeSupplierComp s who) := rfl
    obtain ⟨s₁, hu⟩ := Option.isSome_iff_exists.mp (updSup_some s hbb1)
    have hs₁ := updSup_eq s s₁ hu
    have hr := (acct_rec_le s hrec who).1
    have hac : s₁.acct who = s.acct who := by
      show s₁.accts.getD who noAcct = s.accts.getD who noAcct; rw [hs₁]
    have hst : accrualStart (s₁.acct who).supplierIndex s₁.supplyState.index ≤
        s₁.supplyState.index := by
      have hXi : s₁.supplyState.index =
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hs₁]
      rw [hac, hXi]
      exact start_le_index _ _
        (Nat.le_trans hr (accrueSide_index_le _ _ _))
    obtain ⟨s', hd⟩ := Option.isSome_iff_exists.mp (distSup_some s₁ who hst)
    have hfin : comptroller s (.supplyHook who) = some s' := by
      rw [h2, hu, Option.bind_some]; exact hd
    exact Option.isSome_iff_exists.mpr ⟨s', hfin⟩
  | borrowHook who =>
    have h2 : comptroller s (.borrowHook who) =
        (updateCompBorrowIndex s).bind (fun s => distributeBorrowerComp s who) := rfl
    obtain ⟨s₁, hu⟩ := Option.isSome_iff_exists.mp (updBor_some s hbb2)
    have hs₁ := updBor_eq s s₁ hu
    have hr := (acct_rec_le s hrec who).2
    have hac : s₁.acct who = s.acct who := by
      show s₁.accts.getD who noAcct = s.accts.getD who noAcct; rw [hs₁]
    have hst : accrualStart (s₁.acct who).borrowerIndex s₁.borrowState.index ≤
        s₁.borrowState.index := by
      have hXi : s₁.borrowState.index =
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hs₁]
      rw [hac, hXi]
      exact start_le_index _ _
        (Nat.le_trans hr (accrueSide_index_le _ _ _))
    obtain ⟨s', hd⟩ := Option.isSome_iff_exists.mp (distBor_some s₁ who hst)
    have hfin : comptroller s (.borrowHook who) = some s' := by
      rw [h2, hu, Option.bind_some]; exact hd
    exact Option.isSome_iff_exists.mpr ⟨s', hfin⟩
  | claim who =>
    have h2 : comptroller s (.claim who) = claimComp s who := rfl
    obtain ⟨u₁, hu1⟩ := Option.isSome_iff_exists.mp (updBor_some s hbb2)
    have hu1e := updBor_eq s u₁ hu1
    have hacB : u₁.acct who = s.acct who := by
      show u₁.accts.getD who noAcct = s.accts.getD who noAcct; rw [hu1e]
    have hrB := (acct_rec_le s hrec who).2
    have hstB : accrualStart (u₁.acct who).borrowerIndex u₁.borrowState.index ≤
        u₁.borrowState.index := by
      have hXi : u₁.borrowState.index =
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hu1e]
      rw [hacB, hXi]
      exact start_le_index _ _
        (Nat.le_trans hrB (accrueSide_index_le _ _ _))
    obtain ⟨v₁, hd1⟩ := Option.isSome_iff_exists.mp (distBor_some u₁ who hstB)
    have hd1e := (distBor_eq u₁ who v₁ hd1).2
    unfold St.withAcct at hd1e
    have hv1sup : v₁.supplyState = s.supplyState := by rw [hd1e, hu1e]
    have hv1bn : v₁.blockNumber = s.blockNumber := by rw [hd1e, hu1e]
    have hv1blk : v₁.supplyState.block ≤ v₁.blockNumber := by
      rw [hv1sup, hv1bn]; exact hbb1
    obtain ⟨u₂, hu2⟩ := Option.isSome_iff_exists.mp (updSup_some v₁ hv1blk)
    have hu2e := updSup_eq v₁ u₂ hu2
    have hXu2 : u₂.supplyState = accrueSide v₁.supplyState v₁.blockNumber (totalSupply v₁) := by
      rw [hu2e]
    have e_u2acct : u₂.acct who = v₁.acct who := by
      show u₂.accts.getD who noAcct = v₁.accts.getD who noAcct; rw [hu2e]
    have e_v1supidx : (v₁.acct who).supplierIndex = (s.acct who).supplierIndex := by
      have e1 : (v₁.acct who).supplierIndex = (u₁.acct who).supplierIndex :=
        distBor_keep_sup u₁ who who v₁ hd1
      have e2 : (u₁.acct who).supplierIndex = (s.acct who).supplierIndex := by
        show (u₁.accts.getD who noAcct).supplierIndex = (s.accts.getD who noAcct).supplierIndex
        rw [hu1e]
      exact e1.trans e2
    have hrS := (acct_rec_le s hrec who).1
    have hXi1 : v₁.supplyState.index = s.supplyState.index := by rw [hv1sup]
    have hleS : v₁.supplyState.index ≤
        (accrueSide v₁.supplyState v₁.blockNumber (totalSupply v₁)).index :=
      accrueSide_index_le _ _ _
    have hrec_le : (s.acct who).supplierIndex ≤ u₂.supplyState.index := by
      rw [hXu2]
      exact Nat.le_trans hrS (by rw [← hXi1]; exact hleS)
    have hstS : accrualStart (u₂.acct who).supplierIndex u₂.supplyState.index ≤
        u₂.supplyState.index := by
      rw [e_u2acct, e_v1supidx]
      exact start_le_index _ _ hrec_le
    obtain ⟨v₂, hd2⟩ := Option.isSome_iff_exists.mp (distSup_some u₂ who hstS)
    have hfin : comptroller s (.claim who) = some (grantCompInternal v₂ who) := by
      rw [h2]; unfold claimComp
      simp only [hu1, hd1, hu2, hd2, Option.bind_some]
    exact Option.isSome_iff_exists.mpr ⟨_, hfin⟩
  | setSpeeds a b =>
    have h2 : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl
    have h3 : setCompSpeedInternal s a b =
        (setSupplySpeed s a).bind (fun s => setBorrowSpeed s b) := rfl
    have eS : ∃ s₁, setSupplySpeed s a = some s₁ := by
      by_cases ha : s.supplyState.speed = a
      · have hnn : ¬ s.supplyState.speed ≠ a := fun ne => ne ha
        exact ⟨s, by unfold setSupplySpeed; rw [if_neg hnn]⟩
      · have han : s.supplyState.speed ≠ a := ha
        obtain ⟨t, hu⟩ := Option.isSome_iff_exists.mp (updSup_some s hbb1)
        refine ⟨{ s with supplyState := { t.supplyState with speed := a } }, ?_⟩
        unfold setSupplySpeed
        rw [if_pos han]
        simp only [hu]
    obtain ⟨s₁, hS⟩ := eS
    have hSB : s₁.borrowState = s.borrowState ∧ s₁.blockNumber = s.blockNumber := by
      unfold setSupplySpeed at hS
      by_cases ha : s.supplyState.speed = a
      · have hnn : ¬ s.supplyState.speed ≠ a := fun ne => ne ha
        rw [if_neg hnn] at hS
        have hs1 : s₁ = s := (Option.some_inj.mp hS).symm
        rw [hs1]
        exact ⟨rfl, rfl⟩
      · have han : s.supplyState.speed ≠ a := ha
        rw [if_pos han] at hS
        match hUt : updateCompSupplyIndex s with
        | none => rw [hUt] at hS; simp at hS
        | some t =>
          simp only [hUt] at hS
          have hs1 : s₁ = { s with supplyState := { t.supplyState with speed := a } } :=
            (Option.some_inj.mp hS).symm
          rw [hs1]
          exact ⟨rfl, rfl⟩
    have hbb2' : s₁.borrowState.block ≤ s₁.blockNumber := by
      obtain ⟨sbS, bnS⟩ := hSB
      rw [sbS, bnS]; exact hbb2
    have eB : ∃ s₂, setBorrowSpeed s₁ b = some s₂ := by
      by_cases hb : s₁.borrowState.speed = b
      · have hnn : ¬ s₁.borrowState.speed ≠ b := fun ne => ne hb
        exact ⟨s₁, by unfold setBorrowSpeed; rw [if_neg hnn]⟩
      · have han : s₁.borrowState.speed ≠ b := hb
        obtain ⟨t, hu⟩ := Option.isSome_iff_exists.mp (updBor_some s₁ hbb2')
        refine ⟨{ s₁ with borrowState := { t.borrowState with speed := b } }, ?_⟩
        unfold setBorrowSpeed
        rw [if_pos han]
        simp only [hu]
    obtain ⟨s₂, hB⟩ := eB
    have hfin : comptroller s (.setSpeeds a b) = some s₂ := by
      rw [h2, h3, hS, Option.bind_some]; exact hB
    exact Option.isSome_iff_exists.mpr ⟨s₂, hfin⟩
theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  have h2 : comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind (fun s => distributeSupplierComp s who) := rfl
  rw [h2] at h
  obtain ⟨s₁, hu, hd⟩ : ∃ s₁, updateCompSupplyIndex s = some s₁ ∧
      distributeSupplierComp s₁ who = some s' := by
    match hU : updateCompSupplyIndex s with
    | none => rw [hU] at h; simp at h
    | some s₁ =>
      rw [hU] at h
      have hd : distributeSupplierComp s₁ who = some s' := by simpa using h
      exact ⟨s₁, rfl, hd⟩
  have hs₁ := updSup_eq s s₁ hu
  obtain ⟨hdle, hdeq⟩ := distSup_eq s₁ who s' hd
  have hXi : s₁.supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by rw [hs₁]
  have hac : s₁.acct who = s.acct who := by
    show s₁.accts.getD who noAcct = s.accts.getD who noAcct
    rw [hs₁]
  refine ⟨updSup_block s s₁ hu, ?_, ?_⟩
  · rw [← hac, ← hXi]
    exact hdle
  · rw [hdeq]
    unfold St.withAcct
    rw [hXi, hs₁]

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  have h2 : comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun s => distributeBorrowerComp s who) := rfl
  rw [h2] at h
  obtain ⟨s₁, hu, hd⟩ : ∃ s₁, updateCompBorrowIndex s = some s₁ ∧
      distributeBorrowerComp s₁ who = some s' := by
    match hU : updateCompBorrowIndex s with
    | none => rw [hU] at h; simp at h
    | some s₁ =>
      rw [hU] at h
      have hd : distributeBorrowerComp s₁ who = some s' := by simpa using h
      exact ⟨s₁, rfl, hd⟩
  have hs₁ := updBor_eq s s₁ hu
  obtain ⟨hdle, hdeq⟩ := distBor_eq s₁ who s' hd
  have hXi : s₁.borrowState.index =
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by rw [hs₁]
  have hac : s₁.acct who = s.acct who := by
    show s₁.accts.getD who noAcct = s.accts.getD who noAcct
    rw [hs₁]
  refine ⟨updBor_block s s₁ hu, ?_, ?_⟩
  · rw [← hac, ← hXi]
    exact hdle
  · rw [hdeq]
    unfold St.withAcct
    rw [hXi, hs₁]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  have h2 : comptroller s (.claim who) = claimComp s who := rfl
  rw [h2] at h
  have hb2 : comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun s => distributeBorrowerComp s who) := rfl
  unfold claimComp at h
  match hU1 : updateCompBorrowIndex s with
  | none => rw [hU1] at h; simp at h
  | some u₁ =>
    simp only [hU1, Option.bind_some] at h
    match hD1 : distributeBorrowerComp u₁ who with
    | none => rw [hD1] at h; simp at h
    | some v₁ =>
      simp only [hD1, Option.bind_some] at h
      match hU2 : updateCompSupplyIndex v₁ with
      | none => rw [hU2] at h; simp at h
      | some u₂ =>
        simp only [hU2, Option.bind_some] at h
        match hD2 : distributeSupplierComp u₂ who with
        | none => rw [hD2] at h; simp at h
        | some v₂ =>
          simp only [hD2, Option.bind_some] at h
          have hB : comptroller s (.borrowHook who) = some v₁ := by
            rw [hb2, hU1, Option.bind_some]; exact hD1
          have hs2 : comptroller v₁ (.supplyHook who) =
              (updateCompSupplyIndex v₁).bind (fun s => distributeSupplierComp s who) := rfl
          have hS : comptroller v₁ (.supplyHook who) = some v₂ := by
            rw [hs2, hU2, Option.bind_some]; exact hD2
          have hs' : s' = grantCompInternal v₂ who := (Option.some_inj.mp h).symm
          refine ⟨v₁, v₂, req_borrow_hook s who v₁ hB, req_supply_hook v₁ who v₂ hS, ?_⟩
          rw [hs', grant_eq]
theorem setSup_eq (s : St) (a : Nat) (s₁ : St) (h : setSupplySpeed s a = some s₁) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s₁ = { s with supplyState := if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } ∧
    s₁.borrowState = s.borrowState ∧ s₁.blockNumber = s.blockNumber ∧
    s₁.reserve = s.reserve ∧ s₁.accts = s.accts := by
  unfold setSupplySpeed at h
  by_cases ha : s.supplyState.speed = a
  · have hnn : ¬ s.supplyState.speed ≠ a := fun ne => ne ha
    rw [if_neg hnn] at h
    have hs1 : s₁ = s := (Option.some_inj.mp h).symm
    rw [if_pos ha]
    refine ⟨fun hn => absurd ha hn, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs1]
    · rw [hs1]
    · rw [hs1]
    · rw [hs1]
    · rw [hs1]
  · have han : s.supplyState.speed ≠ a := ha
    rw [if_pos han] at h
    match hUt : updateCompSupplyIndex s with
    | none => rw [hUt] at h; simp at h
    | some t =>
      simp only [hUt] at h
      have hs1 : s₁ = { s with supplyState := { t.supplyState with speed := a } } :=
        (Option.some_inj.mp h).symm
      have ht := updSup_eq s t hUt
      have hts : t.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by
        rw [ht]
      have hcond : s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber :=
        fun _ => updSup_block s t hUt
      have hif : (if s.supplyState.speed = a then s.supplyState
          else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) =
          { t.supplyState with speed := a } := by
        rw [if_neg ha, hts]
      refine ⟨hcond, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs1, hif]
      · rw [hs1]
      · rw [hs1]
      · rw [hs1]
      · rw [hs1]

theorem setBor_eq (s : St) (b : Nat) (s₁ : St) (h : setBorrowSpeed s b = some s₁) :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s₁ = { s with borrowState := if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } ∧
    s₁.supplyState = s.supplyState ∧ s₁.blockNumber = s.blockNumber ∧
    s₁.reserve = s.reserve ∧ s₁.accts = s.accts := by
  unfold setBorrowSpeed at h
  by_cases ha : s.borrowState.speed = b
  · have hnn : ¬ s.borrowState.speed ≠ b := fun ne => ne ha
    rw [if_neg hnn] at h
    have hs1 : s₁ = s := (Option.some_inj.mp h).symm
    rw [if_pos ha]
    refine ⟨fun hn => absurd ha hn, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs1]
    · rw [hs1]
    · rw [hs1]
    · rw [hs1]
    · rw [hs1]
  · have han : s.borrowState.speed ≠ b := ha
    rw [if_pos han] at h
    match hUt : updateCompBorrowIndex s with
    | none => rw [hUt] at h; simp at h
    | some t =>
      simp only [hUt] at h
      have hs1 : s₁ = { s with borrowState := { t.borrowState with speed := b } } :=
        (Option.some_inj.mp h).symm
      have ht := updBor_eq s t hUt
      have hts : t.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
        rw [ht]
      have hcond : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber :=
        fun _ => updBor_block s t hUt
      have hif : (if s.borrowState.speed = b then s.borrowState
          else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) =
          { t.borrowState with speed := b } := by
        rw [if_neg ha, hts]
      refine ⟨hcond, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs1, hif]
      · rw [hs1]
      · rw [hs1]
      · rw [hs1]
      · rw [hs1]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  have h2 : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl
  rw [h2] at h
  have h3 : setCompSpeedInternal s a b =
      (setSupplySpeed s a).bind (fun s => setBorrowSpeed s b) := rfl
  rw [h3] at h
  match hS : setSupplySpeed s a with
  | none => rw [hS] at h; simp at h
  | some s₁ =>
    simp only [hS, Option.bind_some] at h
    match hB : setBorrowSpeed s₁ b with
    | none => rw [hB] at h; simp at h
    | some s₂ =>
      simp only [hB] at h
      have hs' : s' = s₂ := (Option.some_inj.mp h).symm
      obtain ⟨condS, eS, sbS, bnS, resS, acS⟩ := setSup_eq s a s₁ hS
      obtain ⟨condB, eB, ssB, bnB, resB, acB⟩ := setBor_eq s₁ b s₂ hB
      have htb : totalBorrows s₁ = totalBorrows s := by
        unfold totalBorrows
        rw [acS]
      have hB1 : (if s₁.borrowState.speed = b then s₁.borrowState
          else { accrueSide s₁.borrowState s₁.blockNumber (totalBorrows s₁) with speed := b }) =
          (if s.borrowState.speed = b then s.borrowState
          else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) := by
        rw [sbS, bnS, htb]
      rw [hs']
      refine ⟨?_, ?_, ?_⟩
      · exact condS
      · intro hn
        have hn1 : s₁.borrowState.speed ≠ b := by
          show (s₁.borrowState).speed ≠ b
          rw [sbS]
          exact hn
        have hb := condB hn1
        rw [sbS, bnS] at hb
        exact hb
      · rw [eB, hB1, eS]
/-! ## The market reading for the potential argument -/

open ProofForgeFin.Accumulator.Market

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

theorem M_one : M.one = doubleScale := rfl

theorem M_total₁ (s : St) : M.total₁ s = totalSupply s := rfl

theorem M_total₂ (s : St) : M.total₂ s = totalBorrows s := rfl

theorem accrueSide_speed (sd : Side) (now total : Nat) :
    (accrueSide sd now total).speed = sd.speed := by
  unfold accrueSide
  split
  · rfl
  · rfl

theorem settle₁_clock (s t : St)
    (hs : t.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s))
    (hb : t.borrowState = s.borrowState) (hn : t.blockNumber = s.blockNumber) :
    M.clock t = (M.clock s).catchUp₁ M.one (M.total₁ s) := by
  show ProofForgeFin.Accumulator.Clock.mk t.blockNumber t.supplyState.index t.supplyState.block
      t.supplyState.speed t.borrowState.index t.borrowState.block t.borrowState.speed =
    ProofForgeFin.Accumulator.Clock.mk s.blockNumber
      (ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block
        s.supplyState.speed s.blockNumber (M.total₁ s))
      s.blockNumber s.supplyState.speed
      s.borrowState.index s.borrowState.block s.borrowState.speed
  simp only [ProofForgeFin.Accumulator.Clock.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn]
  · rw [hs, accrueSide_eq_catchUp, M_one, ← M_total₁ s]
  · rw [hs, accrueSide_block]
  · rw [hs]; exact accrueSide_speed _ _ _
  · rw [hb]
  · rw [hb]
  · rw [hb]

theorem settle₂_clock (s t : St)
    (hs : t.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s))
    (hb : t.supplyState = s.supplyState) (hn : t.blockNumber = s.blockNumber) :
    M.clock t = (M.clock s).catchUp₂ M.one (M.total₂ s) := by
  show ProofForgeFin.Accumulator.Clock.mk t.blockNumber t.supplyState.index t.supplyState.block
      t.supplyState.speed t.borrowState.index t.borrowState.block t.borrowState.speed =
    ProofForgeFin.Accumulator.Clock.mk s.blockNumber
      s.supplyState.index s.supplyState.block s.supplyState.speed
      (ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block
        s.borrowState.speed s.blockNumber (M.total₂ s))
      s.blockNumber s.borrowState.speed
  simp only [ProofForgeFin.Accumulator.Clock.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn]
  · rw [hb]
  · rw [hb]
  · rw [hb]
  · rw [hs, accrueSide_eq_catchUp, M_one, ← M_total₂ s]
  · rw [hs, accrueSide_block]
  · rw [hs]; exact accrueSide_speed _ _ _

theorem settle₁_of_supplyHook (s : St) (who : Account) (t : St)
    (h : comptroller s (.supplyHook who) = some t) : M.Settle₁ who s t := by
  have h2 : comptroller s (.supplyHook who) =
      (updateCompSupplyIndex s).bind (fun s => distributeSupplierComp s who) := rfl
  rw [h2] at h
  obtain ⟨s₁, hu, hd⟩ : ∃ s₁, updateCompSupplyIndex s = some s₁ ∧
      distributeSupplierComp s₁ who = some t := by
    match hU : updateCompSupplyIndex s with
    | none => rw [hU] at h; simp at h
    | some s₁ =>
      rw [hU] at h
      have hd : distributeSupplierComp s₁ who = some t := by simpa using h
      exact ⟨s₁, rfl, hd⟩
  have hs₁ := updSup_eq s s₁ hu
  obtain ⟨_, hdeq⟩ := distSup_eq s₁ who t hd
  unfold St.withAcct at hdeq
  have htsX : t.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by
    rw [hdeq, hs₁]
  have htbX : t.borrowState = s.borrowState := by rw [hdeq, hs₁]
  have htnX : t.blockNumber = s.blockNumber := by rw [hdeq, hs₁]
  have haccts : s₁.accts = s.accts := by rw [hs₁]
  have ht_sup : t.supplyState = s₁.supplyState := by rw [hdeq]
  have ht_idx : s₁.supplyState.index = (M.clock t).index₁ := by
    show s₁.supplyState.index = t.supplyState.index
    rw [ht_sup]
  refine ⟨settle₁_clock s t htsX htbX htnX, ?_⟩
  refine ⟨fun a =>
    { a with
      supplierIndex := s₁.supplyState.index,
      accrued := a.accrued + creditFor a.supply
        (accrualStart a.supplierIndex s₁.supplyState.index) s₁.supplyState.index }, ?_, ?_⟩
  · rw [hdeq]
    show (s₁.accts.modify who (fun a =>
      { a with
        supplierIndex := s₁.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s₁.supplyState.index) s₁.supplyState.index })) =
      (s.accts.modify who (fun a =>
      { a with
        supplierIndex := s₁.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s₁.supplyState.index) s₁.supplyState.index }))
    rw [haccts]
  · intro a
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact (rfl : M.rec₁ ((fun a =>
        { a with
          supplierIndex := s₁.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s₁.supplyState.index) s₁.supplyState.index }) a) =
        s₁.supplyState.index).trans ht_idx
    · rfl
    · show (a.accrued + a.supply * (s₁.supplyState.index -
          accrualStart a.supplierIndex s₁.supplyState.index) / doubleScale) + a.wallet ≤
        (a.accrued + a.wallet) + a.supply * (t.supplyState.index -
          accrualStart a.supplierIndex t.supplyState.index) / doubleScale
      rw [ht_sup]
      omega

theorem settle₂_of_borrowHook (s : St) (who : Account) (t : St)
    (h : comptroller s (.borrowHook who) = some t) : M.Settle₂ who s t := by
  have h2 : comptroller s (.borrowHook who) =
      (updateCompBorrowIndex s).bind (fun s => distributeBorrowerComp s who) := rfl
  rw [h2] at h
  obtain ⟨s₁, hu, hd⟩ : ∃ s₁, updateCompBorrowIndex s = some s₁ ∧
      distributeBorrowerComp s₁ who = some t := by
    match hU : updateCompBorrowIndex s with
    | none => rw [hU] at h; simp at h
    | some s₁ =>
      rw [hU] at h
      have hd : distributeBorrowerComp s₁ who = some t := by simpa using h
      exact ⟨s₁, rfl, hd⟩
  have hs₁ := updBor_eq s s₁ hu
  obtain ⟨_, hdeq⟩ := distBor_eq s₁ who t hd
  unfold St.withAcct at hdeq
  have htsX : t.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
    rw [hdeq, hs₁]
  have htbX : t.supplyState = s.supplyState := by rw [hdeq, hs₁]
  have htnX : t.blockNumber = s.blockNumber := by rw [hdeq, hs₁]
  have haccts : s₁.accts = s.accts := by rw [hs₁]
  have ht_bor : t.borrowState = s₁.borrowState := by rw [hdeq]
  have ht_idx : s₁.borrowState.index = (M.clock t).index₂ := by
    show s₁.borrowState.index = t.borrowState.index
    rw [ht_bor]
  refine ⟨settle₂_clock s t htsX htbX htnX, ?_⟩
  refine ⟨fun a =>
    { a with
      borrowerIndex := s₁.borrowState.index,
      accrued := a.accrued + creditFor a.borrow
        (accrualStart a.borrowerIndex s₁.borrowState.index) s₁.borrowState.index }, ?_, ?_⟩
  · rw [hdeq]
    show (s₁.accts.modify who (fun a =>
      { a with
        borrowerIndex := s₁.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s₁.borrowState.index) s₁.borrowState.index })) =
      (s.accts.modify who (fun a =>
      { a with
        borrowerIndex := s₁.borrowState.index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex s₁.borrowState.index) s₁.borrowState.index }))
    rw [haccts]
  · intro a
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact (rfl : M.rec₂ ((fun a =>
        { a with
          borrowerIndex := s₁.borrowState.index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex s₁.borrowState.index) s₁.borrowState.index }) a) =
        s₁.borrowState.index).trans ht_idx
    · rfl
    · show (a.accrued + a.borrow * (s₁.borrowState.index -
          accrualStart a.borrowerIndex s₁.borrowState.index) / doubleScale) + a.wallet ≤
        (a.accrued + a.wallet) + a.borrow * (t.borrowState.index -
          accrualStart a.borrowerIndex t.borrowState.index) / doubleScale
      rw [ht_bor]
      omega

theorem grant_step (s t : St) (who : Account) (h : t = grant s who) :
    M.Step s t := by
  unfold grant at h
  by_cases hc : 0 < (s.acct who).accrued ∧ (s.acct who).accrued ≤ s.reserve
  · rw [if_pos hc] at h
    have hadj : M.Adjust who s t := by
      refine ⟨?_, ?_⟩
      · rw [h]; rfl
      · refine ⟨fun a => { a with accrued := 0, wallet := a.wallet + a.accrued }, ?_, ?_, ?_, ?_⟩
        · rw [h]; rfl
        · intro a
          refine ⟨?_, ?_, ?_⟩
          · show 0 + (a.wallet + a.accrued) ≤ a.accrued + a.wallet
            omega
          · rfl
          · rfl
        · exact Or.inl fun a => rfl
        · exact Or.inl fun a => rfl
    exact ProofForgeFin.Accumulator.Market.Step.adjust hadj
  · rw [if_neg hc] at h
    have hclock : M.clock t = M.clock s := by rw [h]
    have haccts : M.accts t = M.accts s := by rw [h]
    exact ProofForgeFin.Accumulator.Market.Step.same hclock haccts

theorem consistent_of_inv {g₁ g₂ : Nat} {sp : Nat × Nat} {s : St}
    (hI : M.Inv g₁ g₂ sp s) : Consistent s := by
  obtain ⟨hl1, hl2, hrec, _, _, _, _⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · exact hl1
  · exact hl2
  · intro a ha
    exact hrec a ha

theorem settle₂_of_borrowDist (s : St) (who : Account) (m₁ : St)
    (h : BorrowDistributed s who m₁) : M.Settle₂ who s m₁ := by
  obtain ⟨hblk, hst, heq⟩ := h
  have hmb : m₁.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
    rw [heq]
  have hms : m₁.supplyState = s.supplyState := by rw [heq]
  have hmn : m₁.blockNumber = s.blockNumber := by rw [heq]
  have ht_idx : (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
      (M.clock m₁).index₂ := by
    show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index = m₁.borrowState.index
    rw [hmb]
  refine ⟨settle₂_clock s m₁ hmb hms hmn, ?_⟩
  refine ⟨fun a =>
    { a with
      borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
      accrued := a.accrued + creditFor a.borrow
        (accrualStart a.borrowerIndex
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }, ?_, ?_⟩
  · rw [heq]; rfl
  · intro a
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact (rfl : M.rec₂ ((fun a =>
        { a with
          borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
          accrued := a.accrued + creditFor a.borrow
            (accrualStart a.borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index }) a) =
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index).trans ht_idx
    · rfl
    · show (a.accrued + a.borrow * ((accrueSide s.borrowState s.blockNumber (totalBorrows s)).index -
          accrualStart a.borrowerIndex
            (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) / doubleScale) +
          a.wallet ≤
        (a.accrued + a.wallet) + a.borrow * (m₁.borrowState.index -
          accrualStart a.borrowerIndex m₁.borrowState.index) / doubleScale
      rw [hmb]
      omega

theorem settle₁_of_supplyDist (s : St) (who : Account) (m₂ : St)
    (h : SupplyDistributed s who m₂) : M.Settle₁ who s m₂ := by
  obtain ⟨hblk, hst, heq⟩ := h
  have hmb : m₂.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by
    rw [heq]
  have hms : m₂.borrowState = s.borrowState := by rw [heq]
  have hmn : m₂.blockNumber = s.blockNumber := by rw [heq]
  have ht_idx : (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
      (M.clock m₂).index₁ := by
    show (accrueSide s.supplyState s.blockNumber (totalSupply s)).index = m₂.supplyState.index
    rw [hmb]
  refine ⟨settle₁_clock s m₂ hmb hms hmn, ?_⟩
  refine ⟨fun a =>
    { a with
      supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
      accrued := a.accrued + creditFor a.supply
        (accrualStart a.supplierIndex
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }, ?_, ?_⟩
  · rw [heq]; rfl
  · intro a
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact (rfl : M.rec₁ ((fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index }) a) =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index).trans ht_idx
    · rfl
    · show (a.accrued + a.supply * ((accrueSide s.supplyState s.blockNumber (totalSupply s)).index -
          accrualStart a.supplierIndex
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) / doubleScale) +
          a.wallet ≤
        (a.accrued + a.wallet) + a.supply * (m₂.supplyState.index -
          accrualStart a.supplierIndex m₂.supplyState.index) / doubleScale
      rw [hmb]
      omega

theorem exec_act (g₁ g₂ : Nat) (sp : Nat × Nat) (s : St) (op : Op)
    (hI : M.Inv g₁ g₂ sp s) :
    M.Act sp s (nextSpeeds sp op) (emittedBy sp op) (exec comptroller s op) := by
  cases op with
  | mint who x =>
    by_cases hw : who < s.accts.length
    · have hc := req_calls_succeed s (.supplyHook who) (consistent_of_inv hI)
      obtain ⟨s₁, hs1⟩ := Option.isSome_iff_exists.mp hc
      have hSettle := settle₁_of_supplyHook s who s₁ hs1
      have hg : M.AdjustsAt (fun a => { a with supply := a.supply + x }) := by
        intro a
        refine ⟨?_, ?_, ?_⟩
        · exact Nat.le_refl _
        · rfl
        · rfl
      have he : exec comptroller s (.mint who x) =
          s₁.withAcct who (fun a => { a with supply := a.supply + x }) := by
        simp only [exec, hw, hs1, ↓reduceIte]
      rw [he]
      exact Act.moves (Settle₁.then_adjust hSettle rfl rfl hg (fun a => rfl))
    · have he : exec comptroller s (.mint who x) = s := by
        simp only [exec, hw, ↓reduceIte]
      rw [he]
      exact Act.moves (Reach.refl s)
  | redeem who x =>
    by_cases hw : who < s.accts.length
    · have hc := req_calls_succeed s (.supplyHook who) (consistent_of_inv hI)
      obtain ⟨s₁, hs1⟩ := Option.isSome_iff_exists.mp hc
      have hSettle := settle₁_of_supplyHook s who s₁ hs1
      by_cases hx : x ≤ (s₁.acct who).supply
      · have hg : M.AdjustsAt (fun a => { a with supply := a.supply - x }) := by
          intro a
          refine ⟨?_, ?_, ?_⟩
          · exact Nat.le_refl _
          · rfl
          · rfl
        have he : exec comptroller s (.redeem who x) =
            s₁.withAcct who (fun a => { a with supply := a.supply - x }) := by
          simp only [exec, hw, hs1, hx, ↓reduceIte]
        rw [he]
        exact Act.moves (Settle₁.then_adjust hSettle rfl rfl hg (fun a => rfl))
      · have he : exec comptroller s (.redeem who x) = s := by
          simp only [exec, hw, hs1, hx, ↓reduceIte]
        rw [he]
        exact Act.moves (Reach.refl s)
    · have he : exec comptroller s (.redeem who x) = s := by
        simp only [exec, hw, ↓reduceIte]
      rw [he]
      exact Act.moves (Reach.refl s)
  | transfer src dst x =>
    by_cases hcnd : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · have hc1 := req_calls_succeed s (.supplyHook src) (consistent_of_inv hI)
      obtain ⟨s₁, hs1⟩ := Option.isSome_iff_exists.mp hc1
      have hS1 := settle₁_of_supplyHook s src s₁ hs1
      have hI1 := (Step.bound (Step.settle₁ hS1) hI).1
      have hc2 := req_calls_succeed s₁ (.supplyHook dst) (consistent_of_inv hI1)
      obtain ⟨s₂, hs2⟩ := Option.isSome_iff_exists.mp hc2
      have hS2 := settle₁_of_supplyHook s₁ dst s₂ hs2
      by_cases hx : x ≤ (s₂.acct src).supply
      · have hg₁ : M.AdjustsAt (fun a => { a with supply := a.supply - x }) := by
          intro a
          refine ⟨?_, ?_, ?_⟩
          · exact Nat.le_refl _
          · rfl
          · rfl
        have hg₂ : M.AdjustsAt (fun a => { a with supply := a.supply + x }) := by
          intro a
          refine ⟨?_, ?_, ?_⟩
          · exact Nat.le_refl _
          · rfl
          · rfl
        have he : exec comptroller s (.transfer src dst x) =
            (s₂.withAcct src (fun a => { a with supply := a.supply - x })).withAcct dst
              (fun a => { a with supply := a.supply + x }) := by
          simp [exec, hcnd, hs1, hs2, hx]
        rw [he]
        exact Act.moves (Settle₁.transfer hS1 hS2 rfl rfl hg₁ hg₂ (fun a => rfl) (fun a => rfl))
      · have he : exec comptroller s (.transfer src dst x) = s := by
          simp [exec, hcnd, hs1, hs2, hx]
        rw [he]
        exact Act.moves (Reach.refl s)
    · have he : exec comptroller s (.transfer src dst x) = s := by
        simp only [exec, hcnd, ↓reduceIte]
      rw [he]
      exact Act.moves (Reach.refl s)
  | borrow who x =>
    by_cases hw : who < s.accts.length
    · have hc := req_calls_succeed s (.borrowHook who) (consistent_of_inv hI)
      obtain ⟨s₁, hs1⟩ := Option.isSome_iff_exists.mp hc
      have hSettle := settle₂_of_borrowHook s who s₁ hs1
      have hg : M.AdjustsAt (fun a => { a with borrow := a.borrow + x }) := by
        intro a
        refine ⟨?_, ?_, ?_⟩
        · exact Nat.le_refl _
        · rfl
        · rfl
      have he : exec comptroller s (.borrow who x) =
          s₁.withAcct who (fun a => { a with borrow := a.borrow + x }) := by
        simp only [exec, hw, hs1, ↓reduceIte]
      rw [he]
      exact Act.moves (Settle₂.then_adjust hSettle rfl rfl hg (fun a => rfl))
    · have he : exec comptroller s (.borrow who x) = s := by
        simp only [exec, hw, ↓reduceIte]
      rw [he]
      exact Act.moves (Reach.refl s)
  | repay who x =>
    by_cases hw : who < s.accts.length
    · have hc := req_calls_succeed s (.borrowHook who) (consistent_of_inv hI)
      obtain ⟨s₁, hs1⟩ := Option.isSome_iff_exists.mp hc
      have hSettle := settle₂_of_borrowHook s who s₁ hs1
      by_cases hx : x ≤ (s₁.acct who).borrow
      · have hg : M.AdjustsAt (fun a => { a with borrow := a.borrow - x }) := by
          intro a
          refine ⟨?_, ?_, ?_⟩
          · exact Nat.le_refl _
          · rfl
          · rfl
        have he : exec comptroller s (.repay who x) =
            s₁.withAcct who (fun a => { a with borrow := a.borrow - x }) := by
          simp only [exec, hw, hs1, hx, ↓reduceIte]
        rw [he]
        exact Act.moves (Settle₂.then_adjust hSettle rfl rfl hg (fun a => rfl))
      · have he : exec comptroller s (.repay who x) = s := by
          simp only [exec, hw, hs1, hx, ↓reduceIte]
        rw [he]
        exact Act.moves (Reach.refl s)
    · have he : exec comptroller s (.repay who x) = s := by
        simp only [exec, hw, ↓reduceIte]
      rw [he]
      exact Act.moves (Reach.refl s)
  | claim who =>
    have hc := req_calls_succeed s (.claim who) (consistent_of_inv hI)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨m₁, m₂, hB, hS, hgr⟩ := req_claim s who t ht
    have he : exec comptroller s (.claim who) = t := by
      simp only [exec, ht, Option.getD_some]
    rw [he]
    have r1 : M.Reach s m₁ :=
      Reach.single (Step.settle₂ (settle₂_of_borrowDist s who m₁ hB))
    have r2 : M.Reach s m₂ := Reach.tail r1 (Step.settle₁ (settle₁_of_supplyDist m₁ who m₂ hS))
    have r3 : M.Reach s t := Reach.tail r2 (grant_step m₂ t who hgr)
    exact Act.moves r3
  | setSpeeds a b =>
    have hc := req_calls_succeed s (.setSpeeds a b) (consistent_of_inv hI)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨condS, condB, heq⟩ := req_set_speeds s a b t ht
    have he : exec comptroller s (.setSpeeds a b) = t := by
      simp only [exec, ht, Option.getD_some]
    rw [he]
    have hac : M.accts t = M.accts s := by rw [heq]; rfl
    have hnow : (M.clock t).now = (M.clock s).now := by rw [heq]; rfl
    have hside₁ : SideMove M.one (M.total₁ s) (M.clock s).now (M.clock s).index₁
        (M.clock s).last₁ (M.clock s).rate₁ (M.clock t).index₁ (M.clock t).last₁
        (M.clock t).rate₁ := by
      by_cases ha : s.supplyState.speed = a
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · show t.supplyState.index = s.supplyState.index
          rw [heq]
          simp [ha]
        · show t.supplyState.block = s.supplyState.block
          rw [heq]
          simp [ha]
        · show t.supplyState.speed = s.supplyState.speed
          rw [heq]
          simp [ha]
      · refine Or.inr ⟨?_, ?_⟩
        · show t.supplyState.index =
            ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block
              s.supplyState.speed s.blockNumber (M.total₁ s)
          rw [heq]
          show ((if s.supplyState.speed = a then s.supplyState else
            { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }).index) =
            ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block
              s.supplyState.speed s.blockNumber (M.total₁ s)
          rw [if_neg ha]
          show (accrueSide s.supplyState s.blockNumber (totalSupply s)).index =
            ProofForgeFin.Accumulator.catchUp M.one s.supplyState.index s.supplyState.block
              s.supplyState.speed s.blockNumber (M.total₁ s)
          rw [accrueSide_eq_catchUp, M_one, ← M_total₁ s]
        · show t.supplyState.block = s.blockNumber
          rw [heq]
          show ((if s.supplyState.speed = a then s.supplyState else
            { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }).block) =
            s.blockNumber
          rw [if_neg ha]
          show (accrueSide s.supplyState s.blockNumber (totalSupply s)).block = s.blockNumber
          rw [accrueSide_block]
    have hside₂ : SideMove M.one (M.total₂ s) (M.clock s).now (M.clock s).index₂
        (M.clock s).last₂ (M.clock s).rate₂ (M.clock t).index₂ (M.clock t).last₂
        (M.clock t).rate₂ := by
      by_cases hb : s.borrowState.speed = b
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · show t.borrowState.index = s.borrowState.index
          rw [heq]
          simp [hb]
        · show t.borrowState.block = s.borrowState.block
          rw [heq]
          simp [hb]
        · show t.borrowState.speed = s.borrowState.speed
          rw [heq]
          simp [hb]
      · refine Or.inr ⟨?_, ?_⟩
        · show t.borrowState.index =
            ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block
              s.borrowState.speed s.blockNumber (M.total₂ s)
          rw [heq]
          show ((if s.borrowState.speed = b then s.borrowState else
            { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }).index) =
            ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block
              s.borrowState.speed s.blockNumber (M.total₂ s)
          rw [if_neg hb]
          show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index =
            ProofForgeFin.Accumulator.catchUp M.one s.borrowState.index s.borrowState.block
              s.borrowState.speed s.blockNumber (M.total₂ s)
          rw [accrueSide_eq_catchUp, M_one, ← M_total₂ s]
        · show t.borrowState.block = s.blockNumber
          rw [heq]
          show ((if s.borrowState.speed = b then s.borrowState else
            { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }).block) =
            s.blockNumber
          rw [if_neg hb]
          show (accrueSide s.borrowState s.blockNumber (totalBorrows s)).block = s.blockNumber
          rw [accrueSide_block]
    have hr1 : (M.clock t).rate₁ = a := by
      show t.supplyState.speed = a
      rw [heq]
      by_cases ha : s.supplyState.speed = a
      · simp [ha]
      · simp [ha]
    have hr2 : (M.clock t).rate₂ = b := by
      show t.borrowState.speed = b
      rw [heq]
      by_cases hb : s.borrowState.speed = b
      · simp [hb]
      · simp [hb]
    exact Act.retune ⟨hac, hnow, hside₁, hside₂⟩ hr1 hr2
  | advance k =>
    have he : exec comptroller s (.advance k) = { s with blockNumber := s.blockNumber + k } :=
      rfl
    rw [he]
    have hadv : M.Advance k s { s with blockNumber := s.blockNumber + k } := by
      refine ⟨?_, ?_⟩
      · rfl
      · rfl
    exact Act.advance k hadv
  | drip x =>
    have he : exec comptroller s (.drip x) = { s with reserve := s.reserve + x } := rfl
    rw [he]
    exact Act.moves (Reach.single (Step.same rfl rfl))

theorem upSupIdx (L : Legacy) :
    (upgrade L).supplyState.index =
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
  by_cases hS : L.supplyIndex = 0 <;> by_cases hB : L.borrowIndex = 0 <;>
    simp [upgrade, initSide, hS, hB]

theorem upSupBlk (L : Legacy) :
    (upgrade L).supplyState.block =
      (if L.supplyIndex = 0 then L.blockNumber else L.supplyBlock) := by
  by_cases hS : L.supplyIndex = 0 <;> by_cases hB : L.borrowIndex = 0 <;>
    simp [upgrade, initSide, hS, hB]

theorem upSupSpd (L : Legacy) : (upgrade L).supplyState.speed = L.compSpeed := by
  by_cases hS : L.supplyIndex = 0 <;> by_cases hB : L.borrowIndex = 0 <;>
    simp [upgrade, initSide, hS, hB]

theorem upBorIdx (L : Legacy) :
    (upgrade L).borrowState.index =
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := by
  by_cases hS : L.supplyIndex = 0 <;> by_cases hB : L.borrowIndex = 0 <;>
    simp [upgrade, initSide, hS, hB]

theorem upBorBlk (L : Legacy) :
    (upgrade L).borrowState.block =
      (if L.borrowIndex = 0 then L.blockNumber else L.borrowBlock) := by
  by_cases hS : L.supplyIndex = 0 <;> by_cases hB : L.borrowIndex = 0 <;>
    simp [upgrade, initSide, hS, hB]

theorem upBorSpd (L : Legacy) : (upgrade L).borrowState.speed = L.compSpeed := by
  by_cases hS : L.supplyIndex = 0 <;> by_cases hB : L.borrowIndex = 0 <;>
    simp [upgrade, initSide, hS, hB]

theorem inv_upgrade (L : Legacy) (hL : L.WellFormed) :
    M.Inv (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
      (L.compSpeed, L.compSpeed) (upgrade L) := by
  unfold Legacy.WellFormed at hL
  obtain ⟨hs1a, hs1b, hb1a, hb1b, hbl1, hbl2, hrec⟩ := hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (upgrade L).supplyState.block ≤ L.blockNumber
    rw [upSupBlk L]
    by_cases h : L.supplyIndex = 0
    · rw [if_pos h]; exact Nat.le_refl _
    · rw [if_neg h]; exact hbl1
  · show (upgrade L).borrowState.block ≤ L.blockNumber
    rw [upBorBlk L]
    by_cases h : L.borrowIndex = 0
    · rw [if_pos h]; exact Nat.le_refl _
    · rw [if_neg h]; exact hbl2
  · intro a ha
    obtain ⟨hrS, hrB⟩ := hrec a ha
    refine ⟨?_, ?_⟩
    · show a.supplierIndex ≤ (upgrade L).supplyState.index
      rw [upSupIdx L]
      by_cases h : L.supplyIndex = 0
      · rw [if_pos h]; omega
      · rw [if_neg h]; exact hrS
    · show a.borrowerIndex ≤ (upgrade L).borrowState.index
      rw [upBorIdx L]
      by_cases h : L.borrowIndex = 0
      · rw [if_pos h]; omega
      · rw [if_neg h]; exact hrB
  · show ((if L.supplyIndex = 0 then compInitialIndex else L.supplyStart) = 0 ∨
        (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart) = compInitialIndex) ∧
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart) ≤
        (upgrade L).supplyState.index
    rw [upSupIdx L]
    exact start_reinit hs1a hs1b
  · show ((if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) = 0 ∨
        (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) = compInitialIndex) ∧
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) ≤
        (upgrade L).borrowState.index
    rw [upBorIdx L]
    exact start_reinit hb1a hb1b
  · exact upSupSpd L
  · exact upBorSpd L

theorem owed_le (L : Legacy) (hL : L.WellFormed) (a : Acct)
    (ha : a ∈ M.accts (upgrade L)) :
    M.owed (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
      (M.clock (upgrade L)) a ≤ L.pendingScaled a := by
  unfold Legacy.WellFormed at hL
  obtain ⟨hs1a, hs1b, hb1a, hb1b, hbl1, hbl2, hrec⟩ := hL
  obtain ⟨hrS, hrB⟩ := hrec a ha
  have e1 := owed_reinit_le (init := compInitialIndex) (g := L.supplyStart)
    (i := L.supplyIndex) (r := a.supplierIndex) (a.supply) hrS
  have e2 := owed_reinit_le (init := compInitialIndex) (g := L.borrowStart)
    (i := L.borrowIndex) (r := a.borrowerIndex) (a.borrow) hrB
  have hnewS : (M.clock (upgrade L)).index₁ =
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
    show (upgrade L).supplyState.index = _
    exact upSupIdx L
  have hnewB : (M.clock (upgrade L)).index₂ =
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := by
    show (upgrade L).borrowState.index = _
    exact upBorIdx L
  show a.supply * ((M.clock (upgrade L)).index₁ -
      legacyStart (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart) a.supplierIndex) +
    a.borrow * ((M.clock (upgrade L)).index₂ -
      legacyStart (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) a.borrowerIndex) ≤
    L.pendingScaled a
  rw [hnewS, hnewB]
  exact Nat.add_le_add e1 e2

theorem owed_dflt (L : Legacy) :
    M.owed (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
      (M.clock (upgrade L)) M.dflt ≤ L.pendingScaled M.dflt := by
  have hrS0 : (M.dflt).supplierIndex ≤ L.supplyIndex := by
    show (0 : Nat) ≤ L.supplyIndex
    exact Nat.zero_le _
  have hrB0 : (M.dflt).borrowerIndex ≤ L.borrowIndex := by
    show (0 : Nat) ≤ L.borrowIndex
    exact Nat.zero_le _
  have e1 := owed_reinit_le (init := compInitialIndex) (g := L.supplyStart)
    (i := L.supplyIndex) (r := (M.dflt).supplierIndex) (M.units₁ M.dflt) hrS0
  have e2 := owed_reinit_le (init := compInitialIndex) (g := L.borrowStart)
    (i := L.borrowIndex) (r := (M.dflt).borrowerIndex) (M.units₂ M.dflt) hrB0
  have hnewS : (M.clock (upgrade L)).index₁ =
      (if L.supplyIndex = 0 then compInitialIndex else L.supplyIndex) := by
    show (upgrade L).supplyState.index = _
    exact upSupIdx L
  have hnewB : (M.clock (upgrade L)).index₂ =
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowIndex) := by
    show (upgrade L).borrowState.index = _
    exact upBorIdx L
  show M.units₁ M.dflt * ((M.clock (upgrade L)).index₁ -
      legacyStart (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart) (M.dflt).supplierIndex) +
    M.units₂ M.dflt * ((M.clock (upgrade L)).index₂ -
      legacyStart (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) (M.dflt).borrowerIndex) ≤
    L.pendingScaled M.dflt
  rw [hnewS, hnewB]
  exact Nat.add_le_add e1 e2

theorem un₁_le (L : Legacy) : (M.clock (upgrade L)).un₁ ≤ L.unindexedSupply := by
  show ProofForgeFin.Accumulator.unindexed (upgrade L).supplyState.block
    (upgrade L).supplyState.speed L.blockNumber ≤ L.unindexedSupply
  rw [upSupBlk L, upSupSpd L]
  exact unindexed_reinit_le _ _ _ _

theorem un₂_le (L : Legacy) : (M.clock (upgrade L)).un₂ ≤ L.unindexedBorrow := by
  show ProofForgeFin.Accumulator.unindexed (upgrade L).borrowState.block
    (upgrade L).borrowState.speed L.blockNumber ≤ L.unindexedBorrow
  rw [upBorBlk L, upBorSpd L]
  exact unindexed_reinit_le _ _ _ _

theorem req_rewards_bounded : RewardsBounded comptroller := by
  intro L as hL
  have hI0 := inv_upgrade L hL
  have hact : ∀ (sp : Nat × Nat) (s : St) (a : Op),
      M.Inv (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
        (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) sp s →
      M.Act sp s (nextSpeeds sp a) (emittedBy sp a) (exec comptroller s a) :=
    fun sp s a hI => exec_act _ _ sp s a hI
  have hq : ∀ a ∈ M.accts (upgrade L),
      M.owed (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
        (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
        (M.clock (upgrade L)) a ≤ L.pendingScaled a :=
    fun a ha => owed_le L hL a ha
  have hs := M.pot_le_of (q := fun a => L.pendingScaled a)
    (U₁ := L.unindexedSupply) (U₂ := L.unindexedBorrow) hq (un₁_le L) (un₂_le L)
  have hone : 0 < M.one := by rw [M_one]; decide
  exact M.rewards_bounded (run comptroller) emitted speedsAfter hact hone hI0 hs as

theorem req_account_bounded : AccountBounded comptroller := by
  intro L as who hL
  have hI0 := inv_upgrade L hL
  have hact : ∀ (sp : Nat × Nat) (s : St) (a : Op),
      M.Inv (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
        (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) sp s →
      M.Act sp s (nextSpeeds sp a) (emittedBy sp a) (exec comptroller s a) :=
    fun sp s a hI => exec_act _ _ sp s a hI
  have hq1 : M.owed (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
      (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart)
      (M.clock (upgrade L)) (M.acct (upgrade L) who) ≤
      L.pendingScaled (L.accts.getD who noAcct) := by
    have hgen := forall_getD who (fun a ha => owed_le L hL a ha) (owed_dflt L)
    exact hgen
  have hs := M.potOf_le_of (R := L.pendingScaled (L.accts.getD who noAcct))
    (U₁ := L.unindexedSupply) (U₂ := L.unindexedBorrow) hq1 (un₁_le L) (un₂_le L)
  have hone : 0 < M.one := by rw [M_one]; decide
  exact M.account_rewards_bounded (run comptroller) emitted speedsAfter hact hone hI0 who hs as

theorem req_no_backdated : NoBackdatedRewards comptroller := by
  intro L history ops who hL hNo
  have hI0 := inv_upgrade L hL
  have hact : ∀ (sp : Nat × Nat) (s : St) (a : Op),
      M.Inv (if L.supplyIndex = 0 then compInitialIndex else L.supplyStart)
        (if L.borrowIndex = 0 then compInitialIndex else L.borrowStart) sp s →
      M.Act sp s (nextSpeeds sp a) (emittedBy sp a) (exec comptroller s a) :=
    fun sp s a hI => exec_act _ _ sp s a hI
  have hone : 0 < M.one := by rw [M_one]; decide
  have h1 : M.units₁ (M.acct (run comptroller (upgrade L) history) who) = 0 := hNo.1
  have h2 : M.units₂ (M.acct (run comptroller (upgrade L) history) who) = 0 := hNo.2
  exact M.rewards_after_no_position_bounded (run comptroller) emitted speedsAfter hact hone
    hI0 history ops who h1 h2

end CompRewards
