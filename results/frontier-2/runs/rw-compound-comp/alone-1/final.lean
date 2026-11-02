import CompRewards.Spec
namespace CompRewards

def updateCompSupplyIndex (s : St) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
  else none

def updateCompBorrowIndex (s : St) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
  else none

def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  if accrualStart (s.acct supplier).supplierIndex s.supplyState.index ≤ s.supplyState.index then
    some { s with accts := s.accts.modify supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } }
  else none

def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  if accrualStart (s.acct borrower).borrowerIndex s.borrowState.index ≤ s.borrowState.index then
    some { s with accts := s.accts.modify borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } }
  else none

def grantCompInternal (s : St) (user : Account) : St :=
  grant s user

def claimComp (s : St) (holder : Account) : Option St := do
  let s ← updateCompBorrowIndex s
  let s ← distributeBorrowerComp s holder
  let s ← updateCompSupplyIndex s
  let s ← distributeSupplierComp s holder
  return grantCompInternal s holder

def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed = supplySpeed then some s
  else if s.supplyState.block ≤ s.blockNumber then
    some { s with supplyState :=
      { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := supplySpeed } }
  else none

def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed = borrowSpeed then some s
  else if s.borrowState.block ≤ s.blockNumber then
    some { s with borrowState :=
      { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := borrowSpeed } }
  else none

def setCompSpeedInternal (s : St) (supplySpeed borrowSpeed : Nat) : Option St := do
  let s ← setSupplySpeed s supplySpeed
  let s ← setBorrowSpeed s borrowSpeed
  return s

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

theorem accrualStart_le_of_le {r idx : Nat} (h : r ≤ idx) :
    accrualStart r idx ≤ idx := by
  unfold accrualStart
  by_cases hr : r = 0
  · subst hr
    by_cases hi : compInitialIndex ≤ idx
    · simp only [hi, ↓reduceIte] at ⊢
    · simp only [hi, ↓reduceIte]
      exact Nat.zero_le idx
  · simp only [hr]
    exact h

theorem accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp only [h, ↓reduceIte]
    exact Nat.le_add_right _ _
  · simp only [h, ↓reduceIte]
    exact Nat.le_refl _

theorem accrueSide_block_eq_of_le {sd : Side} {now total : Nat}
    (h : sd.block ≤ now) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases hc : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · simp [hc]
  · simp [hc]

theorem updB_some {s m : St} (h : updateCompBorrowIndex s = some m) :
    s.borrowState.block ≤ s.blockNumber ∧
    m = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte, Option.some_inj] at h
    exact ⟨hb, h.symm⟩
  · simp only [hb, ↓reduceIte] at h
    cases h

theorem updS_some {s m : St} (h : updateCompSupplyIndex s = some m) :
    s.supplyState.block ≤ s.blockNumber ∧
    m = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte, Option.some_inj] at h
    exact ⟨hb, h.symm⟩
  · simp only [hb, ↓reduceIte] at h
    cases h

theorem distB_some {s m : St} {who : Account}
    (h : distributeBorrowerComp s who = some m) :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
    m = { s with accts := s.accts.modify who fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } } := by
  unfold distributeBorrowerComp at h
  by_cases hd : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤
      s.borrowState.index
  · simp only [hd, ↓reduceIte, Option.some_inj] at h
    exact ⟨hd, h.symm⟩
  · simp only [hd, ↓reduceIte] at h
    cases h

theorem distS_some {s m : St} {who : Account}
    (h : distributeSupplierComp s who = some m) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    m = { s with accts := s.accts.modify who fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by
  unfold distributeSupplierComp at h
  by_cases hd : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index
  · simp only [hd, ↓reduceIte, Option.some_inj] at h
    exact ⟨hd, h.symm⟩
  · simp only [hd, ↓reduceIte] at h
    cases h

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp [comptroller] at h
  cases hU : updateCompSupplyIndex s
  case none => simp [hU] at h
  case some s1 =>
    simp [hU] at h
    obtain ⟨hb, hEqU⟩ := updS_some hU
    obtain ⟨hd1, hEqD⟩ := distS_some h
    have hacct : s1.acct who = s.acct who := by simp [hEqU, St.acct]
    have hidx : s1.supplyState.index =
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by simp [hEqU]
    rw [hacct, hidx] at hd1
    refine ⟨hb, hd1, ?_⟩
    rw [hEqD, hEqU]

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp [comptroller] at h
  cases hU : updateCompBorrowIndex s
  case none => simp [hU] at h
  case some s1 =>
    simp [hU] at h
    obtain ⟨hb, hEqU⟩ := updB_some hU
    obtain ⟨hd1, hEqD⟩ := distB_some h
    have hacct : s1.acct who = s.acct who := by simp [hEqU, St.acct]
    have hidx : s1.borrowState.index =
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hEqU]
    rw [hacct, hidx] at hd1
    refine ⟨hb, hd1, ?_⟩
    rw [hEqD, hEqU]

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  unfold comptroller claimComp grantCompInternal at h
  cases hB : updateCompBorrowIndex s
  case none => simp [hB] at h
  case some mB =>
    simp [hB] at h
    cases hBD : distributeBorrowerComp mB who
    case none => simp [hBD] at h
    case some mBD =>
      simp [hBD] at h
      cases hS : updateCompSupplyIndex mBD
      case none => simp [hS] at h
      case some mS =>
        simp [hS] at h
        cases hSD : distributeSupplierComp mS who
        case none => simp [hSD] at h
        case some mSD =>
          simp [hSD] at h
          subst h
          obtain ⟨hbB, hEqB⟩ := updB_some hB
          obtain ⟨hdB0, hEqBD⟩ := distB_some hBD
          obtain ⟨hbS, hEqS⟩ := updS_some hS
          obtain ⟨hdS0, hEqSD⟩ := distS_some hSD
          have hAcctB : mB.acct who = s.acct who := by simp [hEqB, St.acct]
          have hdB : accrualStart (s.acct who).borrowerIndex
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
            have : mB.borrowState.index =
              (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by simp [hEqB]
            rw [hAcctB] at hdB0
            rw [this] at hdB0
            exact hdB0
          have hBor : BorrowDistributed s who mBD := by
            refine ⟨hbB, hdB, ?_⟩
            rw [hEqBD, hEqB]
          have hAcctS : mS.acct who = mBD.acct who := by simp [hEqS, St.acct]
          have hdS : accrualStart (mBD.acct who).supplierIndex
              (accrueSide mBD.supplyState mBD.blockNumber (totalSupply mBD)).index ≤
              (accrueSide mBD.supplyState mBD.blockNumber (totalSupply mBD)).index := by
            have h1 : mS.supplyState.index =
              (accrueSide mBD.supplyState mBD.blockNumber (totalSupply mBD)).index := by simp [hEqS]
            rw [hAcctS] at hdS0
            rw [h1] at hdS0
            exact hdS0
          have hSup : SupplyDistributed mBD who mSD := by
            refine ⟨hbS, hdS, ?_⟩
            rw [hEqSD, hEqS]
          exact ⟨mBD, mSD, hBor, hSup, rfl⟩

theorem setSup_some {s m : St} {sup : Nat} (h : setSupplySpeed s sup = some m) :
    (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    m = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by
  unfold setSupplySpeed at h
  by_cases he : s.supplyState.speed = sup
  · simp only [he, ↓reduceIte, Option.some_inj] at h
    have hm : m = s := h.symm
    refine ⟨fun hne => absurd he hne, ?_⟩
    rw [hm]
    simp [he]
  · simp only [he, ↓reduceIte] at h ⊢
    by_cases hb : s.supplyState.block ≤ s.blockNumber
    · simp only [hb, ↓reduceIte, Option.some_inj] at h
      exact ⟨fun _ => hb, by simp [←h, he]⟩
    · simp only [hb, ↓reduceIte] at h
      cases h

theorem setBor_some {s m : St} {bor : Nat} (h : setBorrowSpeed s bor = some m) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    m = { s with borrowState := if s.borrowState.speed = bor then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by
  unfold setBorrowSpeed at h
  by_cases he : s.borrowState.speed = bor
  · simp only [he, ↓reduceIte, Option.some_inj] at h
    have hm : m = s := h.symm
    refine ⟨fun hne => absurd he hne, ?_⟩
    rw [hm]
    simp [he]
  · simp only [he, ↓reduceIte] at h ⊢
    by_cases hb : s.borrowState.block ≤ s.blockNumber
    · simp only [hb, ↓reduceIte, Option.some_inj] at h
      exact ⟨fun _ => hb, by simp [←h, he]⟩
    · simp only [hb, ↓reduceIte] at h
      cases h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  unfold comptroller setCompSpeedInternal at h
  cases hSup0 : setSupplySpeed s a
  case none => simp [hSup0] at h
  case some m =>
    simp [hSup0] at h
    cases hBor0 : setBorrowSpeed m b
    case none => simp [hBor0] at h
    case some m2 =>
      simp [hBor0] at h
      subst h
      obtain ⟨hSupC, hEqSup⟩ := setSup_some hSup0
      obtain ⟨hBorC0, hEqBor⟩ := setBor_some hBor0
      have hBorState : m.borrowState = s.borrowState := by simp [hEqSup]
      have hBorBlock : m.blockNumber = s.blockNumber := by simp [hEqSup]
      have hBorAccts : m.accts = s.accts := by simp [hEqSup]
      have hBorTot : totalBorrows m = totalBorrows s := by simp [hBorAccts, totalBorrows]
      have hBorC : s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
        intro hne
        have hne' : m.borrowState.speed ≠ b := by simp [hBorState, hne]
        have := hBorC0 hne'
        simp [hBorState, hBorBlock] at this
        exact this
      refine ⟨hSupC, hBorC, ?_⟩
      have hY : (if m.borrowState.speed = b then m.borrowState
          else { accrueSide m.borrowState m.blockNumber (totalBorrows m) with speed := b }) =
          (if s.borrowState.speed = b then s.borrowState
          else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) := by
        by_cases he : s.borrowState.speed = b
        · have heM : m.borrowState.speed = b := by simp [hBorState, he]
          simp [he, heM, hBorState]
        · have heM : ¬(m.borrowState.speed = b) := by simp [hBorState, he]
          simp [he, heM, hBorState, hBorBlock, hBorTot]
      rw [hEqBor, hY, hEqSup]

theorem getD_le (l : List Acct) (supIdx borIdx : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ supIdx ∧ a.borrowerIndex ≤ borIdx) (who : Nat) :
    (l.getD who noAcct).supplierIndex ≤ supIdx ∧
    (l.getD who noAcct).borrowerIndex ≤ borIdx := by
  induction l generalizing who with
  | nil =>
    simp
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | cons hd tl ih =>
    cases who with
    | zero =>
      simp
      exact h hd List.mem_cons_self
    | succ n =>
      simp
      apply ih
      intro a ha
      exact h a (List.mem_cons_of_mem _ ha)

theorem acct_le_of_consistent {s : St} (hc : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold Consistent at hc
  unfold St.acct
  obtain ⟨hbS, hbB, hall⟩ := hc
  have hS := (getD_le s.accts s.supplyState.index s.borrowState.index hall who).1
  have hB := (getD_le s.accts s.supplyState.index s.borrowState.index hall who).2
  exact ⟨hS, hB⟩

theorem modify_getD_field (l : List Acct) (who : Nat) (f : Acct → Acct) (get : Acct → Nat)
    (hf : ∀ a, get (f a) = get a) :
    get ((l.modify who f).getD who noAcct) = get (l.getD who noAcct) := by
  induction who generalizing l with
  | zero =>
    cases l with
    | nil => simp
    | cons hd tl => simp [hf]
  | succ n ih =>
    cases l with
    | nil => simp
    | cons hd tl =>
      have hmod : (hd :: tl).modify (n + 1) f = hd :: (tl.modify n f) := by simp
      rw [hmod, List.getD_cons_succ, List.getD_cons_succ]
      exact ih tl

theorem map_sum_modify_preserves (l : List Acct) (who : Nat) (f : Acct → Acct) (get : Acct → Nat)
    (hf : ∀ a, get (f a) = get a) :
    ((l.modify who f).map get).sum = (l.map get).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp
    | succ n => simp
  | cons hd tl ih =>
    cases who with
    | zero => simp [hf]
    | succ n => simp [ih]

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  obtain ⟨hbS, hbB, hall⟩ := (by unfold Consistent at hc; exact hc : Consistent s)
  have hacct := acct_le_of_consistent hc
  cases c with
  | supplyHook who =>
    simp only [comptroller]
    have hU : updateCompSupplyIndex s = some
        { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      simp [updateCompSupplyIndex, hbS]
    simp [hU]
    have hle : (s.acct who).supplierIndex ≤ s.supplyState.index := (hacct who).1
    have hmono : s.supplyState.index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrueSide_index_ge _ _ _
    have hle' : (s.acct who).supplierIndex ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      Nat.le_trans hle hmono
    have hstart : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := accrualStart_le_of_le hle'
    have hd : accrualStart (St.acct { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who).supplierIndex ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.index) ≤ ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }.supplyState.index) := by simpa [St.acct] using hstart
    simp [distributeSupplierComp, hd]
  | borrowHook who =>
    simp only [comptroller]
    have hU : updateCompBorrowIndex s = some
        { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      simp [updateCompBorrowIndex, hbB]
    simp [hU]
    have hle : (s.acct who).borrowerIndex ≤ s.borrowState.index := (hacct who).2
    have hmono : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    have hle' : (s.acct who).borrowerIndex ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans hle hmono
    have hstart : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := accrualStart_le_of_le hle'
    have hd : accrualStart (St.acct { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who).borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.index) ≤ ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.index) := by simpa [St.acct] using hstart
    simp [distributeBorrowerComp, hd]
  | claim who =>
    simp only [comptroller, claimComp]
    have hUB : updateCompBorrowIndex s = some
        { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      simp [updateCompBorrowIndex, hbB]
    simp [hUB]
    have hleB : (s.acct who).borrowerIndex ≤ s.borrowState.index := (hacct who).2
    have hmonoB : s.borrowState.index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrueSide_index_ge _ _ _
    have hleB' := Nat.le_trans hleB hmonoB
    have hstartB := accrualStart_le_of_le hleB'
    have hdB : accrualStart (St.acct { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who).borrowerIndex ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.index) ≤ ({ s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }.borrowState.index) := by simpa [St.acct] using hstartB
    simp [distributeBorrowerComp, hdB]
    sorry
  | setSpeeds a b =>
    simp only [comptroller, setCompSpeedInternal]
    sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
