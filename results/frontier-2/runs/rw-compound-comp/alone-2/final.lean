import CompRewards.Spec

namespace CompRewards

/-- `accrueSide` never decreases the index. -/
theorem accrueSide_index_le (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

/-- `accrueSide` brings the block up to date. -/
theorem accrueSide_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  split
  · rfl
  · rfl

/-- `accrualStart` never exceeds the market index when the recorded index is below it. -/
theorem accrualStart_le (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  unfold accrualStart
  split
  next h0 =>
    split
    next h1 => exact h1
    next _ => exact Nat.zero_le _
  next _ => exact h

theorem accrualStart_zero_le (index : Nat) : accrualStart 0 index ≤ index := by
  show (if compInitialIndex ≤ index then compInitialIndex else 0) ≤ index
  split
  next h => exact h
  next _ => exact Nat.zero_le _

/-- `updateCompSupplyIndex`: bring the supply index up to date, or revert when
the side block lies ahead of the current block. -/
def updateCompSupplyIndex (s : St) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
  else none

/-- `updateCompBorrowIndex`. -/
def updateCompBorrowIndex (s : St) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
  else none

/-- `distributeSupplierComp`: credit `supplier` for supply rewards since its start.
An account with no recorded index starts at `compInitialIndex` once the market
index has reached it (rewards began there), and at 0 while the market index is
still below it (that index grew from 0). -/
def distributeSupplierComp (s : St) (supplier : Account) : Option St :=
  if accrualStart (s.acct supplier).supplierIndex s.supplyState.index ≤ s.supplyState.index then
    some (s.withAcct supplier fun a =>
      { a with supplierIndex := s.supplyState.index,
               accrued := a.accrued + creditFor a.supply
                 (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index })
  else none

/-- `distributeBorrowerComp`. -/
def distributeBorrowerComp (s : St) (borrower : Account) : Option St :=
  if accrualStart (s.acct borrower).borrowerIndex s.borrowState.index ≤ s.borrowState.index then
    some (s.withAcct borrower fun a =>
      { a with borrowerIndex := s.borrowState.index,
               accrued := a.accrued + creditFor a.borrow
                 (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index })
  else none

/-- `grantCompInternal`: pay out everything accrued when the reserve covers it. -/
def grantCompInternal (s : St) (user : Account) : St := grant s user

/-- `claimComp`: borrow side for the holder, then supply side, then payment. -/
def claimComp (s : St) (holder : Account) : Option St :=
  match updateCompBorrowIndex s with
  | none => none
  | some s1 =>
    match distributeBorrowerComp s1 holder with
    | none => none
    | some s2 =>
      match updateCompSupplyIndex s2 with
      | none => none
      | some s3 =>
        match distributeSupplierComp s3 holder with
        | none => none
        | some s4 => some (grantCompInternal s4 holder)

/-- The supply branch of `setCompSpeedInternal`. -/
def setSupplySpeed (s : St) (supplySpeed : Nat) : Option St :=
  if s.supplyState.speed ≠ supplySpeed then
    match updateCompSupplyIndex s with
    | none => none
    | some s' =>
      some { s' with supplyState := { s'.supplyState with speed := supplySpeed } }
  else some s

/-- The borrow branch of `setCompSpeedInternal`. -/
def setBorrowSpeed (s : St) (borrowSpeed : Nat) : Option St :=
  if s.borrowState.speed ≠ borrowSpeed then
    match updateCompBorrowIndex s with
    | none => none
    | some s' =>
      some { s' with borrowState := { s'.borrowState with speed := borrowSpeed } }
  else some s

/-- `setCompSpeedInternal`: the supply branch, then the borrow branch. -/
def setCompSpeedInternal (s : St) (supplySpeed borrowSpeed : Nat) : Option St :=
  match setSupplySpeed s supplySpeed with
  | none => none
  | some s' => setBorrowSpeed s' borrowSpeed

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who =>
    match updateCompSupplyIndex s with
    | none => none
    | some s1 => distributeSupplierComp s1 who
  | .borrowHook who =>
    match updateCompBorrowIndex s with
    | none => none
    | some s1 => distributeBorrowerComp s1 who
  | .claim who => claimComp s who
  | .setSpeeds a b => setCompSpeedInternal s a b

theorem updateSupply_some (s s1 : St) (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
      s1 = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  unfold updateCompSupplyIndex at h
  by_cases hb : s.supplyState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    exact ⟨hb, (Option.some_inj.mp h).symm⟩
  · simp only [hb, ↓reduceIte] at h
    exact absurd h (by simp)

theorem updateBorrow_some (s s1 : St) (h : updateCompBorrowIndex s = some s1) :
    s.borrowState.block ≤ s.blockNumber ∧
      s1 = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
  unfold updateCompBorrowIndex at h
  by_cases hb : s.borrowState.block ≤ s.blockNumber
  · simp only [hb, ↓reduceIte] at h
    exact ⟨hb, (Option.some_inj.mp h).symm⟩
  · simp only [hb, ↓reduceIte] at h
    exact absurd h (by simp)

theorem distributeSupply_some (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
      s' = s.withAcct who fun a =>
        { a with supplierIndex := s.supplyState.index,
                 accrued := a.accrued + creditFor a.supply
                   (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } := by
  unfold distributeSupplierComp at h
  by_cases hc : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index
  · simp only [hc, ↓reduceIte] at h
    exact ⟨hc, (Option.some_inj.mp h).symm⟩
  · simp only [hc, ↓reduceIte] at h
    exact absurd h (by simp)

theorem distributeBorrow_some (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index ∧
      s' = s.withAcct who fun a =>
        { a with borrowerIndex := s.borrowState.index,
                 accrued := a.accrued + creditFor a.borrow
                   (accrualStart a.borrowerIndex s.borrowState.index) s.borrowState.index } := by
  unfold distributeBorrowerComp at h
  by_cases hc : accrualStart (s.acct who).borrowerIndex s.borrowState.index ≤ s.borrowState.index
  · simp only [hc, ↓reduceIte] at h
    exact ⟨hc, (Option.some_inj.mp h).symm⟩
  · simp only [hc, ↓reduceIte] at h
    exact absurd h (by simp)

/-- The account record is untouched by an index update. -/
theorem acct_updateSupply (s : St) (who : Account) (s1 : St)
    (h : updateCompSupplyIndex s = some s1) : s1.acct who = s.acct who := by
  obtain ⟨-, rfl⟩ := updateSupply_some s s1 h
  rfl

theorem acct_updateBorrow (s : St) (who : Account) (s1 : St)
    (h : updateCompBorrowIndex s = some s1) : s1.acct who = s.acct who := by
  obtain ⟨-, rfl⟩ := updateBorrow_some s s1 h
  rfl

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  match hu : updateCompSupplyIndex s with
  | none => simp [hu] at h
  | some s1 =>
    simp only [hu] at h
    obtain ⟨hb, heq1⟩ := updateSupply_some s s1 hu
    obtain ⟨hc, heq2⟩ := distributeSupply_some s1 who s' h
    have hacct : s1.acct who = s.acct who := by simp [heq1, St.acct]
    rw [hacct] at hc
    have hs1s : s1.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by
      rw [heq1]
    rw [hs1s] at hc
    rw [hs1s] at heq2
    refine ⟨hb, hc, ?_⟩
    subst heq1
    subst heq2
    rfl

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  match hu : updateCompBorrowIndex s with
  | none => simp [hu] at h
  | some s1 =>
    simp only [hu] at h
    obtain ⟨hb, heq1⟩ := updateBorrow_some s s1 hu
    obtain ⟨hc, heq2⟩ := distributeBorrow_some s1 who s' h
    have hacct : s1.acct who = s.acct who := by simp [heq1, St.acct]
    rw [hacct] at hc
    have hs1b : s1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
      rw [heq1]
    rw [hs1b] at hc
    rw [hs1b] at heq2
    refine ⟨hb, hc, ?_⟩
    subst heq1
    subst heq2
    rfl

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  have hcomp : comptroller s (.claim who) = claimComp s who := rfl
  rw [hcomp] at h
  unfold claimComp at h
  match hb1 : updateCompBorrowIndex s with
  | none => simp [hb1] at h
  | some t1 =>
    simp only [hb1] at h
    match hd1 : distributeBorrowerComp t1 who with
    | none => simp [hd1] at h
    | some t2 =>
      simp only [hd1] at h
      match hs1 : updateCompSupplyIndex t2 with
      | none => simp [hs1] at h
      | some t3 =>
        simp only [hs1] at h
        match hd2 : distributeSupplierComp t3 who with
        | none => simp [hd2] at h
        | some t4 =>
          simp only [hd2] at h
          have hpay : grantCompInternal t4 who = grant t4 who := rfl
          rw [hpay] at h
          have hsome : some (grant t4 who) = some s' := h
          have heqpay : grant t4 who = s' := Option.some_inj.mp hsome
          obtain ⟨hbb, heq1⟩ := updateBorrow_some s t1 hb1
          obtain ⟨hbc, heq2⟩ := distributeBorrow_some t1 who t2 hd1
          have hacct1 : t1.acct who = s.acct who := by simp [heq1, St.acct]
          rw [hacct1] at hbc
          have ht1b : t1.borrowState = accrueSide s.borrowState s.blockNumber (totalBorrows s) := by
            rw [heq1]
          rw [ht1b] at hbc
          rw [ht1b] at heq2
          obtain ⟨hsb, heq3⟩ := updateSupply_some t2 t3 hs1
          obtain ⟨hsc, heq4⟩ := distributeSupply_some t3 who t4 hd2
          have hacct2 : t3.acct who = t2.acct who := by simp [heq3, St.acct]
          rw [hacct2] at hsc
          have ht3s : t3.supplyState = accrueSide t2.supplyState t2.blockNumber (totalSupply t2) := by
            rw [heq3]
          rw [ht3s] at hsc
          rw [ht3s] at heq4
          refine ⟨t2, t4, ⟨hbb, hbc, ?_⟩, ⟨hsb, hsc, ?_⟩, ?_⟩
          · subst heq1
            subst heq2
            rfl
          · subst heq3
            subst heq4
            rfl
          · rw [heqpay]

theorem setSupply_eq (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    (s.supplyState.speed = a ∧ mid = s) ∨
      (s.supplyState.speed ≠ a ∧ s.supplyState.block ≤ s.blockNumber ∧
        mid = { { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } with
          supplyState := { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } }) := by
  unfold setSupplySpeed at h
  by_cases hs : s.supplyState.speed = a
  · have hneg : ¬(s.supplyState.speed ≠ a) := by omega
    rw [if_neg hneg] at h
    have heq : s = mid := Option.some_inj.mp h
    exact Or.inl ⟨hs, heq.symm⟩
  · have hs' : s.supplyState.speed ≠ a := hs
    rw [if_pos hs'] at h
    match hu : updateCompSupplyIndex s with
    | none => simp [hu] at h
    | some t =>
      simp only [hu] at h
      obtain ⟨hsb, heq1⟩ := updateSupply_some s t hu
      have heq2 : mid =
          { t with supplyState := { t.supplyState with speed := a } } :=
        (Option.some_inj.mp h).symm
      refine Or.inr ⟨hs', hsb, ?_⟩
      rw [heq2, heq1]

theorem setBorrow_eq (s : St) (b : Nat) (out : St)
    (h : setBorrowSpeed s b = some out) :
    (s.borrowState.speed = b ∧ out = s) ∨
      (s.borrowState.speed ≠ b ∧ s.borrowState.block ≤ s.blockNumber ∧
        out = { { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } with
          borrowState := { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) := by
  unfold setBorrowSpeed at h
  by_cases hb : s.borrowState.speed = b
  · have hneg : ¬(s.borrowState.speed ≠ b) := by omega
    rw [if_neg hneg] at h
    have heq : s = out := Option.some_inj.mp h
    exact Or.inl ⟨hb, heq.symm⟩
  · have hb' : s.borrowState.speed ≠ b := hb
    rw [if_pos hb'] at h
    match hu : updateCompBorrowIndex s with
    | none => simp [hu] at h
    | some t =>
      simp only [hu] at h
      obtain ⟨hbb, heq1⟩ := updateBorrow_some s t hu
      have heq2 : out =
          { t with borrowState := { t.borrowState with speed := b } } :=
        (Option.some_inj.mp h).symm
      refine Or.inr ⟨hb', hbb, ?_⟩
      rw [heq2, heq1]

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  have hcomp : comptroller s (.setSpeeds a b) = setCompSpeedInternal s a b := rfl
  rw [hcomp] at h
  unfold setCompSpeedInternal at h
  match hmid : setSupplySpeed s a with
  | none => simp [hmid] at h
  | some mid =>
    simp only [hmid] at h
    match hout : setBorrowSpeed mid b with
    | none => simp [hout] at h
    | some out =>
      simp only [hout] at h
      have heqout : out = s' := Option.some_inj.mp h
      obtain hsup := setSupply_eq s a mid hmid
      obtain hbor := setBorrow_eq mid b out hout
      have hmid_acct : mid.accts = s.accts := by
        cases hsup with
        | inl h => obtain ⟨-, heq⟩ := h; rw [heq]
        | inr h => obtain ⟨-, -, heq⟩ := h; rw [heq]
      have hbor_spd : mid.borrowState.speed = s.borrowState.speed := by
        cases hsup with
        | inl h => obtain ⟨-, heq⟩ := h; rw [heq]
        | inr h => obtain ⟨-, -, heq⟩ := h; rw [heq]
      have hmid_blk : mid.blockNumber = s.blockNumber := by
        cases hsup with
        | inl h => obtain ⟨-, heq⟩ := h; rw [heq]
        | inr h => obtain ⟨-, -, heq⟩ := h; rw [heq]
      have hmid_tot : totalBorrows mid = totalBorrows s := by simp [totalBorrows, hmid_acct]
      have hmid_blk2 : mid.borrowState.block = s.borrowState.block := by
        cases hsup with
        | inl h => obtain ⟨-, heq⟩ := h; rw [heq]
        | inr h => obtain ⟨-, -, heq⟩ := h; rw [heq]
      refine ⟨?_, ?_, ?_⟩
      · intro hcon
        have : s.supplyState.speed ≠ a := hcon
        cases hsup with
        | inl h => exact absurd h.1 this
        | inr h => exact h.2.1
      · intro hcon
        cases hbor with
        | inl h =>
          have hcontra : s.borrowState.speed = b := hbor_spd ▸ h.1
          exact absurd hcontra hcon
        | inr h =>
          have hle := h.2.1
          rw [hmid_blk2, hmid_blk] at hle
          exact hle
      · cases hsup with
        | inl hsup0 =>
          obtain ⟨hseq, heqmid0⟩ := hsup0
          cases hbor with
          | inl hbor0 =>
            obtain ⟨hbeq, heqout0⟩ := hbor0
            have hbeq0 : s.borrowState.speed = b := hbor_spd ▸ hbeq
            rw [← heqout, heqout0, heqmid0]
            simp only [hseq, hbeq0, ↓reduceIte]
          | inr hbor1 =>
            obtain ⟨hne, hblk, heq⟩ := hbor1
            have hne0 : s.borrowState.speed ≠ b := fun hcon => hne (hbor_spd ▸ hcon)
            rw [← heqout, heq]
            simp only [hseq, hne0, ↓reduceIte]
            rw [heqmid0]
        | inr hsup1 =>
          obtain ⟨hne, hblk, heqmid⟩ := hsup1
          cases hbor with
          | inl hbor0 =>
            obtain ⟨hbeq, heqout0⟩ := hbor0
            have hbeq0 : s.borrowState.speed = b := hbor_spd ▸ hbeq
            rw [← heqout, heqout0, heqmid]
            simp only [hne, hbeq0, ↓reduceIte]
          | inr hbor1 =>
            obtain ⟨hne2, hblk2, heq2⟩ := hbor1
            have hne0 : s.borrowState.speed ≠ b := fun hcon => hne2 (hbor_spd ▸ hcon)
            have hbor_full : mid.borrowState = s.borrowState := by rw [heqmid]
            have hblk_full : mid.blockNumber = s.blockNumber := by rw [heqmid]
            rw [hbor_full, hblk_full, hmid_tot, heqmid] at heq2
            rw [← heqout, heq2]
            simp only [hne, hne0, ↓reduceIte]

/-- Every account record's supplier index lies below the market index in a
consistent state (out-of-bounds accounts are `noAcct` with index 0). -/
theorem getD_supplier_le (l : List Acct) (who : Nat) (idx : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) : (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    exact Nat.zero_le _
  | cons x xs ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero]
      exact h x (by simp)
    | succ n =>
      simp only [List.getD_cons_succ]
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem getD_borrower_le (l : List Acct) (who : Nat) (idx : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) : (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    simp only [List.getD_nil]
    exact Nat.zero_le _
  | cons x xs ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero]
      exact h x (by simp)
    | succ n =>
      simp only [List.getD_cons_succ]
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem acct_supplier_le_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  obtain ⟨-, -, hmem⟩ := hc
  have h1 : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index := fun a ha => (hmem a ha).1
  exact getD_supplier_le s.accts who s.supplyState.index h1

theorem acct_borrower_le_of_consistent (s : St) (who : Account) (hc : Consistent s) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  obtain ⟨-, -, hmem⟩ := hc
  have h1 : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index := fun a ha => (hmem a ha).2
  exact getD_borrower_le s.accts who s.borrowState.index h1

/-- `List.modify` at `who` preserves the supplier index when `f` does. -/
theorem modify_getD_supplier (l : List Acct) (who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify who f).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.modify, List.getD]
    | succ n => simp [List.modify, List.getD]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp [List.modify, List.getD, hf]
    | succ n =>
      simp [List.modify, List.getD]
      exact ih n

/-- `List.modify` preserves the borrower index when `f` does. -/
theorem modify_getD_borrower (l : List Acct) (who : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    ((l.modify who f).getD who noAcct).borrowerIndex = (l.getD who noAcct).borrowerIndex := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.modify, List.getD]
    | succ n => simp [List.modify, List.getD]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp [List.modify, List.getD, hf]
    | succ n =>
      simp [List.modify, List.getD]
      exact ih n

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hc
  obtain ⟨hsb, hbb, hmem⟩ := hc
  cases c
  case supplyHook who =>
    have hrec : (s.acct who).supplierIndex ≤ s.supplyState.index := by
      have h1 : ∀ a ∈ s.accts, a.supplierIndex ≤ s.supplyState.index :=
        fun a ha => (hmem a ha).1
      exact getD_supplier_le s.accts who s.supplyState.index h1
    have hnew : (s.acct who).supplierIndex ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      Nat.le_trans hrec (accrueSide_index_le _ _ _)
    have hcond : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
      accrualStart_le _ _ hnew
    have hu : updateCompSupplyIndex s =
        some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
      unfold updateCompSupplyIndex
      rw [if_pos hsb]
    have hdist : (distributeSupplierComp
        { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who).isSome = true := by
      unfold distributeSupplierComp
      have hacct : (St.acct
          { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) }
          who).supplierIndex = (s.acct who).supplierIndex := rfl
      rw [hacct]
      simp [hcond]
    have hcomp : comptroller s (Call.supplyHook who) =
        distributeSupplierComp
          { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } who := by
      simp only [comptroller, hu]
    rw [hcomp]
    exact hdist
  case borrowHook who =>
    have hrec : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
      have h1 : ∀ a ∈ s.accts, a.borrowerIndex ≤ s.borrowState.index :=
        fun a ha => (hmem a ha).2
      exact getD_borrower_le s.accts who s.borrowState.index h1
    have hnew : (s.acct who).borrowerIndex ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      Nat.le_trans hrec (accrueSide_index_le _ _ _)
    have hcond : accrualStart (s.acct who).borrowerIndex
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
        (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
      accrualStart_le _ _ hnew
    have hu : updateCompBorrowIndex s =
        some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by
      unfold updateCompBorrowIndex
      rw [if_pos hbb]
    have hdist : (distributeBorrowerComp
        { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who).isSome = true := by
      unfold distributeBorrowerComp
      have hacct : (St.acct
          { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) }
          who).borrowerIndex = (s.acct who).borrowerIndex := rfl
      rw [hacct]
      simp [hcond]
    have hcomp : comptroller s (Call.borrowHook who) =
        distributeBorrowerComp
          { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } who := by
      simp only [comptroller, hu]
    rw [hcomp]
    exact hdist
  case claim who => sorry
  case setSpeeds a b => sorry
/-- Scaled per-account potential: credited (scaled) plus pending plus unindexed (scaled,
only while holding a position). One block of emission grows it by at most the emission. -/
def PhiWho (s : St) (who : Account) : Nat :=
  ((s.acct who).accrued + (s.acct who).wallet) * doubleScale +
  (s.acct who).supply *
    (s.supplyState.index - accrualStart (s.acct who).supplierIndex s.supplyState.index) +
  (s.acct who).borrow *
    (s.borrowState.index - accrualStart (s.acct who).borrowerIndex s.borrowState.index) +
  (if 0 < (s.acct who).supply then (s.blockNumber - s.supplyState.block) * s.supplyState.speed else 0) *
    doubleScale +
  (if 0 < (s.acct who).borrow then (s.blockNumber - s.borrowState.block) * s.borrowState.speed else 0) *
    doubleScale

/-- Any account's supply is bounded by the total supply. -/
theorem getD_supply_le_sum (l : List Acct) (who : Nat) :
    (l.getD who noAcct).supply ≤ (l.map Acct.supply).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.getD, noAcct]
    | succ n => simp [List.getD, noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero, List.map_cons, List.sum_cons]
      exact Nat.le_add_right _ _
    | succ n =>
      simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
      calc (xs.getD n noAcct).supply ≤ (xs.map Acct.supply).sum := ih n
        _ ≤ x.supply + (xs.map Acct.supply).sum := Nat.le_add_left _ _

theorem getD_borrow_le_sum (l : List Acct) (who : Nat) :
    (l.getD who noAcct).borrow ≤ (l.map Acct.borrow).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => simp [List.getD, noAcct]
    | succ n => simp [List.getD, noAcct]
  | cons x xs ih =>
    cases who with
    | zero =>
      simp only [List.getD_cons_zero, List.map_cons, List.sum_cons]
      exact Nat.le_add_right _ _
    | succ n =>
      simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
      calc (xs.getD n noAcct).borrow ≤ (xs.map Acct.borrow).sum := ih n
        _ ≤ x.borrow + (xs.map Acct.borrow).sum := Nat.le_add_left _ _

/-- `(x / y) * y ≤ x`. -/
theorem div_mul_le' (x y : Nat) : x / y * y ≤ x := by
  calc x / y * y = y * (x / y) := Nat.mul_comm _ _
    _ ≤ y * (x / y) + x % y := Nat.le_add_right _ _
    _ = x := Nat.div_add_mod x y

/-- `accrualStart` is monotone in the market index. -/
theorem accrualStart_mono (recorded oldIdx newIdx : Nat) (hle : oldIdx ≤ newIdx) :
    accrualStart recorded oldIdx ≤ accrualStart recorded newIdx := by
  by_cases h0 : recorded = 0
  · subst h0
    by_cases h1 : compInitialIndex ≤ oldIdx
    · have h2 : compInitialIndex ≤ newIdx := Nat.le_trans h1 hle
      unfold accrualStart
      simp [h1, h2]
    · unfold accrualStart
      simp only [↓reduceIte, h1]
      exact Nat.zero_le _
  · unfold accrualStart
    simp [h0]

/-- `(a + d) - b ≤ (a - b) + d`. -/
theorem nat_sub_add_le (a b d : Nat) : (a + d) - b ≤ (a - b) + d := by
  omega

/-- `floor(x / S) * S ≤ x`. -/
theorem credit_scaled_le (x : Nat) : x / doubleScale * doubleScale ≤ x := div_mul_le' x doubleScale

/-- One `advance` grows `PhiWho` by at most the emission. -/
theorem PhiWho_advance (s : St) (k who : Nat) :
    PhiWho ({ s with blockNumber := s.blockNumber + k }) who ≤
      PhiWho s who + k * (s.supplyState.speed + s.borrowState.speed) * doubleScale := by
  unfold PhiWho
  have hacct : (St.acct { s with blockNumber := s.blockNumber + k } who) =
      (St.acct s who) := rfl
  rw [hacct]
  have hsup : ({ s with blockNumber := s.blockNumber + k } : St).supplyState = s.supplyState := rfl
  have hbor : ({ s with blockNumber := s.blockNumber + k } : St).borrowState = s.borrowState := rfl
  have hblk : ({ s with blockNumber := s.blockNumber + k } : St).blockNumber = s.blockNumber + k := rfl
  rw [hsup, hbor, hblk]
  have hsub_s : s.blockNumber + k - s.supplyState.block ≤
      (s.blockNumber - s.supplyState.block) + k := by omega
  have hsub_b : s.blockNumber + k - s.borrowState.block ≤
      (s.blockNumber - s.borrowState.block) + k := by omega
  have hmul_s : (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed ≤
      (s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed := by
    calc (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed
        ≤ ((s.blockNumber - s.supplyState.block) + k) * s.supplyState.speed :=
          Nat.mul_le_mul_right _ hsub_s
      _ = (s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed := by
          rw [Nat.add_mul]
  have hmul_b : (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed ≤
      (s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed := by
    calc (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed
        ≤ ((s.blockNumber - s.borrowState.block) + k) * s.borrowState.speed :=
          Nat.mul_le_mul_right _ hsub_b
      _ = (s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed := by
          rw [Nat.add_mul]
  by_cases hs : 0 < (s.acct who).supply <;> by_cases hb : 0 < (s.acct who).borrow <;>
    simp only [hs, hb, ↓reduceIte]
  · have h1 : (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed * doubleScale ≤
        ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed) * doubleScale :=
        Nat.mul_le_mul_right _ hmul_s
    have h2 : (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed * doubleScale ≤
        ((s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed) * doubleScale :=
        Nat.mul_le_mul_right _ hmul_b
    have h3 : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed) *
          doubleScale +
        (((s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed) *
          doubleScale) ≤
        ((s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale +
          (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale) +
        k * (s.supplyState.speed + s.borrowState.speed) * doubleScale := by
      have e1 : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed) *
          doubleScale = (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale +
          k * s.supplyState.speed * doubleScale := Nat.add_mul _ _ _
      have e2 : ((s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed) *
          doubleScale = (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale +
          k * s.borrowState.speed * doubleScale := Nat.add_mul _ _ _
      rw [e1, e2]
      have e3 : k * (s.supplyState.speed + s.borrowState.speed) * doubleScale =
          k * s.supplyState.speed * doubleScale + k * s.borrowState.speed * doubleScale := by
        rw [Nat.mul_add, Nat.add_mul]
      omega
    omega
  · have h1 : (s.blockNumber + k - s.supplyState.block) * s.supplyState.speed * doubleScale ≤
        ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed) * doubleScale :=
        Nat.mul_le_mul_right _ hmul_s
    have h3 : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed) *
          doubleScale ≤ (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale +
        k * (s.supplyState.speed + s.borrowState.speed) * doubleScale := by
      have e1 : ((s.blockNumber - s.supplyState.block) * s.supplyState.speed + k * s.supplyState.speed) *
          doubleScale = (s.blockNumber - s.supplyState.block) * s.supplyState.speed * doubleScale +
          k * s.supplyState.speed * doubleScale := Nat.add_mul _ _ _
      rw [e1]
      have e3 : k * s.supplyState.speed * doubleScale ≤
          k * (s.supplyState.speed + s.borrowState.speed) * doubleScale := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        omega
      omega
    omega
  · have h2 : (s.blockNumber + k - s.borrowState.block) * s.borrowState.speed * doubleScale ≤
        ((s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed) * doubleScale :=
        Nat.mul_le_mul_right _ hmul_b
    have h3 : ((s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed) *
          doubleScale ≤ (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale +
        k * (s.supplyState.speed + s.borrowState.speed) * doubleScale := by
      have e2 : ((s.blockNumber - s.borrowState.block) * s.borrowState.speed + k * s.borrowState.speed) *
          doubleScale = (s.blockNumber - s.borrowState.block) * s.borrowState.speed * doubleScale +
          k * s.borrowState.speed * doubleScale := Nat.add_mul _ _ _
      rw [e2]
      have e3 : k * s.borrowState.speed * doubleScale ≤
          k * (s.supplyState.speed + s.borrowState.speed) * doubleScale := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        omega
      omega
    omega
  · omega

/-- A `drip` leaves `PhiWho` unchanged. -/
theorem PhiWho_drip (s : St) (x who : Nat) :
    PhiWho ({ s with reserve := s.reserve + x }) who = PhiWho s who := rfl

/-- Supply accrue: pending growth is covered by the unindexed emission. -/
theorem accrue_supply_le (supply recorded : Nat) (sd : Side) (now T : Nat)
    (hle : supply ≤ T) :
    supply * ((accrueSide sd now T).index - accrualStart recorded (accrueSide sd now T).index) ≤
      supply * (sd.index - accrualStart recorded sd.index) + (now - sd.block) * sd.speed * doubleScale := by
  sorry

theorem accrue_borrow_le (borrow recorded : Nat) (sd : Side) (now T : Nat)
    (hle : borrow ≤ T) :
    borrow * ((accrueSide sd now T).index - accrualStart recorded (accrueSide sd now T).index) ≤
      borrow * (sd.index - accrualStart recorded sd.index) + (now - sd.block) * sd.speed * doubleScale := by
  sorry

/-- Supply distribute: the scaled credit is covered by the pending drop. -/
theorem distribute_supply_le (accr wall supply start idx : Nat) :
    (accr + creditFor supply start idx + wall) * doubleScale ≤
      (accr + wall) * doubleScale + supply * (idx - start) := by
  sorry

theorem distribute_borrow_le (accr wall borrow start idx : Nat) :
    (accr + creditFor borrow start idx + wall) * doubleScale ≤
      (accr + wall) * doubleScale + borrow * (idx - start) := by
  sorry

theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
