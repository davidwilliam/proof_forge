import CompRewards.Spec
namespace CompRewards

def supplyCond (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index

def borrowCond (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index

instance instDecSupply (s : St) (who : Account) : Decidable (supplyCond s who) := by
  unfold supplyCond; infer_instance

instance instDecBorrow (s : St) (who : Account) : Decidable (borrowCond s who) := by
  unfold borrowCond; infer_instance

def setCond (s : St) (a b : Nat) : Prop :=
  (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber)

instance instDecSet (s : St) (a b : Nat) : Decidable (setCond s a b) := by
  unfold setCond; infer_instance

def supplyStep (s : St) (who : Account) : St :=
  { s with
    supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
    accts := s.accts.modify who fun a =>
      ({ a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } : Acct) }

def borrowStep (s : St) (who : Account) : St :=
  { s with
    borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
    accts := s.accts.modify who fun a =>
      ({ a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } : Acct) }

def setStep (s : St) (a b : Nat) : St :=
  { s with
    supplyState := (if s.supplyState.speed = a then s.supplyState
      else ({ accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } : Side)),
    borrowState := (if s.borrowState.speed = b then s.borrowState
      else ({ accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } : Side)) }

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => if supplyCond s who then some (supplyStep s who) else none
  | .borrowHook who => if borrowCond s who then some (borrowStep s who) else none
  | .claim who =>
    if _hB : borrowCond s who then
      if _hS : supplyCond (borrowStep s who) who then
        some (grant (supplyStep (borrowStep s who) who) who)
      else none
    else none
  | .setSpeeds a b => if setCond s a b then some (setStep s a b) else none

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hc : supplyCond s who
  · simp only [hc, ite_true] at h
    obtain rfl := Option.some_inj.mp h
    obtain ⟨hc1, hc2⟩ := hc
    exact ⟨hc1, hc2, rfl⟩
  · simp only [hc, ite_false] at h
    contradiction

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hc : borrowCond s who
  · simp only [hc, ite_true] at h
    obtain rfl := Option.some_inj.mp h
    obtain ⟨hc1, hc2⟩ := hc
    exact ⟨hc1, hc2, rfl⟩
  · simp only [hc, ite_false] at h
    contradiction

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  by_cases hB : borrowCond s who
  · simp only [hB, dite_true] at h
    by_cases hS : supplyCond (borrowStep s who) who
    · simp only [hS, dite_true] at h
      obtain rfl := Option.some_inj.mp h
      obtain ⟨hB1, hB2⟩ := hB
      obtain ⟨hS1, hS2⟩ := hS
      exact ⟨borrowStep s who, supplyStep (borrowStep s who) who,
        ⟨hB1, hB2, rfl⟩, ⟨hS1, hS2, rfl⟩, rfl⟩
    · simp only [hS, dite_false] at h
      contradiction
  · simp only [hB, dite_false] at h
    contradiction

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller] at h
  by_cases hc : setCond s a b
  · simp only [hc, ite_true] at h
    obtain rfl := Option.some_inj.mp h
    obtain ⟨hc1, hc2⟩ := hc
    exact ⟨fun hne => hc1 hne, fun hne => hc2 hne, rfl⟩
  · simp only [hc, ite_false] at h
    contradiction

theorem accrue_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)
  · rw [if_pos h]
    exact Nat.le_add_right _ _
  · rw [if_neg h]
    exact Nat.le_refl _

theorem accrue_block (sd : Side) (now total : Nat) :
    (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : (0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total)
  · rw [if_pos h]
  · rw [if_neg h]

theorem accrualStart_le (rec idx : Nat) (h : rec ≤ idx) :
    accrualStart rec idx ≤ idx := by
  unfold accrualStart
  by_cases hr : rec = 0
  · subst hr
    simp only [ite_true]
    by_cases hi : compInitialIndex ≤ idx
    · rw [if_pos hi]; exact hi
    · rw [if_neg hi]; exact Nat.zero_le _
  · rw [if_neg hr]; exact h

theorem getD_mem_of_lt (l : List Acct) (n : Nat) (h : n < l.length) :
    l.getD n noAcct ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp at h
      exact List.mem_cons_of_mem hd (ih n h)

theorem getD_eq_default_of_not_lt (l : List Acct) (n : Nat) (h : ¬ n < l.length) :
    l.getD n noAcct = noAcct := by
  induction l generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.getD_cons_succ]
      apply ih
      simp at h ⊢
      omega

theorem mem_index_le_of_consistent (s : St) (hc0 : Consistent s) (who : Account)
    (hlt : who < s.accts.length) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  have hmem : ∀ a ∈ s.accts,
      a.supplierIndex ≤ s.supplyState.index ∧ a.borrowerIndex ≤ s.borrowState.index :=
    hc0.2.2
  have hm := hmem _ (getD_mem_of_lt _ _ hlt)
  have heq : s.accts.getD who noAcct = s.acct who := rfl
  rw [heq] at hm
  exact hm

theorem acct_le_supply_of_consistent (s : St) (hc0 : Consistent s) (who : Account) :
    (s.acct who).supplierIndex ≤ s.supplyState.index := by
  by_cases hlt : who < s.accts.length
  · exact (mem_index_le_of_consistent s hc0 who hlt).1
  · have hget : s.accts.getD who noAcct = noAcct :=
      getD_eq_default_of_not_lt s.accts who hlt
    have heq : s.acct who = noAcct := by
      unfold St.acct
      exact hget
    rw [heq]
    exact Nat.zero_le _

theorem acct_le_borrow_of_consistent (s : St) (hc0 : Consistent s) (who : Account) :
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  by_cases hlt : who < s.accts.length
  · exact (mem_index_le_of_consistent s hc0 who hlt).2
  · have hget : s.accts.getD who noAcct = noAcct :=
      getD_eq_default_of_not_lt s.accts who hlt
    have heq : s.acct who = noAcct := by
      unfold St.acct
      exact hget
    rw [heq]
    exact Nat.zero_le _

theorem supplyCond_of_consistent (s : St) (hc0 : Consistent s) (who : Account) :
    supplyCond s who := by
  unfold supplyCond
  have hsb : s.supplyState.block ≤ s.blockNumber := hc0.1
  refine ⟨hsb, ?_⟩
  have hle : (s.acct who).supplierIndex ≤ s.supplyState.index :=
    acct_le_supply_of_consistent s hc0 who
  have hge := accrue_ge s.supplyState s.blockNumber (totalSupply s)
  have hle2 : (s.acct who).supplierIndex ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index :=
    Nat.le_trans hle hge
  exact accrualStart_le _ _ hle2

theorem borrowCond_of_consistent (s : St) (hc0 : Consistent s) (who : Account) :
    borrowCond s who := by
  unfold borrowCond
  have hbb : s.borrowState.block ≤ s.blockNumber := hc0.2.1
  refine ⟨hbb, ?_⟩
  have hle : (s.acct who).borrowerIndex ≤ s.borrowState.index :=
    acct_le_borrow_of_consistent s hc0 who
  have hge := accrue_ge s.borrowState s.blockNumber (totalBorrows s)
  have hle2 : (s.acct who).borrowerIndex ≤
      (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index :=
    Nat.le_trans hle hge
  exact accrualStart_le _ _ hle2

theorem setCond_of_consistent (s : St) (hc0 : Consistent s) (a b : Nat) :
    setCond s a b := by
  unfold setCond
  have hsb : s.supplyState.block ≤ s.blockNumber := hc0.1
  have hbb : s.borrowState.block ≤ s.blockNumber := hc0.2.1
  exact ⟨fun _ => hsb, fun _ => hbb⟩

theorem get_supplier_modify (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify who f).getD who noAcct).supplierIndex = (l.getD who noAcct).supplierIndex := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have hm0 : (hd :: tl).modify 0 f = f hd :: tl := rfl
      simp only [hm0, List.getD_cons_zero]
      exact h hd
    | succ n =>
      have hm1 : (hd :: tl).modify (n + 1) f = hd :: tl.modify n f := rfl
      simp only [hm1, List.getD_cons_succ]
      exact ih n

theorem map_supply_modify_eq (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).supply = a.supply) :
    (List.map Acct.supply (l.modify who f)).sum = (List.map Acct.supply l).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have hm : (hd :: tl).modify 0 f = f hd :: tl := rfl
      rw [hm]
      simp only [List.map_cons, List.sum_cons, h hd]
    | succ n =>
      have hm : (hd :: tl).modify (n + 1) f = hd :: tl.modify n f := rfl
      rw [hm]
      simp only [List.map_cons, List.sum_cons, ih n]

theorem map_borrow_modify_eq (l : List Acct) (who : Nat) (f : Acct → Acct)
    (h : ∀ a, (f a).borrow = a.borrow) :
    (List.map Acct.borrow (l.modify who f)).sum = (List.map Acct.borrow l).sum := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero => rfl
    | succ n => rfl
  | cons hd tl ih =>
    cases who with
    | zero =>
      have hm : (hd :: tl).modify 0 f = f hd :: tl := rfl
      rw [hm]
      simp only [List.map_cons, List.sum_cons, h hd]
    | succ n =>
      have hm : (hd :: tl).modify (n + 1) f = hd :: tl.modify n f := rfl
      rw [hm]
      simp only [List.map_cons, List.sum_cons, ih n]

theorem totalSupply_borrowStep (s : St) (who : Account) :
    totalSupply (borrowStep s who) = totalSupply s := by
  unfold totalSupply borrowStep
  simp only
  apply map_supply_modify_eq
  intro a
  rfl

theorem supplyCond_borrowStep (s : St) (who : Account)
    (h1 : s.supplyState.block ≤ s.blockNumber)
    (h2 : accrualStart (s.acct who).supplierIndex
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) :
    supplyCond (borrowStep s who) who := by
  unfold supplyCond
  have htot : totalSupply (borrowStep s who) = totalSupply s :=
    totalSupply_borrowStep s who
  have hblk : (borrowStep s who).blockNumber = s.blockNumber := rfl
  have hss : (borrowStep s who).supplyState = s.supplyState := rfl
  rw [hblk, hss, htot]
  have hsup : ((borrowStep s who).acct who).supplierIndex =
      (s.acct who).supplierIndex := by
    unfold St.acct borrowStep
    simp only
    apply get_supplier_modify
    intro a
    rfl
  rw [hsup]
  exact ⟨h1, h2⟩

theorem req_calls_succeed : CallsSucceed comptroller := by
  intro s c hcon
  cases c with
  | supplyHook who =>
    simp only [comptroller]
    have h := supplyCond_of_consistent s hcon who
    simp only [h, ite_true, Option.isSome_some]
  | borrowHook who =>
    simp only [comptroller]
    have h := borrowCond_of_consistent s hcon who
    simp only [h, ite_true, Option.isSome_some]
  | claim who =>
    simp only [comptroller]
    have hB := borrowCond_of_consistent s hcon who
    simp only [hB, dite_true]
    obtain ⟨h1, h2⟩ := supplyCond_of_consistent s hcon who
    have hS := supplyCond_borrowStep s who h1 h2
    simp only [hS, dite_true, Option.isSome_some]
  | setSpeeds a b =>
    simp only [comptroller]
    have h := setCond_of_consistent s hcon a b
    simp only [h, ite_true, Option.isSome_some]

theorem req_rewards_bounded : RewardsBounded comptroller := by sorry
theorem req_account_bounded : AccountBounded comptroller := by sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := by sorry

end CompRewards
