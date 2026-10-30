import CompRewards.Spec
namespace CompRewards

def doSupply (s : St) (who : Account) : Option St :=
  if s.supplyState.block ≤ s.blockNumber then
    if accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index then
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s), accts := s.accts.modify who fun a => { a with supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index) (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }
    else none
  else none

def doBorrow (s : St) (who : Account) : Option St :=
  if s.borrowState.block ≤ s.blockNumber then
    if accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index then
      some { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s), accts := s.accts.modify who fun a => { a with borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index) (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }
    else none
  else none

def doSetSpeeds (s : St) (sup bor : Nat) : Option St :=
  if s.supplyState.speed = sup ∨ s.supplyState.block ≤ s.blockNumber then
    if s.borrowState.speed = bor ∨ s.borrowState.block ≤ s.blockNumber then
      some { s with supplyState := if s.supplyState.speed = sup then s.supplyState else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup }, borrowState := if s.borrowState.speed = bor then s.borrowState else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }
    else none
  else none

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => doSupply s who
  | .borrowHook who => doBorrow s who
  | .claim who =>
    match doBorrow s who with
    | none => none
    | some m1 =>
      match doSupply m1 who with
      | none => none
      | some m2 => some (grant m2 who)
  | .setSpeeds sup bor => doSetSpeeds s sup bor

theorem accrue_block_thm (sd : Side) (now total : Nat) : (accrueSide sd now total).block = now := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos h]
  · rw [if_neg h]

theorem accrue_ge_thm (sd : Side) (now total : Nat) : sd.index ≤ (accrueSide sd now total).index := by
  unfold accrueSide
  by_cases h : 0 < now - sd.block ∧ 0 < sd.speed ∧ 0 < total
  · rw [if_pos h]
    exact Nat.le_add_right _ _
  · rw [if_neg h]
    exact Nat.le_refl _

theorem as_le_of_thm (rec idx : Nat) (h : rec ≤ idx) : accrualStart rec idx ≤ idx := by
  unfold accrualStart
  by_cases h0 : rec = 0
  · subst h0
    by_cases h1 : compInitialIndex ≤ idx
    · rw [if_pos rfl, if_pos h1]
      exact h1
    · rw [if_pos rfl, if_neg h1]
      exact Nat.zero_le _
  · rw [if_neg h0]
    exact h

theorem getD_sup_le_aux (l : List Acct) (who idx : Nat) (h : ∀ a ∈ l, a.supplierIndex ≤ idx) : (l.getD who noAcct).supplierIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero =>
      show (noAcct).supplierIndex ≤ idx
      unfold noAcct
      exact Nat.zero_le _
    | succ n =>
      show (noAcct).supplierIndex ≤ idx
      unfold noAcct
      exact Nat.zero_le _
  | cons hd tl ih =>
    cases who with
    | zero =>
      show hd.supplierIndex ≤ idx
      exact h hd (by simp)
    | succ n =>
      show (tl.getD n noAcct).supplierIndex ≤ idx
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem getD_bor_le_aux (l : List Acct) (who idx : Nat) (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) : (l.getD who noAcct).borrowerIndex ≤ idx := by
  induction l generalizing who with
  | nil =>
    cases who with
    | zero =>
      show (noAcct).borrowerIndex ≤ idx
      unfold noAcct
      exact Nat.zero_le _
    | succ n =>
      show (noAcct).borrowerIndex ≤ idx
      unfold noAcct
      exact Nat.zero_le _
  | cons hd tl ih =>
    cases who with
    | zero =>
      show hd.borrowerIndex ≤ idx
      exact h hd (by simp)
    | succ n =>
      show (tl.getD n noAcct).borrowerIndex ≤ idx
      apply ih
      intro a ha
      exact h a (by simp [ha])

theorem rec_sup_le_thm (s : St) (who : Account) (h : Consistent s) : (s.acct who).supplierIndex ≤ s.supplyState.index := by
  unfold St.acct
  exact getD_sup_le_aux s.accts who s.supplyState.index (fun a ha => (h.2.2 a ha).1)

theorem rec_bor_le_thm (s : St) (who : Account) (h : Consistent s) : (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  unfold St.acct
  exact getD_bor_le_aux s.accts who s.borrowState.index (fun a ha => (h.2.2 a ha).2)

theorem supply_start_ok_thm (s : St) (who : Account) (h : Consistent s) : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  apply as_le_of_thm
  exact Nat.le_trans (rec_sup_le_thm s who h) (accrue_ge_thm _ _ _)

theorem borrow_start_ok_thm (s : St) (who : Account) (h : Consistent s) : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index := by
  apply as_le_of_thm
  exact Nat.le_trans (rec_bor_le_thm s who h) (accrue_ge_thm _ _ _)

theorem doSupply_spec_thm (s : St) (who : Account) (s' : St) (h : doSupply s who = some s') : SupplyDistributed s who s' := by
  unfold doSupply at h
  by_cases h1 : s.supplyState.block ≤ s.blockNumber
  · rw [if_pos h1] at h
    by_cases h2 : accrualStart (s.acct who).supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤ (accrueSide s.supplyState s.blockNumber (totalSupply s)).index
    · rw [if_pos h2] at h
      refine ⟨h1, h2, ?_⟩
      cases h
      rfl
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    cases h

theorem doBorrow_spec_thm (s : St) (who : Account) (s' : St) (h : doBorrow s who = some s') : BorrowDistributed s who s' := by
  unfold doBorrow at h
  by_cases h1 : s.borrowState.block ≤ s.blockNumber
  · rw [if_pos h1] at h
    by_cases h2 : accrualStart (s.acct who).borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤ (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index
    · rw [if_pos h2] at h
      refine ⟨h1, h2, ?_⟩
      cases h
      rfl
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    cases h

theorem doSetSpeeds_spec_thm (s : St) (sup bor : Nat) (m : St) (h : doSetSpeeds s sup bor = some m) : SpeedsSet s sup bor m := by
  unfold doSetSpeeds at h
  by_cases hs : s.supplyState.speed = sup ∨ s.supplyState.block ≤ s.blockNumber
  · rw [if_pos hs] at h
    by_cases hb : s.borrowState.speed = bor ∨ s.borrowState.block ≤ s.blockNumber
    · rw [if_pos hb] at h
      cases h
      refine ⟨?_, ?_, rfl⟩
      · intro hne
        rcases hs with he | hle
        · exact absurd he hne
        · exact hle
      · intro hne
        rcases hb with he | hle
        · exact absurd he hne
        · exact hle
    · rw [if_neg hb] at h
      cases h
  · rw [if_neg hs] at h
    cases h

theorem req_calls_succeed : CallsSucceed comptroller := sorry

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  have h' : doSupply s who = some s' := h
  exact doSupply_spec_thm s who s' h'

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  have h' : doBorrow s who = some s' := h
  exact doBorrow_spec_thm s who s' h'

theorem req_claim : ClaimEffects comptroller := sorry

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  have h' : doSetSpeeds s a b = some s' := h
  exact doSetSpeeds_spec_thm s a b s' h'

theorem req_rewards_bounded : RewardsBounded comptroller := sorry

theorem req_account_bounded : AccountBounded comptroller := sorry

theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
