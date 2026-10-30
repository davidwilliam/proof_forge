import CompRewards.Spec

namespace CompRewards

def borrowStep (s : St) (who : Account) : St :=
  { s with
    borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s),
    accts := s.accts.modify who fun a =>
      { a with
        borrowerIndex := (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index,
        accrued := a.accrued + creditFor a.borrow
          (accrualStart a.borrowerIndex (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index)
          (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index } }

def supplyStep (s : St) (who : Account) : St :=
  { s with
    supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
    accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
          (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } }

def borrowCond (s : St) (who : Account) : Prop :=
  s.borrowState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).borrowerIndex
    (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index ≤
  (accrueSide s.borrowState s.blockNumber (totalBorrows s)).index

def supplyCond (s : St) (who : Account) : Prop :=
  s.supplyState.block ≤ s.blockNumber ∧
  accrualStart (s.acct who).supplierIndex
    (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
  (accrueSide s.supplyState s.blockNumber (totalSupply s)).index

def speedCond (s : St) (sup bor : Nat) : Prop :=
  (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
  (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber)

instance borrowCondDec (s : St) (who : Account) : Decidable (borrowCond s who) := by
  unfold borrowCond; infer_instance

instance supplyCondDec (s : St) (who : Account) : Decidable (supplyCond s who) := by
  unfold supplyCond; infer_instance

instance speedCondDec (s : St) (sup bor : Nat) : Decidable (speedCond s sup bor) := by
  unfold speedCond; infer_instance

def comptroller : Impl := fun s c => match c with
  | .supplyHook who => if _ : supplyCond s who then some (supplyStep s who) else none
  | .borrowHook who => if _ : borrowCond s who then some (borrowStep s who) else none
  | .claim who =>
    if _ : borrowCond s who then
      if _ : supplyCond (borrowStep s who) who then some (grant (supplyStep (borrowStep s who) who) who)
      else none
    else none
  | .setSpeeds sup bor =>
    if _ : speedCond s sup bor then
      some { s with
        supplyState := if s.supplyState.speed = sup then s.supplyState
          else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup },
        borrowState := if s.borrowState.speed = bor then s.borrowState
          else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } }
    else none

theorem req_calls_succeed : CallsSucceed comptroller := sorry

theorem req_supply_hook : SupplyHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  unfold supplyCond supplyStep at h
  split at h
  · next heq =>
    obtain ⟨h1, h2⟩ := heq
    refine ⟨h1, h2, ?_⟩
    cases h
    rfl
  · next heq => cases h

theorem req_borrow_hook : BorrowHookEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  unfold borrowCond borrowStep at h
  split at h
  · next heq =>
    obtain ⟨h1, h2⟩ := heq
    refine ⟨h1, h2, ?_⟩
    cases h
    rfl
  · next heq => cases h

theorem req_claim : ClaimEffects comptroller := by
  intro s who s' h
  simp only [comptroller] at h
  split at h
  · next hb =>
    split at h
    · next hs =>
      cases h
      obtain ⟨hb1, hb2⟩ := hb
      obtain ⟨hs1, hs2⟩ := hs
      apply Exists.intro (borrowStep s who)
      apply Exists.intro (supplyStep (borrowStep s who) who)
      apply And.intro
      · exact ⟨hb1, hb2, rfl⟩
      · apply And.intro
        · exact ⟨hs1, hs2, rfl⟩
        · rfl
    · next hs =>
      cases h
  · next hb =>
    cases h

theorem req_set_speeds : SetSpeedsEffects comptroller := by
  intro s a b s' h
  simp only [comptroller] at h
  unfold speedCond at h
  split at h
  · next heq =>
    obtain ⟨hsup, hbor⟩ := heq
    refine ⟨hsup, hbor, ?_⟩
    cases h
    rfl
  · next heq =>
    cases h

theorem req_rewards_bounded : RewardsBounded comptroller := sorry

theorem req_account_bounded : AccountBounded comptroller := sorry

theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
