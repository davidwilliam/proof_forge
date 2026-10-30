import CompRewards.Spec
namespace CompRewards

def supplyNew (s : St) : Side :=
  accrueSide s.supplyState s.blockNumber (totalSupply s)

def borrowNew (s : St) : Side :=
  accrueSide s.borrowState s.blockNumber (totalBorrows s)

def supplyUpd (s : St) (who : Account) : St :=
  { s with
    supplyState := supplyNew s,
    accts := s.accts.modify who fun a => { a with supplierIndex := (supplyNew s).index, accrued := a.accrued + creditFor a.supply (accrualStart a.supplierIndex (supplyNew s).index) (supplyNew s).index } }

def borrowUpd (s : St) (who : Account) : St :=
  { s with
    borrowState := borrowNew s,
    accts := s.accts.modify who fun a => { a with borrowerIndex := (borrowNew s).index, accrued := a.accrued + creditFor a.borrow (accrualStart a.borrowerIndex (borrowNew s).index) (borrowNew s).index } }

def supplySet (s : St) (a : Nat) : Side :=
  if s.supplyState.speed = a then s.supplyState else { supplyNew s with speed := a }

def borrowSet (s : St) (b : Nat) : Side :=
  if s.borrowState.speed = b then s.borrowState else { borrowNew s with speed := b }

def supplyGuard (s : St) (who : Account) : Prop :=
  s.supplyState.block <= s.blockNumber /\ accrualStart (s.acct who).supplierIndex (supplyNew s).index <= (supplyNew s).index

def borrowGuard (s : St) (who : Account) : Prop :=
  s.borrowState.block <= s.blockNumber /\ accrualStart (s.acct who).borrowerIndex (borrowNew s).index <= (borrowNew s).index

def speedsGuard (s : St) (a b : Nat) : Prop :=
  (s.supplyState.speed != a -> s.supplyState.block <= s.blockNumber) /\ (s.borrowState.speed != b -> s.borrowState.block <= s.blockNumber)

instance decSupplyGuard (s : St) (who : Account) : Decidable (supplyGuard s who) := by
  unfold supplyGuard
  infer_instance

instance decBorrowGuard (s : St) (who : Account) : Decidable (borrowGuard s who) := by
  unfold borrowGuard
  infer_instance

instance decSpeedsGuard (s : St) (a b : Nat) : Decidable (speedsGuard s a b) := by
  unfold speedsGuard
  infer_instance

def comptroller : Impl := fun s c =>
  match c with
  | .supplyHook who => if supplyGuard s who then some (supplyUpd s who) else none
  | .borrowHook who => if borrowGuard s who then some (borrowUpd s who) else none
  | .claim who =>
    if hB : borrowGuard s who then
      let m1 := borrowUpd s who
      if supplyGuard m1 who then some (grant (supplyUpd m1 who) who) else none
    else none
  | .setSpeeds a b =>
    if speedsGuard s a b then
      some ({ s with supplyState := supplySet s a, borrowState := borrowSet s b })
    else none

theorem req_calls_succeed : CallsSucceed comptroller := sorry
theorem req_supply_hook : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook : BorrowHookEffects comptroller := sorry
theorem req_claim : ClaimEffects comptroller := sorry
theorem req_set_speeds : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
