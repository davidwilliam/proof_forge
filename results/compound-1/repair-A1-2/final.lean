import CompRewards.Spec
namespace CompRewards

theorem mod_zero_thm (l : List Acct) (f : Acct → Acct) :
    l.modify 0 f = match l with | [] => [] | a :: as => f a :: as := by
  cases l <;> rfl

theorem mod_succ_thm (l : List Acct) (n : Nat) (f : Acct → Acct) :
    l.modify (n+1) f = match l with | [] => [] | a :: as => a :: as.modify n f := by
  cases l <;> rfl

theorem getD_zero_thm (hd : Acct) (tl : List Acct) :
    (hd :: tl).getD 0 noAcct = hd := by rfl

theorem getD_succ_thm (hd : Acct) (tl : List Acct) (n : Nat) :
    (hd :: tl).getD (n+1) noAcct = tl.getD n noAcct := by rfl

theorem getD_nil_zero : ([] : List Acct).getD 0 noAcct = noAcct := by rfl

theorem getD_nil_succ (n : Nat) : ([] : List Acct).getD (n+1) noAcct = noAcct := by rfl

def supplyStep (s : St) (who : Account) : Option St := sorry
def borrowStep (s : St) (who : Account) : Option St := sorry
def speedsStep (s : St) (sup bor : Nat) : Option St := sorry
def comptroller : Impl := sorry

theorem req_calls_succeed : CallsSucceed comptroller := sorry

theorem req_supply_hook : SupplyHookEffects comptroller := sorry

theorem req_borrow_hook : BorrowHookEffects comptroller := sorry

theorem req_claim : ClaimEffects comptroller := sorry

theorem req_set_speeds : SetSpeedsEffects comptroller := sorry

theorem req_rewards_bounded : RewardsBounded comptroller := sorry

theorem req_account_bounded : AccountBounded comptroller := sorry

theorem req_no_backdated : NoBackdatedRewards comptroller := sorry

end CompRewards
