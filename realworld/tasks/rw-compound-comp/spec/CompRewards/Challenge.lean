import CompRewards.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`CompRewards.comptroller` is a Comptroller definition hole. A solution must define it and prove
every theorem below with exactly these statements.
-/

namespace CompRewards

def comptroller : Impl := sorry

theorem req_calls_succeed       : CallsSucceed comptroller := sorry
theorem req_supply_hook         : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook         : BorrowHookEffects comptroller := sorry
theorem req_claim               : ClaimEffects comptroller := sorry
theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
