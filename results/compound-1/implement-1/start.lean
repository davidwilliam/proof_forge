import CompRewards.Spec

namespace CompRewards

-- Placeholder body; replace it with an implementation that meets the spec.
def comptroller : Impl := fun _ _ => none

theorem req_calls_succeed       : CallsSucceed comptroller := sorry
theorem req_supply_hook         : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook         : BorrowHookEffects comptroller := sorry
theorem req_claim               : ClaimEffects comptroller := sorry
theorem req_set_speeds          : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded     : RewardsBounded comptroller := sorry
theorem req_account_bounded     : AccountBounded comptroller := sorry
theorem req_no_backdated        : NoBackdatedRewards comptroller := sorry

end CompRewards
