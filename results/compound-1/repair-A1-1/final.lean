import CompRewards.Spec
namespace CompRewards
def comptroller : Impl := fun s _ => some s

theorem req_calls_succeed : CallsSucceed comptroller := by sorry

theorem req_supply_hook : SupplyHookEffects comptroller := by sorry

theorem req_borrow_hook : BorrowHookEffects comptroller := by sorry

theorem req_claim : ClaimEffects comptroller := by sorry

theorem req_set_speeds : SetSpeedsEffects comptroller := by sorry

theorem req_rewards_bounded : RewardsBounded comptroller := by sorry

theorem req_account_bounded : AccountBounded comptroller := by sorry

theorem req_no_backdated : NoBackdatedRewards comptroller := by sorry

end CompRewards
