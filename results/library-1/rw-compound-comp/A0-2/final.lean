import CompRewards.Spec
namespace CompRewards
#print List.modify
#print List.getD
#print List.modifyTailIdx
#check @List.length_modify
#check @List.getElem_modify
#check @List.ext_getElem
def comptroller : Impl := fun s _ => some s
theorem req_calls_succeed : CallsSucceed comptroller := sorry
theorem req_supply_hook : SupplyHookEffects comptroller := sorry
theorem req_borrow_hook : BorrowHookEffects comptroller := sorry
theorem req_claim : ClaimEffects comptroller := sorry
theorem req_set_speeds : SetSpeedsEffects comptroller := sorry
theorem req_rewards_bounded : RewardsBounded comptroller := sorry
theorem req_account_bounded : AccountBounded comptroller := sorry
theorem req_no_backdated : NoBackdatedRewards comptroller := sorry
end CompRewards
