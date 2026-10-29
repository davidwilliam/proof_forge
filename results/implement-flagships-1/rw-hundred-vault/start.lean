import ShareVault.Spec

namespace ShareVault

-- Placeholder body; replace it with an implementation that meets the spec.
def vault : Impl := fun _ _ => none

theorem req_deposit_succeeds    : DepositSucceeds vault := sorry
theorem req_redeem_succeeds     : RedeemSucceeds vault := sorry
theorem req_withdraw_succeeds   : WithdrawSucceeds vault := sorry
theorem req_deposit_effects     : DepositEffects vault := sorry
theorem req_redeem_effects      : RedeemEffects vault := sorry
theorem req_withdraw_effects    : WithdrawEffects vault := sorry
theorem req_deposit_rounds_down : DepositRoundsDown vault := sorry
theorem req_redeem_rounds_down  : RedeemRoundsDown vault := sorry
theorem req_withdraw_rounds_up  : WithdrawRoundsUp vault := sorry
theorem req_share_value         : ShareValueNeverFalls vault := sorry

end ShareVault
