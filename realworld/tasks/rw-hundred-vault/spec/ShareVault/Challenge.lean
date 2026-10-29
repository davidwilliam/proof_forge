import ShareVault.Spec
/-!
# Locked challenge (owner-reviewed; never imports candidate code)

`ShareVault.vault` is a Comparator definition hole. A solution must define it and prove every
theorem below with exactly these statements.
-/

namespace ShareVault

def vault : Impl := sorry

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
