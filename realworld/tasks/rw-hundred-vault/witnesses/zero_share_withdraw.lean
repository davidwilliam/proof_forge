import Solution
/-!
Kernel-checked refutation of the Hundred hToken port (`candidate/Solution.lean`) by an actor
that holds no shares. `redeemUnderlying` of an amount worth less than one share unit truncates
the shares to burn to 0 and still pays the amount. Upstream Compound v2 rejects this case in
`Comptroller.redeemVerify` (`redeemTokens == 0 && redeemAmount > 0`); Hundred's
`CToken.redeemFresh` does not call `redeemVerify`.

Actor 0 deposits 1 satoshi (50 share units) and 99 satoshi are donated, so a share unit is
worth 2 satoshi. Actor 2, with no shares, withdraws 1 satoshi.
-/
open ShareVault

def setup : Vault := run vault empty [.call (.deposit 0 1), .donate 99]

theorem setup_state : setup.assets = 100 ∧ setup.supply = 50 ∧ setup.balance 2 = 0 := by decide

theorem free_withdrawal :
    let s := run vault setup [.call (.withdraw 2 1)]
    (vault setup (.withdraw 2 1)).isSome ∧ s.assets = 99 ∧ s.supply = 50 ∧ s.balance 2 = 0 := by
  decide

/-- REQ-SHARE-VALUE fails: the value of a share falls from 100 / 50 to 99 / 50. -/
theorem port_refuted_share_value : ¬ ShareValueNeverFalls vault := by
  intro h
  have hv := h [.call (.deposit 0 1), .donate 99] [.call (.withdraw 2 1)] (by decide)
  revert hv
  decide
