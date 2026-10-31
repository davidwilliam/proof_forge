import ShareVault.Spec
/-!
Port of the share accounting of Hundred Finance's hToken implementation on Optimism
(`CErc20Delegate` at 0x7100CBCa885905F922a19006cF7fD5d0E1bBb26c, the implementation behind
hWBTC; a Compound v2 fork). Source: `contracts/protocol/token/CToken.sol`,
`contracts/protocol/math/Exponential.sol` and `ExponentialNoError.sol`.

Exchange rates are 18-decimal fixed-point mantissas, and every division truncates:
* `exchangeRateStoredInternal`: `initialExchangeRateMantissa` when `totalSupply == 0`, else
  `getExp(cash + totalBorrows - totalReserves, totalSupply)`.
* `mintFresh`: `mintTokens = divScalarByExpTruncate(actualMintAmount, exchangeRate)`.
* `redeemFresh` with `redeemTokensIn > 0`: `redeemAmount = mulScalarTruncate(exchangeRate,
  redeemTokensIn)`.
* `redeemFresh` with `redeemAmountIn > 0` (`redeemUnderlying`): `redeemTokens =
  divScalarByExpTruncate(redeemAmountIn, exchangeRate)`.
* `redeemFresh` fails on `totalSupply - redeemTokens` or `accountTokens - redeemTokens`
  underflowing, and on `getCashPrior() < redeemAmount`.

Modelled: no borrows and no reserves (`assets` is cash), the comptroller allows every call,
interest has been accrued, and the underlying moves as requested. Arithmetic is unbounded, so
CarefulMath overflow errors never occur. A failure code or a revert is `none`.
-/
namespace ShareVault

/-- `expScale` (ExponentialNoError.sol). -/
def expScale : Nat := 10 ^ 18

/-- hWBTC's `initialExchangeRateMantissa`: 0.02 underlying per share. -/
def initialExchangeRateMantissa : Nat := 2 * 10 ^ 16

/-- `getExp(num, denom)` (Exponential.sol): the mantissa `num * expScale / denom`; division by
zero is a math error. -/
def getExp (num denom : Nat) : Option Nat :=
  if denom = 0 then none else some (num * expScale / denom)

/-- `truncate(exp)` (ExponentialNoError.sol): `exp.mantissa / expScale`. -/
def truncate (mantissa : Nat) : Nat := mantissa / expScale

/-- `mulScalarTruncate(a, scalar)` (Exponential.sol). -/
def mulScalarTruncate (mantissa scalar : Nat) : Nat := truncate (mantissa * scalar)

/-- `divScalarByExpTruncate(scalar, divisor)` (Exponential.sol):
`truncate(getExp(expScale * scalar, divisor.mantissa))`. -/
def divScalarByExpTruncate (scalar mantissa : Nat) : Option Nat :=
  (getExp (expScale * scalar) mantissa).map truncate

/-- `exchangeRateStoredInternal` (CToken.sol). -/
def exchangeRateStored (s : Vault) : Option Nat :=
  if s.supply = 0 then some initialExchangeRateMantissa else getExp s.assets s.supply

/-- `mintFresh(minter, mintAmount)` (CToken.sol). -/
def mintFresh (s : Vault) (minter : Actor) (mintAmount : Nat) : Option Vault :=
  match exchangeRateStored s with
  | none => none
  | some rate =>
    match divScalarByExpTruncate mintAmount rate with
    | none => none
    | some mintTokens =>
      some { assets := s.assets + mintAmount, supply := s.supply + mintTokens,
             balance := fun b => if b = minter then s.balance b + mintTokens else s.balance b }

/-- The two branches of `redeemFresh` (CToken.sol): `(redeemTokens, redeemAmount)`. -/
def redeemAmounts (rate redeemTokensIn redeemAmountIn : Nat) : Option (Nat × Nat) :=
  if redeemTokensIn > 0 then some (redeemTokensIn, mulScalarTruncate rate redeemTokensIn)
  else (divScalarByExpTruncate redeemAmountIn rate).map fun t => (t, redeemAmountIn)

/-- `redeemFresh(redeemer, redeemTokensIn, redeemAmountIn)` (CToken.sol). -/
def redeemFresh (s : Vault) (redeemer : Actor) (redeemTokensIn redeemAmountIn : Nat) :
    Option Vault :=
  match exchangeRateStored s with
  | none => none
  | some rate =>
    match redeemAmounts rate redeemTokensIn redeemAmountIn with
    | none => none
    | some (redeemTokens, redeemAmount) =>
      if s.supply < redeemTokens then none
      else if s.balance redeemer < redeemTokens then none
      else if s.assets < redeemAmount then none
      else some { assets := s.assets - redeemAmount, supply := s.supply - redeemTokens,
                  balance := fun b =>
                    if b = redeemer then s.balance b - redeemTokens else s.balance b }

def vault : Impl := fun s c =>
  match c with
  | .deposit who x => mintFresh s who x
  | .redeem who t => redeemFresh s who t 0
  | .withdraw who x => redeemFresh s who 0 x

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
