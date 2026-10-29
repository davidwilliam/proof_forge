import Solution
/-!
Unit tests of the kind Compound v2 ships, run against the Hundred hToken port
(`candidate/Solution.lean`). Each test is checked by the Lean kernel (`decide`).

Tests 1 to 8 restate tests of compound-finance/compound-protocol v2.8.1
(commit 23eac9425accafb82551777c93896ee7678a85a3): `tests/Tokens/mintAndRedeemTest.js` uses an
exchange rate of 50e3 (50,000 underlying per cToken), mints 10e4 underlying for 2 cTokens and
redeems 10e3 cTokens for 5e8 underlying, by `redeem` and by `redeemUnderlying`, and checks the
failure paths; `tests/Tokens/cTokenTest.js` checks `exchangeRateStored`. Compound's harness sets
the exchange rate directly; here a state with `assets / supply` equal to that rate is used.
Tests 9 to 12 are the usual end-to-end scenarios: deposit and redeem round trips, two
depositors, and interest or a donation raising the value of every share.

All twelve pass. None of them withdraws from a market with very few shares outstanding and a
large balance, which is what the attack does (`witnesses/hundred_attack.lean`).
-/
open ShareVault

/-- A state with `assets` and `supply`, all shares held by `holder`. -/
def market (assets supply : Nat) (holder : Actor) : Vault :=
  { assets := assets, supply := supply, balance := fun b => if b = holder then supply else 0 }

def minter : Actor := 2
def redeemer : Actor := 3

/-- Exchange rate 50e3: 5e8 underlying backing 1e4 cTokens, all held by the redeemer. -/
def rate50k : Vault := market 500000000 10000 redeemer

/-- 1. `exchangeRateStored` returns the initial exchange rate with zero supply. -/
example : exchangeRateStored empty = some initialExchangeRateMantissa := by decide

/-- 2. `exchangeRateStored` with cash and supply (cTokenTest: 500 cash, 5 cTokens, rate 100). -/
example : exchangeRateStored (market (500 * 10 ^ 18) (5 * 10 ^ 18) 0) = some (100 * 10 ^ 18) := by
  decide

/-- 3. mintFresh mints the correct number of tokens: 10e4 at 50e3 gives 2, and moves the cash. -/
example :
    let s := run vault rate50k [.call (.deposit minter 100000)]
    s.balance minter = 2 ∧ s.supply = 10002 ∧ s.assets = 500100000 ∧ s.balance redeemer = 10000 := by
  decide

/-- 4. mintFresh fails if the exchange calculation fails (exchange rate 0). -/
example : (vault (market 0 10000 redeemer) (.deposit minter 100000)).isNone := by decide

/-- 5. redeemFresh by tokens: 10e3 cTokens at 50e3 pay 5e8. -/
example :
    let s := run vault rate50k [.call (.redeem redeemer 10000)]
    s.balance redeemer = 0 ∧ s.supply = 0 ∧ s.assets = 0 := by
  decide

/-- 6. redeemFresh by amount: 5e8 underlying burns 10e3 cTokens. -/
example :
    let s := run vault rate50k [.call (.withdraw redeemer 500000000)]
    s.balance redeemer = 0 ∧ s.supply = 0 ∧ s.assets = 0 := by
  decide

/-- 7. redeemFresh fails if the account balance would underflow, by tokens and by amount. -/
example : (vault rate50k (.redeem minter 10000)).isNone ∧
    (vault rate50k (.withdraw minter 500000000)).isNone := by
  decide

/-- 8. redeemFresh fails if total supply is less than the redemption. -/
example : (vault rate50k (.redeem redeemer 10001)).isNone := by decide

/-- 9. Deposit 1 WBTC into an empty market at the initial rate (50 shares per satoshi), then
redeem every share: the depositor gets 1 WBTC back and the market is empty again. -/
example :
    let s1 := run vault empty [.call (.deposit 0 100000000)]
    let s2 := run vault s1 [.call (.redeem 0 5000000000)]
    s1.balance 0 = 5000000000 ∧ s2.assets = 0 ∧ s2.supply = 0 ∧ s2.balance 0 = 0 := by
  decide

/-- 10. The same round trip with `redeemUnderlying` for the full amount. -/
example :
    let s := run vault empty [.call (.deposit 0 100000000), .call (.withdraw 0 100000000)]
    s.assets = 0 ∧ s.supply = 0 ∧ s.balance 0 = 0 := by
  decide

/-- 11. Two depositors, then 0.04 WBTC of interest or donation: each redeems its deposit plus
its share of it (1.01 and 3.03 WBTC). -/
example :
    let s := run vault empty
      [.call (.deposit 0 100000000), .call (.deposit 1 300000000), .donate 4000000]
    let a := run vault s [.call (.redeem 0 5000000000)]
    let b := run vault a [.call (.redeem 1 15000000000)]
    s.balance 1 = 15000000000 ∧ s.assets - a.assets = 101000000 ∧ a.assets - b.assets = 303000000 ∧
      b.supply = 0 := by
  decide

/-- 12. `redeemUnderlying` of a depositor's full value after interest burns all its shares and
leaves the other depositor's shares worth the same. -/
example :
    let s := run vault empty
      [.call (.deposit 0 100000000), .call (.deposit 1 300000000), .donate 4000000]
    let a := run vault s [.call (.withdraw 0 101000000)]
    a.balance 0 = 0 ∧ a.supply = 15000000000 ∧ a.assets = 303000000 := by
  decide
