# Share vault accounting: the Hundred Finance exploit

This task holds a Lean specification of share accounting for a lending market (deposit
underlying for shares, redeem shares, withdraw an amount of underlying, donations sent
straight to the vault), a proved reference implementation, and a port of the share
accounting of Hundred Finance's hToken. Hundred Finance is a Compound v2 fork, and its hWBTC
market on Optimism was drained on 2023-04-15. The port is refuted in the Lean kernel by the
attack's own amounts. The deployed contract, run on a fork of Optimism, gives the same
result as the port on every sequence tested.

## What happened

All figures in this section are read from chain data or from the verified source; the
commands are in `eval/vault.py` and `realworld/adapters/hundred`.

- Transaction `0x6e9ebcdebbabda04fa9f2e3bc21ea8b2e4fb4bf4f4670cb8483e2f0b2604f451`, Optimism
  block 90761918, 2023-04-15 14:12:00 UTC, sent by `0x155da45d374a286d383839b1ef27567a15e67528`.
- Market: hWBTC `0x35594E4992DFefcB0C20EC487d7af22a30bDec60`, a `CErc20Delegator` whose
  implementation at the block before the attack was `CErc20Delegate`
  `0x7100CBCa885905F922a19006cF7fD5d0E1bBb26c`. Its source is verified on Sourcify with an exact
  match of runtime and creation bytecode (solc 0.5.16, optimizer 200 runs). Before the attack the
  market had 1503167295 share units (15.03167295 hWBTC), all held by the attacker's contract
  `0x978d0ce23869ec666bfde9868a8514f3d2754982`, 30064194 satoshi of cash, 377 satoshi of
  reserves and no borrows.
- First round, from the transaction's Mint, Redeem and Transfer events on hWBTC:
  1. the attacker's contract redeems all 1503167295 share units for 30063816 satoshi, which
     leaves 0 shares and 1 satoshi above the reserves;
  2. a second attacker contract mints with 400000000 satoshi (4 WBTC) and receives
     20000000000 share units (200 hWBTC; `initialExchangeRateMantissa`, storage slot 7 of the
     market, is 20000000000000000, 0.02 WBTC per hWBTC);
  3. it redeems 19999999998 share units for 400000000 satoshi, which leaves 2 share units
     backed by 1 satoshi;
  4. it transfers 50030063816 satoshi (500.30063816 WBTC) straight to the market. The
     exchange rate mantissa becomes 25015031908500000000000000000, so one share unit is worth
     about 250 WBTC;
  5. it borrows 1021.915074492787011273 ETH from hETH (`0x1a61a72f5cf5e857f15ee502210b81f8b3a66263`)
     against its 2 share units;
  6. it calls `redeemUnderlying(50030063815)`. The share units this amount is worth are
     50030063815 * 2 / 50030063817 = 1.99999999992. The contract burns 1, pays 500.30063815
     WBTC, and leaves 1 share unit backed by 2 satoshi as the only collateral for the ETH loan;
  7. the first attacker contract liquidates the loan (repaying 267919888739 wei of ETH and
     seizing the 1 share unit), redeems that unit for 2 satoshi, and the market is empty again.
- The same transaction repeats this round six more times, borrowing from hSNX, hUSDC, hDAI,
  hUSDT, hSUSD and hFRAX. Reported losses are about $7 million (rekt.news and BlockSec give
  about $7.4M).

Sources: the transaction receipt (Optimism RPC), the verified implementation source
(https://repo.sourcify.dev/contracts/full_match/10/0x7100CBCa885905F922a19006cF7fD5d0E1bBb26c/),
https://rekt.news/hundred-rekt2 and
https://blocksec.com/blog/6-hundred-finance-incident-catalyzing-the-wave-of-precision-related-exploits-in-vulnerable-forked-protocols.
The write-ups disagree with each other on some amounts and on the date; this README uses
only the on-chain values.

## The vulnerable lines

In the verified `contracts/protocol/token/CToken.sol` of the implementation (SHA-256
`611130d6441649d22331075edb398807e6c4f9f5c99d69f9486329e8af3ee7bd`):

| Line | Code | Rounding |
|---|---|---|
| 371 (`exchangeRateStoredInternal`) | `getExp(cashPlusBorrowsMinusReserves, _totalSupply)` | rate mantissa truncated: `floor(assets * 1e18 / supply)` |
| 545 (`mintFresh`) | `divScalarByExpTruncate(vars.actualMintAmount, Exp({mantissa: vars.exchangeRateMantissa}))` | shares minted rounded down |
| 644 (`redeemFresh`, `redeemTokensIn > 0`) | `mulScalarTruncate(Exp({mantissa: vars.exchangeRateMantissa}), redeemTokensIn)` | underlying paid rounded down |
| 655 (`redeemFresh`, `redeemAmountIn > 0`, used by `redeemUnderlying`) | `divScalarByExpTruncate(redeemAmountIn, Exp({mantissa: vars.exchangeRateMantissa}))` | shares burned rounded down: the wrong direction |

`divScalarByExpTruncate(s, r)` is `truncate(getExp(1e18 * s, r.mantissa))`
(`math/Exponential.sol` lines 103 to 130) and `truncate` is `mantissa / 1e18`
(`math/ExponentialNoError.sol` line 30), so line 655 burns `floor(redeemAmount * 1e18 / rate)`
share units. The same four lines are in upstream compound-finance/compound-protocol v2.8.1
(commit `23eac9425accafb82551777c93896ee7678a85a3`, `contracts/CToken.sol` lines 362, 535, 633
and 644). Upstream also calls `comptroller.redeemVerify` at line 704, which reverts when
`redeemTokens == 0 && redeemAmount > 0` (`contracts/Comptroller.sol` line 330). Hundred's
`redeemFresh` does not call `redeemVerify`. That check would not have stopped this attack,
which burns 1 share unit, not 0.

## The specification

`spec/ShareVault/Spec.lean` models the vault state as `assets` (for a cToken,
`cash + totalBorrows - totalReserves`), `supply` and per-actor `balance`. The implementation
`vault : Impl` handles three calls: `deposit` (cToken `mint`), `redeem` and `withdraw` (cToken
`redeemUnderlying`). Donations are operations defined by the specification, outside the
implementation. A refused call leaves the state unchanged. Ten requirements are locked in
`spec/ShareVault/Challenge.lean`:

| Requirement | Statement |
|---|---|
| REQ-DEPOSIT-SUCCEEDS | a deposit succeeds when the vault holds no shares or holds some underlying |
| REQ-REDEEM-SUCCEEDS | redeeming shares the caller holds succeeds |
| REQ-WITHDRAW-SUCCEEDS | withdrawing `x` succeeds when `x * supply <= balance * assets` (the caller's shares are worth at least `x`) |
| REQ-DEPOSIT-EFFECTS, REQ-REDEEM-EFFECTS, REQ-WITHDRAW-EFFECTS | the full next state: assets, supply and the caller's balance change by the amounts of the call, every other balance is unchanged, and nothing is paid that the vault or the caller does not hold |
| REQ-DEPOSIT-ROUNDS-DOWN | shares minted are `x * supply / assets` rounded down (50 per unit into a vault with no shares, hWBTC's initial rate) |
| REQ-REDEEM-ROUNDS-DOWN | underlying paid is `t * assets / supply` rounded down |
| REQ-WITHDRAW-ROUNDS-UP | shares burned are `x * supply / assets` rounded up, and a withdrawal needs outstanding shares |
| REQ-SHARE-VALUE | the sequence-level property below |

The main requirement, verbatim:

```lean
/-- REQ-SHARE-VALUE: starting from the empty vault, after any history of operations by any
actors, no further sequence of operations by any actors, including donations and refused
calls, lowers the underlying value of a share while shares stay outstanding. ... -/
def ShareValueNeverFalls (vault : Impl) : Prop :=
  ∀ history ops : List Op,
    (∀ v ∈ trace vault (run vault empty history) ops, 0 < v.supply) →
    ValueNotBelow (run vault empty history) (run vault (run vault empty history) ops)

def ValueNotBelow (s s' : Vault) : Prop :=
  s.assets * s'.supply ≤ s'.assets * s.supply

theorem req_share_value : ShareValueNeverFalls vault := sorry
```

Put another way, as long as shares stay outstanding, the vault always holds enough
underlying to pay every outstanding share at least the value a share had at any earlier
point. In the attack, the lending markets accepted the attacker's share units as collateral
at about 250 WBTC each. One `redeemUnderlying` call later, each remaining unit was worth
2 satoshi.

The requirements are not vacuous. `spec/ShareVault/Sanity.lean` proves `honest_sequence`: every
implementation that meets the nine per-call requirements runs this sequence from the empty
vault with exactly these results. Actor 0 deposits 100 and actor 1 deposits 300 (5,000 and
15,000 shares), 40 is donated, actor 0 withdraws 110, and actor 1 redeems its 15,000 shares for
330. Each actor gets back its deposit plus its share of the donation, and the vault ends empty.

## What was proved

- `reference/SolutionA.lean` defines `vault` and proves all ten requirements. The judge
  (`lake comparator --paranoid` with the Lean default and paranoid kernels plus lean4lean,
  nanoda, con-leche and con-ron, then `leanchecker`) accepts it. Its executable passes 1,001
  generated property cases (`validation.json`). Shares are priced from the exact ratio
  `assets / supply`: deposits round down, redemptions round down, and withdrawals burn
  `(x * supply + assets - 1) / assets` shares.
- `spec/ShareVault/Sanity.lean` proves `honest_sequence` (above).
- Muse Spark 1.3 (arm A1, no planner, $10 list cap) repaired the port and proved all ten
  requirements on its first attempt, in 1,200 s, at $0.65 list ($0.037 charged). Its Passport
  is VERIFIED (sha256 `08fe86f17f27c49d60bda786d1498200d333c1c8d63d2f858ab668cd4f7fe7c4`), and
  `bin/proofforge verify` reproduces it. Details are in `results/vault-1/README.md`.

## What the port corresponds to

`candidate/Solution.lean` (also `attacks/hundred_port.lean`) transcribes
`exchangeRateStoredInternal`, `mintFresh` and `redeemFresh` with `getExp`, `truncate`,
`mulScalarTruncate` and `divScalarByExpTruncate`, the 18-decimal mantissa, hWBTC's
`initialExchangeRateMantissa` of `2e16`, and the three failure checks of `redeemFresh`
(supply underflow, balance underflow, insufficient cash). It leaves out the following:

- borrows, reserves and interest (assets are cash);
- the comptroller, which is assumed to allow every call;
- the freshness check, with interest assumed accrued;
- uint256 overflow, since arithmetic is unbounded;
- transfer fees, since the underlying moves as requested.

Evidence that it matches the deployed contract on these paths
(`results/vault-1/real-code/report.json`):

- On a fork of Optimism at block 90761917, the market is emptied as in step 1. The admin then
  withdraws the 377 satoshi of reserves (the model has none), which leaves 1 satoshi of cash
  and no shares. From there, 501 operation sequences ran on the deployed bytecode: the
  documented attack and 500 generated sequences of deposits, redeems, withdrawals and
  donations by up to four actors. The port gave identical success flags, assets, supply and
  balances after every operation of all 501 sequences.
- The deployed contract reproduces the attack's on-chain amounts: 20000000000 share units
  minted, 2 share units backed by 1 satoshi, 50030063817 after the donation, and 1 share unit
  backed by 2 satoshi after `redeemUnderlying(50030063815)`.

## What refutes the port

- `witnesses/hundred_attack.lean`, checked by the Lean kernel with `decide`. From the empty
  vault, deposit 400000000, redeem 19999999998, donate 50030063816, withdraw 50030063815.
  The port then ends with assets 2, supply 1 and balance 1. `port_refuted_share_value :
  ¬ ShareValueNeverFalls vault` holds (50030063817 / 2 before, 2 / 1 after), and so does
  `port_refuted_withdraw_rounds_up : ¬ WithdrawRoundsUp vault` (1 share unit burned for
  1.99999999992). The reference burns both share units.
- `witnesses/zero_share_withdraw.lean`: an actor holding no shares withdraws 1 satoshi from a
  vault where a share unit is worth 2, and burns 0 shares (this is the case upstream's
  `redeemVerify` rejects). The deployed contract shows the same behavior on the fork
  (generated case 2 in the report: 35 satoshi withdrawn by an address with no shares).
- The generated tests also find redemptions that pay one unit less than the exact
  rounded-down value, because the stored rate is truncated. Generated case 387 on the deployed
  contract redeems all 300 share units of a vault holding 7 satoshi and is paid 6. The binary
  tests further find deposits that mint a few share units more than the exact rounded-down
  value; these occur in states with a heavily truncated rate.
- `harness/validate_task.py`: the judge rejects the port, and its binary is REFUTED on the
  generated cases (REQ-WITHDRAW-ROUNDS-UP, REQ-SHARE-VALUE, REQ-DEPOSIT-ROUNDS-DOWN,
  REQ-REDEEM-ROUNDS-DOWN, REQ-REDEEM-SUCCEEDS). `attacks/partial_fix_round_up.lean` rounds
  the shares burned by `redeemUnderlying` up but keeps the truncated rate everywhere else; it
  is rejected and refuted as well (it over-mints on deposit and underpays on redeem). It is not
  a release of any project.

The port passes the kind of unit tests such projects ship. `tests/PortUnitTests.lean` restates
the mint, redeem, `redeemUnderlying` and `exchangeRateStored` tests of Compound v2.8.1
(`tests/Tokens/mintAndRedeemTest.js`, `tests/Tokens/cTokenTest.js`) and adds round trips,
two depositors and interest. All twelve pass on the port, checked by the kernel. None of
them withdraws from a market that has very few shares outstanding and a large balance.

## What was not proved

- The deployed Solidity contract is not proved. It was run on 501 sequences on a fork and
  compared, operation by operation, with the port and with the requirements.
- That the port is faithful is tested, not proved. It covers only the share accounting paths
  listed above. The comptroller (collateral factors, liquidity checks, borrowing,
  liquidation), interest accrual, reserves, borrows and price oracles are not modelled. The
  loss in the attack came from borrowing against the overvalued share. This specification
  states the share value property that the borrow relied on; it does not model the borrow.
- The specification does not prevent the first-depositor inflation attack. A deposit worth
  less than one share mints zero shares, which REQ-DEPOSIT-ROUNDS-DOWN requires, and that value
  goes to the existing holders.
- The initial price of 50 shares per unit is fixed, and there is no bound on integer sizes.
- The JSON wrapper `app/Main.lean` is tested, not proved.

## Reproduce

```sh
python3 harness/lock.py realworld/tasks/rw-hundred-vault       # owner only, after review
python3 harness/validate_task.py realworld/tasks/rw-hundred-vault
python3 eval/vault.py --cases 500 --out results/vault-1        # needs forge and an archive RPC (PF_OP_RPC)
```
