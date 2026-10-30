# rw-balancer-upscale: the Balancer V2 rounding exploit

This task holds a Lean specification of the rounding in Balancer V2's swap wrapper, stated
for any pool math that meets a stated contract, a proved reference implementation, and a port
of the wrapper as deployed for the osETH/WETH Composable Stable Pool on Ethereum. The port is
refuted in the Lean kernel by a batch of small swaps in the shape of the November 2025 attack.
The port, run with a port of Balancer's StableMath, reproduces the amount in of all 90 token
swaps the attack made on that pool. On a fork of Ethereum, the deployed Vault and pool give the
same results as the port on every batch tested.

## What happened

From the sources listed at the end:

- On 2025-11-03 attackers drained Balancer V2 Composable Stable Pools and forks of them on several
  chains. The Block reports that estimates "rose from around $70 million to over $128 million"
  (Nansen and PeckShield) and quotes Balancer's preliminary report: "a rounding error in the
  upscale function for EXACT_OUT swaps within the v2 vault's batchSwap feature". OpenZeppelin puts
  the loss at "$120+ million across Balancer and its forks", BlockSec at over $125 million. The
  loss figures were not checked here.
- OpenZeppelin, Certora and BlockSec agree on the mechanism. `BaseGeneralPool._swapGivenOut`
  upscales the requested amount out with `_upscale`, which rounds down (`FixedPoint.mulDown`), so
  the pool math prices less than the trader takes. The attacker first sold BPT for the pool's
  tokens to push the balances down to a few wei, where one unit of rounding is a large part of a
  balance, then repeated rounds of three swaps inside one `batchSwap`.
- Certora writes that its 2022 verified properties "did not constrain the relationship between
  individual swaps or rounding behavior".

Read from chain data here (Ethereum, public archive RPC `https://eth.drpc.org`):

- Transaction `0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742`, block
  23717397, 2025-11-03 07:46:47 UTC, sent by `0x506d1f9efe24f0d47853adca907eb8d89ae03207` (it
  creates the contract `0x54b53503c0e2173df29f8da735fbd45ee8aba30d`). It emits 226 Swap events:
  121 on the osETH/WETH pool `0xDACf5Fa19b1f720111609043ac67A9818262850c` and 105 on the
  wstETH/WETH pool `0x93d199263632a4ef4bb438f1feb99e57b4b5f0bd`.
- The osETH/WETH pool (version 5, `20230711-composable-stable-pool-v5`) has amplification 200
  (`getAmplificationParameter()` returns 200000), a 0.01% swap fee (1e14), and scaling factors
  1e18 for WETH and 1058132408689971699 for osETH during the transaction (the cached osETH rate,
  refreshed by its first swap; `getScalingFactors()` at the end of the block). Before the
  transaction it held 4922356564867078856521 wei of WETH and 6851581236039298760900 wei of osETH.
- Swap events 1 to 22 sell BPT for WETH and osETH (given out) until the pool holds 67,000 wei of
  each. Swap events 23 to 112 are 30 rounds of three given-out swaps: osETH out until 18 wei are
  left, then 17 wei of osETH out, then WETH out paid with osETH. In the exploit swap, 17 wei of
  osETH is worth 17 * 1.058132408689971699 = 17.988 of the pool's 18-decimal units; `_upscale`
  passes 17 to the math, and the pool's 18 wei are 19 units, so the math prices taking 17 of 19
  units instead of 18 of 19. The first exploit swap is charged 625,492 wei of WETH.
- After the 90 swaps the pool holds 889 wei of WETH and 1,472 wei of osETH, and its invariant D
  (computed by the StableMath port below) has fallen from 137,893 to 2,445. On a fork, the deployed
  pool's `getRate()` (the BPT price) is 1029274992349090474 after the first 22 swaps and
  18250218330832792 after the 90. Swap events 113 to 121 then buy BPT back at that price.

## The vulnerable lines

The pool's source is verified on Sourcify with an exact match of runtime and creation bytecode
(solc 0.7.1, optimizer 800 runs). In it:

| File (SHA-256) | Lines | Code |
|---|---|---|
| `@balancer-labs/v2-pool-utils/contracts/BaseGeneralPool.sol` (`a48d3fe6...`) | 68 to 85 | `_swapGivenOut`: `_upscaleArray(balances, ...)`; `swapRequest.amount = _upscale(swapRequest.amount, scalingFactors[indexOut])`; `_onSwapGivenOut`; `_downscaleUp`; `_addSwapFeeAmount` |
| `@balancer-labs/v2-pool-utils/contracts/BasePool.sol` (`9fec78a4...`) | 680 to 686 | `_upscale`: `return FixedPoint.mulDown(amount, scalingFactor);` |
| `contracts/ComposableStablePool.sol` (`49222c43...`) | 214 to 231 | `_swapGivenOut` forwards a swap between two non-BPT tokens to `BaseGeneralPool._swapGivenOut` |

The comment on `_upscale` records the assumption that failed: "This is the only place where we
round in the same direction for all amounts, as the impact of this rounding is expected to be
minimal". The same logic is in balancer/balancer-v2-monorepo at commit
`88842344fb5f44d8ed6f8f944acd3be80627df87` (2025-10-26, the last commit before the exploit):
`pkg/solidity-utils/contracts/helpers/ScalingHelpers.sol` lines 35 to 40 and
`pkg/pool-utils/contracts/BaseGeneralPool.sol` lines 68 to 85. There `_upscale` moved from
`BasePool` to `ScalingHelpers`, and some `FixedPoint` and `Math` functions are written in assembly;
they compute the same values. StableMath differs from the deployed copy only in two comment lines.
No later commit, up to master at `e91a2b643a49856f51a648d175667c1b48cf3377` (2026-08-03), changes
code in these files; the six commits after the pinned one change comments, documentation and
dependencies.

## The specification

`spec/BalancerSwap/Spec.lean` models what the swap path sees: a pool of `n` tokens with raw
balances (as the Vault stores them), scaling factors (`10^(18 - decimals)` times the token's
rate) and a swap fee. The implementation `onSwap : Impl` is the swap wrapper: given the pool math,
the pool and a request (given in or given out), it returns the amount the pool calculates, or
`none`. The Vault's side (`step`: index checks, moving the balances, refusing to pay out more
than the pool holds) and batches (`run`: swaps in order, the whole batch reverts if one swap
does) are defined by the specification, outside the implementation.

The abstraction of the pool formula. The pool math is a parameter, not StableMath. A
`PoolMath` is an invariant on 18-decimal balances (StableMath's `D` for a stable pool) and the two
pricing functions (`_calcOutGivenIn` and `_calcInGivenOut`), all on whole 18-decimal units. The
requirements hold for every math with this contract (`WellBehaved m n`):

1. the invariant does not decrease when no balance of the `n` tokens decreases;
2. a given-in trade priced by the math pays out at most the balance and does not lower the
   invariant;
3. a given-out trade of less than the balance, priced by the math, does not lower the invariant.

The price requirements also assume that more in pays out at least as much and more out costs at
least as much (`PriceMonotone`). StableMath's `_calcOutGivenIn` subtracts 1 and `_calcInGivenOut`
adds 1 to meet this contract on whole units, but no proof is given that StableMath meets it.
`spec/BalancerSwap/Sanity.lean` proves that a two-token constant-product pool meets both
(`constantProduct_wellBehaved`, `constantProduct_priceMonotone`), so the hypotheses are satisfiable.

The pool's value is the invariant of its balances in 18-decimal units rounded down, as the pool
itself computes it (`value`). For a Composable Stable Pool this is the `D` behind `getRate()`, and a
token swap does not change the BPT supply, so a fall in value is a fall in the BPT price.

Eight requirements are locked in `spec/BalancerSwap/Challenge.lean`:

| Requirement | Statement |
|---|---|
| REQ-GIVEN-IN-SUCCEEDS | for well-behaved math, a given-in swap between two tokens of the pool goes through when the token out has a positive scaling factor and the fee is below 100% |
| REQ-GIVEN-OUT-SUCCEEDS | for well-behaved math, a given-out swap goes through when the exact amount out rounded up is below the pool's scaled balance of that token, the token in has a positive scaling factor and the fee is below 100% |
| REQ-GIVEN-IN-PAYS-AT-MOST | for monotone prices, the trader receives at most what the math prices the exact amount in, net of the fee, rounded down |
| REQ-GIVEN-IN-PAYS-AT-LEAST | and at least what the math prices one raw unit less, less one raw unit out |
| REQ-GIVEN-OUT-CHARGES-AT-LEAST | for monotone prices, the charge, after the fee, is at least what the math prices the exact amount out rounded up to a whole 18-decimal unit |
| REQ-GIVEN-OUT-CHARGES-AT-MOST | and one raw unit less than the charge is below that price plus one raw unit: at most one unit for the conversion back and one for the fee |
| REQ-SWAP-KEEPS-VALUE | for well-behaved math, a swap that goes through never lowers the pool's value |
| REQ-BATCH-KEEPS-VALUE | for well-behaved math, any pool and any batch of swaps of either kind, a batch that goes through never lowers the pool's value |

The main requirements, verbatim:

```lean
/-- REQ-GIVEN-OUT-CHARGES-AT-LEAST: ... -/
def GivenOutChargesAtLeast (impl : Impl) : Prop :=
  ∀ m p s c, PriceMonotone m → s.kind = .givenOut → Valid p s → impl m p s = some c →
    ONE * ONE * outPrice m p s ≤ c * (ONE - p.fee) * p.rate s.tokenIn

def outPrice (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))

/-- REQ-BATCH-KEEPS-VALUE: ... -/
def BatchKeepsValue (impl : Impl) : Prop :=
  ∀ m p ss p', WellBehaved m p.n → run impl m p ss = some p' → value m p ≤ value m p'
```

`scaleUp a r` is `(a * r + (1e18 - 1)) / 1e18`, the exact 18-decimal value of the raw amount
rounded up. In words: for any pool math with the contract above, a given-out swap is charged at
least the math's price of the exact amount out, rounded in the pool's favour, and no swap and no
batch of swaps of any length lowers the pool's value.

The requirements are not vacuous. `exploit_swap_charge` in `Sanity.lean` takes the pool as it was
before each exploit swap (374,353 wei of WETH, 18 wei of osETH, the real scaling factors and fee)
and the request for 17 wei of osETH. With the constant-product math, every implementation that meets
REQ-GIVEN-OUT-SUCCEEDS, -CHARGES-AT-LEAST and -CHARGES-AT-MOST accepts the swap and charges 6,739,028
or 6,739,029 wei of WETH.

## What was proved

- `reference/SolutionA.lean` is the port with the given-out amount upscaled with `mulUp` instead of
  `mulDown`, and the swap refused when that amount is not below the scaled balance (the math cannot
  take a whole balance). Everything else is Balancer's code unchanged. It proves all eight
  requirements; the judge (`lake comparator --paranoid` with the Lean default and paranoid kernels
  plus lean4lean, nanoda, con-leche and con-ron, then `leanchecker`) accepts it, and its executable
  passes 1,001 generated property cases (`validation.json`) and 2,001 in its Passport
  (`results/balancer-1/passports/reference.json`, VERIFIED). The proofs use only `propext`,
  `Classical.choice` and `Quot.sound`.
- `spec/BalancerSwap/Sanity.lean` proves that the constant-product math is well behaved and
  price-monotone, and `exploit_swap_charge` (above).
- Muse Spark 1.3 (Contributor tier, $10 list cap and 14,400 s per run) repaired the port with the
  Muse Wonder planner (arm A2) and proved all eight requirements, in 2,344 s, at $2.51 list ($0.41
  charged). Its fix is the reference's: the amount out is upscaled rounding up and the swap is
  refused unless that amount is below the scaled balance. Its Passport is VERIFIED (sha256
  `48930efdd4d67460bfd22bb15dfa9625caafc36cd6fca3a8fee444d5f3b204ba`), and `bin/proofforge verify`
  reproduces it. Without the planner (arm A1) the first attempt reached the cap with six of the
  eight requirements proved in session (both value requirements open); the second made the same fix
  and proved all eight (3,212 s, $3.03 list, $0.16 charged; Passport
  `eb1adce9d7aa20d3373ac6a1b0787e08c84aa284e31ec29cec796c8098ce7a19`, reproduced). In implement mode,
  from a stub generated from the locked challenge, the first attempt reached the cap with six of
  eight, and the second proved all eight (4,444 s, $3.81 list, $0.21 charged; Passport
  `65d5a81fef2352eb67a72f032ade091fd051b30ebf44c310b1d0c6dcb1b84d3d`, reproduced). Details are in
  `results/balancer-1/README.md`.

## What the port corresponds to

`candidate/Solution.lean` (also `attacks/balancer_port.lean`) transcribes, from the deployed
source: `BaseGeneralPool._swapGivenIn` (lines 49 to 66) and `_swapGivenOut` (68 to 85);
`BasePool._addSwapFeeAmount`, `_subtractSwapFeeAmount`, `_upscale`, `_upscaleArray`,
`_downscaleDown` and `_downscaleUp`; `FixedPoint.mulDown`, `mulUp`, `divDown`, `divUp` and
`complement`; and the first check of `StableMath._calcInGivenOut` (the amount out may not exceed
the balance). A revert is `none`. It leaves out:

- swaps involving the pool's own BPT (`_swapWithBpt`, which are joins and exits), protocol fees
  and the BPT supply: the model covers swaps between two of the pool's tokens;
- the Vault's other checks (deadlines, limits, relayers, internal balances) and the `amount == 0`
  convention of `batchSwap` for multihop swaps;
- the rate providers: the scaling factors are fixed for a batch (the pool caches token rates);
- uint256 overflow, since arithmetic is unbounded.

`spec/BalancerSwap/StableMath.lean` (protected, executable, not proved) transcribes StableMath's
`_calculateInvariant`, `_calcOutGivenIn`, `_calcInGivenOut` and
`_getTokenBalanceGivenInvariantAndAllOtherBalances`, with its reverts. It is used by the
executable and the tests, never by a requirement.

Evidence that the port matches the deployed contracts:

- `witnesses/attack_batch.lean`, part 2, checked by the kernel: from the 67,000-wei state, the port
  with the StableMath port and the pool's parameters charges exactly the logged amount in of each of
  Swap events 23 to 112, ends with 889 and 1,472 wei, and D falls from 137,893 to 2,445.
- On a fork of Ethereum taken just before the attack transaction (`eval/realworld_balancer.py`,
  `results/balancer-1/real-code/report.json`), the attack's first 22 swaps run as one `batchSwap`
  bring the deployed pool to 67,000 wei of each token, as on chain. Then 501 batches ran through
  the deployed Vault's `swap`: the attack's 90 swaps and 500 generated batches (10,385 swaps), from
  that state or from the state before the transaction. The port, run with the StableMath port and
  the scaling factors, fee and amplification the fork reports, gave the same success flag, amount
  and balances as the deployed code on every swap of all 501 batches. The deployed code charges
  each of the 90 attack swaps exactly the amount the transaction logged.

## What refutes the port

`witnesses/attack_batch.lean`, part 1, checked by the kernel with `decide`, with the
constant-product math (proved well behaved, so these are counterexamples to the locked
requirements):

- From the 67,000-wei state with the real scaling factors and fee, four rounds of the attack's shape
  (osETH out down to 18 wei, 17 wei of osETH out, WETH out paid with osETH) go through, and the
  pool's value falls from 4,749,898,000 to 297,229,191; its WETH goes from 67,000 to 4,193 wei.
  `port_refuted_batch_keeps_value : ¬ BatchKeepsValue onSwap`.
- The single exploit swap of `Sanity.lean` is charged 3,182,320 wei of WETH, where the math prices
  the exact amount out rounded up at 6,738,354 before the fee:
  `port_refuted_charges_at_least : ¬ GivenOutChargesAtLeast onSwap`. It halves the pool's value,
  from 7,112,707 to 3,556,673: `port_refuted_swap_keeps_value : ¬ SwapKeepsValue onSwap`.
- `harness/validate_task.py`: the judge rejects the port and its binary is REFUTED on the generated
  cases (REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE, REQ-BATCH-KEEPS-VALUE).
  `attacks/plus_one.lean` (upscale with `mulDown` and add one unit, not a release of any project) is
  rejected and refuted as well: it overcharges whenever the exact amount out is a whole number of
  units (REQ-GIVEN-OUT-CHARGES-AT-MOST) and refuses swaps it must accept (REQ-GIVEN-OUT-SUCCEEDS).

The port passes the kind of unit tests Balancer ships. `tests/PortUnitTests.lean` restates the
`upscale`, `downscaleDown` and `downscaleUp` tests of `pkg/solidity-utils/test/ScalingHelpers.test.ts`
and the regular-swap tests of `pkg/pool-stable/test/ComposableStablePool.test.ts` (0.1 token given
in and given out on a two-token pool with balances 1 and 0.9, amplification 200 and the test
helper's 0.0001% fee, within the original 0.001% tolerance of the helper's decimal StableSwap
solution), repeats the swaps with a token rate of 1.058132408689971699, and adds a round trip. All
eleven pass on the port, checked by the kernel; they pass on the reference too. None of them trades
against a balance of a few wei.

## The deployed contracts against the proved component

The same 501 batches on the fork (`results/balancer-1/real-code`), with the proved component being
the accepted Muse repair (arm A2), both Lean executables using the StableMath port:

| Check | Result |
|---|---|
| deployed code identical to the port, every swap | 501 of 501 batches |
| deployed code identical to the proved component | 194 of 501 batches |
| given-out swaps the deployed code charged less than the proved component | 546 |
| batches from the 67,000-wei state that go through on the deployed code | 85 of 344; D falls in 56, and the deployed pool's `getRate()` falls in the same 56 |
| batches from the state before the transaction that go through | 88 of 157; D falls in none |
| batches that go through on the proved component | 119 of 501; D falls in none |
| falls of D on the deployed code's balances restated as `decide` goals and checked in the kernel | 6 of 6 (`real-code/Confirm.lean`) |

On the attack's own 90 swaps the proved component charges 315,795 wei for the first swap (the
chain logged 307,353) and 1,071,109 for the first exploit swap (the chain logged 625,492); after
the first round D has risen to 158,835 instead of falling, and the next swap, which asks for 5,165
wei of osETH out of the 11 left, fails, so the batch reverts. From the state before the
transaction, the deployed pool's `getRate()` fell slightly in 25 of the 88 batches (by at most
0.022%) while D did not fall; this was not investigated (`getRate()` also counts protocol fees
owed in the BPT supply). With StableMath as the math, the proved component's results are tested,
not proved.

## What is not proved

- The deployed Solidity contracts are not proved. They were run on a fork, batch by batch, and
  compared with the port and the proved component.
- That the port is faithful is tested, not proved. It covers the regular-swap path listed above.
  Joins, exits and BPT swaps, which the attacker used to push the balances down and to buy BPT back,
  are not modelled. The loss came from buying BPT at the depressed price; the specification states
  the property that price relied on (the pool's invariant never falls through swaps), not the BPT
  trades.
- StableMath is not proved to meet `WellBehaved`. With the StableMath port, the proved component's
  results on the fork's batches are tested only.
- The requirements fix Balancer's fee rule only through the bounds of REQ-GIVEN-IN-PAYS-AT-LEAST and
  REQ-GIVEN-OUT-CHARGES-AT-MOST. There is no upstream fix of the V2 code to compare with. Balancer
  states that V3 was not affected, and Certora reports that in V3 the rounding was correct.
- The JSON wrapper `app/Main.lean` is tested, not proved.

## Sources

- OpenZeppelin, root cause, vulnerable functions and introducing commits:
  https://www.openzeppelin.com/news/understanding-the-balancer-v2-exploit
- Certora, rounding direction and the scope of its earlier verified properties:
  https://www.certora.com/blog/breaking-down-the-balancer-hack
- The Block, loss estimates, the preliminary report's wording, affected chains:
  https://www.theblock.co/post/377863/balancer-identifies-rounding-error-as-root-cause-of-multi-chain-defi-exploit
- BlockSec, attack phases: https://blocksec.com/blog/in-depth-analysis-the-balancer-v2-exploit
- Verified pool source: https://sourcify.dev/server/v2/contract/1/0xdacf5fa19b1f720111609043ac67a9818262850c?fields=sources
- Upstream source at the pinned commit:
  https://github.com/balancer/balancer-v2-monorepo/blob/88842344fb5f44d8ed6f8f944acd3be80627df87/pkg/solidity-utils/contracts/helpers/ScalingHelpers.sol
  and https://github.com/balancer/balancer-v2-monorepo/blob/88842344fb5f44d8ed6f8f944acd3be80627df87/pkg/pool-utils/contracts/BaseGeneralPool.sol
- Balancer's own post-mortem on Medium
  (https://medium.com/balancer-protocol/nov-3-exploit-post-mortem-51dcbeb6b020) returned HTTP 403 and
  was not read; Balancer's wording here is quoted from The Block.

## Reproduce

```sh
python3 harness/lock.py realworld/tasks/rw-balancer-upscale       # owner only, after review
python3 harness/validate_task.py realworld/tasks/rw-balancer-upscale
python3 eval/realworld_balancer.py --cases 500 --out results/balancer-1   # needs forge and an archive RPC (PF_ETH_RPC)
```
