# rw-kyber-swapstep: the swap step of KyberSwap Elastic

This task holds a Lean specification of the swap step of KyberSwap Elastic for amounts in token1
(`SwapMath.computeSwapStep` with `isToken0 = false`, the functions it calls, and the test of
`Pool.swap` that decides whether a step crossed the next tick), a port of the code that was
exploited on 2023-11-22, and a repair with a complete proof. The start candidate is the deployed
code. It is refuted in the Lean kernel on two branches: the exploited exact-input branch, and the
exact-output branch, whose defect is not documented elsewhere as far as the build team found.

The code is a composition of six functions with sixteen divisions and a square root, each rounded down or up.
What makes it hard to prove is that the rounding errors of two separately computed closed forms (the
amount that reaches the target, and the price after a smaller amount with its fee reinvested) must
combine in the right direction for every input, and on the exact-output branch that the integer
smaller root of a quadratic lands on the right side of the real root.

## The code

`KyberNetwork/ks-elastic-sc` at commit `4ab08c0a60f74809f731bdd333076e32d05f1d17`, compiled with
Solidity 0.8.9 (checked arithmetic):

| File and lines | Function | Port |
|---|---|---|
| `contracts/libraries/SwapMath.sol` 28 to 98 | `computeSwapStep`: the reach amount, the choice between a step that ends on the target and one that stops before it, the fee liquidity, the next price, the returned amount | `computeSwapStepWith`, the definition hole `computeSwapStep` |
| `SwapMath.sol` 102 to 164 | `calcReachAmount` | `calcReachAmount` |
| `SwapMath.sol` 169 to 216 | `estimateIncrementalLiquidity`: the fee liquidity of a step that stops before the target (exact input: lines 186 to 193; exact output: the smaller root of `a x² - 2 b x + c`) | `estimateIncrementalLiquidity` |
| `SwapMath.sol` 220 to 249 | `calcIncrementalLiquidity`: the fee liquidity of a step that ends on the target | `calcIncrementalLiquidity` |
| `SwapMath.sol` 253 to 280 | `calcFinalPrice` | `calcFinalPrice` |
| `SwapMath.sol` 285 to 320 | `calcReturnedAmount` | `calcReturnedAmount` |
| `contracts/libraries/QuadMath.sol` 8 to 30 | `getSmallerRootOfQuadEqn`, `sqrt` (Babylonian method) | `getSmallerRootOfQuadEqn`, `sqrt`, `babylonian` |
| `contracts/libraries/FullMath.sol` 15 to 126 | `mulDivFloor`, `mulDivCeiling` | `mulDivFloor`, `mulDivCeiling` |
| `contracts/Pool.sol` 371 to 419 | one iteration of the loop of `swap`: the target of the step (388 to 392) and the crossing test (412 to 419) | `loopTarget`, `loopStep` |

`uint256` is `BitVec 256`; every checked operation is the exact natural-number result when it fits
and `none` (a revert) otherwise; `int256` values are `Int`. The `while` loop of `QuadMath.sqrt` has
no bound in Solidity; the port runs it with a bound of 512 iterations and the protected lemma
`toNat_sqrt` proves that it returns the square root rounded down (`Nat.sqrt`) on every `uint256`
(the iterates reach the root within 256 iterations; on `2^256 - 1` the loop stops after 135). The port of the step evaluates in the kernel, so
`decide` checks concrete steps.

`computeSwapStepWith r` is the deployed computation with each of eighteen choices given by
`r : Rounding`: the rounding direction of every division, the square root rounded down or up, and
whether the fee liquidity of an exact-input step is computed as deployed or from the virtual input
`absDelta * 2^96 / currentSqrtP` rounded first. The code at 4ab08c0 is `computeSwapStepWith
deployed`.

The defect. Lines 186 to 193 say "so we round up deltaL, to round down nextSqrtP" and compute
`deltaL` with `FullMath.mulDivFloor`. The floor was introduced by `KyberNetwork/ks-elastic-sc-legacy`
pull request 95, "fix ceiling to floor swapmath" (commit
`33446757d93619b73403573dc309b9a072b167b1`, 2022-06-04, merged 2022-06-06), which replaced
`FullMath.mulDivCeiling`. With an amount one unit below the reach amount, the next price can pass
the target; `Pool.swap` then sees a price different from the tick's price, stops without crossing
the tick, and sets the current tick from a price beyond it. KyberSwap's post-mortem reports about
$55.23M taken on 2023-11-22 with `swapAmount = amountSwapToCrossTick - 1`; BlockSec's analysis
names the line. Kyber's own Echidna test (`contracts/echidna/SwapMathEchidnaTest.sol` lines 32 to
55 and 83 to 90) states the violated property.

## Requirements

`ExactIn` and `ExactOut` describe the inputs `Pool.swap` passes to a step: a liquidity
`0 < L < 2^129`, a fee below `FEE_UNITS = 100000`, two prices within `[MIN_SQRT_RATIO,
MAX_SQRT_RATIO)` less than a 5% price move apart (`100 * hi² < 105 * lo²`, the assumption of the
code's comments and of `MAX_TICK_DISTANCE = 480`), and the specified amount positive and below
`2^255` (token1 in, price up) or negative and at least `-2^255` (token1 out, price down).

| Requirement | Lean statement (`spec/KyberSwapStep/Spec.lean`) |
|---|---|
| REQ-IN-WITHIN-TARGET | an exact-input step ends with `c ≤ next ≤ t`: never past the target, never down |
| REQ-OUT-WITHIN-TARGET | an exact-output step ends with `t ≤ next ≤ c` |
| REQ-STEP-REACH | a step that does not use the whole specified amount ends on the target, uses less than specified, and at most the exact amount that moves the price to the target (cross-multiplied) |
| REQ-STEP-PAID | token1 in: `(L + deltaL) * next ≤ L * c + used * 2^96` (the token1 reserve after the step is backed), except for a step that ends on the target and reinvests nothing; token1 out: `(L + deltaL) * 2^96 * c ≤ next * (L * 2^96 + returned * c)` (the token0 reserve is backed by the input) |
| REQ-IN-FEE-LIQUIDITY | an exact-input step that stops before the target reinvests `fee * used * 2^96 / (2 * c)` (fee in units of `FEE_UNITS`) within one unit |
| REQ-OUT-FEE-LIQUIDITY | an exact-output step that stops before the target reinvests no more than the smaller root of the exact fee equation of `estimateIncrementalLiquidity` (the polynomial is not negative at `deltaL`) |
| REQ-POOL-CROSSES | an iteration of the loop of `Pool.swap` stops without crossing the next tick only when the price is strictly before the tick's price |
| REQ-DEPLOYED-STEP | `∃ r : Rounding, ∀ inputs, computeSwapStep inputs = computeSwapStepWith r inputs`: the step is the deployed computation with some choice of roundings |

REQ-DEPLOYED-STEP keeps the deployed formulas. Without it, the price could be capped at the target
(`min(next, target)`) with the deployed rounding: every other requirement holds for that step, and
`attacks/cap_restated.lean` proves all seven of them with REQ-DEPLOYED-STEP restated as `True`
(ordinary checking accepts it; Comparator rejects the restated statement). A step without fee
liquidity is refuted by REQ-IN-FEE-LIQUIDITY. The requirement is extensional: any step equal to a
member of the family on every input meets it.

Protected lemmas (`spec/KyberSwapStep/Lemmas.lean`, readable by every candidate): each checked
operation, `mulDivFloor`, `mulDivCeiling` and cast through `toNat` (`add_eq_some_iff`,
`mulDivFloor_spec`, ...), the values of the constants, `toNat_sqrt` (the port of `QuadMath.sqrt`
is `Nat.sqrt`), `sqrt_spec` and `sqrtUp_spec`.

## Why the proof is hard

Exact input. The reach amount is `R = ⌊⌊L * 2 * (t - c) / (2 c - fee t)⌋ * c / 2^96⌋` and the next
price `⌊(L + tmp) c / (L + deltaL)⌋` with `tmp = ⌊a 2^96 / c⌋`. For `a < R`, the inner floor `m` of
`R` bounds `tmp ≤ m`, and `m (2 c - fee t) ≤ 2 L (t - c)`; the price stays at most `t` exactly when
the fee liquidity is at least `fee * tmp / 2`. The deployed `deltaL` is the floor of
`fee * a * 2^96 / (2 c)`, which can be below that bound. Rounding the same expression up instead
(the code before pull request 95) puts one unit of fee liquidity on an input that adds no virtual
liquidity and moves the price down (`attacks/legacy_ceiling.lean`). The reference computes
`deltaL = ⌈fee * tmp / 2⌉` from the rounded virtual input, which satisfies both bounds.

Exact output. `deltaL` is the smaller root `(b - √(b² - F c')) / F` of the fee equation, with `b`
and `c'` rounded towards a smaller root, and the price `⌈(L - tmp) c / (L + deltaL)⌉`. The price
stays at least `t` when `deltaL` is at most the liquidity `X` that puts it on the target. With the
square root rounded down, `deltaL` can exceed the real root. With it rounded up, `deltaL` is on the
non-negative side of the quadratic, below the vertex; the reach amount gives
`a 2^96 d ≤ L n (c - t)` (`d = 2 t - fee c`, `n = d - fee t`, in units of `FEE_UNITS`), and the
identity `d * G = -w (w + L t² (2 - fee))` with `w = L (c - t) n - a 2^96 d` shows that the
quadratic is not positive at `X`, so the root is at most `X`. Without real numbers, every step is a
cross-multiplied inequality on products of several 256-bit values.

## Results

| Lean file | Code | Verdict |
|---|---|---|
| `candidate/Solution.lean` (= `attacks/deployed_4ab08c0.lean`) | the code at 4ab08c0 | REFUTED: REQ-IN-WITHIN-TARGET, REQ-OUT-WITHIN-TARGET, REQ-OUT-FEE-LIQUIDITY, REQ-POOL-CROSSES, each by a kernel-checked refutation |
| `attacks/legacy_ceiling.lean` | the exact-input fee liquidity rounded up as before pull request 95 | REFUTED |
| `attacks/exact_input_repaired_only.lean` | the exact-input repair alone | REFUTED (exact output) |
| `attacks/exact_output_repaired_only.lean` | the exact-output repair alone | REFUTED (exact input) |
| `attacks/zero_fee.lean` | no fee liquidity | REFUTED |
| `attacks/cap_restated.lean` | the price capped at the target, REQ-DEPLOYED-STEP restated as `True`, every other requirement proved | rejected by Comparator (statement mismatch); property tests pass; ordinary checking accepts |
| `reference/SolutionA.lean` | the code at 4ab08c0 with the two repairs, with a complete proof | VERIFIED |

Kernel-checked counterexamples (`witnesses/deployed_4ab08c0.lean`, `decide`): with liquidity
529700652, current price 26908681593376338809905220921561871, target
27180014754403994732126507336932861, fee 300 and an exact input of 1816821696332 units of token1
(one below the reach amount), the deployed step ends at 27180014754675749645719300096015422, above
the target. With liquidity 3391575, current price 316297169264893702192209790286789, target
312702479284222327139907330712089, fee 10 and an output of 153872678 units, it ends at
312702477359235854013914346495714, below the target.

The reference proof imports `ProofForgeFin.QuadRoot`, `ProofForgeFin.RoundCompose` and
`ProofForgeFin.Rounding`. Validation, Passports and spec strength: `validation.json` and
`results/hard-task-2/`.

## What is proved and what is not

- Proved, for the accepted candidate: every requirement above, for every input in the deployed
  range.
- The Solidity code is not proved. The port is a reviewed hand translation; the 512-bit
  `FullMath` algorithm is modeled by its specification (`ProofForgeFin.Evm.FullMath` proves the
  algorithm equal to it).
- Only the token1 branches are ported; the token0 branches (`isToken0 = true`) are not.
- The loop of `Pool.swap` is modeled for one iteration; tick lookup, `TickMath`, liquidity updates
  when a tick is crossed, fees to the government and the oracle are not.
- The repair is the build team's; Kyber has not published a fix of this code.
- The JSON wrapper `app/Main.lean` is tested, not proved.

## Sources

- `SwapMath.sol`: https://github.com/KyberNetwork/ks-elastic-sc/blob/4ab08c0a60f74809f731bdd333076e32d05f1d17/contracts/libraries/SwapMath.sol
- `QuadMath.sol`: https://github.com/KyberNetwork/ks-elastic-sc/blob/4ab08c0a60f74809f731bdd333076e32d05f1d17/contracts/libraries/QuadMath.sol
- `Pool.sol`: https://github.com/KyberNetwork/ks-elastic-sc/blob/4ab08c0a60f74809f731bdd333076e32d05f1d17/contracts/Pool.sol
- Echidna test: https://github.com/KyberNetwork/ks-elastic-sc/blob/4ab08c0a60f74809f731bdd333076e32d05f1d17/contracts/echidna/SwapMathEchidnaTest.sol
- `ks-elastic-sc-legacy` pull request 95: https://github.com/KyberNetwork/ks-elastic-sc-legacy/pull/95
- KyberSwap post-mortem: https://blog.kyberswap.com/post-mortem-kyberswap-elastic-exploit/
- BlockSec analysis: https://blocksec.com/blog/yet-another-tragedy-of-precision-loss-an-in-depth-analysis-of-the-kyber-swap-incident-1
