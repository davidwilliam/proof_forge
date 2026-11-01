# rw-oz-sqrt: the integer square root of OpenZeppelin `Math` and a pool's first deposit

This task holds a Lean specification of OpenZeppelin's `Math.sqrt` and of the first deposit of a
volatile pool that calls it, a port of the deployed code with a complete proof, and a start
candidate that differs from the deployed code in one line: six Newton steps instead of seven. The
start candidate is a plausible variant, not an OpenZeppelin release. It is wrong only from 204-bit
inputs on, which no ordinary unit test reaches; it is refuted in the Lean kernel.

The code is short (twelve lines). What makes it hard to prove is the mathematics: that seven
Newton steps from a power-of-two estimate always reach the root, for every `uint256`, needs an
error bound for Newton's method with floor divisions.

## The code

OpenZeppelin Contracts v4.9.6, commit `dc44c9f1a4c3b10af99492eed84f83ed244203f6`,
`contracts/utils/math/Math.sol` (the same `sqrt` is in v4.8.0 and v5.0.x):

| Lines | Function | Port in `spec/OzSqrt/Spec.lean` |
|---|---|---|
| 152 to 183 | `sqrt(uint256 a)`: `result = 1 << (log2(a) >> 1)`, seven lines `result = (result + a / result) >> 1`, `return min(result, a / result)` | the definition hole `sqrt`; `newtonSqrt k` is the same shape with `k` steps |
| 188 to 193 | `sqrt(uint256 a, Rounding rounding)`: `result + (rounding == Rounding.Up && result * result < a ? 1 : 0)` | `sqrtUp` |
| 199 to 234 | `log2(uint256 value)`: binary search on the bits | `log2`, `log2Step` |
| 26 to 28 | `min(uint256 a, uint256 b)` | `min` |

Pull request 4403 (2024-02-16, released in v5.1.0) replaced this `sqrt` with a 3/2 estimate and
six Newton steps, with the error analysis in its comments.

The caller is Aerodrome's `Pool.mint` (aerodrome-finance/contracts, commit
`d5e48b3b36a08726abd74432974c5bcdb4507bc9`, `contracts/Pool.sol` lines 313 to 315 and 323 to 324,
built against OpenZeppelin 4.8.0): on the first deposit of a volatile pool,
`liquidity = Math.sqrt(_amount0 * _amount1) - MINIMUM_LIQUIDITY` with `MINIMUM_LIQUIDITY = 10 ** 3`,
which is locked at `address(1)`, and a revert when `liquidity == 0`. The port is `firstMint`.
Velodrome V2 (commit `e3f62b897fa517bd5e3a5057f7e02ab4b35edbeb`, line 305) makes the same call but
reverts when `liquidity < MINIMUM_LIQUIDITY` (line 314); that variant is not ported.

Solidity's `uint256` is `BitVec 256`; inside `unchecked` the operations wrap exactly like
`BitVec`'s; the checked product and subtraction of `mint` revert on overflow and underflow, which
is `none`.

## Requirements

| Requirement | Lean statement (`spec/OzSqrt/Spec.lean`) |
|---|---|
| REQ-SQRT-NOT-ABOVE | `∀ a, (sqrt a).toNat * (sqrt a).toNat ≤ a.toNat`: the root is never overstated |
| REQ-SQRT-NOT-BELOW | `∀ a, a.toNat < ((sqrt a).toNat + 1) * ((sqrt a).toNat + 1)`: never understated |
| REQ-SQRT-UP-COVERS | the root rounded up, squared, is at least the input |
| REQ-SQRT-UP-TIGHT | `0 < r → (r - 1) * (r - 1) < a` for the root rounded up `r` |
| REQ-MINT-BACKED | `firstMint sqrt a0 a1 = some l → (l + 1000) * (l + 1000) ≤ a0 * a1`: the LP supply created, locked units included, never exceeds the geometric mean of the amounts |
| REQ-MINT-FULL | `firstMint sqrt a0 a1 = some l → a0 * a1 < (l + 1001) * (l + 1001)`: the depositor is not shortchanged by a unit |
| REQ-MINT-LIVE | a first deposit whose product fits in 256 bits and is at least `1001 * 1001` does not revert |
| REQ-NEWTON-BUDGET | `∃ k ≤ 7, ∀ a, sqrt a = newtonSqrt k a`: the routine is the deployed algorithm (the `log2` estimate, at most seven Newton steps, the final `min`) |

REQ-NEWTON-BUDGET keeps the deployed algorithm and its gas budget. Without it, a candidate could
replace the routine by Lean core's `Nat.sqrt`, whose bounds `Nat.sqrt_le` and `Nat.lt_succ_sqrt`
are in the core library, and prove the other seven requirements without any error analysis
(`attacks/nat_sqrt_restated.lean` does exactly that, with REQ-NEWTON-BUDGET restated; Comparator
rejects it). The requirement is extensional: any routine equal to the deployed algorithm on every
input meets it, and showing that equality for a different routine needs the same error analysis.
Mutants that change the code but not its values (for example the arguments of `min` swapped) meet
it, which is why the spec-strength gate reports them as possibly equivalent.

Protected lemmas (`spec/OzSqrt/Lemmas.lean`, readable by every candidate): `toNat_log2` (the
port of `log2` is `Nat.log2`), `toNat_newtonStep` (a Newton line is `(r + a / r) / 2` when it
does not wrap), `toNat_min`, `firstMint_eq_some`, `firstMint_isSome`, and two sanity theorems:
`floor_unique` (any routine meeting the first two requirements returns `2^102 - 1` at
`2^204 - 1`) and `mint_example` (with such a routine the first deposit of `2^102 + 1` and
`2^102 - 1` mints `2^102 - 1001` units).

## Why the proof is hard

With `s` the floor of the root of `a` and `E = 2^(log2(a) / 2)` the estimate, `E ≤ s < 2 * E`. A
Newton step `x' = (x + a / x) / 2` with floor divisions satisfies, from either side of the root,
`2 * x * (x' - s) ≤ (x - s)^2 + 2 * s`. From that relation:

1. the first step leaves an error of at most `s / 4 + 2`;
2. each further step turns an error bound `s / 2^k + 2` into `s / 2^(2k+1) + 2`, so after six steps
   the error is at most `s / 2^95 + 2`, whose square is at most `s` because `s < 2^128`;
3. the seventh step then gives `s`, or `s + 1` with `s * (s + 1) ≤ a`, and `min(result, a / result)`
   returns `s` in both cases;
4. no step wraps a 256-bit word.

With six steps, `min` is applied to the sixth iterate, for which the argument gives only the bound
`s / 2^95 + 2`; that does not place it at the root or the root plus one when the root is large.
At `a = 2^204 - 1` the sixth iterate is above the root plus one and `min` returns the root minus
one; at `a = 2^256 - 1` the sixth iterate is 198202505 above the root and `min` returns the root
minus 198202503. Lean has no real numbers without Mathlib, so the whole
argument is in natural-number arithmetic with floors.

## Results

| Lean file | Code | Verdict |
|---|---|---|
| `candidate/Solution.lean` (= `attacks/six_steps.lean`) | v4.9.6 `sqrt` with six Newton steps: plausible variant, not a release | REFUTED: REQ-SQRT-NOT-BELOW, REQ-SQRT-UP-COVERS, REQ-MINT-FULL |
| `attacks/no_min.lean` | seven steps without the final `min`, the flaw class of CVE-2025-26622 in Vyper's `sqrt` (plausible variant, not a release) | REFUTED: REQ-SQRT-NOT-ABOVE (returns 2 at `a = 3`), REQ-SQRT-UP-TIGHT, REQ-MINT-BACKED |
| `attacks/nat_sqrt_restated.lean` | Lean core's `Nat.sqrt`, REQ-NEWTON-BUDGET restated as `True` | rejected by Comparator (statement mismatch); property tests pass; ordinary checking accepts |
| `reference/SolutionA.lean` | v4.9.6 `sqrt`, seven steps, with a complete proof | VERIFIED |

Kernel-checked counterexample (`witnesses/six_steps.lean`, `decide`, axiom `propext` only): the
six-step routine returns `2^102 - 2` at `2^204 - 1`, refuting REQ-SQRT-NOT-BELOW, and the first
deposit of `2^102 + 1` and `2^102 - 1` mints `2^102 - 1002` units where `2^102 - 1001` are owed,
refuting REQ-MINT-FULL.

The reference proof is 281 non-blank lines of Lean (19 theorems); it imports
`ProofForgeFin.Sqrt` for the one-step facts (the error relation, AM-GM with floors, the end of
the iteration and the final correction). Validation, Passports and spec strength:
`validation.json` and `results/hard-task-1/README.md`.

## What is proved and what is not

- Proved, for the accepted candidate: every requirement above, for every `uint256` input and
  every pair of deposit amounts.
- The Solidity code is not proved. The port is a reviewed hand translation; `unchecked`
  arithmetic is modeled as `BitVec`, which wraps as the EVM does.
- Only the volatile, first-deposit branch of Aerodrome's `Pool.mint` is modeled; the token
  transfers, `_mint`, reserves and the stable-pool checks are not.
- The six-step start candidate and the `min`-less attack are plausible variants, not releases of
  OpenZeppelin or of any project known to the build team.
- The JSON wrapper `app/Main.lean` is tested, not proved.

## Sources

- OpenZeppelin Contracts v4.9.6, `Math.sol`: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/math/Math.sol
- Pull request 4403, "Improved integer square root": https://github.com/OpenZeppelin/openzeppelin-contracts/pull/4403
- Aerodrome `Pool.sol`: https://github.com/aerodrome-finance/contracts/blob/d5e48b3b36a08726abd74432974c5bcdb4507bc9/contracts/Pool.sol
- Velodrome V2 `Pool.sol`: https://github.com/velodrome-finance/contracts/blob/e3f62b897fa517bd5e3a5057f7e02ab4b35edbeb/contracts/Pool.sol
- Vyper advisory GHSA-2p94-8669-xg86 (CVE-2025-26622): https://github.com/vyperlang/vyper/security/advisories/GHSA-2p94-8669-xg86
