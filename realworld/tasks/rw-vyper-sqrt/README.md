# rw-vyper-sqrt: Vyper's `sqrt()` builtin and CVE-2025-26622

This task holds a Lean specification of the code the Vyper compiler inlines for the builtin
`sqrt(d: decimal) -> decimal`, a port of that code as released in Vyper v0.4.0, and the fix
released in v0.4.1 with a complete proof. The v0.4.0 port is refuted in the Lean kernel on the
input of the security advisory.

## What happened

Vyper is the contract language of Curve and other DeFi protocols. Its `sqrt()` builtin computes the
square root of a `decimal` (a signed 168-bit integer read as a multiple of `10^-10`) with a
Babylonian loop. Advisory GHSA-2p94-8669-xg86 (CVE-2025-26622, "sqrt doesn't define rounding
behavior", published 2025-02-21, versions below 0.4.1 affected) reports that the loop handles
"the oscillating final states" improperly: for `0.9999999998` the result is `0.9999999999`, the
root rounded up, while other inputs are rounded down. Pull request 4486 (merged 2025-02-23, merge
commit `2ffc8b3db8b7e32257a72560fa89e7dcf81b5384`) adds, after the loop, `if y < z: z = y`; its
commit message says the undefined rounding "could be an issue for applications which use `sqrt()`
to determine boundary conditions". Vyper v0.4.1 (2025-03-01) ships the fix. Loss figures: none
are claimed.

## The code

Vyper v0.4.0, commit `e9db8d9f7486eae38f5b86531629019ad28f514e`, `vyper/builtins/functions.py`,
class `Sqrt`, lines 2117 to 2172, inlines:

```
assert x >= 0.0
z: decimal = 0.0
if x == 0.0:
    z = 0.0
else:
    z = x / 2.0 + 0.5
    y: decimal = x
    for i: uint256 in range(256):
        if z == y:
            break
        y = z
        z = (x / z + z) / 2.0
```

The decimal operations are those of `vyper/codegen/arithmetic.py` at the same commit: `a + b` is
`add` followed by the `int168` range check (`clamp_basetype`); `a / b` is
`sdiv(mul(a, 10^10), b)` after a check that `b` is not zero, followed by the range check. The port
(`spec/VyperSqrt/Spec.lean`) models a decimal as its raw `Int` value, a revert as `none`,
`sdiv` as `Int.tdiv` (the 256-bit `mul` never wraps on decimals: `|a * 10^10| < 2^201`), and the
loop as `loop x n y z` with `n` iterations left. `vyperSqrtWith fin` is the whole routine with
`fin y z` chosen from the last two iterates: v0.4.0 is `fin y z = z`, the fix is
`fin y z = if y < z then y else z`.

## Requirements

For a raw decimal `x` (`IsDecimal x`: `-2^167 ≤ x ≤ 2^167 - 1`) and a result `r`:

| Requirement | Lean statement (`spec/VyperSqrt/Spec.lean`) |
|---|---|
| REQ-SQRT-NOT-ABOVE | `sqrt x = some r → r * r ≤ x * 10^10`: the root is rounded down, never up |
| REQ-SQRT-NOT-BELOW | `sqrt x = some r → x * 10^10 < (r + 1) * (r + 1)`: less than `10^-10` below the root |
| REQ-SQRT-TOTAL | `0 ≤ x → (sqrt x).isSome`: a non-negative decimal never reverts |
| REQ-SQRT-NEG-REVERTS | `x < 0 → sqrt x = none` (`assert x >= 0.0`) |
| REQ-DEPLOYED-LOOP | `∃ fin, ∀ x, sqrt x = vyperSqrtWith fin x`: the deployed loop (the seed `x / 2.0 + 0.5`, at most 256 iterations, a stop when two successive iterates are equal) followed by a choice between the last two iterates, which is where the fix changed the code |

Without REQ-DEPLOYED-LOOP a candidate could return Lean core's `Nat.sqrt` of `x * 10^10` and prove
the other four requirements from `Nat.sqrt_le` and `Nat.lt_succ_sqrt`, with no analysis of the
loop (`attacks/nat_sqrt_restated.lean`; Comparator rejects it).

Protected lemmas (`spec/VyperSqrt/Lemmas.lean`): on non-negative values the decimal operations are
operations on natural numbers (`ddiv_nat`, `dadd_nat`), the loop stops on equal iterates
(`loop_stop`), one iteration from a positive iterate is `(x * 10^10 / z + z) / 2` when it stays in
range (`loop_step`), the seed is `x / 2 + 5 * 10^9` (`seed_div`, `seed_add`), and on a positive
decimal the routine is the loop from the seed followed by the choice (`vyperSqrtWith_pos`).

## Why the proof is hard

With `N = x * 10^10` and `s` the floor of its root, the loop is Newton's method for `N` with floor
divisions, started at `x / 2 + 5 * 10^9`, which can be about `2^66` times the root (for `x` near
`2^167`). The proof needs:

1. a bound on the number of iterations: above the root the error at least halves each step
   (`x' - s ≤ (x - s) / 2 + 1`), so from an error below `2^167 + 2` it falls to 3 within 167
   steps, and one more step reaches `s` or `s + 1` (a square error at most `2 * s`); 170 of the
   256 iterations suffice;
2. the oscillation: from `s` or `s + 1` the iterates stay there, and alternate between them exactly
   when `N + 1` is a perfect square, so the smaller of the last two iterates is `s` and the last
   one alone is not;
3. the early stop: two equal successive iterates are a fixed point of the step, which is `s`
   (the first comparison, of the seed with `x` itself, holds only for `x = 10^10 - 1` and
   `x = 10^10`, whose roots are themselves);
4. range: no operation leaves the `int168` range of a decimal.

## Results

| Lean file | Code | Verdict |
|---|---|---|
| `candidate/Solution.lean` (= `attacks/v040_port.lean`) | v0.4.0 | REFUTED: REQ-SQRT-NOT-ABOVE |
| `attacks/nat_sqrt_restated.lean` | Lean core's `Nat.sqrt`, REQ-DEPLOYED-LOOP restated as `True` | rejected by Comparator (statement mismatch); property tests pass; ordinary checking accepts |
| `reference/SolutionA.lean` | v0.4.1 (v0.4.0 plus pull request 4486) with a complete proof | VERIFIED |

Kernel-checked counterexample (`witnesses/v040_port.lean`, `decide +kernel`, no axioms): the
v0.4.0 port returns `9999999999` for `9999999998`; `9999999999^2 > 9999999998 * 10^10`, refuting
REQ-SQRT-NOT-ABOVE. The property tests generate inputs with `x * 10^10 + 1` a perfect square
from the four square roots of 1 modulo `10^10`, which is where the oscillation happens.

The reference proof is 218 non-blank lines of Lean (14 theorems); it imports `ProofForgeFin.Sqrt`
for the one-step facts (halving, the end of the iteration, the only fixed point, the smaller of
two iterates). Validation, Passports and spec strength: `validation.json` and
`results/hard-task-1/README.md`.

## What is proved and what is not

- Proved, for the accepted candidate: every requirement above for every `decimal` input.
- The compiler is not proved. The port is a reviewed hand translation of the Vyper source the
  compiler inlines and of the decimal arithmetic it generates; the EVM bytecode is not compared.
- The JSON wrapper `app/Main.lean` is tested, not proved.

## Sources

- Advisory GHSA-2p94-8669-xg86 (CVE-2025-26622): https://github.com/vyperlang/vyper/security/advisories/GHSA-2p94-8669-xg86
- Pull request 4486, "fix[lang]: define rounding mode for sqrt": https://github.com/vyperlang/vyper/pull/4486
- Vyper v0.4.0 `functions.py`: https://github.com/vyperlang/vyper/blob/e9db8d9f7486eae38f5b86531629019ad28f514e/vyper/builtins/functions.py
- Vyper v0.4.0 `arithmetic.py`: https://github.com/vyperlang/vyper/blob/e9db8d9f7486eae38f5b86531629019ad28f514e/vyper/codegen/arithmetic.py
