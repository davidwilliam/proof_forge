import Solution
import BalancerSwap.StableMath
/-!
Unit tests of the kind Balancer V2 ships, run against the port of the swap wrapper
(`candidate/Solution.lean`). Each test is checked by the Lean kernel (`decide`).

Tests 1 to 6 restate `pkg/solidity-utils/test/ScalingHelpers.test.ts` of
balancer/balancer-v2-monorepo at commit 88842344fb5f44d8ed6f8f944acd3be80627df87 (upscale,
downscaleDown and downscaleUp, with their rounding cases).

Tests 7 and 8 restate the regular-swap tests of `pkg/pool-stable/test/ComposableStablePool.test.ts`
("token out given token in" and "token in given token out", `swaps tokens`) for a two-token pool:
balances of 1 and 0.9 tokens, amplification 200 and the test helper's default swap fee of 0.0001%
(`pvt/helpers/src/models/types/TypesConverter.ts`), 0.1 token in or out. The pool math is the
StableMath port (`BalancerSwap.StableMath`). As in the original, the result must be within
0.001% (`equalWithError(expected, 0.00001)`) of the helper's estimate, which solves the
StableSwap equations in decimal arithmetic (`pvt/helpers/src/models/pools/stable/math.ts`);
the expected values here were computed with the same formulas at 60 significant digits.
Tests 9 and 10 repeat them with a token rate of 1.058132408689971699 on the token out (the
ComposableStablePool tests use rate providers), the expectation computed on the scaled balances.
Test 11 is the usual round trip: 0.1 token in and the same amount back out costs the trader the
fees and leaves the pool's invariant no lower.

All eleven pass. None of them trades against a balance of a few wei, which is where the attack
works (`witnesses/attack_batch.lean`).
-/
open BalancerSwap

def fp (whole tenths : Nat) : Nat := whole * ONE + tenths * (ONE / 10)

/-- 1. upscale returns the amount multiplied by the scaling factor: 42 * 1.6 = 67.2. -/
example : upscale (fp 42 0) (fp 1 6) = fp 67 2 := by decide

/-- 2. upscale rounds down: upscale(1, 1) = 0. -/
example : upscale 1 1 = 0 := by decide

/-- 3. downscaleDown returns the amount divided by the scaling factor: 60 / 1.6 = 37.5. -/
example : downscaleDown (fp 60 0) (fp 1 6) = some (fp 37 5) := by decide

/-- 4. downscaleDown rounds down: 5 / 2e18 * 1e18 = 2. -/
example : downscaleDown 5 (fp 2 0) = some 2 := by decide

/-- 5. downscaleUp returns the amount divided by the scaling factor: 60 / 1.6 = 37.5. -/
example : downscaleUp (fp 60 0) (fp 1 6) = some (fp 37 5) := by decide

/-- 6. downscaleUp rounds up: 5 / 2e18 * 1e18 = 3. -/
example : downscaleUp 5 (fp 2 0) = some 3 := by decide

/-- A two-token pool with balances 1 and 0.9 and the test helper's default fee (1e12). -/
def testPool (rateOut : Nat) : Pool where
  n := 2
  balance k := if k = 0 then fp 1 0 else if k = 1 then fp 0 9 else 0
  rate k := if k = 1 then rateOut else ONE
  fee := 1000000000000

/-- `actual` is within `expected * 0.00001` of `expected`. -/
def withinError (actual expected : Nat) : Prop :=
  expected - expected / 100000 ≤ actual ∧ actual ≤ expected + expected / 100000

instance (a e : Nat) : Decidable (withinError a e) := by unfold withinError; infer_instance

def amp200 : PoolMath := stableMath 200000 2

/-- `true` when the swap goes through with an amount within 0.001% of `expected`. -/
def swapsWithin (p : Pool) (s : Swap) (expected : Nat) : Bool :=
  match onSwap amp200 p s with
  | some y => decide (withinError y expected)
  | none => false

/-- 7. Swaps tokens given in: 0.1 of token 0 in; the helper estimates 0.099892402915257594 out. -/
example : swapsWithin (testPool ONE) ⟨.givenIn, 0, 1, fp 0 1⟩ 99892402915257594 = true := by decide

/-- 8. Swaps tokens given out: 0.1 of token 1 out; the helper estimates 0.100107774940813963 in. -/
example : swapsWithin (testPool ONE) ⟨.givenOut, 0, 1, fp 0 1⟩ 100107774940813963 = true := by decide

/-- 9. Given in, with a rate of 1.058132408689971699 on token 1. -/
example : swapsWithin (testPool 1058132408689971699) ⟨.givenIn, 0, 1, fp 0 1⟩ 94433851146999936 = true := by decide

/-- 10. Given out, with a rate of 1.058132408689971699 on token 1. -/
example : swapsWithin (testPool 1058132408689971699) ⟨.givenOut, 0, 1, fp 0 1⟩ 105897597860111865 = true := by decide

/-- The round trip of test 11: `true` when both swaps go through, the trader gets back less
token 0 than it paid in, and the pool's invariant does not fall. -/
def roundTrip : Bool :=
  let s1 : Swap := ⟨.givenIn, 0, 1, fp 0 1⟩
  match step onSwap amp200 (testPool ONE) s1, onSwap amp200 (testPool ONE) s1 with
  | some p1, some y =>
    match step onSwap amp200 p1 ⟨.givenIn, 1, 0, y⟩ with
    | some p2 => decide (fp 1 0 < p2.balance 0 ∧ value amp200 (testPool ONE) ≤ value amp200 p2)
    | none => false
  | _, _ => false

/-- 11. Round trip: 0.1 of token 0 in for token 1, then the token 1 received back in for token 0.
The trader gets back less than 0.1, and the pool's invariant does not fall. -/
example : roundTrip = true := by decide
