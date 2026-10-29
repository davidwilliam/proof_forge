import BalancerSwap.Spec
/-!
# StableMath port (protected, executable, not proved)

A transcription of the swap functions of Balancer V2's `StableMath` library
(`contracts/StableMath.sol` of the Composable Stable Pool deployed at
0xDACf5Fa19b1f720111609043ac67A9818262850c on Ethereum, verified on Sourcify with an exact
match; identical to `pkg/pool-stable/contracts/StableMath.sol` of balancer/balancer-v2-monorepo
at commit 88842344fb5f44d8ed6f8f944acd3be80627df87 except for two comment lines):
`_calculateInvariant` (lines 57 to 120), `_calcOutGivenIn` (124 to 159), `_calcInGivenOut`
(164 to 199) and `_getTokenBalanceGivenInvariantAndAllOtherBalances` (399 to 449), with
`Math.divDown` and `Math.divUp` of `Math.sol`.

It is used by the executable wrapper and by the tests to run the real pool formula through a
candidate's `onSwap`. Nothing here is proved, and no requirement refers to it: whether
StableMath meets `WellBehaved` is not established. Where the Solidity code reverts (a checked
subtraction that would go below zero, a division by zero, a Newton iteration that does not
converge in 255 steps), the functions here return `none`, and `stableMath` returns `REVERTED`
(2^256), which the Vault cannot hold (balances are below 2^112), so the swap fails.
-/

namespace BalancerSwap.StableMath

/-- `StableMath._AMP_PRECISION`. -/
def AMP_PRECISION : Nat := 1000

/-- `Math.divDown`: reverts on division by zero. -/
def divDown (a b : Nat) : Option Nat := if b = 0 then none else some (a / b)

/-- `Math.divUp`: `a == 0 ? 0 : 1 + (a - 1) / b`; reverts on division by zero. -/
def divUp (a b : Nat) : Option Nat :=
  if b = 0 then none else if a = 0 then some 0 else some (1 + (a - 1) / b)

/-- Checked subtraction (`Math.sub`, `FixedPoint.sub`): reverts below zero. -/
def sub (a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

/-- The returned value standing for a revert. -/
def REVERTED : Nat := 2 ^ 256

/-- One step of the D_P loop of `_calculateInvariant` over tokens `j` in `js`. -/
def dpLoop (b : Nat → Nat) (n inv : Nat) : List Nat → Nat → Option Nat
  | [], dP => some dP
  | j :: js, dP => do
    let dP' ← divDown (dP * inv) (b j * n)
    dpLoop b n inv js dP'

/-- The Newton iteration of `_calculateInvariant`, with `fuel` iterations left. -/
def invariantLoop (b : Nat → Nat) (n ampTimesTotal sum : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, inv => do
    let dP ← dpLoop b n inv (List.range n) inv
    let num := (ampTimesTotal * sum / AMP_PRECISION + dP * n) * inv
    let den := (ampTimesTotal - AMP_PRECISION) * inv / AMP_PRECISION + (n + 1) * dP
    let inv' ← divDown num den
    if inv' > inv then
      if inv' - inv ≤ 1 then some inv' else invariantLoop b n ampTimesTotal sum fuel inv'
    else if inv - inv' ≤ 1 then some inv' else invariantLoop b n ampTimesTotal sum fuel inv'

/-- `_calculateInvariant(amp, balances)` for the `n` balances `b 0, ..., b (n - 1)`. -/
def calculateInvariant (amp : Nat) (b : Nat → Nat) (n : Nat) : Option Nat :=
  let sum := (List.range n).foldl (fun s k => s + b k) 0
  if sum = 0 then some 0 else invariantLoop b n (amp * n) sum 255 sum

/-- The Newton iteration of `_getTokenBalanceGivenInvariantAndAllOtherBalances`. -/
def balanceLoop (inv c bb : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, tb => do
    let den ← sub (tb * 2 + bb) inv
    let tb' ← divUp (tb * tb + c) den
    if tb' > tb then
      if tb' - tb ≤ 1 then some tb' else balanceLoop inv c bb fuel tb'
    else if tb - tb' ≤ 1 then some tb' else balanceLoop inv c bb fuel tb'

/-- The P_D and sum loop over tokens `1, ..., n - 1`. -/
def pdLoop (b : Nat → Nat) (n inv : Nat) : List Nat → Nat × Nat → Option (Nat × Nat)
  | [], acc => some acc
  | j :: js, (pD, sum) => do
    let pD' ← divDown (pD * b j * n) inv
    pdLoop b n inv js (pD', sum + b j)

/-- `_getTokenBalanceGivenInvariantAndAllOtherBalances(amp, balances, invariant, t)`. -/
def tokenBalanceGiven (amp : Nat) (b : Nat → Nat) (n inv t : Nat) : Option Nat := do
  let ampTimesTotal := amp * n
  let (pD, sum) ← pdLoop b n inv ((List.range n).drop 1) (b 0 * n, b 0)
  let sum := sum - b t
  let inv2 := inv * inv
  let q ← divUp inv2 (ampTimesTotal * pD)
  let c := q * AMP_PRECISION * b t
  let q2 ← divDown inv ampTimesTotal
  let bb := sum + q2 * AMP_PRECISION
  let tb ← divUp (inv2 + c) (inv + bb)
  balanceLoop inv c bb 255 tb

/-- `_calcOutGivenIn(amp, balances, i, j, x, invariant)`. -/
def calcOutGivenIn (amp : Nat) (b : Nat → Nat) (n i j x inv : Nat) : Option Nat := do
  let b' := fun k => if k = i then b i + x else b k
  let finalOut ← tokenBalanceGiven amp b' n inv j
  let d ← sub (b j) finalOut
  sub d 1

/-- `_calcInGivenOut(amp, balances, i, j, x, invariant)`. -/
def calcInGivenOut (amp : Nat) (b : Nat → Nat) (n i j x inv : Nat) : Option Nat := do
  let bj ← sub (b j) x
  let b' := fun k => if k = j then bj else b k
  let finalIn ← tokenBalanceGiven amp b' n inv i
  let d ← sub finalIn (b i)
  some (d + 1)

end BalancerSwap.StableMath

namespace BalancerSwap

open StableMath in
/-- The pool math of a Composable Stable Pool with amplification `amp` (`A * 1000`) and `n`
tokens, as `_onRegularSwap` calls it: the invariant is computed from the balances, then
`_calcOutGivenIn` or `_calcInGivenOut` is called with it. A revert gives `REVERTED`. -/
def stableMath (amp n : Nat) : PoolMath where
  invariant b := (calculateInvariant amp b n).getD 0
  outGivenIn b i j x :=
    ((calculateInvariant amp b n).bind (calcOutGivenIn amp b n i j x)).getD REVERTED
  inGivenOut b i j x :=
    ((calculateInvariant amp b n).bind (calcInGivenOut amp b n i j x)).getD REVERTED

end BalancerSwap
