/-!
# Swap rounding specification (protected)

Owner-reviewed definitions for the swap path of a Balancer V2 pool that holds tokens with
different scaling factors (a Composable Stable Pool, for example). The Vault stores raw token
balances. Before pricing a swap the pool converts every amount to 18-decimal units with the
token's scaling factor (`10^(18 - decimals)` times the token's rate, as an 18-decimal fixed-point
number), runs its pricing math on those units, and converts the result back to raw units.
Each conversion rounds. This file states, for any pool math that meets the contract below,
which way every rounding must go: always in the pool's favour.

The pool math is abstract. A `PoolMath` is an invariant on 18-decimal balances (for a stable
pool, StableMath's `D`) and two pricing functions on 18-decimal amounts (`_calcOutGivenIn` and
`_calcInGivenOut`). It is well behaved for an `n`-token pool when the invariant does not
decrease when balances grow, and when a trade priced by the math, applied at whole 18-decimal
units, never lowers the invariant (`WellBehaved`). The requirements on the swap wrapper are
stated for every math with this contract, so they say nothing about whether a particular
formula (StableMath's Newton iteration, for example) meets it.

The implementation `onSwap : Impl` is the wrapper (`BaseGeneralPool._swapGivenIn` and
`_swapGivenOut`): given the math, the pool and a swap request, it returns the amount the pool
calculates (the amount out for a given-in swap, the amount in for a given-out swap), or `none`
when it refuses. The Vault's side of a swap (`step`: index checks, moving the balances, a
batch reverting as a whole) is defined here, outside the implementation. Candidates may not
edit this file; the locked challenge (`BalancerSwap/Challenge.lean`) applies every requirement
to the definition hole `BalancerSwap.onSwap`.

All quantities are natural numbers. Exact values are rationals; requirements state them by
cross-multiplication or with an explicit rounding direction.
-/

namespace BalancerSwap

/-- `FixedPoint.ONE`: one, as an 18-decimal fixed-point number. -/
def ONE : Nat := 1000000000000000000

/-- The 18-decimal value of the raw amount `a` at scaling factor `r`, rounded down:
`a * r / 1e18`. This is how the pool measures its own balances. -/
def scaleDown (a r : Nat) : Nat := a * r / ONE

/-- The 18-decimal value of the raw amount `a` at scaling factor `r`, rounded up: the least
whole 18-decimal unit at or above the exact value `a * r / 1e18`. -/
def scaleUp (a r : Nat) : Nat := (a * r + (ONE - 1)) / ONE

/-- A pool as the swap path sees it. Tokens are numbered `0` to `n - 1` (the pool's own BPT is
not one of them). `balance k` is the raw balance of token `k` held by the Vault, `rate k` its
scaling factor (`10^(18 - decimals)` times its rate, 18-decimal fixed point; `1e18` for an
18-decimal token without a rate provider), and `fee` the swap fee percentage (18-decimal fixed
point; `1e14` is 0.01%). -/
structure Pool where
  n : Nat
  balance : Nat → Nat
  rate : Nat → Nat
  fee : Nat

/-- Swap kinds: the amount given is the amount in (`GIVEN_IN`) or the amount out
(`GIVEN_OUT`, called EXACT_OUT in Balancer's report). -/
inductive Kind where
  | givenIn
  | givenOut
  deriving DecidableEq

/-- One swap request: token `tokenIn` for token `tokenOut`, with the given `amount` in raw
units of the token it refers to (`tokenIn` for a given-in swap, `tokenOut` for a given-out
swap). -/
structure Swap where
  kind : Kind
  tokenIn : Nat
  tokenOut : Nat
  amount : Nat

/-- `b` with entry `i` replaced by `x` and entry `j` replaced by `y` (for `i ≠ j`). -/
def update2 (b : Nat → Nat) (i x j y : Nat) : Nat → Nat :=
  fun k => if k = i then x else if k = j then y else b k

/-! ## The pool math and its contract -/

/-- Pool math on 18-decimal balances `b`.
* `invariant b`: the pool's invariant (StableMath's `D` for a stable pool).
* `outGivenIn b i j x`: the amount of token `j` out for `x` of token `i` in.
* `inGivenOut b i j x`: the amount of token `i` in for `x` of token `j` out. -/
structure PoolMath where
  invariant : (Nat → Nat) → Nat
  outGivenIn : (Nat → Nat) → Nat → Nat → Nat → Nat
  inGivenOut : (Nat → Nat) → Nat → Nat → Nat → Nat

/-- The invariant does not decrease when no balance of the `n` tokens decreases (and it
depends on those balances only). -/
def InvariantMonotone (m : PoolMath) (n : Nat) : Prop :=
  ∀ b b' : Nat → Nat, (∀ k, k < n → b k ≤ b' k) → m.invariant b ≤ m.invariant b'

/-- A given-in trade priced by the math pays out at most the balance and does not lower the
invariant. -/
def OutGivenInSound (m : PoolMath) (n : Nat) : Prop :=
  ∀ (b : Nat → Nat) (i j x : Nat), i ≠ j → i < n → j < n →
    m.outGivenIn b i j x ≤ b j ∧
    m.invariant b ≤ m.invariant (update2 b i (b i + x) j (b j - m.outGivenIn b i j x))

/-- A given-out trade of less than the balance, priced by the math, does not lower the
invariant. -/
def InGivenOutSound (m : PoolMath) (n : Nat) : Prop :=
  ∀ (b : Nat → Nat) (i j x : Nat), i ≠ j → i < n → j < n → x < b j →
    m.invariant b ≤ m.invariant (update2 b i (b i + m.inGivenOut b i j x) j (b j - x))

/-- The contract a pool's math must meet for an `n`-token pool. This is a hypothesis of the
requirements below, not an assumption about any particular formula. -/
structure WellBehaved (m : PoolMath) (n : Nat) : Prop where
  monotone : InvariantMonotone m n
  outGivenIn : OutGivenInSound m n
  inGivenOut : InGivenOutSound m n

/-- Prices grow with the amount traded: more in pays out at least as much, more out costs
at least as much. -/
def PriceMonotone (m : PoolMath) : Prop :=
  (∀ (b : Nat → Nat) (i j x y : Nat), x ≤ y → m.outGivenIn b i j x ≤ m.outGivenIn b i j y) ∧
  (∀ (b : Nat → Nat) (i j x y : Nat), x ≤ y → m.inGivenOut b i j x ≤ m.inGivenOut b i j y)

/-! ## The Vault's side of a swap -/

/-- An implementation returns the amount the pool calculates for a swap (out for given-in, in
for given-out), or `none` when it refuses (the swap reverts). -/
abbrev Impl := PoolMath → Pool → Swap → Option Nat

/-- The pool's balances in 18-decimal units, rounded down: what the pool prices with and how
it values itself. -/
def scaledBalances (p : Pool) : Nat → Nat := fun k => scaleDown (p.balance k) (p.rate k)

/-- The pool's value as the pool itself measures it: the invariant of its balances in
18-decimal units, rounded down. For a Composable Stable Pool this is the `D` behind
`getRate()`, the price of one BPT (`D / supply`; a token swap does not change the supply). -/
def value (m : PoolMath) (p : Pool) : Nat := m.invariant (scaledBalances p)

/-- The Vault's checks on a request: two different tokens of the pool. -/
def Valid (p : Pool) (s : Swap) : Prop :=
  s.tokenIn ≠ s.tokenOut ∧ s.tokenIn < p.n ∧ s.tokenOut < p.n

instance (p : Pool) (s : Swap) : Decidable (Valid p s) := by
  unfold Valid; infer_instance

/-- Raw amount entering the pool, given the amount the pool calculated. -/
def amountIn (s : Swap) (q : Nat) : Nat :=
  match s.kind with
  | .givenIn => s.amount
  | .givenOut => q

/-- Raw amount leaving the pool, given the amount the pool calculated. -/
def amountOut (s : Swap) (q : Nat) : Nat :=
  match s.kind with
  | .givenIn => q
  | .givenOut => s.amount

/-- The Vault moves the balances; it reverts when more would leave than the pool holds. -/
def settle (p : Pool) (s : Swap) (q : Nat) : Option Pool :=
  if amountOut s q ≤ p.balance s.tokenOut then
    some { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s q)
                                     s.tokenOut (p.balance s.tokenOut - amountOut s q) }
  else none

/-- One swap through the Vault: checks, the implementation's quote, settlement. -/
def step (impl : Impl) (m : PoolMath) (p : Pool) (s : Swap) : Option Pool :=
  if Valid p s then
    match impl m p s with
    | some c => settle p s c
    | none => none
  else none

/-- A batch (`batchSwap`): swaps run in order against the balances left by the previous
ones; if any swap reverts, the whole batch reverts. -/
def run (impl : Impl) (m : PoolMath) (p : Pool) : List Swap → Option Pool
  | [] => some p
  | s :: ss =>
    match step impl m p s with
    | some p' => run impl m p' ss
    | none => none

/-! ## Exact values the requirements refer to -/

/-- The amount given in a given-in swap net of the swap fee, in 18-decimal units, rounded
down: `amount * (1 - fee) * rate / 1e18`. -/
def netInDown (p : Pool) (s : Swap) : Nat :=
  s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE)

/-- The same for one raw unit less: `(amount * (1 - fee) - 1) * rate / 1e18`, rounded down. -/
def netInLessOneDown (p : Pool) (s : Swap) : Nat :=
  (s.amount * (ONE - p.fee) - ONE) * p.rate s.tokenIn / (ONE * ONE)

/-- The math's price of a given-out swap, at the exact amount out rounded up to a whole
18-decimal unit. -/
def outPrice (m : PoolMath) (p : Pool) (s : Swap) : Nat :=
  m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut (scaleUp s.amount (p.rate s.tokenOut))

/-! ## Requirements on the implementation -/

/-- REQ-GIVEN-IN-SUCCEEDS: a given-in swap between two tokens of the pool goes through, for any
well-behaved math, when the scaling factor of the token out is positive and the fee is below
100%. -/
def GivenInSucceeds (impl : Impl) : Prop :=
  ∀ m p s, WellBehaved m p.n → s.kind = .givenIn → Valid p s → 0 < p.rate s.tokenOut →
    p.fee < ONE → (step impl m p s).isSome

/-- REQ-GIVEN-OUT-SUCCEEDS: a given-out swap between two tokens of the pool goes through, for any
well-behaved math, when the exact amount out rounded up is below the pool's balance of that
token (both in 18-decimal units), the scaling factor of the token in is positive and the fee
is below 100%. -/
def GivenOutSucceeds (impl : Impl) : Prop :=
  ∀ m p s, WellBehaved m p.n → s.kind = .givenOut → Valid p s → 0 < p.rate s.tokenIn →
    p.fee < ONE →
    scaleUp s.amount (p.rate s.tokenOut) < scaleDown (p.balance s.tokenOut) (p.rate s.tokenOut) →
    (step impl m p s).isSome

/-- REQ-GIVEN-IN-PAYS-AT-MOST: in a given-in swap the trader receives at most what the math
prices the exact amount in, net of the fee, rounded down: `y * rate_out / 1e18` is at most
`outGivenIn` of that amount. Rounding never pays out more than the trader paid for. -/
def GivenInPaysAtMost (impl : Impl) : Prop :=
  ∀ m p s y, PriceMonotone m → s.kind = .givenIn → Valid p s → impl m p s = some y →
    y * p.rate s.tokenOut ≤ ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInDown p s)

/-- REQ-GIVEN-IN-PAYS-AT-LEAST: and it receives at least what the math prices one raw unit less
than the net amount in, less one raw unit out: the rounding costs the trader at most one unit
on each side. -/
def GivenInPaysAtLeast (impl : Impl) : Prop :=
  ∀ m p s y, PriceMonotone m → s.kind = .givenIn → Valid p s → impl m p s = some y →
    ONE * m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut (netInLessOneDown p s) <
      (y + 1) * p.rate s.tokenOut

/-- REQ-GIVEN-OUT-CHARGES-AT-LEAST: in a given-out swap the trader is charged, after the fee,
at least what the math prices the exact amount out rounded up to a whole 18-decimal unit:
`c * (1 - fee) * rate_in / 1e18` is at least `outPrice`. Rounding never lets the trader take
more than it pays for. -/
def GivenOutChargesAtLeast (impl : Impl) : Prop :=
  ∀ m p s c, PriceMonotone m → s.kind = .givenOut → Valid p s → impl m p s = some c →
    ONE * ONE * outPrice m p s ≤ c * (ONE - p.fee) * p.rate s.tokenIn

/-- REQ-GIVEN-OUT-CHARGES-AT-MOST: and one raw unit less than the charge, after the fee, is below
that price plus one raw unit of the token in: the rounding costs the trader at most one unit for
the conversion back to raw units and one for the fee. -/
def GivenOutChargesAtMost (impl : Impl) : Prop :=
  ∀ m p s c, PriceMonotone m → s.kind = .givenOut → Valid p s → impl m p s = some c →
    (c - 1) * (ONE - p.fee) * p.rate s.tokenIn < ONE * (ONE * outPrice m p s + p.rate s.tokenIn)

/-- REQ-SWAP-KEEPS-VALUE: for any well-behaved math, a swap that goes through never lowers the
pool's value as the pool measures it (`value`). -/
def SwapKeepsValue (impl : Impl) : Prop :=
  ∀ m p s p', WellBehaved m p.n → step impl m p s = some p' → value m p ≤ value m p'

/-- REQ-BATCH-KEEPS-VALUE: for any well-behaved math, any pool and any batch of swaps of either
kind, a batch that goes through never lowers the pool's value as the pool measures it. The
rounding of one swap cannot be repeated inside a batch to drain the pool. -/
def BatchKeepsValue (impl : Impl) : Prop :=
  ∀ m p ss p', WellBehaved m p.n → run impl m p ss = some p' → value m p ≤ value m p'

/-! ## Example math -/

/-- A two-token constant-product pool (tokens 0 and 1): invariant `b 0 * b 1`, given-in
priced at `b j * x / (b i + x)` rounded down, given-out at `b i * x / (b j - x)` rounded up
(and `b i * x` when `x` is not below the balance). `BalancerSwap.Sanity` proves it well
behaved and its prices monotone. -/
def constantProduct : PoolMath where
  invariant b := b 0 * b 1
  outGivenIn b i j x := b j * x / (b i + x)
  inGivenOut b i j x := if x < b j then (b i * x + (b j - x - 1)) / (b j - x) else b i * x

end BalancerSwap
