import ProofForgeFin.DeFi
/-!
# Demonstration: the value requirements of `rw-balancer-upscale` with the library

The first section copies `realworld/tasks/rw-balancer-upscale/spec/BalancerSwap/Spec.lean` without
change (its namespace body, with every doc string). The task files are not imported or modified.

The second section proves, for every implementation, that REQ-BATCH-KEEPS-VALUE follows from
REQ-SWAP-KEEPS-VALUE, and that the rounding requirements REQ-GIVEN-IN-PAYS-AT-MOST and
REQ-GIVEN-OUT-CHARGES-AT-LEAST make a swap keep the pool's value, with the library's pool-math
interface (`ProofForgeFin.DeFi.AMM.WellBehaved.scaled_swapIn`, `scaled_swapOut`). It also re-proves
`constantProduct_wellBehaved` of `spec/BalancerSwap/Sanity.lean` from the library's instance.
-/

namespace ProofForgeFinDemo.DeFi.Balancer

/-! ## Copied from `spec/BalancerSwap/Spec.lean` -/


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

/-! ## Re-proved with the library

The reference solution proves REQ-SWAP-KEEPS-VALUE and REQ-BATCH-KEEPS-VALUE for its own
implementation, through a domination lemma for the scaled balances and an induction over the
batch. Here, for every implementation:

* REQ-BATCH-KEEPS-VALUE follows from REQ-SWAP-KEEPS-VALUE (`batch_keeps_value`), with
  `AMM.runAll_invariant_le` and the pool's token count kept by every swap;
* a given-in swap keeps the value for every well-behaved math with monotone prices when the
  implementation meets REQ-GIVEN-IN-PAYS-AT-MOST (`given_in_keeps_value`), and a given-out swap
  does when it meets REQ-GIVEN-OUT-CHARGES-AT-LEAST and the exact amount out rounded up is below
  the pool's scaled balance (`given_out_keeps_value`, the condition the reference implementation
  checks before pricing), with `AMM.WellBehaved.scaled_swapIn` and `scaled_swapOut`;
* the task's constant product is well behaved (`constantProduct_wellBehaved`, proved in
  `spec/BalancerSwap/Sanity.lean`), from the library's `AMM.constantProduct_wellBehaved`. -/

/-- One is positive. -/
theorem one_pos : 0 < ONE := by unfold ONE; decide

/-- The task's `scaleDown` is the library's at scale `ONE`. -/
theorem scaleDown_eq (a r : Nat) : scaleDown a r = ProofForgeFin.scaleDown ONE a r := rfl

/-- The task's `scaleUp` is the library's at scale `ONE`. -/
theorem scaleUp_eq (a r : Nat) : scaleUp a r = ProofForgeFin.scaleUp ONE a r := by
  unfold scaleUp
  rw [ProofForgeFin.scaleUp, ProofForgeFin.mulUp, ProofForgeFin.mulDivUp,
    ProofForgeFin.ceilDiv_eq_add_pred _ _ one_pos]

/-- The task's `update2` is the library's. -/
theorem update2_eq : update2 = ProofForgeFin.DeFi.AMM.update2 := rfl

/-- The task's pool math as the library's. -/
def toLib (m : PoolMath) : ProofForgeFin.DeFi.AMM.PoolMath := ⟨m.invariant, m.outGivenIn, m.inGivenOut⟩

/-- The task's contract is the library's. -/
theorem wellBehaved_iff (m : PoolMath) (n : Nat) :
    WellBehaved m n ↔ ProofForgeFin.DeFi.AMM.WellBehaved (toLib m) n :=
  ⟨fun h => ⟨h.monotone, h.outGivenIn, h.inGivenOut⟩, fun h => ⟨h.monotone, h.outGivenIn, h.inGivenOut⟩⟩

/-- The task's constant product is the library's. -/
theorem toLib_constantProduct : toLib constantProduct = ProofForgeFin.DeFi.AMM.constantProduct := by
  simp only [toLib, constantProduct, ProofForgeFin.DeFi.AMM.constantProduct,
    ProofForgeFin.DeFi.AMM.PoolMath.mk.injEq, true_and]
  funext b i j x
  split
  · rw [ProofForgeFin.ceilDiv_eq_add_pred _ _ (by omega)]
  · rfl

/-- `BalancerSwap.Sanity.constantProduct_wellBehaved`, from the library's instance. -/
theorem constantProduct_wellBehaved : WellBehaved constantProduct 2 :=
  (wellBehaved_iff _ _).2 (toLib_constantProduct ▸ ProofForgeFin.DeFi.AMM.constantProduct_wellBehaved)

/-- The task's batch is the library's atomic run. -/
theorem run_eq (impl : Impl) (m : PoolMath) (p : Pool) (ss : List Swap) :
    run impl m p ss = ProofForgeFin.Seq.runAll (step impl m) p ss := by
  induction ss generalizing p with
  | nil => rfl
  | cons s ss ih =>
    simp only [run, ProofForgeFin.Seq.runAll]
    split <;> simp_all

/-- A successful swap: the request is valid, the implementation quoted `c`, the amount out is
within the balance, and the balances moved by the amounts in and out. -/
theorem step_some {impl : Impl} {m : PoolMath} {p p' : Pool} {s : Swap}
    (h : step impl m p s = some p') :
    Valid p s ∧ ∃ c, impl m p s = some c ∧ amountOut s c ≤ p.balance s.tokenOut ∧
      p' = { p with balance := update2 p.balance s.tokenIn (p.balance s.tokenIn + amountIn s c)
                                       s.tokenOut (p.balance s.tokenOut - amountOut s c) } := by
  unfold step at h
  split at h
  · rename_i hv
    split at h
    · rename_i c hc
      unfold settle at h
      split at h
      · cases h; exact ⟨hv, c, hc, ‹_›, rfl⟩
      · cases h
    · cases h
  · cases h

/-- Every swap keeps the pool's token count. -/
theorem step_n {impl : Impl} {m : PoolMath} {p p' : Pool} {s : Swap}
    (h : step impl m p s = some p') : p'.n = p.n := by
  obtain ⟨-, c, -, -, rfl⟩ := step_some h; rfl

/-- The fee-net amount in, scaled, is at most the amount in scaled. -/
theorem netInDown_le (p : Pool) (s : Swap) : netInDown p s * ONE ≤ s.amount * p.rate s.tokenIn := by
  have h1 := Nat.div_mul_le_self (s.amount * (ONE - p.fee) * p.rate s.tokenIn) (ONE * ONE)
  have h2 : s.amount * (ONE - p.fee) * p.rate s.tokenIn ≤ s.amount * ONE * p.rate s.tokenIn :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have h3 : netInDown p s * ONE * ONE ≤ s.amount * p.rate s.tokenIn * ONE := by
    unfold netInDown
    calc _ = s.amount * (ONE - p.fee) * p.rate s.tokenIn / (ONE * ONE) * (ONE * ONE) :=
          Nat.mul_assoc _ _ _
      _ ≤ s.amount * ONE * p.rate s.tokenIn := Nat.le_trans h1 h2
      _ = s.amount * p.rate s.tokenIn * ONE := Nat.mul_right_comm _ _ _
  exact Nat.le_of_mul_le_mul_right h3 one_pos

/-- The scaled balances of a pool with new raw balances `b`, as the library reads them. -/
theorem scaled_with (p : Pool) (b : Nat → Nat) :
    scaledBalances { p with balance := b } = fun k => ProofForgeFin.scaleDown ONE (b k) (p.rate k) :=
  rfl

section Requirements

variable {impl : Impl}

/-- REQ-BATCH-KEEPS-VALUE follows from REQ-SWAP-KEEPS-VALUE, for every implementation. -/
theorem batch_keeps_value (h : SwapKeepsValue impl) : BatchKeepsValue impl := by
  intro m p ss p' hw hr
  rw [run_eq] at hr
  exact ProofForgeFin.Seq.runAll_rel_of_inv (R := fun x y => value m x ≤ value m y)
    (I := fun q => q.n = p.n) (fun _ => Nat.le_refl _) (fun _ _ _ h1 h2 => Nat.le_trans h1 h2)
    (fun _ _ _ hn hs => (step_n hs).trans hn)
    (fun q s q' hn hs => h m q s q' (hn ▸ hw) hs) rfl hr

/-- A given-in swap keeps the value when the implementation pays at most what the math prices the
fee-net amount in (REQ-GIVEN-IN-PAYS-AT-MOST), for every well-behaved math with monotone prices. -/
theorem given_in_keeps_value (hIn : GivenInPaysAtMost impl) {m : PoolMath} {p p' : Pool} {s : Swap}
    (hw : WellBehaved m p.n) (hpm : PriceMonotone m) (hk : s.kind = .givenIn)
    (h : step impl m p s = some p') : value m p ≤ value m p' := by
  obtain ⟨hv, c, hc, hle, rfl⟩ := step_some h
  have eIn : amountIn s c = s.amount := by simp [amountIn, hk]
  have eOut : amountOut s c = c := by simp [amountOut, hk]
  rw [eOut] at hle
  rw [eIn, eOut]
  have hy := hIn m p s c hpm hk hv hc
  unfold value
  rw [scaled_with, update2_eq]
  exact ((wellBehaved_iff m p.n).1 hw).scaled_swapIn one_pos p.balance p.rate hv.1 hv.2.1 hv.2.2
    (netInDown_le p s) (by rw [Nat.mul_comm _ ONE]; exact hy) hle

/-- A given-out swap keeps the value when the implementation charges at least what the math prices
the exact amount out rounded up (REQ-GIVEN-OUT-CHARGES-AT-LEAST) and that amount is below the
pool's scaled balance, for every well-behaved math with monotone prices. -/
theorem given_out_keeps_value (hOut : GivenOutChargesAtLeast impl) {m : PoolMath} {p p' : Pool}
    {s : Swap} (hw : WellBehaved m p.n) (hpm : PriceMonotone m) (hk : s.kind = .givenOut)
    (hb : scaleUp s.amount (p.rate s.tokenOut) < scaledBalances p s.tokenOut)
    (h : step impl m p s = some p') : value m p ≤ value m p' := by
  obtain ⟨hv, c, hc, hle, rfl⟩ := step_some h
  have eIn : amountIn s c = c := by simp [amountIn, hk]
  have eOut : amountOut s c = s.amount := by simp [amountOut, hk]
  rw [eOut] at hle
  rw [eIn, eOut]
  have hch := hOut m p s c hpm hk hv hc
  have hgain : outPrice m p s * ONE ≤ c * p.rate s.tokenIn := by
    have h1 : c * (ONE - p.fee) * p.rate s.tokenIn ≤ c * ONE * p.rate s.tokenIn :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h2 : outPrice m p s * ONE * ONE ≤ c * p.rate s.tokenIn * ONE := by
      calc outPrice m p s * ONE * ONE = ONE * ONE * outPrice m p s := by ac_rfl
        _ ≤ c * ONE * p.rate s.tokenIn := Nat.le_trans hch h1
        _ = c * p.rate s.tokenIn * ONE := Nat.mul_right_comm _ _ _
    exact Nat.le_of_mul_le_mul_right h2 one_pos
  have hloss : s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE := by
    rw [scaleUp_eq]; exact ProofForgeFin.le_mulUp_mul ONE _ _ one_pos
  unfold value
  rw [scaled_with, update2_eq]
  exact ((wellBehaved_iff m p.n).1 hw).scaled_swapOut one_pos p.balance p.rate hv.1 hv.2.1 hv.2.2
    hb hloss hgain hle

end Requirements

end ProofForgeFinDemo.DeFi.Balancer
