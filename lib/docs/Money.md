# ProofForgeFin.Money: money, rounding modes and allocation

`ProofForgeFin.Money` (area root `lib/ProofForgeFin/Money.lean`, modules under
`lib/ProofForgeFin/Money/`) states and proves the arithmetic of money code in minor units:
rounding modes on integer fractions, allocation of an amount by ratios and equal splits of
signed amounts, currencies with different exponents, percentage fees, currency conversion,
interest and amortization. It depends on the Lean core library and on `ProofForgeFin.Rounding`
and `ProofForgeFin.FixedPoint` (`ceilDiv`, `mulDiv`, `mulDivUp`, their bounds), and
`ProofForgeFin.Ledger` (`equalSplit`).

The area has 299 theorems and 69 definitions in eight modules (counted in the source; the
audit also counts generated constants), plus four demonstrations (32 theorems) that re-prove
requirements and lemmas of tasks in `realworld/tasks/` and `tasks/`. Every definition,
structure field, constructor and theorem of the library has a doc string; the demonstrations
keep the definitions they copy from the tasks as they are.

## Conventions

* Amounts are `Int` numbers of minor units (negative for a debit, a refund or an income) unless
  a module says `Nat` (fees, conversion and compound interest of customer amounts). Ratios are
  `Nat`. Denominators are positive and taken as hypotheses (`0 < d`).
* A rounded result `q` of the fraction `n / d` is measured by its error `q * d - n` (the result
  minus the exact value, in units of `1 / d`). Every bound is linear in `q * d`, so `omega`
  combines the library's statements with the facts of a proof.
* An allocation of `a` by ratios `rs` with `S = rs.sum > 0` is measured by the excess
  `x * S - a * r` of each share `x` (the share minus the exact share `a * r / S`, in units of
  `1 / S`); the predicates are the ones the task specifications state.
* Negative amounts. The floor convention (Euclidean division, remainders in `[0, d)`) gives
  every party the floor of its exact share and hands out nonnegative leftover units; it is the
  convention of the definitions here. The symmetric convention (truncating division, units of
  `-1` for a negative amount, as in go-money) is `symAlloc f`: allocate `-a` and negate.
  `symAlloc_of_forall_nonneg` transfers every requirement that negation preserves from the
  nonnegative amounts to all amounts.

## `ProofForgeFin.Money.Round`: rounding modes

`RoundingMode` has nine modes and `rdiv m n d` rounds `n / d` with mode `m`:

| mode | Lean | characterization (`q = rdiv m n d`) | real code |
|------|------|--------------------------------------|-----------|
| `floor` | `n / d` | `q * d ≤ n < q * d + d` (`ediv_eq_iff`) | `FLOOR`, `Int.fdiv` |
| `ceil` | `divCeil` | `q * d - d < n ≤ q * d` (`divCeil_eq_iff`) | `CEILING` |
| `towardZero` | | floor for `0 ≤ n`, ceil for `n < 0` | `ROUND_DOWN`, Go and C integer division, `Int.tdiv` |
| `awayFromZero` | | ceil for `0 ≤ n`, floor for `n < 0` | `ROUND_UP` |
| `halfCeil` | `divHalfCeil` | `-d < 2 * (q * d - n) ≤ d` (`divHalfCeil_eq_iff`) | JavaScript `Math.round`, `ROUND_HALF_POSITIVE_INFINITY` |
| `halfFloor` | `divHalfFloor` | `-d ≤ 2 * (q * d - n) < d` (`divHalfFloor_eq_iff`) | `ROUND_HALF_NEGATIVE_INFINITY` |
| `halfUp` | | halfCeil for `0 ≤ n`, halfFloor for `n < 0` | `HALF_UP`, `ROUND_HALF_UP` |
| `halfDown` | | halfFloor for `0 ≤ n`, halfCeil for `n < 0` | `HALF_DOWN`, `ROUND_HALF_DOWN` |
| `halfEven` | `divHalfEven` | `-d ≤ 2 * (q * d - n) ≤ d` and `q` even on a tie (`divHalfEven_eq_iff`) | `HALF_EVEN`, banker's rounding |

Main statements (for `0 < d`):

* `ediv_le_rdiv_le_divCeil`: `n / d ≤ rdiv m n d ≤ divCeil n d`; `divCeil_le_ediv_add_one`;
  `divCeil_eq_ediv_iff`: `divCeil n d = n / d ↔ n % d = 0`; `rdiv_eq_ediv_or_divCeil`.
* `rdiv_bounds`: `-d < rdiv m n d * d - n < d` (every mode is within one unit).
* Nearest-integer modes (`m.isHalf = true`): `rdiv_half_bounds`
  (`-d ≤ 2 * (q * d - n) ≤ d`), `rdiv_half_nearest` (no integer `z` has a smaller
  `|z * d - n|`), `divHalfFloor_le_rdiv_le_divHalfCeil`, `rdiv_half_eq_of_not_tie`
  (`2 * (n % d) ≠ d` makes all half modes agree), `divHalfFloor_eq_divHalfCeil_iff`.
* `rdiv_mono` (monotone in the numerator), `rdiv_mul_mul` (`rdiv m (n * k) (d * k) = rdiv m n d`),
  `rdiv_le_rdiv_of_mul_le` (`n * d' ≤ n' * d → rdiv m n d ≤ rdiv m n' d'`: every mode respects the
  order of fractions with different denominators).
* `rdiv_neg`: `rdiv m (-n) d = -rdiv m.neg n d` (floor and ceil swap, halfCeil and halfFloor
  swap, the other modes are odd).
* `rdiv_mul_self` (`rdiv m (k * d) d = k`), `rdiv_zero_left`, `rdiv_of_emod_eq_zero`,
  `rdiv_nonneg`, `rdiv_nonpos`, `rdiv_add_mul` (floor, ceil, halfCeil, halfFloor commute with
  adding `k * d`).
* Magnitudes: `natAbs_towardZero_le`, `natAbs_le_awayFromZero`, `natAbs_towardZero_mul_le`
  (`|rdiv .towardZero n d| * d ≤ |n|`).
* Sums: `sum_ediv_le_ediv_sum` (`Σ floor ≤ floor Σ`), `ediv_sum_lt_sum_ediv_add_length`
  (`floor Σ < Σ floor + length`), `divCeil_sum_le_sum_divCeil`,
  `sum_divCeil_lt_divCeil_sum_add_length`, `rdiv_sum_sub_sum_rdiv` (in every mode
  `|rdiv m (Σ n) d - Σ rdiv m n d| ≤ length`), `rdiv_sum_sub_sum_rdiv_half` (for the half modes
  `|2 * (rdiv m (Σ n) d - Σ rdiv m n d)| ≤ length + 1`), and the general `sum_error_bounds`.
* Bridges: `rdiv_floor_natCast`, `rdiv_ceil_natCast` (to `Nat` division and `ceilDiv`),
  `rdiv_towardZero_eq_tdiv`, `rdiv_floor_eq_fdiv`; the cancellation lemmas
  `le_of_mul_lt_mul_add`, `eq_of_mul_lt_mul_add` used throughout.

## `ProofForgeFin.Money.Allocation`: requirements and remainder to the first parties

Requirements on one input and output: `OneShareEachOn`, `ConservesOn`, `WithinOneUnitOn`
(`-S < excess < S`), `AtMostOneUnitOn` (`-S ≤ excess ≤ S`), `ZeroRatioOn`, `SignOn`,
`LargestRemainderOn`, `MonotoneOn`. They are word for word the predicates of
`rw-moneyphp-allocate` and `rw-spliit-balances`, so a task proof can close a requirement with a
library theorem.

* `within_iff_floor_or_ceil`: a share is less than one unit from exact exactly when it is the
  floor or the ceiling of `a * r / S`; `excess_bounds_of_floor_or_succ`: the floor or the floor
  plus one is within `(-S, S]`.
* Implications: `zeroRatioOn_of_withinOneUnitOn`, `signOn_of_withinOneUnitOn`,
  `atMostOneUnitOn_of_withinOneUnitOn`, `monotoneOn_of_largestRemainderOn` (within one unit and
  the largest-remainder rule give monotonicity in the ratios: a smaller ratio never receives
  more for a nonnegative amount, nor less for a nonpositive one), `le_add_one_of_le_ratio`.
* Negation: `excess_neg`, `conservesOn_neg`, `withinOneUnitOn_neg`, `atMostOneUnitOn_neg`,
  `zeroRatioOn_neg`, `signOn_neg`, `largestRemainderOn_neg`; `symAlloc`, `symAlloc_neg`,
  `symAlloc_of_forall_nonneg`.
* Floors: `floorShare`, `floors`, `leftover`; `leftover_mul` (`leftover * S` is the sum of the
  remainders), `leftover_nonneg`, `leftover_le_countP` (at most the number of nonzero ratios),
  `leftover_lt_length`, `sum_floors_le`.
* `allocFirst a rs` (floors, then one leftover unit each to the first parties):
  `allocFirst_conserves`, `getElem_allocFirst`, `allocFirst_floor_or_succ`,
  `allocFirst_excess_bounds` (`-S < excess ≤ S`), `allocFirst_atMostOneUnit`, `allocFirst_sign`
  (nonnegative amounts), and under the symmetric convention `symAlloc_allocFirst_conserves`,
  `symAlloc_allocFirst_atMostOneUnit`, `symAlloc_allocFirst_sign`. Natural-number form:
  `getElem_allocFirst_natCast`, `leftover_toNat_natCast`, `sum_floors_natCast`.
  `allocFirst_example`: `allocFirst 5 [0, 7, 3] = [1, 3, 1]` (moneyphp issue 436: the zero ratio
  is paid).
* `allocFirstNonzero a rs` (the same, skipping zero ratios): `allocFirstNonzero_conserves`,
  `allocFirstNonzero_zeroRatio`, `allocFirstNonzero_floor_or_succ`,
  `allocFirstNonzero_excess_bounds`.

Models: moneyphp `Money::allocate` in 3.0.9 (`allocFirst`, the port
`rw-moneyphp-allocate/attacks/buggy_original.lean` is `addFirst` over the floors), moneyphp 3.1.3
to 3.2.0 (`allocFirstNonzero`, the port `attacks/v3_2_0_skip_zero_ratio.lean`), go-money
`Allocate` (`symAlloc allocFirst`, by the argument in the limits below), the weighted payout of
`tasks/payouts-weighted-*` (`weightedShare` is `allocFirst` on a natural-number amount).

## `ProofForgeFin.Money.Hamilton`: the largest-remainder method

`largestRemainder a rs`: floors, then one leftover unit at a time to the party furthest below
exact, the first on ties. For `0 < rs.sum` and every amount:

* `largestRemainder_conserves`, `length_largestRemainder`, `largestRemainder_within`
  (`WithinOneUnitOn`), `largestRemainder_zeroRatio`, `largestRemainder_sign`,
  `largestRemainder_largestRemainder` (`LargestRemainderOn`), `largestRemainder_monotone`
  (`MonotoneOn`), `largestRemainder_floor_or_ceil`.
* Symmetric convention: `symAlloc_largestRemainder_conserves`, `_within`,
  `_largestRemainder`, `_oneShareEach`.
* `largestRemainder_example`: `[0, 4, 1]` for moneyphp issue 436;
  `largestRemainder_example_thirds`: `largestRemainder 100 [1, 1, 1] = [34, 33, 33]` (Spliit
  issue 374, where rounding each share separately gave 99).

The proof is the loop invariant `Hamilton.Inv` (every share within one unit of exact, a share
above exact no further from exact than a share below it plus one unit, total shortfall equal to
the units left), generalized from the reference solution of `rw-moneyphp-allocate`.

Models: the requirements of `rw-moneyphp-allocate` and `rw-spliit-balances`, and the selection
rule of moneyphp's `Money::allocate` from 3.2.1 on (largest fractional parts first); the
equality with moneyphp's sort-based loop is not proved.

## `ProofForgeFin.Money.Split`: equal splits of signed amounts

* `splitEven a n` (floor convention: `a / n` each, one more for the first `a % n` parts):
  `sum_splitEven`, `length_splitEven`, `mem_splitEven`, `splitEven_within`
  (`-n < x * n - a < n`), `splitEven_sign`, `splitEven_le_add_one`, `splitEven_antitone`,
  `splitEven_natCast` (on a natural-number amount it is `Ledger.equalSplit`, which this
  generalizes to signed amounts).
* `splitSym a n` (symmetric convention): `splitSym_eq_tdiv` proves it equal to go-money's
  `Money.Split` from 1.0.6 on (`a.tdiv n` for every part and `|a.tmod n|` units of the sign of
  `a` to the first parts); `sum_splitSym`, `length_splitSym`, `splitSym_within`,
  `splitSym_sign`, `splitSym_le_add_one`, `splitSym_neg`, `splitSym_example`
  (`splitSym (-101) 4 = [-26, -25, -25, -25]`, the input on which go-money 1.0.3 panicked).

## `ProofForgeFin.Money.Currency`: currencies and exponents

`Currency` (code, exponent), `Money` (currency, signed minor units), `Money.add?` (defined only
within one currency: `isSome_add?_iff`, `add?_comm`, `add?_assoc`), `Money.ValueLe` (comparison
across exponents by cross-multiplication, reflexive and transitive).

`rescale m e e' a` converts minor units at exponent `e` to exponent `e'`:

* `rescale_eq_rdiv`: `rescale m e e' a = rdiv m (a * 10 ^ e') (10 ^ e)` for every pair of
  exponents, so every `Round` lemma applies; `rescale_bounds`
  (`-10^e < rescale * 10^e - a * 10^e' < 10^e`), `rescale_mono`, `rescale_neg`.
* `rescale_rescale_of_le` (to more places and back is the identity), `rescale_floor_rescale`
  (to fewer places rounded down and back: `a - 10^(e - e') < back ≤ a`),
  `rescale_rescale_bounds` (any modes: `|back - a| < 10^(e - e')`), `Money.rescaleTo_bounds`.
* `rescale_example`: 1.0050 dollars at four places is 1.00 dollars by banker's rounding and 1.01
  dollars half up.

## `ProofForgeFin.Money.Fee`: percentage fees

`feeDown scale r a = a * r / scale`, `feeUp scale r a = ceilDiv (a * r) scale`,
`bpsFee bps a = feeDown 10000 bps a`.

* `feeDown_spec`, `feeUp_spec`, `feeDown_le_feeUp`, `feeUp_le_feeDown_add_one`, `feeDown_le`,
  `feeUp_le`, `feeDown_add_net`, `feeUp_add_net` (fee plus net equals gross for `r ≤ scale`).
* `net_feeDown`: `a - feeDown scale r a = ceilDiv (a * (scale - r)) scale`; `net_feeUp`:
  `a - feeUp scale r a = a * (scale - r) / scale`; hence `net_feeDown_mono`, `net_feeUp_mono`.
* `feeDown_add_le`, `le_feeDown_add`, `feeUp_add_le`, `le_feeUp_add` (splitting a payment
  changes the fee by at most one unit), `feeDown_le_add` (the fee rises by at most the rise of
  the amount).
* `clampFee lo hi f a = min a (min hi (max lo f))`: `clampFee_le_amount`, `clampFee_le_cap`,
  `le_clampFee`, `clampFee_of_le`, `clampFee_mono`, `clampFee_add_net`,
  `net_clampFeeDown_mono` (the net after a clamped percentage fee is monotone in the gross).
* Gross-up: `le_net_feeUp_iff` (`n ≤ a - feeUp scale r a ↔ grossUpFeeUp scale r n ≤ a`),
  `le_net_feeDown_iff` (the same with `grossUpFeeDown`).

Models: `tasks/payouts-fee-*` (`feeOf bps amount = bpsFee bps amount` by definition), card and
platform fees with a minimum and a cap.

## `ProofForgeFin.Money.FX`: currency conversion

`fxDown rn rd a = a * rn / rd` (paid out), `fxUp rn rd a = ceilDiv (a * rn) rd` (charged),
`fxCost rn rd b = fxUp rd rn b`.

* `fxDown_spec`, `fxUp_spec`, `fxDown_le_fxUp`, `fxDown_mono`, `fxUp_mono`, `fxDown_anti`.
* `le_fxDown_iff`: `b ≤ fxDown rn rd a ↔ fxCost rn rd b ≤ a` (the cost of `b` is the least
  amount that buys it); `le_fxDown_fxCost`.
* Round trips: `fxDown_fxDown_inv_le` (`fxDown rd rn (fxDown rn rd a) ≤ a`),
  `lt_fxDown_fxDown_inv` (`a * rn < back * rn + rn + rd`: the loss is below `1 + rd / rn`).
* No arbitrage: `fxDown_round_trip_le` (buy at `bn / bd`, sell at `sn / sd`,
  `bn * sn ≤ bd * sd → fxDown sn sd (fxDown bn bd a) ≤ a`), `fxChain_mul_le` and `fxChain_le`
  (a cycle of conversions whose rates multiply to at most one never gains).
* `fxMinor` (minor units across exponents) with `fxMinor_spec`; `fxInt` (signed amounts in any
  mode) with `fxInt_bounds`, `natAbs_fxInt_towardZero_le` (rounding toward zero pays out at most
  the exact magnitude for credits and debits), `fxInt_floor_natCast`.

## `ProofForgeFin.Money.Interest`: interest and amortization

`g = rd + rn` is the growth factor `1 + rn / rd` scaled by `rd`.

* `simpleInterest rn rd P t = P * rn * t / rd`: `simpleInterest_spec`, `simpleInterest_mono`,
  `simpleInterest_add_le`, `le_simpleInterest_add`.
* `compound rn rd n P` (interest `C * rn / rd` added every period) and `compoundUp` (rounded
  up): `compound_mul_le` (`C * rd^n ≤ P * g^n`), `le_compound`
  (`rn * (P * g^n) + (rd - 1) * rd^n ≤ rn * (C * rd^n) + (rd - 1) * g^n`: the loss is below
  `Σ_{j<n} (1 + rn/rd)^j` units), `le_compoundUp_mul`, `compoundUp_le` (the same two bounds for
  rounding up), `compound_le_compoundUp`, `compound_mono` (principal and rate),
  `compoundUp_mono`, `compound_mono_time`, `add_mul_simple_le_compound`
  (`P + n * (P * rn / rd) ≤ compound rn rd n P`).
* Amortization on signed balances with any interest function `i` and payment `p`:
  `balanceAfter`, `interestPaid`, `finalPayment`, `payments`; `finalPayment_closes` (the final
  payment leaves a zero balance), `balanceAfter_add_mul` (balance plus payments is principal
  plus interest), `sum_payments` (`(payments i p n B).sum = B + interestPaid i p n B`),
  `length_payments`.
* With interest rounded down (`interestDown rn rd b = b * rn / rd`):
  `balanceAfter_interestDown_le` (the rounded balance is at most the exact balance),
  `finalPayment_le` (if `rn * B * g^n ≤ p * rd * (g^n - rd^n)`, the final payment is at most
  `p`), `annuityPayment` (the exact annuity payment rounded up) and
  `finalPayment_annuityPayment_le`; `annuity_example` (10000 at 1% a month over 12 months: payment
  889, final payment 878).

## Demonstrations

`lib/ProofForgeFinDemo/Money/` (root `lib/ProofForgeFinDemo/Money.lean`). Each file copies the
task definitions it needs, with their doc strings, from the task files named in its header; no
task file is imported or modified. Sizes are lines of Lean code without comments, doc strings or
blank lines; the demonstration counts only its own implementation, bridging lemmas and proofs,
not the copied definitions.

| demonstration | task | what is re-proved | reference | with the library |
|---------------|------|-------------------|-----------|------------------|
| `Allocation.lean` | `rw-moneyphp-allocate` (and `rw-spliit-balances`, same specification) | all eight requirements for a largest-remainder allocation | `reference/SolutionA.lean`: 321 lines, 31 theorems | 39 lines, 10 theorems; each requirement is one library theorem |
| `EqualSplit.lean` | `rw-gomoney-split` | all six requirements, for a port of go-money's fixed `Money.Split` (the reference proves them for the Euclidean split) | `reference/SolutionA.lean`: 93 lines, 9 theorems | 38 lines, 8 theorems, through `splitSym_eq_tdiv` |
| `WeightedPayout.lean` | `payouts-weighted-b1` | `leftover_lt`, `sum_weighted`, `weighted_bound` | 111 lines in 10 lemmas | 60 lines, of which 25 identify the task's `natSum`, `sumRange`, `leftover` and `weightedShare` with `List.sum` and `allocFirst` |
| `FeePayout.lean` | `payouts-fee-b1` | `fee_le`, `split_sum` | 12 lines | 10 lines; the file adds `net_eq`, `net_mono`, `fee_split`, which the reference does not state |

## Audit

`lib/Audit.lean` covers the area through `ProofForgeFin.lean` and `ProofForgeFinDemo.lean`. In the
pinned image after this work:

```
axioms used: [Classical.choice, Quot.sound, propext]
audit: 2493 constants, 847 theorems, 0 violations
```

`#print axioms` for main results of the area (run on a scratch file; `Audit.lean` is unchanged):

```
'ProofForgeFin.Money.divHalfEven_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.rdiv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.rdiv_half_nearest' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.rdiv_le_rdiv_of_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.rdiv_sum_sub_sum_rdiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.monotoneOn_of_largestRemainderOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.largestRemainder_largestRemainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.splitSym_eq_tdiv' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Money.rescale_eq_rdiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.net_clampFeeDown_mono' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Money.fxChain_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.le_compound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Money.finalPayment_annuityPayment_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFinDemo.Money.Allocation.req_largest_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFinDemo.Money.EqualSplit.req_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Several ring identities in the proofs are closed by `grind`, whose proofs use only these three
axioms.

## Limits

* Fractions are pairs of integers with a positive denominator; there is no rational type and no
  real-valued exact interest. Exact values appear only cross-multiplied.
* `halfOdd` (`ROUND_HALF_ODD` of moneyphp) and rounding to a multiple other than one unit (cash
  rounding to 5 cents) are not defined; `rdiv_add_mul` is not proved for `halfEven` (it holds
  only for even shifts) or for the sign-dependent modes.
* Floating point is not modeled. The ports of moneyphp and Spliit in the task directories
  compute exactly, and so does this library.
* `symAlloc allocFirst` is the semantics of go-money's `Allocate` (truncating division is odd,
  so its result on a negative amount is the negation of its result on the absolute amount); the
  equality with a port of the Go code is proved for `Split` (`splitSym_eq_tdiv`) but not for
  `Allocate`. go-money also returns zeros when the ratios sum to zero; the allocation theorems
  assume a positive sum.
* `largestRemainder` is defined by the greedy loop; its equality with a sort-based
  implementation (moneyphp sorts the fractional parts) is not proved.
* Allocation methods are on lists of `Nat` ratios; weights with fractional parts must be scaled
  to integers first.
* Fees, conversion and compound interest are on `Nat` amounts; signed conversion is `fxInt`.
  Compound interest is per-period with a constant rate; day-count conventions, variable rates
  and amortization schedules with rounding of the payment itself other than the fixed `p` are
  not covered. `finalPayment_le` gives an upper bound on the final payment; no lower bound
  (the final payment can be below `p`) and no nonnegativity of the balances is proved.
* The demonstrations re-prove requirements over copied definitions; they are not wired into the
  task projects or the judge (see the scope section of `lib/README.md`).
