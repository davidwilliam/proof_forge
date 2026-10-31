# ProofForgeFin

ProofForgeFin is a Lean 4 library of proved facts for specifications and proofs about money code:
rounding and fixed-point arithmetic on `Nat`, share accounting, runs of operations with invariants
over every reachable state, and conservation over accounts. It depends on the Lean core library
only (no Mathlib), builds with the pinned toolchain (Lean v4.35.0) in the judge image, and every
theorem is proved with no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

The task specifications and reference solutions in this repository re-derive the same
foundations task by task: floor and ceiling bounds, cross-multiplied share value, `run` over a
list of operations with an induction, sums over account lists. The library states each of them
once, for every scale, state type and operation type, so a specification can name a library
definition and a proof can cite a library theorem.

The library has 1,724 theorems and 445 definitions in 70 files under fourteen top-level modules
(`Rounding`, `FixedPoint`, `Word`, `Shares`, `Seq`, `Ledger`, `Trading`, `Machine`, `Evm`, `Money`,
`DeFi`, `Tactic`, `Sums`, `Accrual`) and the two generated ones (`Harvested`, `Salvaged`; source
declarations counted with comments excluded, as `web/tests/contribution.test.ts` recounts them),
plus demonstrations (329 theorems in 32 files)
that re-prove lemmas of task reference solutions with it and exercise the modules. Every definition, structure
field and constructor has a doc string; the build enables `linter.missingDocs` for the library and
emits no warning.

## Contents

Statements below are paraphrased; the Lean names are exact. `a / b` is `Nat` division (rounded
down); every bound is stated by cross-multiplication, so `q * b ≤ a` reads "`q` is at most the
exact quotient".

### `ProofForgeFin.Rounding`: floor and ceiling division

`ceilDiv a b := (a + b - 1) / b`.

* `floor_spec`: for `0 < b`, `a / b * b ≤ a ∧ a < (a / b + 1) * b`; `div_eq_of_bounds` (uniqueness).
* `ceilDiv_spec`: for `0 < b`, `a ≤ ceilDiv a b * b ∧ ceilDiv a b * b < a + b`;
  `ceilDiv_eq_of_bounds`, `ceilDiv_le_iff`, `lt_ceilDiv_iff`.
* `div_le_ceilDiv`, `ceilDiv_le_div_add_one`, `ceilDiv_eq_div_iff` (equal exactly when `a % b = 0`),
  `ceilDiv_eq_div_add_one`.
* The forms deployed code uses are `ceilDiv`: `ceilDiv_eq_add_pred` (`(a + (b - 1)) / b`, Balancer
  `scaleUp`) and `ceilDiv_eq_ite` (`if a = 0 then 0 else (a - 1) / b + 1`, Balancer `mulUp`, `divUp`).
* Monotonicity: `div_mono_left`, `div_anti_right`, `ceilDiv_mono_left`, `ceilDiv_anti_right`; order of
  rationals: `div_le_div_of_mul_le`, `ceilDiv_le_ceilDiv_of_mul_le` (`a * d ≤ c * b` gives
  `a / b ≤ c / d` and the same for `ceilDiv`).
* `mul_div_le_of_le`: `t ≤ s → t * a / s ≤ a` (a pro-rata payout never exceeds the pot).
* Sums of rounded parts: `div_add_div_le`, `div_add_le_div_add_div_add_one`, `sum_div_mul_le`,
  `sum_lt_sum_div_add_length_mul` (rounding each of `n` parts down loses less than `n` units),
  `sum_div_le_div_sum`.
* `le_add_div_of_mul_le`: `0 < D → X * D ≤ Y * D + P → X ≤ Y + P / D` (from a scaled potential to
  an amount).

Recurs in: `rw-hundred-vault/reference/SolutionA.lean` (`floor_spec`, `ceil_spec`,
`mul_div_le_self`), `rw-balancer-upscale/reference/SolutionA.lean` (`scaleUp_ge`, `scaleUp_lt`,
`mulUp_eq`, `divUp_spec`), `rw-cetus-shlw/spec/ClmmMath/Lemmas.lean` (`divRound_up`,
`divRound_down`), `rw-compound-comp/reference/SolutionA.lean` (`div_bound`), the fee and share
arithmetic of `tasks/payouts-*`.

### `ProofForgeFin.FixedPoint`: fixed point at any scale

`mulDiv a n d := a * n / d`, `mulDivUp a n d := ceilDiv (a * n) d`; `mulDown one a b`, `mulUp one a b`
(`a * b / one`), `divDown one a b`, `divUp one a b` (`a * one / b`); `scaleDown`, `scaleUp`,
`unscaleDown`, `unscaleUp` (Balancer's `_upscale` and `_downscale*`); `convertDecimalsDown`,
`convertDecimalsUp` (an amount with `d` decimals as one with `e` decimals). The scale `one` is a
parameter: `10^18`, `10^36` and `2^64` are instances, and the lemmas need only `0 < one`.

* `mulDown_spec`: `mulDown one a b * one ≤ a * b ∧ a * b < (mulDown one a b + 1) * one` (within one
  unit below the exact product); `mulUp_spec`: `a * b ≤ mulUp one a b * one ∧ mulUp one a b * one < a * b + one`.
* `divDown_spec`, `divUp_spec`: the same for `a * one / b`, for `0 < b`.
* `mulDown_le_mulUp`, `mulUp_le_mulDown_add_one`, `divDown_le_divUp`, `divUp_le_divDown_add_one`,
  `mulDivUp_eq_mulDiv_iff`.
* Monotonicity in each argument (`mulDown_mono`, `mulUp_mono`, `divDown_mono_left`,
  `divDown_anti_right`, `divUp_mono_left`, `divUp_anti_right`), commutativity, identities
  (`mulDown_one`, `divUp_one`, ...).
* Balancer's formulas are these operations: `mulUp_eq_ite`, `mulUp_eq_add_pred`, `divUp_eq_ite`.
* Round trips: `divDown_mulDown_le` (`divDown one (mulDown one a b) b ≤ a`), `mulDown_divDown_le`,
  `le_divUp_mulUp`, `le_mulUp_divUp`: converting and converting back in the direction that favours
  the holder of the funds never gains a unit.
* Two products: `mulDown_mulDown_le`, `le_mulUp_mulUp` (bounds at scale `one * one`).
* `convertDecimals_spec`, `convertDecimalsDown_of_le` (to more decimals the conversion is exact).

Recurs in: `rw-balancer-upscale/reference/SolutionA.lean` (`FixedPoint` port, `le_div_one_one`,
`div_one_one_le`), `rw-balancer-upscale/spec/BalancerSwap/Spec.lean` (`scaleDown`, `scaleUp`),
`rw-euler-donate/spec/EulerLending/Spec.lean` (1e18 liquidation terms),
`rw-compound-comp/spec/CompRewards/Spec.lean` (`creditFor`, `accrueSide` at `doubleScale`).

### `ProofForgeFin.Word`: machine words

* `mul_two_pow_lt_iff`: for `k ≤ w`, `a * 2^k < 2^w ↔ a < 2^(w - k)`. For `w = 256`, `k = 64` this is the
  overflow condition a correct `checked_shlw` must test (`n < 2^192`).
* `toNat_shiftLeft_of_lt`, `toNat_shiftLeft_of_lt_two_pow`, `toNat_ushiftRight`, `toNat_mul_of_lt`,
  `toNat_add_of_lt`, `toNat_sub_of_le`, `toNat_setWidth_of_le`, `toNat_ofNat_of_lt`: when a `BitVec`
  operation is exact.
* `toNat_fullMul`: the product of two `w`-bit words widened to `2w` bits is exact (`full_mul`).

Recurs in: `rw-cetus-shlw/spec/ClmmMath/Lemmas.lean` (`toNat_fullMul`, `toNat_absDiff`) and
`rw-cetus-shlw/reference/SolutionA.lean` (`flag_false_iff`, `value_of_flag`).

### `ProofForgeFin.Shares`: share accounting

`Pool` (`assets`, `supply`); `ValueNotBelow p q := p.assets * q.supply ≤ q.assets * p.supply`; the
ERC-4626 conversions rounded in the vault's favour: `previewDeposit` (down), `previewMint` (up),
`previewRedeem` (down), `previewWithdraw` (up); `Pool.add`, `Pool.sub`; a vault model `Op` and
`step` (deposit, mint, redeem, withdraw, donate; refused calls leave the books unchanged).

* Exactness: `previewDeposit_spec`, `previewMint_spec`, `previewRedeem_spec`, `previewWithdraw_spec`.
* `valueNotBelow_trans`: `ValueNotBelow p q → ValueNotBelow q r → 0 < q.supply → ValueNotBelow p r`.
* `add_value`: `t * assets ≤ x * supply → ValueNotBelow p (p.add x t)`; `sub_value`:
  `y * supply ≤ t * assets → ValueNotBelow p (p.sub y t)`. Every conversion below is an instance.
* Share value does not fall when rounding favours the vault: `deposit_value`, `mint_value`,
  `redeem_value`, `withdraw_value`, `donate_value`.
* `previewRedeem_le_of_value`: if value did not fall, redeeming the same shares later pays at least
  as much.
* Round trips never return more than was put in: `deposit_redeem_le`, `mint_redeem_le`,
  `redeem_deposit_le`, `withdraw_mint_ge`.
* `previewDeposit_eq_zero_iff`: a deposit mints nothing exactly when `x * supply < assets` (the
  first-depositor inflation condition); `previewRedeem_le_assets`, `previewWithdraw_le_supply`,
  monotonicity, `previewDeposit_le_previewWithdraw`, `previewRedeem_le_previewMint`.
* `step_value`: from a vault with outstanding shares no operation lowers share value;
  `run_value`: share value never falls over any sequence of operations along which shares stay
  outstanding.

Recurs in: `rw-hundred-vault/spec/ShareVault/Spec.lean` (`ValueNotBelow`, the rounding
requirements, `ShareValueNeverFalls`) and its reference solution (`value_trans`, `exec_value`,
`run_value`); `rw-balancer-upscale` (pool value under a batch).

### `ProofForgeFin.Seq`: sequences of operations

`run step s ops` (state after the operations), `trace step s ops` (every state passed through),
`Preserves step I`, `accum next f g ops` (a total computed from the operations with a ghost state
`g`), `skip` (a partial step whose refusals leave the state unchanged), `runAll` (an atomic run of a
partial step), `Reachable step init`.

* Runs: `run_append`, `run_snoc`, `run_eq_foldl`, `length_trace`, `self_mem_trace`, `run_mem_trace`,
  `run_take_mem_trace`, `exists_take_of_mem_trace`.
* Induction principle: `run_invariant` (`Preserves step I → I s → I (run step s ops)`),
  `trace_invariant` (on every state of the trace), `run_invariant_of_imp` (strengthening),
  `run_invariant_under` (an invariant relative to another), `Preserves.and`, `run_of_step`,
  `run_invariant_of_mem` (operations of one list only).
* Relations along runs: `run_rel` (reflexive, transitive), `run_rel_of_trace` (a relation that
  composes only through states satisfying `C`, for runs whose trace stays in `C`: share value with
  outstanding shares), `run_ge`, `run_le`.
* Accumulated bounds: `run_eq_of_step_eq`, `run_eq_of_mem`, `run_eq_add_sum`,
  `run_le_add_sum` (`(∀ s a, P (step s a) ≤ P s + f a) → P (run step s ops) ≤ P s + (ops.map f).sum`),
  `run_le_add_sum_of_inv`.
* Ghost accumulators: `accum_append`, `accum_const`; `run_total_invariant` (an invariant
  `Inv g e s` over the ghost state, the total so far and the state; with
  `Inv g e s := Q s ≤ Q₀ + e ∧ J g s` it states "credited ≤ initial + emitted so far");
  `run_le_accum`, `run_le_scaled_accum` (`P (run step s ops) ≤ P s + c * accum next f g ops`);
  `run_bound_via_potential` (from `Q s * c ≤ P s` and `P s ≤ B * c + R` at the start,
  `Q (run step s ops) ≤ B + accum next f g ops + R / c`); `run_pair`.
* Partial steps: `skip_preserves`, `skip_rel`, `runAll_cons_eq_some`, `runAll_append`, `runAll_some`,
  `runAll_invariant`, `runAll_rel` (a batch never lowers a value no single operation lowers),
  `runAll_rel_of_inv`.
* Reachable states: `Reachable.invariant`, `Reachable.invariant_of_imp`, `reachable_of_runAll`,
  `exists_runAll_of_reachable`, `reachable_iff` (reachable exactly when some atomic run reaches it),
  `reachable_run_skip`.

Recurs in: `rw-hundred-vault` (`run`, `trace`, `run_value`), `rw-euler-donate` (`Reachable`,
`runAll`, `req_no_bad_debt`), `rw-balancer-upscale` (`run` of a batch, `req_batch_keeps_value`),
`rc-knight-router/spec/OrderRouter/Lemmas.lean` (`run` as a fold, `run_induction`),
`rw-compound-comp` (`run`, `emitted` with the speeds as ghost state, `run_inv`, `run_pot`,
`spec_rewards_bounded`), `tasks/transfers-batch-*` (`applyLegs`).

### `ProofForgeFin.Ledger`: conservation over accounts

`sumOver l f` (the right fold the task specifications use), `adjust`, `transfer`, `Move`,
`applyMoves`, `upd`, `SupplyMatches holders bal supply`, `equalSplit a n`.

* `sumOver` algebra: `sumOver_eq_sum_map`, `sumOver_append`, `sumOver_add`, `sumOver_sub`,
  `sumOver_congr`, `sumOver_ite_eq` (an indicator over a duplicate-free list), `sumOver_le_sumOver`.
* `sumOver_adjust`, `sumOver_transfer'`, `sumOver_transfer` (a transfer between two accounts of a
  duplicate-free list conserves the total), `sumOver_applyMoves` (so does any batch of them),
  `applyMoves_other`.
* Natural-number balances: `le_sum_map`, `sum_map_upd` (updating one account), `sum_map_upd_of_not_mem`,
  `sum_map_le_sum_map`, `sum_map_congr`.
* Shares and supply: `SupplyMatches.balance_le` (a holder holds at most the supply),
  `SupplyMatches.mint`, `SupplyMatches.burn`, `SupplyMatches.move`.
* Splitting: `length_equalSplit`, `sum_equalSplit` (the parts add up to the amount),
  `mem_equalSplit_bounds` (each part within one unit of `a / n`), `equalSplit_le_add_one`.
* Accounts indexed by position (`List.modify`, `List.getD`): `getD_modify`, `getD_modify_self`,
  `getD_modify_ne`, `modify_of_length_le`, `getD_mem_or`, `sum_map_modify`, `sum_map_modify_le`,
  `sum_map_modify_eq`, `sum_map_modify_modify` (moving an amount between two positions conserves
  the total), `getD_le_sum_map`, `sum_map_le_add`, `sum_map_mul_le`, `sum_map_mul_right`.

Recurs in: `tasks/transfers-batch-*/spec/Batch/Lemmas.lean` and the same `sumOver_*` lemmas in
the `Lemmas.lean` of the `transfers-overdraft`, `payouts-fee`, `payouts-flagship`,
`payouts-weighted`, `ledgers-journal` and `ledgers-reversal` families; the reference solutions of
`transfers-batch-*` (`sum_shift`, `sum_applyLegs`); `rw-compound-comp/reference/SolutionA.lean`
(the `List.modify` lemmas, `totalSupply`, `St.credited`); `rc-knight-router/spec/OrderRouter/Lemmas.lean`
(`sentFor_append`, `execFor_le_sentFor`); `rw-gomoney-split` (conservation and one-unit bounds of
an equal split, there for signed amounts).

### `ProofForgeFin.Harvested`: lemmas harvested from verified candidates

Generated by `harness/harvest.py` (`docs/HARVEST.md`) from the helper lemmas of verified
candidates of the dev, val and real-world tasks (the test split is held out): 86 lemmas whose
statement holds without the task and that no default tactic, library tactic or `exact?` proves
from the rest of the library and the core library, and 27 support lemmas their proofs cite, in
`Harvested.Arith`, `Harvested.List` and `Harvested.Fin`. Each doc string names the source file,
its SHA-256 and the Passport or `eval.json` SHA-256. No harvested lemma has a `simp` attribute.
Regenerate with `python3 harness/harvest.py run` rather than editing by hand.

### `ProofForgeFin.Sums`: sums over lists and positions

Written for the goal shapes runs that were not accepted failed on most often
(`results/feedback-library-1`): sums restated by recursion, sums over the positions of a list,
sums after one entry changes, and sums of rounded-down parts. Every lemma is stated for the forms
specifications write (`List.sum` of a mapped list on `Nat` and `Int`, and `Ledger.sumOver`).

* `Sums.Eqns`: a sum identified by its equations: `eq_sum_map_of_eqns` (`F [] = 0`,
  `F (a :: l) = f a + F l` give `F l = (l.map f).sum`), `_int`, `eq_sumOver_of_eqns`,
  `eq_sum_range_of_eqns` (`F 0 = 0`, `F (n + 1) = F n + f n` give the sum over `List.range n`),
  `_int`, `eq_sumOver_range_of_eqns`; folds: `foldl_add_eq`, `foldl_add_eq_int`, `foldr_add_eq`.
* `Sums.Index`: `sumOver_eq_sumOver_range` and `sum_map_eq_sum_range_of_getElem` (a sum over a
  list is the sum of `g` over its positions when the summand at position `i` is `g i`, as for a
  share looked up by position), `map_getD_range`, `sum_map_eq_sum_range`, `_int`,
  `sumOver_eq_sumOver_range_getD`; `sum_range_succ_head`, `sum_range_succ_tail` (and `_int`,
  `sumOver_range_succ_head`); `sum_range_indicator` (the first `m` of `n` positions: `min m n`),
  `_int`, `sumOver_range_indicator`; `sum_range_ite_eq`, `_int`; `sum_map_const`, `_int`;
  `sum_map_ite_count`, `_int`, `sum_map_add_ite`, `_int` (a bonus on the elements where a test
  holds).
* `Sums.Update`: `sum_set_add`, `sum_set_int`, `sum_map_set_add`, `sum_map_set_int`,
  `sumOver_set`, `sum_map_set_eq` (one position of a list set); over accounts without duplicates,
  `sumOver_add_ite`, `sumOver_sub_ite`, `sumOver_ite_update`, `sumOver_move` (a delta, an
  overwrite and a move written with `if`, as specifications write them).
* `Sums.Floor`: `sum_map_div_add_mod`, `sum_map_mod_le`, `sum_map_mod_lt`, `sum_map_mul_left`,
  `mul_sum_eq_floor_add_mod`, `sum_floor_shares_le` (the rounded-down parts of `A` add up to at
  most `A`), `floor_shares_leftover_lt_length` (the leftover is less than the number of parts).

### `ProofForgeFin.Accrual`: rounding per operation and capped increments

* `within_one_of_floor_le`: a part between `a / W` and `a / W + 1` is within one unit of the exact
  value (`x * W ≤ a + W ∧ a < x * W + W`); `floor_add_bit_within`, `floor_add_bit_within_int`
  (the rounded-down part plus a leftover bit `e ≤ 1`, on `Nat` and with `Int` casts).
* `add_min_sub_le`, `add_min_sub_eq_min`, `le_add_min_sub`, `sub_add_min_sub`: adding
  `min q (cap - done)` to `done ≤ cap` (a fill, a route, a draw) stays within the cap, never
  decreases and uses up exactly the amount added.

### `ProofForgeFin.Tactic.LibDefs`: `lib_defs`

`lib_defs` replaces every definition of the goal and the hypotheses that is defined outside the
library and is definitionally equal to a ProofForgeFin definition (a specification's own
`sumOver`, `upd`, ceiling division or fixed-point product) by the library's, so that the library
lemmas apply by name and `exact?` finds them; `lib_defs?` reports the replacements
(`lib/docs/Tactic.md`).

### `ProofForgeFin.Salvaged`: lemmas runs that were not accepted did prove

Generated by `harness/harvest.py run --unverified` (`docs/HARVEST.md`) from the final candidates
of 44 runs that were not accepted, of the tasks in the mining set of
`results/feedback-library-1/split.json` (the held-out tasks are skipped): 36 lemmas whose statement
holds without the task, whose proof compiles on its own without `sorry`, and that no default
tactic, library tactic or `exact?` proves from the rest of the library (the harvested modules and
`Sums` included), and 10 support lemmas their proofs cite, in `Salvaged.Arith`, `Salvaged.List`
and `Salvaged.Fin`. Each doc string names its source in
`results/feedback-library-1/salvage/harvest.json` (run, file hash, verdict), not the task.

## Demonstrations

`ProofForgeFinDemo` re-proves lemmas of task reference solutions with the library. Each file copies
the task definitions it needs verbatim (with their doc strings) from the task files named in its
header; no task file is imported or modified.

* `ShareVault.lean` (`rw-hundred-vault`): `req_share_value : ShareValueNeverFalls vault` for the
  reference implementation. The reference proof states its own floor and ceiling bounds and
  cross-multiplied transitivity, then does the arithmetic of each call and an induction over the
  trace. Here
  each successful call is a library conversion (`Shares.deposit_value`, `redeem_value`,
  `withdraw_value`, `donate_value`) and the induction is `Seq.run_rel_of_trace` with
  `Shares.valueNotBelow_trans`, after `run_eq` and `trace_eq` identify the task's `run` and `trace`
  with the library's.
* `BatchTransfer.lean` (`transfers-batch-b3`): `sum_shift` and `sum_applyLegs` of the reference
  solution (an admissible batch conserves the total), from `Ledger.sumOver_transfer` and
  `Ledger.sumOver_applyMoves`, with `shift` identified as `Ledger.transfer` by `rfl`.
* `Compound.lean` (`rw-compound-comp`): the sequence half of the reward bounds, for every
  implementation, invariant and potential: `run_inv`, `run_pot` (a potential that each operation
  raises by at most `doubleScale` times the COMP it emits is raised by a sequence by at most
  `doubleScale * emitted sp ops`) and `credited_bound` (the final division step of
  `spec_rewards_bounded`). `emitted` is shown to be `Seq.accum nextSpeeds emittedBy`. The per-operation
  lemmas of the reference (`exec_inv`, `exec_pot`) are hypotheses, not re-proved.
* `Euler.lean` (`rw-euler-donate`): `noBadDebt_of_staysHealthy : StaysHealthy step → NoBadDebt step`
  for every implementation, via `Seq.Reachable.invariant` after `reachable_iff` identifies the task's
  `Reachable` with the library's; `runAll_healthy` extends it to every successful session.

## Axiom audit

`Audit.lean` (not part of the library targets) imports the library and the demonstrations, collects
with `Lean.collectAxioms` the axioms of every constant declared in a `ProofForgeFin` or
`ProofForgeFinDemo` module, and reports a violation for any axiom outside `propext`,
`Classical.choice` and `Quot.sound` and for any axiom declared in those modules. A `sorry` appears as
`sorryAx`; in Lean 4.35 `native_decide` and `bv_decide` declare an auxiliary axiom
(`<theorem>._native.native_decide.ax_...`, `<theorem>._native.bv_decide.ax_...`) that the theorem
depends on, so all three are reported; `tests/test_fin_lib.py` checks this on a probe copy. The
audit then prints `#print axioms` for the main results.

Output in the pinned image (`proofforge-lean:4.35.0`,
`sha256:7d5b583a0fe4c4cef9d78f4a5b0c929da97d6ec20f11cfc6b6806e005f76e18a`, linux/arm64):

```
axioms used: [Classical.choice, Quot.sound, propext]
audit: 1331 constants, 419 theorems, 0 violations
'ProofForgeFin.floor_spec' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.ceilDiv_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.mulDown_spec' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.mulUp_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.mulDown_le_mulUp' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.mulUp_le_mulDown_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.divDown_spec' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.divUp_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.le_divUp_mulUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.mul_two_pow_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.toNat_fullMul' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Shares.valueNotBelow_trans' depends on axioms: [propext]
'ProofForgeFin.Shares.deposit_value' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Shares.withdraw_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Shares.deposit_redeem_le' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Shares.step_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Shares.run_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Seq.run_invariant' does not depend on any axioms
'ProofForgeFin.Seq.run_rel_of_trace' depends on axioms: [propext]
'ProofForgeFin.Seq.run_le_add_sum' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Seq.run_total_invariant' does not depend on any axioms
'ProofForgeFin.Seq.run_bound_via_potential' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Seq.runAll_rel' does not depend on any axioms
'ProofForgeFin.Seq.reachable_iff' depends on axioms: [propext]
'ProofForgeFin.Ledger.sumOver_transfer' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Ledger.sumOver_applyMoves' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Ledger.SupplyMatches.move' depends on axioms: [propext, Quot.sound]
'ProofForgeFin.Ledger.sum_map_modify_modify' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Ledger.sum_equalSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFin.Ledger.mem_equalSplit_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFinDemo.ShareVault.req_share_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofForgeFinDemo.BatchTransfer.sum_applyLegs' depends on axioms: [propext, Quot.sound]
'ProofForgeFinDemo.Compound.run_pot' depends on axioms: [propext, Quot.sound]
'ProofForgeFinDemo.Compound.credited_bound' depends on axioms: [propext, Quot.sound]
'ProofForgeFinDemo.Euler.noBadDebt_of_staysHealthy' does not depend on any axioms
```

The counts include the constants Lean generates for each declaration (recursors, matchers,
`injEq` theorems, auxiliary proofs). When this output was recorded the source declared 233 library
theorems and 27 demonstration theorems, in the first six modules; the kernel check below covers the
current sources.

## Building

In the pinned image, from the repository root:

```
.venv/bin/python harness/lean.py lib "lake build && lake env lean Audit.lean"
```

`harness/lean.py` runs the command in `proofforge-lean:4.35.0` with `lib/` mounted at `/work` and
takes one of the judge's container slots. The test builds the library, runs the audit, and checks
the audit on a probe copy with a `sorry`, a `native_decide` and a `bv_decide`:

```
.venv/bin/python tests/test_fin_lib.py
```

## Scope

Covered: rounding and fixed point on `Nat`, share accounting with exact ratios, sequences of total
and partial steps, sums over account lists and lists indexed by position, equal splits.

Not covered: rounding of signed amounts (`Int` floor and ceiling toward zero or toward negative
infinity, and the equal split of a negative amount in `rw-gomoney-split`); allocation by ratios with the largest
remainder (`rw-moneyphp-allocate`, `rw-spliit-balances`); a library form of the `BitVec` `div_round` routine of
`rw-cetus-shlw`; the per-operation lemmas of the Compound reward potential (`exec_pot`), which
depend on that task's model; overflow-checked word versions of the fixed-point operations beyond the
exactness conditions of `ProofForgeFin.Word`.

## Integration with the judge and the prover

Candidates may import the library; the task projects are unchanged. `harness/fin_lib.py` does the
following, and `docs/ARCHITECTURE.md` (section "ProofForgeFin in judged projects") gives the
details and the trust argument.

* Imports. A candidate's `Solution.lean` may import `ProofForgeFin` and any `ProofForgeFin.*`
  module in addition to the task's `Spec` and `Lemmas`, `Init.*` and `Std.*`.
  `ProofForgeFinDemo` and `Lean` are refused. Importing the library brings `Lean` into scope (the
  tactics of `ProofForgeFin.Tactic` are metaprograms), so the implementation scan refuses every way
  for candidate code to define or run its own: `macro`, `elab`, `syntax`, `elab_rules`,
  `macro_rules`, `run_tac`, `by_elab`, simprocs, `register_*`, `declare_*`, `initialize` and
  attributes such as `@[tactic]` and `@[command_elab]`.
* Version. The library version is `source_tree_sha256`, a hash of the files the package is built
  from (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `ProofForgeFin.lean`,
  `ProofForgeFin/**/*.lean`); the demonstrations, `Audit.lean` and the docs are not part of it. Show
  the current version with `.venv/bin/python harness/fin_lib.py version`.
* Vendoring. The judge, the binary check and the counterexample stage copy the built package
  into the fresh project at `.lake/packages/proofforge-fin` and require it by path, only when a
  candidate file imports the library. The build is made once per version, in the pinned image with
  no network, from the committed sources (`.venv/bin/python harness/fin_lib.py build`; it also runs
  automatically on first use). No image rebuild is needed when the library changes.
* Library scan. The library modules a candidate imports, transitively, must not contain
  `implemented_by`, `extern`, `unsafe`, `@[export]`, `@[csimp]`, `initialize`, `#eval`,
  `run_cmd`, `run_elab`, `run_meta`, `native_decide`, `bv_decide`, `set_option`, `opaque`, `axiom`,
  `sorry` or `partial`, and may import only `ProofForgeFin`, `Init`, `Std` and `Lean`. Tactic and
  syntax definitions are allowed in library code. A library change that breaks this rule makes the
  judge reject every candidate that imports the affected modules; `tests/test_fin_integration.py`
  runs the scan.
* Checking. Comparator's export for a solution contains the library declarations its theorems
  depend on, so the six kernels check them; the axiom audit covers them; permitted axioms are still
  only `propext`, `Classical.choice` and `Quot.sound`.
* Passport. Every new Passport has a `library` record: the source tree hash available to the
  judge and whether it was vendored; for a candidate that imports the library, the modules
  imported, the size of their closure, the library scan, the commit whose library sources were
  vendored, and the image and toolchain of the build. `bin/proofforge verify` compares the record,
  and reproduces a Passport of an older library version with that version's sources from the
  recorded commit.
* Prover. `agents/repair.py --library on` (the default for arms A1 and A2) vendors the library into
  the agent's workspace and gives the model a prompt section generated from the declaration index
  (`harness/FinIndex.lean`, run against the built library: every module doc, theorem, definition,
  structure, tactic and simp set with its signature and doc string, and for a theorem the shape of
  its conclusion), a `search_library` tool, an `add_import` tool and, for each obligation, the
  declarations the index ranks highest for it. The ranking is goal-aware once an obligation is
  known: BM25 over the text combined with how well each theorem's conclusion matches the
  obligation's and a usage prior from verified proofs (`harness/fin_lib.py`, `Index.scored`;
  evaluated in `results/feedback-library-1/retrieval.json`). A0
  (`agents/baseline.py`) never gets the library.

Measured with `tests/fixtures/library/compound_lib.lean`, a candidate for `rw-compound-comp` whose
three sequence bounds are the library argument of `ProofForgeFinDemo/DeFi/Compound.lean`: VERIFIED,
eight of eight requirements, six kernels. Two of the kernels, con-leche and con-ron, ran out of
fuel on four steps of an earlier version of the demonstration (they unfold `doubleScale = 10 ^ 36`
in equations such as `A * doubleScale + 0 = A * doubleScale`); the fixture and the demonstration
now prove that arithmetic over an abstract scale and instantiate it.

### After a library change

Nothing in the judge or the image changes: the next judged candidate that imports the library
triggers a build of the new version (or run `.venv/bin/python harness/fin_lib.py build`), the new
source tree hash goes into new Passports, and the agent's index is regenerated with the build.
Passports of the earlier version still reproduce: verify extracts that version's sources from the
commit the Passport records, or, when it records none, from the commit in the history of `lib/`
whose sources have the recorded tree hash (`fin_lib.root_for`). Run `tests/test_fin_lib.py`, `tests/test_fin_kernels.py` and
`tests/test_fin_integration.py`.

## Writing proofs that every judge kernel accepts

The judge accepts a proof only when all six kernels of `lake comparator --paranoid` (Lean default
and paranoid, lean4lean, nanoda, con-leche, con-ron) and `leanchecker` accept it, and every
library declaration a candidate's theorems depend on is in the export they check. A library proof
that Lean's kernel accepts can still be rejected by another kernel, and then the judge rejects
every candidate that uses it. The case met so far: con-leche and con-ron reduce under a fuel
bound, and a definitional check such as `A * doubleScale + 0 = A * doubleScale`, with `A` a
variable and `doubleScale = 10 ^ 36`, makes them unfold and reduce the literal until the fuel
runs out (`fuel exhausted: whnfCore`), where Lean's kernel settles it without unfolding. In
library and demonstration code:

* State arithmetic over a variable scale and instantiate it. A lemma over `D` (or the library's
  `one`), applied at `doubleScale`, is checked by substitution, so no kernel unfolds `10 ^ 36`.
  `advance_arith`, `upgrade_arith` and `noPosition_arith` in `ProofForgeFinDemo/DeFi/Compound.lean`
  are the pattern; the statements that mention `doubleScale` stay as they are.
* Do not leave a step to the kernel's evaluation when one side has a variable next to a large
  literal: `simp`, `simpa`, `omega` and `rfl` can produce such steps (`... + 0`, `0 / doubleScale`,
  products reordered). Rewrite with `Nat` lemmas over the variable instead (`Nat.add_zero`,
  `Nat.zero_div`, `Nat.mul_comm`; `le_mul_add_zero` and `le_of_le_add_zero_div` in the Compound
  demonstration).
* Closed computations on literals are fine: `decide` on `0 < 10 ^ 36` (`doubleScale_pos`) passes
  every kernel, which evaluate `Nat` operations on literals directly. Library lemmas take
  positivity of a scale as a hypothesis (`0 < one`) and do not depend on its value.
* `@[irreducible]` changes what the elaborator unfolds, not what a kernel unfolds, so it is not a
  fix; `opaque` is not allowed in library code.
* After a change, run the checker in the pinned image:

  ```
  .venv/bin/python harness/fin_kernels.py
  ```

  It builds the library and the demonstrations, exports every declaration with the exporter
  Comparator uses, runs the export through `lake comparator --paranoid` as the judge does, and
  replays every module with `leanchecker`; it names each declaration a kernel rejects with the
  kernel's reason. `tests/test_fin_kernels.py` runs it (slow) and fails on any rejection.

Measured in the pinned image: before the change to the Compound demonstration, con-leche and
con-ron rejected `psi_moves`, `psi_upgrade` and `psi_noPosition` (`fuel exhausted: whnfCore`), and
the three bounds that depend on them (`account_bounded`, `no_backdated`, `bounds_of_calls`) could
not be checked; every other declaration passed all six kernels. Now all 10,126 safe constants of
the library and the demonstrations (5,982 theorems, counting compiler-generated ones) pass all
six kernels in one Comparator run, and `leanchecker` accepts all 87 modules that declare
constants (`results/feedback-library-1/kernels-full.json`). The 60 `_unsafe_rec` constants (Lean's compiled form of recursive definitions, which no
proof mentions) pass Lean's kernels and lean4lean; nanoda, con-leche and con-ron decline `unsafe`
code by design.
