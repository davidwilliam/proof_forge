# ProofForgeFin.Machine: ledgers, state machines and operation sequences

`ProofForgeFin.Machine` is the layer above `ProofForgeFin.Seq` (runs, traces, invariants,
accumulated bounds) and `ProofForgeFin.Ledger` (sums over accounts, transfers). It covers
double-entry bookkeeping, balances as functions with an explicit account list, idempotent
operations, refinement of a specification by an implementation that keeps its own counters,
invariant construction, safety properties of runs, reordering of commuting operations, atomic
batches, and the bookkeeping lemmas for records and function updates that state machine proofs
end with.

The area root is `ProofForgeFin/Machine.lean`; `import ProofForgeFin` imports it. Everything is in
the namespace `ProofForgeFin.Machine` (the journal in `ProofForgeFin.Machine.Journal`). It depends
on the Lean core library only, and every theorem is proved with no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.

The area has 246 theorems and 44 definitions (structures and inductive types included) in eight
modules, one simp set (`machine_simps`) and one tactic (`machine_norm`). Four demonstrations under
`ProofForgeFinDemo/Machine/` (81 theorems) re-prove requirements of `ledgers-journal-b3`,
`ledgers-reversal-b3`, `ledgers-log-b4` and `rc-knight-router` over copied definitions.

Statements below are paraphrased; the Lean names are exact. `sumOver l f` is `Ledger.sumOver`,
the right fold `f a₁ + (f a₂ + ...)` over the list `l`, which is the `sumOver` every ledger task
defines (equal to the library's by `rfl`). `upd f k v` is `Ledger.upd`,
`fun j => if j = k then v else f j`.

## Modules

### `Machine.Attr` and `Machine.Record`: records, updates, projections

* `machine_simps`: a simp set (registered in `Attr` because a simp attribute cannot be used in the
  module that declares it). It holds `upd_self`, `upd_upd_self`, `upd_eq_self`, `fst_ite`,
  `snd_ite`, `fst_dite`, `snd_dite`, `ite_apply_fun`, `getD_map`, the `run`, `trace`, `runAll` and
  `sumOver` equations of `Seq` and `Ledger`, and the unfolding equations of the `Machine`
  modules (`netOf_cons`, `post_apply`, `postAll_cons`, `couple_fst`, `keyTotal_append`, ...).
* `machine_norm`: `dsimp only` on the goal and every hypothesis, then
  `simp only [machine_simps]` on all of them; neither step fails without progress. `dsimp only`
  reduces `{ st := st, tr := tr }.st` to `st`, `{ s with f := v }.f` to `v` and
  `{ s with f := v }.g` to `s.g`.
* Function update: `upd_apply` (the definition), `upd_ne'`, `upd_of_eq`, `upd_upd_self`
  (`upd (upd f k v) k w = upd f k w`), `upd_eq_self` (`upd f k (f k) = f`), `upd_comm`
  (`k ≠ k' → upd (upd f k v) k' w = upd (upd f k' w) k v`), `upd_eq_iff`
  (`upd f k v = g ↔ v = g k ∧ ∀ j ≠ k, f j = g j`), `upd_congr`, `comp_upd`
  (`g ∘ upd f k v = upd (g ∘ f) k (g v)`), and the per-key forms `forall_upd`,
  `forall_upd_of_forall`, `forall_upd_iff`
  (`(∀ j, P j (upd f k v j)) ↔ P k v ∧ ∀ j ≠ k, P j (f j)`).
* Conditionals: `fst_ite`, `snd_ite`, `fst_dite`, `snd_dite`, `ite_apply_fun`, `apply_ite'`,
  `ite_prop`, `prod_ext_iff`; options: `getD_map`, `eq_some_getD`.

These serve every task whose state is a structure with function-valued fields updated at one key
(`parents := upd s.parents id ...` in `rc-knight-router`, `adjust` in the ledger tasks) and whose
step returns `if valid then (.ok, s') else (.rejected, s)`.

### `Machine.Accounts`: balances with an explicit account list

* Order: `sumOver_perm` (`l₁ ~ l₂ → sumOver l₁ f = sumOver l₂ f`), `sumOver_eq_of_mem_iff`
  (two duplicate-free lists with the same members), `sumOver_reverse`, `sumOver_append_comm`.
* Algebra: `sumOver_neg`, `sumOver_mul_left`, `sumOver_const`, `sumOver_map`, `sumOver_eq_zero`,
  `sumOver_nonneg`, `le_sumOver`, `sumOver_natCast`, `sumOver_ite_eq'`, `sumOver_ite_eq_apply`,
  and `sumOver_comm`:
  `sumOver l (fun a => sumOver m (g a)) = sumOver m (fun b => sumOver l (fun a => g a b))`.
* Splitting: `sumOver_filter_add`, `sumOver_eq_filter`, `sumOver_ite`.
* Finite support: `Supported l bal` (`∀ a ∉ l, bal a = 0`) with `supported_zero`,
  `Supported.mono`, `Supported.add`, `Supported.upd`; `sumOver_eq_of_subset` and
  `sumOver_eq_of_supported` (the total of a function supported on a duplicate-free `l` is the same
  over every duplicate-free list containing `l`).
* Updates and conservation: `sumOver_upd` (`k ∈ l`, `l.Nodup` give
  `sumOver l (upd bal k v) = sumOver l bal - bal k + v`), `sumOver_upd_of_not_mem`,
  `sumOver_add_of_sum_zero` (a change `d` with `sumOver l d = 0` keeps the total),
  `sumOver_add_delta`, `sumOver_eq_of_change`, `sumOver_eq_of_eqOn`.
* Natural-number totals: `sum_map_perm`, `sum_map_add`, `sum_map_ite_eq`, `sum_map_zero`.
* Per-key totals of a list of records: `keyTotal key f l j`, the sum of `f x` over the records
  `x ∈ l` with `key x = j`, with `keyTotal_nil`, `keyTotal_cons`, `keyTotal_append`,
  `keyTotal_eq_zero`, `keyTotal_eq_zero_of_field`, `keyTotal_le_keyTotal`, `le_keyTotal`,
  `keyTotal_set` (replacing the record at a position), `keyTotal_set_add` and `keyTotal_set_eq`
  (replacing it by a record with the same key and a field larger by `d`, or equal), and
  `sum_keyTotal` (summing the per-key totals over a duplicate-free list containing every key
  gives the total over all records).

The representation is a function `κ → Int` (or `κ → Nat`) with a separate key list, the one the
task states use (`accounts : List AccountId`, `balance : AccountId → Int`): reads are
applications, updates are `upd` or `adjust`, equality is `funext`. `keyTotal` covers the
specifications that recompute a total from a list of records by recursion (`sentFor`, `execFor`
in `rc-knight-router`; `logSum` in `ledgers-log-b4` is its signed counterpart `Journal.netOf`).

### `Machine.Journal`: double-entry bookkeeping

Lines are `κ × Int` (positive for a debit, negative for a credit), the `Line` of the ledger tasks.

* `netOf ls a`, `lineSum ls`, `post bal ls := fun a => bal a + netOf ls a`, and `postLines` (the
  line-by-line loop with `adjust` that the task solutions write), with `postLines_apply` and
  `postLines_eq_post`.
* `sumOver_netOf`: `l.Nodup → Known l ls → sumOver l (netOf ls) = lineSum ls`;
  `sumOver_netOf_eq` without the `Known` hypothesis.
* Trial balance: `sumOver_post` (`sumOver l (post bal ls) = sumOver l bal + lineSum ls`),
  `trial_balance_post` (a balanced entry over known accounts keeps the total),
  `trial_balance_postAll` (any sequence of balanced entries over known accounts keeps the total),
  `sumOver_postAll`.
* Reversal: `negate`, `netOf_negate`, `lineSum_negate`, `negate_negate`, `Balanced.negate`,
  `Known.negate`, `post_post_negate` (`post (post bal ls) (negate ls) = bal`),
  `post_negate_post`, `post_negate_apply`, and over sequences `postAll_reverse_restores` (posting
  the negations of the entries, in any order, restores the opening balances) and
  `postAll_reverse_restores'` (in reverse order).
* Order: `post_append`, `post_comm`, `postAll_append`, `postAll_apply`
  (`postAll lines bal es a = bal a + sumOver es (fun e => netOf (lines e) a)`), `postAll_perm`.
* Transfers: `transferLines src dst x`, `post_transferLines` (posting it is `Ledger.transfer`),
  `balanced_transferLines`.
* Debits and credits: `debits`, `credits`, `lineSum_eq_debits_sub_credits`,
  `balanced_iff_debits_eq_credits`, `debits_nonneg`, `credits_nonneg`.
* Reversal marks: `sumOver_mark`: in a journal with distinct identifiers, adding the identifier
  `i` of the entry `e` to the reversed set removes exactly `g e` from
  `sumOver j (fun x => if id x ∈ R then 0 else g x)`.
* T-accounts: `TBook` (a debit and a credit column per account), `Leg` (account, `Side`, amount),
  `TBook.postLeg`, `TBook.postLegs`, `TBook.dr_postLegs`, `TBook.cr_postLegs`,
  `TBook.drTotal_postLegs`, `TBook.crTotal_postLegs`, `TBook.Balanced.postLegs`, and
  `TBook.balanced_run`: from a book whose total debits equal its total credits, after any
  sequence of entries with equal debits and credits over known accounts, total debits equal total
  credits. `TBook.net_postLegs` and `lineSum_signed` connect the T-account ledger to signed lines.

These serve `ledgers-journal-*`, `ledgers-reversal-*` (posting, trial balance, round trip, the
consistency of balances with the entries not reversed), `transfers-batch-*` (a batch of transfers
as entries).

### `Machine.Keyed`: idempotent operations

`keyed key step (s, seen) a` applies `step` when `key a ∉ seen` and records the key; otherwise it
changes nothing.

* `keyed_keyed` (applying an operation twice is applying it once), `keyed_resubmit` (a later
  operation with the same key and any other fields is ignored), `keyed_of_mem`,
  `keyed_of_not_mem`, `mem_keyed_seen`, `key_mem_keyed`.
* Runs: `run_keyed_twice` (replaying a log a second time changes nothing),
  `run_keyed_of_seen`, `run_keyed_append_of_seen`, `mem_run_keyed_of_mem`, `key_mem_run_keyed`.
* `fresh key seen ops`: the first occurrence of every new key. `run_keyed_fst`: the state after a
  run with resubmissions is `Seq.run step s (fresh key seen ops)`; `run_keyed_snd`;
  `fresh_keys` (distinct, new keys); `fresh_of_nodup` and `run_keyed_of_nodup` (with distinct new
  keys the wrapper is invisible).
* `keyed_preserves`, `keyed_seen_nodup`.

These serve REQ-IDEMPOTENCY of `ledgers-journal-*`, REQ-DUPLICATE of `ledgers-log-*`, any payment API
keyed by a client identifier. Posting a journal entry once per identifier is
`keyed (·.id) (fun b e => Journal.post b e.lines)`.

### `Machine.Refine`: refinement and simulation

* `Simulates abs impl spec` (`abs (impl s a) = spec (abs s) a`): `Simulates.run`
  (`abs (run impl s ops) = run spec (abs s) ops`), `Simulates.trace`, `Simulates.invariant`
  (every specification invariant holds of the abstraction of every implementation state),
  `Simulates.transfer` (any property of all specification runs, inductive or not),
  `Simulates.refl`, `Simulates.comp`, `Simulates.pair`.
* `SimulatesOn J`: the square only on states satisfying an implementation invariant `J`, with
  `SimulatesOn.run`, `SimulatesOn.invariant`, `Simulates.on`.
* `SimulatesBy abs impl spec f`: one implementation operation as the list `f a` of specification
  operations (empty for an internal step); `SimulatesBy.run`
  (`abs (run impl s ops) = run spec (abs s) (ops.flatMap f)`), `SimulatesBy.invariant`,
  `Simulates.by_singleton`.
* `ForwardSim R impl spec`: `ForwardSim.run`, `ForwardSim.transfer`, `ForwardSim.comp` (through an
  intermediate model), `ForwardSim.and_inv` (strengthening by an implementation invariant),
  `Simulates.forwardSim`, `ForwardSim.simulates`, `ForwardSim.toOpt`.
* Partial steps: `ForwardSimOpt`, `ForwardSimOpt.runAll`, `ForwardSimOpt.reachable` (every
  reachable implementation state is related to a reachable specification state),
  `ForwardSimOpt.invariant`.
* Steps with outputs: `couple impl obs` (the implementation returns its next state and an output;
  the observer records the output into the specification's facts), `couple_fst`, `couple_snd`,
  `couple_of_eq` (a whole-state step equation gives a plain pair), `run_couple_fst`,
  `run_couple_invariant`; `outputs`, `SimulatesOut`, `SimulatesOut.simulates`,
  `SimulatesOut.outputs` (equal outputs on every run).
* Cached fields: `cache_run` (a cache that matches the specification view and that every step
  keeps matching matches after every run); `view_append_list`; `cache_log_invariant` and
  `cache_log_invariant'` (a cache kept next to an append-only log, where the view of the log is a
  left fold and every step appends to the log and folds the same events into the cache, equals the
  view of the log in every reachable state); `run_cache_add` and `run_cache_add_key` (running
  totals: `cache (run impl s ops) k = cache s k + sumOver ops (fun a => d a k)`).
* History: `withHistory`, `run_withHistory`, `withHistory_simulates`.

These serve the tasks where the specification computes the truth from the events and the
implementation keeps counters: `rc-knight-router` (`Truth.sent`, `Truth.exec` against
`ParentRec.sent`, `ParentRec.cum`), `ledgers-log-*` (cached balances against `logSum`),
`rw-compound-comp` (credited rewards against emitted rewards), and any port proved equal to a
canonical model (`reference/SolutionB.lean` of `rc-knight-router` proves its router computes the
same as a canonical one).

### `Machine.Invariant`: building invariants

* Conjunctions: `AllOf Is`, `allOf_nil`, `allOf_cons`, `Preserves.allOf`, `Preserves.allOf_under`
  (each component may use all of them), `Preserves.mutual`, `run_invariant_left`.
* Strengthening: `Preserves.under` (`I` preserved on states satisfying the invariant `J`, so
  `I ∧ J` is an invariant), `Preserves.of_iff`, `Preserves.of_forall`.
* Ghost history: `run_hist_invariant` (`I s hist` extended by every step holds after a run with
  the history extended by its operations), `run_hist_invariant_nil`, `run_take_hist_invariant`,
  `run_take_hist_invariant_of_prefix` (the step may use that the history is a prefix of a fixed
  operation list and that the next operation is `ops[k]`).
* Per-key invariants and frames: `Frame view step touched` (an operation changes `view s j` only
  for `j ∈ touched a`), `FrameOne view step key`, `FrameOne.frame`, `Frame.preserves_forall` and
  `FrameOne.preserves_forall` (a property of every key is preserved when every operation
  re-establishes it on the keys it touches), `Frame.run_untouched` and `FrameOne.run_untouched`
  (a key no operation of a run touches keeps its value), `frameOne_of_upd`, `frameOne_of_upd_or`
  (a step that writes one key with `upd`, or leaves the view unchanged, has the frame property),
  `frame_of_pointwise`, and `forallKey_preserves`, `forallKey_preserves_touched` for properties
  `P j s` of the whole state.

These serve per-account and per-order invariants (`∀ id < nOrders, ...` in `rc-knight-router`,
`∀ a ∈ accounts, 0 ≤ balance a` in `ledgers-log-*`), invariants relative to the operations
performed so far.

### `Machine.Trace`: safety properties, reordering, atomic batches

* `Always step P s ops` (every state of the trace), `Never`, `always_of_preserves`,
  `never_of_preserves`, `always_nil`, `always_cons`, `always_append`, `always_iff_take`
  (`Always ↔ ∀ k, P (run step s (ops.take k))`), `Always.run`, `Always.start`, `Always.mono`,
  `always_and`.
* Along a run: `run_take_of_le`, `stable_after` (a preserved property true after `i` operations is
  true after every `j ≥ i`), `run_take_rel`, `run_take_mono`, `run_take_anti`.
* Counting changes: `changes view step s ops` (operations of the run that change `view`),
  `changes_nil`, `changes_cons`, `changes_append`, `changes_le_length`, `changes_eq_zero`,
  `changes_eq_zero_of_final`, `changes_le_one_of_final` (a value final once it satisfies `D`, with
  every change landing in `D`, changes at most once), `changes_le_one_of_writeOnce` (an `Option`
  set once), `changes_le_one_of_flag` (a flag that stays set), `changes_le_of_mono`
  (`changes P step s ops + P s ≤ P (run step s ops)` for a nondecreasing counter),
  `changes_le_of_bounded`. With `view s := s.reversed.contains i` or `view s := status s id` these
  give "reversed at most once" and "a key is updated at most once after it is set"; the per-key
  form is the same theorem with `view s := f s k`, and "after X" is `changes_append` with the
  prefix up to X.
* Commuting operations: `Commute step a b`, `Commute.symm`, `Commute.refl`, `run_swap`, `run_perm`
  (when the operations of a list commute pairwise, every permutation gives the same final state),
  `run_perm_of_forall`, `run_step_comm` (an operation commuting with a run can be moved to its end),
  `commute_of_independent` (steps on disjoint components of a product state commute).
* Atomic batches: `batch step s ops := (runAll step s ops).getD s`, `batch_of_some`,
  `batch_of_none`, `batch_eq_or` (all or nothing), `runAll_eq_none_iff` (a batch fails exactly when
  some operation fails on the state its prefix reaches), `runAll_append_of_none`,
  `run_skip_of_runAll`, `batch_invariant`, `run_batch_invariant` (any sequence of batches),
  `batch_rel`, `batch_reachable`.

These serve REQ-STOP-WHEN-FILLED style requirements (once filled, nothing more is sent),
REQ-REVERSE-ONCE, monotone indices and counters, batch transfers that revert entirely
(`transfers-batch-*`), and order independence of postings and of commuting operations.

## Demonstrations

All four copy the task definitions without change; the task files are not imported or modified.
Line counts are lines of Lean code in theorem and proof bodies (blank lines and comments excluded),
measured on the reference solution and on the demonstration.

| Demonstration | Reference | With the library |
|---|---|---|
| `JournalPosting`: the seven requirements of `ledgers-journal-b3` for `reference/SolutionA.lean` | 70 lines, plus the `sumOver` lemmas of `Journal/Lemmas.lean`; the generic part (`postLines_eq`, `sumOver_zero`, `sum_netOf`) is 32 | 34; the generic part is the 6-line `postLines_eq`, and REQ-TRIAL-BALANCE is `Journal.trial_balance_post` |
| `Reversal`: the ten requirements of `ledgers-reversal-b3` for `reference/SolutionA.lean` | 284 lines: generic facts (`postLines_eq`, `netOf_negate`, `sumOver_zero`, `sum_netOf`, `active_reverse`) 74, journal lookup and step cases 97, requirements 113 | 161 lines: generic facts 9 (bridges to the library), lookup and step cases 83 (task-specific, not from the library), requirements 69 |
| `EntryLog`: REQ-CONSISTENT of `ledgers-log-b4` | 19 lines (`req_consistent` 11, `step_state` 8) | 28 lines through `cache_log_invariant'`, and 3 more for the statement over every run, which the task does not ask for |
| `KnightRouter`: the task's `OrderRouter/Lemmas.lean` | 88 lines (91 with `sentFor_new_cons`, which the reference solutions do not use); the append, `set` and bound lemmas are 46 | 72 lines including 14 lines of bridges to `keyTotal`; the append, `set` and bound lemmas are 22 |
| `KnightRouter`: the requirement layer of `rc-knight-router` for `reference/SolutionA.lean` (`route_out` and the six requirement theorems) | 43 lines | 30 lines, given `reqs_of_invariant` (30 lines, proved once for every router and every invariant) |

`Reversal` and the Knight requirement layer are where the library removes the most: the
reversal-mark induction (`active_reverse`, 35 lines) is `Journal.sumOver_mark`, and the trial
balance of a reversal (21 lines) is `trial_balance_post` with `Known.negate` and
`Balanced.negate`. In `EntryLog` the library version is longer for one step; its two facts (the
log view is a fold, each step has one of two shapes) give the invariant over every run for free.
In `KnightRouter` the per-event invariant proof `inv_advance` (104 lines) is copied unchanged and
runs on the re-proved lemmas; the library does not shorten it.

`reqs_of_invariant` states the last step of the Knight task once: for every router and every
invariant of the coupled system that gives `sent ≤ qty`, `cum = exec` for every existing parent,
the expected child order on a routing opportunity and none on other events, REQ-ROUTES-AVAILABLE,
REQ-NEVER-OVERROUTE, REQ-STOP-WHEN-FILLED, REQ-NO-EXCESS-EXECUTION and REQ-FILL-ACCOUNTING hold.

## Projections of structure literals

In a harness run on `rc-knight-router` (`results/knight-1/A2-2`, a snippet attempt for the lemma
`plan3_invFillAcc_route`), Lean reported an "Application type mismatch" whose two sides were
displayed with unreduced projections such as
`{ st := (routeBySent x.st rid liq).fst, tr := ... }.tr`. Checked in the pinned toolchain:
projections of structure literals are definitional, and `rw`, `omega` and `exact` see through
them (a goal `({ st := a, tr := t } : Sys).tr.sent id ≤ t.qty id` closes by `omega` from
`t.sent id ≤ t.qty id`). The mismatch in that run came from a propositional rewrite inside the
literal (`rw [hout]` replaced the router's output by a list), after which the hypothesis and the
lemma's expected type were no longer definitionally equal. The library addresses it in two ways:
`couple_of_eq` (and `advance_of_eq` in the Knight demonstration) rewrite a whole-state step
equation `step b s e = (s', out)` into a plain pair before anything is projected, and
`machine_norm` normalizes the goal and every hypothesis the same way so that both sides of such a
comparison are shown reduced.

## Limits

* No `Std.HashMap` or `Std.TreeMap` interface: account maps are functions with an explicit key
  list. A task whose implementation uses a hash map needs its own lemmas relating the map to a
  function (`get?` after `insert`), after which this module applies.
* Balances are `Int` (signed ledgers) or `Nat` (columns, shares, counts); no fixed-point or
  rounding interaction (that is `ProofForgeFin.Rounding` and `ProofForgeFin.FixedPoint`).
* Only safety properties over finite runs: no liveness, fairness or infinite traces.
* `run_perm` needs pairwise commutation of every two operations of the list; partial
  commutation (a dependency relation, Mazurkiewicz traces) is not covered.
* The refinement theorems are for deterministic steps (`σ → α → σ`, `σ → α → Option σ`, or a step
  with an output). Nondeterministic specifications given as relations are covered only through
  `ForwardSimOpt` and `Seq.Reachable` with a deterministic implementation.
* `Keyed` keeps the seen identifiers as a list; a task that keeps them as a field of its state
  maps to the pair through an abstraction function.
* The demonstrations re-prove requirements of reference solutions; they do not replace the task
  projects; candidates may import the library (see `lib/README.md`, Integration).
