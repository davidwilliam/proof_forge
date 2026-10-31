# feedback-library-1: failure mining into ProofForgeFin, and retrieval by goal shape

Two features, built and measured without model calls:

1. Failure mining. The goals runs left open are read from every run that was not accepted, on a
   mining set of tasks fixed beforehand; their shapes are clustered; general library lemmas and
   a tactic are written for the recurring ones; declarations that failed runs did prove are
   salvaged into the library; the effect is measured on held-out tasks only.
2. Retrieval by goal shape. The library index records the shape of every theorem's conclusion,
   and `search_library` ranks against the goal being proved (BM25, conclusion match, usage
   prior). Recall is measured offline on the goals library lemmas were actually used on.

Library version: `source_tree_sha256` before
`34d63d5e60d7027c0c3a6fea8171bd4238182ada1c9110a7a095398c885bfde3` (commit `0b54831`), after
`5552fae308ba444d87cdc15da779a2c38625d376e3fa95b2259f96184b200301` (commit `8c9819a`). The
salvage and the retrieval uses were made at
`ecb69ecac31ce01b33bdebe3420e9adf3053fb16ac563d8812f0d0fb06eb97eb` (commit `4433f37`), which has
the same theorems and differs only in `lib_defs`; the recall evaluation was run on both indexes
and gives the same recall on every set. Older versions stay reproducible:
`fin_lib.find_commit` finds `34d63d5e` at `0b54831` and `f2fbb0d3` (the version `library-1` ran
with) at `a837ff2`, and `fin_lib.materialize` extracts them. No committed Passport vendors the
library; `tests/test_committed_passports.py` passes.

Runs were read from the main checkout's `results/` (`library-1`, `balancer-1`,
`baseline-flagships-1`, `compound-1`, `knight-1`, `frontier-1`, `realworld-1`, the `e1-*`
directories and the others with candidates and events).

## Files

| File | What |
|---|---|
| `split.json` | the task split, its rule and rationale (committed before any goal was read) |
| `goals-mining.jsonl` | every open goal of the failed mining-set runs, with source, kind and shape tags |
| `clusters.json` | goals per shape, with runs, families and examples |
| `lemmas.json` | the lemmas and the tactic written from the clusters, by module, with statements |
| `salvage/harvest.json` | the salvage harvest: sources, every declaration, class, verdict and reason |
| `kernels-full.json` | six kernels, `leanchecker` and the axiom audit, whole library and demonstrations |
| `open-mining.json` | the open goals of the mining set, closed before and after (in-sample) |
| `open-held-out.json` | the open goals of the held-out set, closed before and after |
| `reprove-held-out.json` | the proofs of accepted held-out runs, re-proved before and after, with sizes |
| `uses.json` | every use of a library theorem with the goal it was used on |
| `retrieval.json`, `retrieval-ranks.json` | recall of the two rankings, the tuning grid, every rank |

## Split

The unit is the task family (`task.json` `family`), so the variants of one specification and the
real-world tasks of one domain never fall on both sides. Every family with a task in the frozen
test split is held out (the test split is never mined into the library, as in
`harness/harvest.py`). Of the six other families, the two with the smallest
`sha256("feedback-library-1/" + family)` are held out too: drawn, not chosen, so the held-out set
does not depend on which goals look easy. The split was committed (`2027493`) before any goal
was read.

| | families | tasks |
|---|---|---:|
| mining | order-routing (Knight), payouts (dev payouts tasks, flagship, go-money, moneyphp, Spliit), rate-limiters, transfers | 33 |
| held out | ledgers (test split and Hundred), permissions, queues (test split); lending (Compound, Euler) and fixed-point (Balancer, Cetus), drawn | 35 |

Mining read only runs of mining-set tasks; every measurement of effect below is on held-out tasks.

## Mining

`harness/mine.py goals --set mining` read 161 runs of mining-set tasks, 45 of them not accepted
(44 with a final candidate), and collected 620 open goals: 186 theorems still proved by `sorry` in
the final candidate (101 required theorems, 85 helpers), 48 planner lemmas the final candidate
does not prove, and 386 last `unsolved goals` texts. `mine.py clusters` tags each conclusion by
shape (a goal can have several tags); the main clusters (`clusters.json`):

| shape | goals | runs | families |
|---|---:|---:|---|
| no structure to read: a required property stated as a named predicate (`Conserves step`) | 160 | 39 | order-routing, payouts, transfers |
| mentions a definition the task restates from the library (its text equals the library's) | 102 | 19 | payouts, transfers |
| a sum over a list or a range | 99 | 17 | payouts, transfers |
| a sum after one entry changes | 17 | 9 | payouts |
| truncated subtraction | 90 | 23 | order-routing, payouts, transfers |
| list length, positions | 72 | 19 | order-routing, payouts |
| a result case (`Outcome`, `Option`, `match`) | 65 | 23 | order-routing, payouts, transfers |
| membership, `Nodup`, `filter` | 53 | 18 | order-routing, payouts, transfers |
| `min`/`max`, capped increments (`sent + min q (qty - sent)`) | 45 | 7 | order-routing, payouts |
| a record update | 34 | 13 | order-routing, payouts, transfers |
| a projection of a step's result | 27 | 17 | payouts, transfers |
| a floor-division bound (`a / W * W ≤ a`, within one unit) | 31 | 13 | payouts |
| a quotient-remainder equation | 10 | 9 | payouts |
| a remainder (`%`) | 25 | 10 | payouts |
| a product bound | 18 | 8 | payouts |
| a running quantity that only grows | 21 | 4 | order-routing |
| a run of operations | 7 | 3 | order-routing |
| an invariant over a run | 2 | 2 | order-routing |

The battery of `mine.py open` (default tactics, the library tactics, `grind`, `exact?`) with the
library before this work closes 102 of the 359 open goals Lean can state in the candidate's
context (231 `sorry` sites and failing theorems of the final candidates, 99 unsolved goals and 29
planner lemmas that elaborate; 17 did not). Reading the 257 it does not close, the recurring
reason a library fact was not used is that the task restates the definition the fact is about:
the payouts and transfers specifications define their own `sumOver` (the library's
`Ledger.sumOver`, word for word), Knight its own `upd` (`Ledger.upd` on `Nat` keys), the
weighted payouts a recursive `natSum`, candidates their own `sumFinNat`; `exact?` and `simp` do not
see through them. The other recurring shapes are sums over the positions of a recipient list,
sums after one position or account changes, rounded-down shares plus a leftover unit within one
unit of the exact share, and capped increments.

## What was written

Modules (`lemmas.json`, every declaration with its statement and doc string; no lemma mentions a
task, a protocol or a task type, `tests/test_feedback_library.py` checks it):

| module | theorems | for |
|---|---:|---|
| `ProofForgeFin.Sums.Eqns` | 9 | sums restated by recursion (lists, ranges) or as folds, identified by their equations |
| `ProofForgeFin.Sums.Index` | 22 | sums over the positions of a list; indicator, one-position, constant and counting sums |
| `ProofForgeFin.Sums.Update` | 10 | the total after one position of a list or one account changes |
| `ProofForgeFin.Sums.Floor` | 10 | sums of rounded-down parts and their remainders, common factors |
| `ProofForgeFin.Accrual` | 10 | a floor plus at most one unit within one unit; floors given by bounds; capped increments |
| `ProofForgeFin.Tactic.LibDefs` | tactic | `lib_defs` and `lib_defs?` |

`lib_defs` replaces every definition of the goal and the hypotheses that is defined outside the
library and is definitionally equal to a ProofForgeFin definition by the library's (a change of the
goal, checked by the kernel, no axiom), and rewrites a sum restated by recursion on a list or a
natural number into `List.sum` with the `Sums.Eqns` lemmas (`lib/docs/Tactic.md`; tests in
`ProofForgeFinDemo/Tactic/LibDefs.lean`).

Salvage (`harvest.py run --unverified`, `salvage/harvest.json`): the final candidates of the 44
failed mining-set runs (66 held-out ones listed and skipped) have 1,909 helper theorems; 753 state
a general fact (614 as written, 132 restated over library definitions, 7 with a task structure
abstracted), 714 of them have a proof that compiles on its own without `sorry`; of their 306
distinct statements, 131 are trivial for the battery, 137 duplicate the library or `exact?` proves
them from it, 2 were dropped at the final compile, and 36 were accepted. With the 10 support lemmas
their proofs cite, 46 lemmas are written to `ProofForgeFin.Salvaged` (`Arith` 19, `List` 24,
`Fin` 3).

In all: 61 new theorems written by hand, 46 salvaged, one tactic (two syntaxes); the library goes
from 1,617 to 1,724 theorems and from 59 to 70 files.

## Checks

`kernels-full.json` (`harness/fin_kernels.py` through `mine.py kernels`, whole library and
demonstrations, library `5552fae3`): all 10,128 safe constants pass Lean default, Lean paranoid,
lean4lean, nanoda, con-leche and con-ron in one `lake comparator --paranoid` run, none rejected;
`leanchecker` replays all 87 modules that declare constants; the 60 `_unsafe_rec` constants pass Lean
default, Lean paranoid and lean4lean (nanoda, con-leche and con-ron decline unsafe code by
design). Axiom audit (`lib/Audit.lean`): 10,200 constants, 3,219 theorems, 0 violations; axioms
used `propext`, `Classical.choice`, `Quot.sound`. The library builds without warnings with
`linter.missingDocs`, the library scan passes for the new modules, and the demonstrations
(including the new `ProofForgeFinDemo/Tactic/LibDefs.lean`) build.

## Held-out measurement

Library before: `34d63d5e` (commit `0b54831`). Library after: `5552fae3` (commit `8c9819a`; the
same theorems as `ecb69eca`, with `lib_defs` restricted to structurally recursive sums for speed).
The battery is the same for both, except that the library after also tries `lib_defs` followed
by `simp_all`, `grind` or `exact?` (before `exact?` alone): default tactics, `fin_simp`,
`div_norm`, `grind`, `exact?`, at most 4,000,000 heartbeats per declaration. A goal counts as
closed when the battery closes it with no error; the closing term `exact?` suggests is recorded.

Open goals of the held-out failed runs (`open-held-out.json`). 66 failed held-out runs have a final
candidate; 11 do not compile apart from their `sorry` sites (errors outside every theorem) and
are skipped; the other 55 have 529 goals Lean can state: 413 `sorry` sites or failing theorems of
the final candidates, 105 last unsolved goals and 11 planner lemmas that elaborate in the
candidate (25 did not).

| runs | goals | closed before | closed after | closed only after |
|---|---:|---:|---:|---:|
| `library-1` (Compound, Balancer) | 162 | 33 | 33 | 0 |
| `compound-1` | 57 | 13 | 13 | 0 |
| `balancer-1` | 22 | 7 | 7 | 0 |
| `baseline-flagships-1`, `frontier-1` (Compound, Balancer) | 59 | 4 | 4 | 0 |
| `e1-test-1`, `e1-test-open-1`, `e1-test-glimmer-1` (test split) | 229 | 30 | 30 | 0 |
| total | 529 | 87 | 87 | 0 |

20 goals are not reached by either battery (an earlier error in the same proof stops
elaboration first). Zero held-out open goals close only with the new library: no new lemma and no
`lib_defs` rewrite finishes any of them. The goals that stay open are the requirements of the
Compound reward model (bounds over a run with an emission potential), the Balancer swap value
bounds and the per-step cases of the test-split ledgers, permissions and queues; the held-out
specifications restate `sumOver` too, but their open goals need the per-operation reasoning, not
a sum fact.

Proofs of accepted held-out runs re-proved (`reprove-held-out.json`): for each held-out task the
accepted final candidate with the most proofs of at least 300 non-whitespace characters (one
candidate per task, 32 tasks, 187 proofs, one per distinct statement), each proof replaced by the
battery while the others keep theirs:

| | proofs | closed before | closed after | closed only after |
|---|---:|---:|---:|---:|
| re-proved | 187 | 12 | 14 | 2 |

The two closed only after are in `queues-ring` candidates (`e1-test-1/queues-ring-b2/A1`,
`e1-test-1/queues-ring-b4/A2`), by the salvaged `ProofForgeFin.Salvaged.range_succ_map`; their
original proofs total 895 non-whitespace characters, the `exact` replacements 102. The 12 closed
before and after (5,824 characters of original proof) close with the same replacement size under
both libraries. Proof size change on the held-out proofs: 793 characters fewer over 2 of 187
proofs; none for the other 185.

In-sample, for comparison (`open-mining.json`, the mining set the lemmas were written from): of
359 open goals, 102 close before and 127 after (25 only after, none only before): 17 by an
existing library lemma that `lib_defs` makes applicable to a restated `sumOver` (9 `Machine`
subset, support and cast lemmas, 8 harvested range, indicator and constant sums), 7 by the new
`Sums` and `Accrual` lemmas (four of them after `lib_defs` rewrites a recursive range sum), and
one by the battery after `lib_defs`. The in-sample gain does not carry over to the held-out tasks.

## Retrieval

`harness/FinGoals.lean` elaborates every library, harvested, salvaged and demonstration module, and
the final candidates of the runs that import the library, with info trees, and prints each use of
a library theorem with the goal the innermost enclosing tactic ran on (hypotheses and target, as
Lean displays them). `uses.json`: 6124 uses in the library's own proofs
(3687 in a tactic, with a goal), 1582 in the demonstrations
(1520), 373 in the harvested and salvaged modules
(210), 50 in run candidates (38; only
the failed Compound runs name library theorems in their declarations without `sorry`; the
accepted Knight and Balancer runs that import the library name none).

Each query is one goal; the lemma used on it must be found. The old ranking is BM25 over the goal
text (`Index.search(goal, goal="")`), the new one the goal-aware ranking
(`Index.search(goal, goal=goal)`); the declaration being proved is left out of both, and the usage
prior (from the demonstrations, the harvested and salvaged modules and the run candidates, never
the library's own proofs) leaves out the query's own source file. The mixing weights were tuned
on the library's own proofs (grid in `retrieval.json`; chosen BM25 1.0, conclusion 1.0, prior 0.15,
the default) and the other sets are evaluation sets. Recall, old / new:

| set | uses | goals | at 1 | at 5 | at 10 |
|---|---:|---:|---:|---:|---:|
| library proofs (tuning) | 1722 | 679 | 0.157 / 0.203 | 0.408 / 0.494 | 0.519 / 0.616 |
| demonstrations | 1326 | 111 | 0.032 / 0.053 | 0.062 / 0.083 | 0.090 / 0.110 |
| harvested and salvaged lemmas | 107 | 55 | 0.103 / 0.159 | 0.290 / 0.383 | 0.383 / 0.477 |
| run candidates | 19 | 18 | 0.158 / 0.053 | 0.316 / 0.632 | 0.368 / 0.684 |

The goal-aware ranking finds more of the lemmas proofs used on every set at 5 and 10, and at 1 on
all but the run candidates, where 19 uses are too few to read much into (one fewer at rank 1, six
more within 5). The demonstrations are hard for both: 1,326 uses fall on 111 goals, many lemmas used
on the same large goal of a copied task model, of which a list of ten can hold few.

`search_library` in `agents/repair.py` now passes the obligation's statement as the goal
(`library_hints` sets it when it builds the obligation prompt; later searches reuse it), and a
query that reads as a statement is its own goal. Without a goal the ranking is BM25 as before.

## Reproduce

```
python3 harness/mine.py goals --set mining --results DIR      # goals-mining.jsonl
python3 harness/mine.py clusters results/feedback-library-1/goals-mining.jsonl
python3 harness/harvest.py run --unverified --results DIR      # lib/ProofForgeFin/Salvaged
python3 harness/mine.py kernels                                # kernels-full.json
python3 harness/mine.py open --set held-out --results DIR --base OLD_LIB --new lib --out ...
python3 harness/mine.py reprove --set held-out --results DIR --base OLD_LIB --new lib --out ...
python3 harness/fin_retrieval.py uses --results DIR && python3 harness/fin_retrieval.py prior
python3 harness/fin_retrieval.py eval --tune
python3 tests/test_feedback_library.py
```

`OLD_LIB` is the library sources of the commit before this work, extracted with
`fin_lib.materialize(commit, sha)`. Lean ran in the pinned image (`proofforge-lean:4.35.0`), one
or two containers at a time with 4 CPUs each.
