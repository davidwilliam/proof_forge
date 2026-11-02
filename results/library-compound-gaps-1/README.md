# library-compound-gaps-1: the frontier-3 runs on `rw-compound-comp`, and the changes they call for

In `results/frontier-3`, Muse Code with ProofForge verified `rw-compound-comp` (Compound Proposal
62) in 2 of 10 runs, the first verified repairs of this task. This directory reads the ten
`proofforge-full` runs from their committed records, says where the eight others spent their
budget and where they stopped, and records the changes to ProofForge built from that reading:
the `lean_build` output of the full toolset, the skill, and `ProofForgeFin`.

The changes were written knowing this task and the frontier-3 runs. No model was called. Their
effect on the verified rate is not measured here; a run of the same setup (frontier-4) measures
it.

## Result

* What separated the verified runs from the others was the first phase, not the library
  argument. The two verified runs proved the five per-call requirements at $2.83 and $3.33 (list)
  and then needed $3.41 and $3.69 more for the three bounds over runs of operations with
  `ProofForgeFin.Accumulator.Market`. Six of the eight other runs never got to the `Market`
  argument: five did not finish the per-call requirements within the $10 cap and one finished
  them only in its final file. The two that did (proofforge-full-3 and -7) reached them at $4.62
  and $5.02 and stopped at the cap with the case analysis of `exec` half written. Of the $71.32
  the eight runs spent, $65.17 went to the phase before the `Market` argument.
* Three runs (1, 2, 4) spent 69 to 82 percent of their budget editing the file through streaks of
  10, 10 and 21 failed builds in a row; the verified runs never had more than two. In those
  streaks the model often could not see where the error was: `lean_build` returned the last
  4,000 characters of Lean's output, and 90 of the 138 failed builds of the eight runs began
  inside a message, without the position of the first error.
* Every run wrote list glue the library did not have: all ten proved their own `modify_congr`,
  eight their own "a property of every account holds of the account read by position", and the
  two verified runs spent 89 and 146 lines on the start of the argument (the invariant and the
  potential at the upgrade).

Changes, on branch `compound-gaps-1`:

| Change | What | Evidence it answers |
|---|---|---|
| `lean_build` (full toolset) | Lean's output read whole (400,000 characters) and cut from the end: the first errors whole, each later message by its first line; the same for `try_snippet` and `check_candidate`'s `lean_errors`. From the third failed build in a row, the result names the declarations with errors and the `check_snippet_fast` route. The `lean` and `proofforge` toolsets are unchanged. | 90 of 138 failed builds began inside a message; $25.44 of the eight runs' $71.32 went to streaks of three or more failed builds |
| Skill, step 4 | When the specification gives a call's result in closed form, write the call as `if <preconditions> then some <that form> else none` with the specification's definitions; a line-by-line port needs an equation lemma per call first | five runs never finished the per-call requirements; the only run whose code used the specification's definitions finished them first (9.7 minutes) |
| Skill, steps 7 and 8 | follow a library module's recipe when one fits; fix a failed build from its first error; what the streak note asks | the streaks above; the recipe below |
| `ProofForgeFin.Ledger` | `getD_of_forall`, `modify_congr`, `getD_modify_of_keeps` | written by 8, 10 and 3 runs |
| `ProofForgeFin.Accumulator.Market` | `Clock.reinit`, `reinitStart`, `inv_reinit`, `owed_reinit_le'`, `pot_reinit_le`, `potOf_reinit_le`; `Clock.catchUp₁_mk`, `catchUp₂_mk`, `advance_mk`; the module doc's recipe as templates, step by step | the start took 89 and 146 lines in the verified runs; constructors written through `M` (`M.Act.moves`, `M.Reach.refl`) failed with "Invalid field" in four runs; the settlement lemmas and `exec` cases where runs 3 and 7 stopped |

A candidate written with the changed library (outside the repository, not committed) is
VERIFIED with 260 lines, against 306 for the same candidate written with the library before the
change.

## Every run

Figures from `diagnose.py` (committed records only). "Per-call done": the first `lean_build` that
proved all five per-call requirements (minutes from the first model call, list dollars of the
calls made by then). "`Market` from": the first snippet with `Market` glue (`M.Settle`, `M.Act`,
`M.Inv`, `Market.Reach` and the like). Requirements: CS calls succeed, SH supply hook, BH borrow
hook, CL claim, SP set speeds, RB rewards bounded, AB account bounded, NB no backdated rewards.

| Run | Proved at the end | List dollars, minutes | Per-call done | `Market` from | Failed builds (began inside a message) | Longest failed streak, dollars in streaks of 3+ | Snippets |
|---|---|---|---|---|---|---|---|
| proofforge-full-1 | CS SH BH CL (4) | $9.56, 25.0 | no | no | 32 (27) | 10, $7.68 | 43 |
| proofforge-full-2 | SH BH CL (3) | $9.58, 27.3 | no | an edit at the end | 31 (10) | 10, $6.62 | 44 |
| proofforge-full-3 | CS SH BH CL SP (5) | $7.22, 39.3 | 25.4 min, $4.62 | 29.0 min, $5.27 | 2 (0) | 1, $0 | 86 |
| proofforge-full-4 | none (0) | $8.09, 14.2 | no | no | 21 (20) | 21, $6.62 | 24 |
| proofforge-full-5 | all 8, VERIFIED | $6.70, 49.2 | 23.5 min, $2.83 | 27.2 min, $3.30 | 2 (1) | 1, $0 | 89 |
| proofforge-full-6 | SH BH CL SP (4) | $9.60, 38.0 | no | no | 26 (19) | 9, $2.27 | 36 |
| proofforge-full-7 | CS SH BH CL SP (5) | $8.57, 53.1 | 34.3 min, $5.02 | 35.4 min, $5.08 | 4 (1) | 3, $0.99 | 114 |
| proofforge-full-8 | CS SH BH CL SP (5) | $9.11, 29.7 | in the final file only | no | 16 (11) | 3, $1.26 | 66 |
| proofforge-full-9 | all 8, VERIFIED | $7.41, 18.6 | 9.7 min, $3.33 | 10.3 min, $3.50 | 4 (4) | 2, $0 | 53 |
| proofforge-full-10 | SH BH CL (3) | $9.59, 39.9 | no | no | 6 (2) | 1, $0 | 123 |

Every run read `Market.lean`, eight of them all 1,308 lines. `search_library` was called 7 times
in the ten runs; the runs looked for library lemmas with `grep` and `sed` on the
vendored sources. Every run started from the port of the deployed code it was given, fixed the
start condition (`>` to `>=`) in its first two minutes and kept the port's structure; run 9 also
rewrote the two distribution functions with the specification's definitions.

## Where each run stopped

Line numbers are lines of the run's `mcp-calls.jsonl` (each line one tool call with its result as
the model received it, up to 4,000 characters).

* **proofforge-full-1** (4 of 8). From minute 3.9 it built the file after almost every edit of
  the comptroller's helpers (`upd_supply_some`, `dist_*_some`) and the per-call proofs: 32 of its
  36 builds failed, in streaks of 7, 10, 9 and 6. The result at line 19 begins `ialIndex ... in
  the application @ite`, the end of a message whose position was cut off, and 27 of the 32 failed
  builds began that way. Four requirements at minute 19.5 ($7.25); the rest went to
  `req_set_speeds` (the two-phase speed update against `SpeedsSet`), open at the cap.
* **proofforge-full-2** (3 of 8). Hooks and claim by minute 15.6 ($4.58). Then ten failed builds
  of `req_set_speeds` ending in `No goals to be solved` at the same places of the proof (lines 66
  to 91), with restores of the best version between them, and attempts at `req_calls_succeed`. It
  defined `M` and the `catchUp` bridge in its last minutes.
* **proofforge-full-3** (5 of 8). The five per-call requirements at minute 25.4 ($4.62), built
  in snippets (86) with nine builds. It then wrote the reading `M`, the two settlement lemmas and
  the cases mint, redeem, transfer, borrow and repay of `exec` (155 lines added at minute 38.7),
  after an `Invalid field moves` and an `Invalid field refl` error (lines 82 and 84:
  `M.Act.moves`, `M.Reach.refl`). It stopped at the cap ($7.22, the next request's worst case
  would have passed $10) with the cases claim, set speeds, advance and drip, the start and the
  three bounds to go.
* **proofforge-full-4** (0 of 8). Wrote about 550 lines into the file in its first four minutes
  (the comptroller's helpers and all five per-call proofs) and never had it compile again: 21
  failed builds in a row (lines 31 to 51), 20 of them beginning inside a message. The best
  compiling version proved nothing, so restoring it would have discarded everything; it never
  did.
* **proofforge-full-5** (VERIFIED). Per-call requirements at $2.83, the `Market` argument from
  $3.30 to $6.24 (including 89 lines for the start), accepted at $6.70.
* **proofforge-full-6** (4 of 8). Supply, borrow, claim and set speeds by minute 15.8 ($4.42),
  then `req_calls_succeed` (the second hook of a claim succeeds after the first) for the remaining
  $5.18: seven failed builds at lines 86 to 92, each `No goals to be solved` at lines 407 to 412
  of its file, two restores, open at the cap.
* **proofforge-full-7** (5 of 8). The five per-call requirements only at minute 34.3 ($5.02),
  after 89 snippets. It wrote `M`, the settlement lemmas and part of `exec_act`, hit
  `Invalid field moves` (line 113), then parse errors it could not place (`unexpected token 'at'`
  at line 120, `unexpected token 'show'` at lines 121 and 122) and inspected its file byte by byte
  with `od -c`; it stopped at the cap ($8.57).
* **proofforge-full-8** (5 of 8). Four requirements by minute 18.2 ($4.99), then
  `req_calls_succeed` until the cap; the last version on disk proves it, no `Market` glue.
* **proofforge-full-9** (VERIFIED). At minute 1.9 it rewrote the two distribution functions of
  the port with the specification's `accrualStart` and `creditFor` and the per-account update in
  the specification's form (`a.supply` inside the update), and had the five per-call
  requirements at minute 9.7 ($3.33). The `Market` argument took $3.50 to $7.02 (146 lines for
  the start), accepted at $7.41.
* **proofforge-full-10** (3 of 8). Hooks and claim by minute 20.6 ($4.92), then
  `req_set_speeds` and `req_calls_succeed` in 123 snippets in all; set speeds still failing at the
  cap (line 145, a result again beginning inside a message).

## Failure patterns, by the number of runs they cost

1. **The per-call requirements of a ported implementation outlasted the budget** (runs 1, 2, 4,
   6, 8, 10; 6 runs). The requirements state each call's result in closed form; every run kept the
   port of the deployed code (`Option` binds, `subChecked`, `fraction`, local `let`s, a two-phase
   speed update), so every requirement first needed an equation from the port to that form. The
   hard ones: `req_set_speeds` (runs 1, 2, 10) and `req_calls_succeed`, the second hook of a claim
   at the state the first one left (runs 2, 6, 8, 10). The skill's new step 4 answers it.
2. **Editing the file through streaks of failed builds** (runs 1, 2, 4, 6, 7, 8; 6 runs, of which
   1, 2 and 4 lost most of their budget there). The verified runs and runs 3 and 7 worked
   declarations out in snippets and built the file between them (7 to 13 builds against 19 to 48
   in the six others). The streak note of `lean_build` and step 8 of the skill answer it.
3. **Build output without the first error's position** (7 of the 8 runs; 90 of their 138 failed
   builds, 27 of 32 in run 1, 20 of 21 in run 4, 19 of 26 in run 6). `lean_build` now keeps the
   first errors.
4. **The `Market` argument not finished in the budget** (runs 3, 7; 2 runs): the settlement lemmas
   and the case analysis of `exec` were being written when the cap came; neither had started the
   start of the argument. The recipe templates, `inv_reinit`, `pot_reinit_le` and
   `potOf_reinit_le` shorten exactly these parts; `M.Act.moves`, `M.Reach.refl` and the like,
   which do not elaborate, cost runs 3, 5, 7 and 9 one or two failed snippets each.
5. **List glue rewritten in every run** (10 runs, a few dollars at most each): `modify_congr`,
   the property of an account read by position, a field a change keeps. Now in `Ledger`.

No run was stopped by a statement mismatch, a forbidden construct or a kernel rejection; every
UNRESOLVED Passport is `sorry` in the required theorems.

## The changes

### `lean_build`, `try_snippet` and `check_candidate` in the full toolset

`judge.run` keeps the last 4,000 characters of a command's output, and the MCP server returned
that tail. `judge.run` and `judge.in_container` now take `keep` (default 4,000, unchanged for
every other caller); the full toolset reads 400,000 characters and passes Lean's output through
`clip_lean`, which keeps messages whole from the first while they fit and names every later one by
its first line. From the third failed build of the candidate in a row, `lean_build` adds a line
naming the declarations with errors (with the line of each first error) and asking to put `sorry`
in their place and work them out with `check_snippet_fast`. The `lean` toolset of the Muse-alone
arm and the `proofforge` toolset return what they returned before. `check_snippet_fast` already
showed the first message in 672 of its 678 results and is unchanged.
`tests/test_muse_build_output.py` covers the cut, the toolsets, the note and the frontier-3
counts.

### The skill

A new step 4, "Write the fix in the specification's terms": when the specification gives a call's
result in closed form, write that call as `if <preconditions> then some <that form> else none`
with the specification's definitions, the corrected condition where the bug was; a line-by-line
port needs one equation lemma per call to that form before any requirement. Step 7 points to a
library module's recipe when one fits; step 8 asks to fix a failed build from its first error and
says what the streak note asks. The workspace `AGENTS.md` carries the first point. Both forms of
the fix are judged the same way; the skill names the cost of the port, it does not forbid it.

### `ProofForgeFin`

`ProofForgeFin.Ledger`: `getD_of_forall`, `modify_congr`, `getD_modify_of_keeps`.
`ProofForgeFin.Accumulator.Market`: `Clock.reinit` and `reinitStart` (a start where rewards begin
on the sides that never had any: each index still at 0 set to `init`, its last update moved to
now), `inv_reinit`, `owed_reinit_le'`, `pot_reinit_le`, `potOf_reinit_le` (the invariant and both
potential bounds there, from facts about the clock before), `Clock.catchUp₁_mk`,
`Clock.catchUp₂_mk`, `Clock.advance_mk` (for `simp` on a clock written by its fields), and the
module doc's "Using the module" rewritten as templates, step by step, with the bridges that hold
by `rfl`, the constructor names that elaborate, and the start bound stated before the `exact` that
uses it (written inside it, Lean can run out of heartbeats unifying it with the requirement, as it
did on the scratch candidate). No task, protocol or codebase is named. 12 theorems and 2
definitions.

## Checks

* Kernels: the 448 constants of `ProofForgeFin.Ledger` and `ProofForgeFin.Accumulator.Market`
  with the additions (278 theorems) are accepted by the six kernels of
  `lake comparator --paranoid` (Lean paranoid, lean4lean, nanoda, con-leche, con-ron, Lean
  default) and `leanchecker` replays both modules (`kernels.json`, from
  `harness/fin_kernels.py --modules ProofForgeFin.Ledger ProofForgeFin.Accumulator.Market`;
  library source tree `f3c7b22fb8a75007ef4486cfa33b5c2543962070ab9ce0bff494d708491c46a2`, judge
  image `sha256:7d5b583a0fe4`). A full run of `tests/test_fin_kernels.py` with the additions
  exports 10,909 safe constants of the library and its demonstrations, which all six kernels
  accept, and `leanchecker` exits 0.
* `tests/test_fin_lib.py` (the library and the demonstrations build, the axiom audit reports no
  violation), `tests/test_fin_integration.py` (14 tests, with Lean), `tests/test_fin_kernels.py`,
  `tests/test_muse_build_output.py`, `tests/test_muse_keep_best.py`,
  `tests/test_muse_hint_diffs.py`, `tests/test_muse_tools.py`, `tests/test_muse_mcp.py`,
  `tests/test_muse_tool_arguments.py`, `tests/test_muse_core_tactics.py`,
  `tests/test_muse_session_end.py`, `tests/test_muse_runner.py`,
  `tests/test_muse_snippet_imports.py`, `tests/test_muse_seen_versions.py`,
  `tests/test_container_view.py` and `tests/test_feedback_library.py` pass; `cd web && npx vitest
  run` passes (199 tests).
* Counts: 2,051 theorems and 478 definitions in 82 files (from 2,039 and 476), in `README.md`,
  `lib/README.md` and `web/lib/contribution.ts`; `web/public/evidence.json` and
  `web/public/llms.txt` regenerated with `node web/scripts/evidence.mjs`.
* Scratch candidate. A candidate for `rw-compound-comp` written with the changed library (the
  distribution in the specification's terms, the per-call requirements by unfolding, the three
  bounds with `Market`; outside the repository, not committed) is VERIFIED, 8 of 8, six kernels,
  2,001 property cases, with 260 lines (Passport
  `340a7846a152da1904fd4a50b5e17edd9d1229c4690fa50bf4b9805876717785`, library source tree
  `f3c7b22fb8a75007`, reproduced by `bin/proofforge verify`). The same candidate written with
  the library before the change, in the same session, is VERIFIED with 306 lines: the part after
  the per-call requirements takes 141 lines instead of 185, and the start 14 instead of 41. Both
  were written by the build team, which knows the task; the verified frontier-3 runs had 985 and
  1,518 lines.

## Not resolved

* The effect on the verified rate is not measured; frontier-4 does that, against the same
  preregistered setup.
* The skill's step 4 changes the shape of the fix the model is likely to write (the call
  written with the specification's definitions rather than a port of the deployed code). The
  judge accepts either, and the property tests check the executable either way.
* `lib/ProofForgeFin/Ledger.lean` and `lib/ProofForgeFin/DeFi/Rewards.lean` already named a
  protocol and its proposals in comments and doc strings before this change; the additions here
  name none, and those earlier mentions are unchanged.
* The cost of reading the library is not addressed: eight runs read all of `Market.lean` (about
  65,000 characters) at the start, and it stays in the input of every later request.

## Files

| File | What |
|---|---|
| `diagnose.py` | the per-run figures above, from the committed run records (`--json` for all fields) |
| `kernels.json` | six kernels and `leanchecker` on `ProofForgeFin.Ledger` and `ProofForgeFin.Accumulator.Market` |
