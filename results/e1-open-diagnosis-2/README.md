# Why A1 spent its budget on four permissions tasks in e1-test-open-2

In `results/e1-test-open-2` (Muse Spark Open, $3 and 3,600 s per run, code at 57d1ed5) A0 (`agents/baseline.py`) verified permissions-acl-b3, permissions-grants-b3 and permissions-grants-b4 for $0.32, $1.46 and $0.06, while A1 (`agents/repair.py --planner none`) stopped at the dollar cap on all three ($2.88, $2.81, $2.97) and on permissions-acl-b2 ($2.86), which neither arm completed. This note gives the cause on each from the recorded runs, the five changes made to the repair agent, and how to confirm them. No model was called. Lean was run only to replay recorded files and tactics.

The short answer: A1 fixed the definition in phase 0 against the property tests only, as a Boolean re-encoding of the specification, and then spent its budget proving requirements about that definition one dialog at a time, a definition its later phases were told not to change. A0, writing definition and proofs together, defined the code in the specification's terms from its first attempt. Two harness defects made it worse: every proof the tactic portfolio found in the run was lost when banked, and nothing kept budget for the whole-file phase, which is the only phase that may rewrite the definition. All four are fixed in general, with no task named.

The evidence is read from `events.jsonl`, `summary.json`, `ledger.json` and the `candidate_vNNN.lean` files of each run directory. Dollars are list dollars at $1.25, $0.15 and $4.25 per million uncached input, cached input and output tokens.

## Where the dollars went

| Task (A1) | Phase 0 | Phase 1 (one dialog per requirement) | Phase 2 (repeat) | Phase 3 (whole file) | Requests lost, charged at worst case | Final |
|---|---|---|---|---|---|---|
| permissions-acl-b3 | 2 calls, $0.03 | 108 calls, $0.72, 0 of 9 proved | 242 calls (3 rounds), $1.94, 2 of 9 | never reached | 1, $0.20 | 2 of 9 |
| permissions-grants-b4 | 4 calls, $0.03 | 96 calls, $0.89, 1 of 8 | 202 calls (3 rounds), $1.72, 4 of 8 | 1 attempt (23.9 KB file, did not compile) | 1, about $0.22 | 4 of 8 |
| permissions-grants-b3 | 2 calls, $0.02 | 81 calls, $0.77, 2 of 8 | 72 calls (1 round), $0.74, 2 of 8 | 20 attempts, $1.29, none compiled | 0 | 2 of 8 |
| permissions-acl-b2 | 2 calls, $0.02 | 104 calls, $0.79, 1 of 9 | 165 calls (3 rounds), $1.37, 8 of 9 | 5 attempts, $0.68 with 2 lost requests, none compiled | 2 | 8 of 9 |

| Task (A0) | Attempts | List $ | Outcome |
|---|---|---|---|
| permissions-acl-b3 | 11, accepted at the 11th | 0.32 | completed |
| permissions-grants-b4 | 4, accepted at the 4th | 0.06 | completed |
| permissions-grants-b3 | 47, accepted at the 47th | 1.46 | completed |
| permissions-acl-b2 | 28, judge accepted at the 28th | 0.86 | binary BUILD_FAILED (its `step` is `noncomputable`, decided by `Classical.propDecidable`) |

- Calls, not context, are the cost. A1 made 353, 304, 176 and 278 model calls against A0's 11, 4, 47 and 28. Per call, the dialog prompts were 13.5k tokens on average in phase 1 and 16k to 21k in phase 2, 89 to 93% of them cached; a dialog starts near 9.7k tokens and grows to 15k to 37k by its last turn. Output (reasoning included, 26 to 37% of it) was 43 to 51% of each run's dollars, cached input 16 to 26%, uncached input 18 to 33%, lost requests 0 to 15%.
- Phases 1 and 2 cost 175, 75, 77 and 34 calls per requirement proved (acl-b3, grants-b4, grants-b3, acl-b2). A0 needed 1.2, 0.5, 5.9 and 3.1 attempts per requirement.
- Repetition was not the problem: 310 snippets in acl-b3 were 308 distinct texts (243 and 237 in acl-b2, 269 and 267 in grants-b4, 145 and 145 in grants-b3). Every one of the 1,621 snippets rejected in the 30 A1 runs was answered with an error or a `sorry` in the returned text; none looks like a false rejection (not replayed with Lean; see below).
- No accepted candidate existed in any of the four runs, and no compiling version with more proved requirements than the final one was lost: the final files hold the most any compiling version held (2, 4, 2 and 8). What was lost were proofs Lean had found (next section): acl-b3 ended with `req_effects` open and grants-b3 with `req_others_unchanged` open, both proved by the portfolio at version 1.

## Cause on each task

### permissions-acl-b3

Phase 0 rewrote `decision` as a fold over Boolean `matchesB` and guarded `step` on `s.users.contains r.user && r.user != 0`; the tests passed and the nine phase-1 dialogs then used all 12 turns each and proved nothing ($0.72). Phase 2 ran three rounds because each proved something (2 requirements for $1.94), and the run reached the cap at $2.88 with the whole-file phase never started. A0's first attempt already read `if h : ValidQuery s r then let g := decide (Permitted s.entries r) ...`, the specification's own predicates, and its 11th attempt was accepted at $0.32; the portfolio, on A0's definitions with every proof removed, proves 5 of the 9 requirements by itself, against 1 on A1's phase-0 file. The one proof it found on A1's file (`req_effects`, at version 1) failed to bank, and 48 later turns ($0.22) did not find it again.

### permissions-grants-b4

The buggy candidate decides validity case by case with `contains`, `isAdmin` and `any`; phase 0 fixed the one-line bug (`u == r.target` instead of `u == r.target && q == r.role` on revoke) and kept that shape, so every requirement had to relate those Booleans to the specification's `ValidCommand`. Phases 1 and 2 took 298 calls and $2.61 for 4 of 8, 64 of those turns ($0.44) on `req_no_self_grant` and `req_others_unchanged`, which the portfolio had proved at version 3 and failed to bank. Phase 3 started with $0.33 and produced one 23.9 KB file that kept the Boolean guard. A0's first file was `if _h : ValidCommand s r then (.ok, { users := s.users, has := expectedHas s r }) else (.rejected, s)` with three one-line lemmas about it, accepted at its fourth attempt for $0.06.

### permissions-grants-b3

Same phase-0 shape as grants-b4; phase 1 proved 2 of 8 for $0.77, a phase-2 round proved nothing more ($0.74) and phase 2 stopped as designed. Phase 3 then had $1.29: 20 whole-file attempts, every one keeping the phase-0 Boolean guard, none compiling, at $0.061 per call (prompt 36.9k tokens, output 7.5k, files averaging 20.4 KB) against A0's $0.031 (23.7k, 3.8k, 8.5 KB). A0 defined `step` by one Boolean `validBool` with `validBool_true_iff : validBool s r = true ↔ ValidCommand s r` proved once and the specification's `expectedHas`, and needed 47 attempts in this run (3 attempts and $0.06 in e1-test-open-1, 3 and $0.13 in e1-test-1). The portfolio's proofs of `req_no_self_grant` and `req_others_unchanged` at version 1 were lost to banking; 28 turns ($0.22) went to them afterwards.

### permissions-acl-b2

Phase 0 again guarded on `s.users.contains r.user && r.user != 0`. Phase 2 made real progress, from 1 to 8 of 9 for $1.37, but `req_invalid_noop` (an invalid query changes nothing) took 42 snippets across phases 1 and 2, every one stuck on relating that guard to `¬ ValidQuery s r`; on A0's definitions the portfolio proves it outright. Phase 3 had $0.68: five 21.5 KB attempts at $0.097 per call (two of seven requests lost), the last of which switched to `if _h : ValidQuery s r`, none compiling. The final file has 8 of 9. A0's judge-accepted file decides `Permitted` with `Classical.propDecidable`, so its executable does not build; a definition in the specification's terms must stay computable, which phase 0's `run_tests` checks.

### Common to the four

1. **The definition is chosen against the tests and then locked.** Phase 0 asks only for passing tests, and every later dialog is told "Do not change `step` or anything already proved". On permissions-acl and -grants in e1-test-open-1, e1-test-open-2 and e1-test-1, A1 verified 11 of 11 runs whose phase-0 definition used the specification's predicates or functions and 4 of 10 whose definition used none (e1-test-1 ran Muse Spark 1.3; this is an association across runs, not an experiment). In e1-test-open-2 alone: 2 of 2 with, 1 of 5 without (grants-b2 the exception). The A1-only wins have it the other way: on ledgers-reversal-b1, -b2 and -b3, A1's phase-0 definition already used `ValidPost`, `findEntry` and `netOf`, phase 1 proved 7, 6 and 6 of 10 for $0.58 to $0.84, and A0 failed all three at $2.67 to $2.73.
2. **Every portfolio proof was lost.** `unfold_grind` and `grind_defs` are tactics of three and two lines. The batch file indented only the first line and the stored text carried the others at two spaces; `bank_text` indented every line again, so the banked proof had its later lines at four spaces and Lean read `intros` as an argument of the line above. In the 30 A1 runs the portfolio closed 29 goals in 15 runs and banked none (`summary.json` `portfolio.closed` is 0 everywhere); the model then spent $1.53 of turns on those goals. The same text is what the MCP tool `try_tactics` returns.
3. **No budget was kept for the whole-file phase.** Phases 1 and 2 have turn limits but no dollar limit. Phase 3 got $0, $0.33, $1.29 and $0.68.
4. **The whole-file phase kept the definition it was given.** Phase 3 runs A0's protocol on the current file, labelled "partly repaired". 20 of 20 attempts on grants-b3 and 1 of 1 on grants-b4 kept a Boolean guard instead of `ValidCommand` (some grants-b3 attempts wrote `decide (_ ∈ _)` where phase 0 had `contains`); acl-b2 switched to `ValidQuery` in its 5th and last attempt. A0 starts from the buggy file and wrote the definition in the specification's terms in its first attempt on acl-b3, grants-b3 and grants-b4.

## The questions asked

- **Was A0's approach available to A1?** In phase 0, yes (`write_solution`), but phase 0 ends at the first passing test run and its request said nothing about proofs. In phases 1 and 2, `replace_declaration` can replace `step` (acl-b3 replaced `decision` and `best` five times, two of them reverted), but the request forbids it. In phase 3, yes, and the model did not take it (point 4 above), on acl-b3 because phase 3 never ran.
- **Would a cheap first whole-file attempt have solved it?** For grants-b4, yes: A0 was accepted at its 4th attempt here and at its 3rd and 4th in the two earlier runs. Not for the others: acl-b3 needed 11 attempts, grants-b3 47. Simulated on the 113 paired A0 and A1 runs of e1-test-open-2, e1-test-open-1, e1-test-1 and e1-dev-2 (a probe of A0's first k attempts, then A1 with what is left, both as recorded): k = 4 adds grants-b4 for $0.10 more per run on average; k = 12 adds acl-b3, grants-b4 and e1-test-open-1 workflow-b1 and loses e1-test-open-1 ledgers-reversal-b1 and -b3, which needed more than $3 minus the probe. A probe was not adopted.
- **Would a context or cost discipline have solved it?** Context trimming would not: cached input was 16 to 26% of the dollars. A dollar discipline that keeps the whole-file phase funded when the per-requirement phases stall changes the outcome conditions on acl-b3 and grants-b4; it is the reserve below. Replayed on the recorded spend, it stops acl-b3 at $1.85 with 7 of 9 open and grants-b4 at $2.07 with 5 of 8 open, leaving $1.15 and $0.93 for phase 3, three to fifteen times what A0 spent on them.

## Changes

| Commit | Change | Evidence |
|---|---|---|
| 4b1ec56 | Portfolio tactics are stored without indentation and `proof_body()` indents every line, in the batch file (unchanged byte for byte) and the banked text alike, so the banked proof is the proof Lean checked; also fixes the text `try_tactics` returns | 29 goals closed, 0 banked in e1-test-open-2. Replayed with Lean: all 19 recorded failed bank attempts on the four tasks bank with the new text, and `#print axioms` shows each requirement proved |
| 89377e7 | Whole-file reserve, `--whole-file-reserve R` (default 0.5, 0 for off): while the per-requirement phases run, no dialog turn or planner call is made once list dollars reach cap - R * cap * open / n (`open` of `n` required theorems still `sorry` in their own text). With nothing proved they may spend half the cap; with all but one proved, all but R/n of it. Phase 3 is never stopped by it. Event `phase` `reserve`; `whole_file_reserve` in `summary.json` | acl-b3: $2.69 in phases 1 and 2, no phase 3. On the recorded spend of the A1 runs of e1-test-open-2, -open-1, e1-test-1, e1-dev-1, e1-dev-2, e1-test-glimmer-1 and implement-1, R = 0.5 stops three runs (acl-b3 twice, grants-b4), none of which verified, and no run that verified; R = 0.6 stops the same three |
| 38e3955 | Phase 0's request ends with `SPEC_SHAPED`: the definition will be proved about and not changed, so write it in the specification's terms where it provides them (decide validity with its predicate, with a `Decidable` instance, or with one Boolean function and one lemma equating it to the predicate; build results with its functions; stay computable) | The association in point 1. Replayed with Lean, nothing banked: the portfolio proves both validity requirements (valid input answered, invalid input a no-op) on A0's definitions of acl-b2, acl-b3 and grants-b4 and on none of A1's phase-0 files (6 of 8 against 0 of 8 over the four tasks; A0's grants-b3 definition needs its `_iff` lemma first) |
| b21ef39 | Phase 3's first request ends with `WHOLE_FILE_NOTE`: the earlier phases kept the definition fixed, it may be rewritten with the proofs, and how. `baseline.run` takes the note as an optional argument; A0 passes none | Point 4: 21 of 21 phase-3 files on grants-b3 and -b4 kept a Boolean guard |
| 74caeaa | `--spec-notes on|off` (default on): with off, the phase-0 and phase-3 requests are those of e1-test-open-2, for ablation | |
| 7044972 | `docs/ARCHITECTURE.md` | |

Nothing names a task or a family. A0 is unchanged: `agents/baseline.py` gained only the optional `note` argument, which A0 never passes, and its first request on three tasks is byte for byte the one of the code that ran e1-test-open-2 (sha256 of model, messages, purpose and options, in the test). The prompts of the per-requirement dialogs are unchanged.

## Tests

- `python3 tests/test_repair_spend.py` (new, fixtures in `tests/fixtures/repair_e1open2/` extracted from the recorded runs): the banked proof equals the batch proof for every portfolio entry, and the four recorded grants-b4 texts were indented twice; the reserve on eleven recorded A1 trajectories (stops acl-b3 at $1.85 with 7 open and grants-b4 at $2.07 with 5 open, no verified run), `dialog()` makes no model call once it is reached, phase 3 is never stopped by it; A0's first request unchanged; the phase-0 request carries `SPEC_SHAPED` in both modes and the obligation request does not; phase 3's first request ends with `WHOLE_FILE_NOTE` and, with `--spec-notes off`, equals the old one. With Lean: the recorded grants-b4 closure banks on the recorded candidate and is PROVED while the recorded text does not bank; the portfolio proves both validity requirements of acl-b3 on A0's definitions and neither on A1's phase-0 file. All pass.
- Existing tests, all passing: `tests/test_repair_verdicts.py` (with Lean; its fake whole-file run now accepts the `note` keyword), `tests/test_model_failures.py`, `tests/test_budget_controls.py`, `tests/test_implement_mode.py`, `tests/test_isolation.py`, `tests/test_feedback.py` (with Lean, including the portfolio tests).

## What remains unknown

- Whether Muse Spark Open follows the phase-0 note, and whether the requirements then close in phase 1 as they did on the runs whose definitions were already in the specification's terms. Only a model run shows it.
- Whether phase 3, with the reserve's $0.93 to $1.15 and the rewrite note, verifies acl-b3 and grants-b4. A0 needed $0.32 and $0.06 from the buggy file; A1's phase-3 calls cost 1.5 to 3 times A0's on these tasks because its files were 2 to 4 times larger, which a rewritten definition should shrink.
- A0's cost on the same task varies widely between runs (grants-b3: $0.06, $0.13, $1.46; acl-b3: $1.15, $0.32, a failure at $2.70), so one paired run per task decides little.
- The reserve value rests on three triggering runs. No recorded winner is stopped, but a run that would have won late in phase 2 above the limit would be.
- The snippet verdicts of the persistent Lean session (297 of 310 snippets in acl-b3) were not replayed with Lean in this round; the returned texts show an error or a `sorry` for every rejection.
- The queues runs of e1-test-open-2 (both arms at $0.15 to $0.35, the provider's billing refusals of addendum 1) were not analysed.

## How to confirm (not run)

1. No-model checks: `python3 tests/test_repair_spend.py` and the existing tests above.
2. A preregistered run after the current rerun ends, on the dev split first (the changes were made knowing these test tasks), then the 30 test tasks, both arms, the same model and caps. Primary outcome as before (completed, McNemar). Secondary, stated in advance: on the permissions tasks, the share of A1 phase-0 definitions that use the specification's predicates or functions (the classifier used here: specification names in the body of the required definitions), requirements proved after phase 1, `portfolio.closed` and banked portfolio proofs, reserve stops and the dollars phase 3 receives, dollars per completed repair, and that the ledgers-reversal tasks stay verified.
3. To attribute the effect, three A1 settings on the ten permissions and three ledgers-reversal tasks: all changes; `--whole-file-reserve 0`; `--spec-notes off` (the portfolio fix stays in all three, since it only adds proofs Lean already checked). Given A0's variance, three runs per task and setting on permissions-acl-b2, -acl-b3, -grants-b3 and -grants-b4, with A0 alongside (at most 4 x 4 x 3 x $3 = $144 at the caps).
