# Why A1 lost three tasks to A0 in e1-test-open-1

In `results/e1-test-open-1` (Muse Spark Open, $3 and 3,600 s per run) A1 (`agents/repair.py --planner none`) verified 24 of 30 tasks and A0 (`agents/baseline.py`) 21. A0 alone verified permissions-acl-b2, permissions-workflow-b1 and permissions-workflow-b3. This note gives the cause on each of the three from the recorded runs only, the changes made to the repair agent, and the evidence for each. No model was called and no measurement was run; Lean was run only to replay recorded snippets and files.

The run used `agents/repair.py` at commit 36fc8d3 (the sha256 in `config.json`). The defects below are in that version and were still in the repair agent at ed3bd49, where these changes start. Line numbers refer to `events.jsonl` of the A1 run directory.

## Where A1's budget went

| Task | Phase 0 | Phase 1 (one dialog per requirement) | Phase 2 (repeat) | Phase 3 (whole file) | Proved before phase 3 |
|---|---|---|---|---|---|
| permissions-workflow-b1 | $0.01 | $0.53, 5 of 9 proved | $0.30, 0 of 4 | $1.91, 47 attempts, none compiled | 5 of 9 |
| permissions-workflow-b3 | $0.01 | $0.58, 1 of 9 | $0.54, 0 of 8 | $1.67, 49 attempts, none compiled | 1 of 9 |
| permissions-acl-b2 | $0.01 | $0.48, 2 of 9 | $0.37, 0 of 7 | $1.92, 39 attempts, none compiled | 2 of 9 |

A0 verified the same tasks in 12 attempts ($0.31), 60 attempts ($2.38) and 63 attempts ($2.52). In all three A1 runs the last event is `restore last compiling version` with the byte count of the file that entered phase 3 (lines 549, 735 and 660: 5042, 2276 and 3222 bytes): not one whole-file attempt compiled. The six A1 phase-3 sessions in this run that failed all ended this way (21 to 49 attempts each); the nine that succeeded were accepted within 3 to 35 attempts.

## Cause on each task

### permissions-workflow-b1

1. Correct proofs refused for linter warnings. At line 52 (91 s) the model proved `req_invalid_noop`; Lean's only messages were `This simp argument is unused` warnings, and the orchestrated loop counted any warning as unclean (only the top-down loop accepted linter warnings). The same happened to `req_authorization` (line 61), to `req_single_doc` with four helper lemmas (line 79, 126 s) and again to `req_invalid_noop` in phase 2 (line 331). Replayed with Lean: the recorded final candidate with these two snippets added compiles, and `#print axioms` shows `req_invalid_noop` and `req_single_doc` without `sorryAx`. The run ended with both still `sorry`.
2. A proof with errors reported as compiling. At lines 242 and 252 try_snippet answered `snippet compiles with no errors or warnings` for a proof of `req_effects`; banking it failed and was reverted twice (writes at lines 241 and 251, `revert banked req_effects`), and the model, told nothing, sent the same code again. Replayed, the snippet has 5 errors (`unknown tactic` for `by_contra`, unsolved goals). The verdict was taken from the output that `judge.run` keeps, the last 4000 characters; the last error's goal state filled them, so no error header was left and the parser saw no message at all.
3. With 7 of 9 within reach after phase 1, the run entered phase 3 with 5 of 9 and spent $1.91 there without a compiling file.

### permissions-workflow-b3

1. The same linter rule refused proofs of `req_published_immutable` (line 175, 250 s), `req_audit_append_only` (lines 271, 297), `req_valid_succeeds` (line 366), `req_no_unpublish` (lines 512, 518) and others; 17 snippet results of this run were warnings only. Replayed with Lean, the recorded final candidate with the four proofs added compiles and `#print axioms` shows all four free of `sorryAx`. The run proved 1 of 9 (`req_authorization`) in phases 1 and 2; with these it would have had 5 of 9.
2. Five other warning-only results (three proofs of `req_no_unpublish` at 297 to 312 s, two of `req_effects` in phase 2) were truncation artifacts: their whole output (7,500 to 8,500 characters) has 4 to 8 errors whose headers fell outside the 4000-character tail, so the model saw only the end of a goal and some warnings.
3. Exploration snippets were banked into the candidate: `theorem dummy : True`, `#print Workflow.step` and `req_audit_append_only_dup` (lines 254 and 583) are in the final file and in every later prompt.

### permissions-acl-b2

1. No snippet verdict was wrong in this run (replayed: every recorded clean result is clean with the whole output). The per-requirement dialogs failed on their merits: phase 0 rewrote the decision with `List.max?` on depths of matching entries and kept the Boolean guard `s.users.contains r.user && r.user != 0`, and 16 obligation dialogs proved 2 of the 9 requirements about it (17 clean snippets out of 160, most of them `#check` and `example` explorations). A0's accepted file guards on the specification's `ValidQuery` and proves `_iff` lemmas linking its Boolean helpers to the specification's predicates.
2. The exploration was banked: `testIsPrefix`, `myMax?`, `foo`, `dummyX`, `test_lemma2`, `isPrefix_lemma_test`, `tmp1`, `tmp2` and `isPrefixOf_true_of_prefix2` were inserted (lines 237 to 569) with their trailing `#check` and `example` commands.
3. Phase 3 then had $1.92, less than the $2.52 A0 needed, and the model saw only the last 4000 characters of each failed build: for this definition, part of the last error's goal and no location for the others.

### Common to the three

- Phase 2 of A1 repeats the phase 1 dialog with the same prompt; in the three runs it made no progress (0 of 19 dialogs) for $0.30 to $0.54. It does make progress elsewhere (permissions-grants-b1: 4 of 6, workflow-b2: 6 of 11, ledgers-reversal-b3: 6 of 14), so it was not changed.
- Phase 3 runs A0's protocol on the repair session, whose saves move every required theorem to the end of the file; A0's `FileSession` saves files as written. Of the 88 A0 candidates the judge accepted under `results/`, 20 are changed by this reordering (their lines shift, so Lean's error lines do not match the file the model sent) and 2 would no longer compile (`results/e1-test-open-1/queues-ring-b2/A0` and `results/e1-test-1/queues-ring-b4/A0`, where a helper uses a required theorem).

## The six tasks only A1 verified

ledgers-reversal-b1, -b2, -b3 and queues-prio-b1 reached 9 of 10, 8 of 10, 9 of 10 and 7 of 8 required theorems through phases 1 and 2 and were accepted in phase 3 after 21, 3, 7 and 5 attempts; queues-ring-b3 and -b4 were accepted before phase 3. What made them work, per-requirement banking that leaves phase 3 a nearly complete file, is unchanged. Those runs also lost proofs to the same defects (ledgers-reversal-b1: 10 warning-only snippet results, ledgers-reversal-b3: 14 and 5 reverted banks), which the changes recover.

## The e1-dev-1 defect

In `results/e1-dev-1` the 12 failed A1 runs stopped after $0.39 to $0.88 of $3 (one recorded no spend): a failed phase 0 ended the session and there was no whole-file phase. Commit f8e0e6d made phase 3 run whenever the session is not accepted. In the current code `orchestrate()` calls `baseline.run` with up to 200 turns whenever `s.accepted` is false, whether phase 0 succeeded or not, and that loop ends only at acceptance, at the budget stop, or on an API error that is not transient (0, 429 and 5xx are retried). `test_whole_file_phase_runs_verbatim_whenever_not_accepted` in `tests/test_repair_verdicts.py` checks both paths. The `--loop free` mode has no phase 3, but no E1 arm uses it.

## Changes

| Commit | Change | Evidence |
|---|---|---|
| dea92c4 | try_snippet decides from Lean's whole output (written to a file and read back) and the exit status of `lean`, never from the 4000-character tail; a failed `lean` without a located error is not clean; each message shown is shortened on its own so every header stays visible (also in the persistent session's fast path) | workflow-b1 lines 242 and 252: 5 errors reported as clean; 61 of 129 distinct snippets of that run produced more than 4000 characters of output |
| 0fda254 | a snippet whose warnings all name a linter option is clean in every loop and in the fast path; `sorry` still blocks; deprecations neither block nor are shown | the refused proofs above; replayed with Lean, every recorded warning-only result without an error in its whole output is clean |
| 545999c | try_snippet names each declaration it did not bank and why; a reverted insertion is no longer reported as banked; banked chunks drop `#check`, `#print`, `#eval` and `example` | workflow-b1 lines 241 to 252; junk in the final files of workflow-b3 and acl-b2; 266 `#check` lines in A1 final files under `results/` |
| 7540269 | every compile of the repair session reports each error with its location (`build_digest`), at most 4000 characters, instead of the tail; A0's `FileSession` keeps the plain tail it was measured with | the 4000-character cap of `judge.run`; goal states of these definitions run to several thousand characters per error |
| 8b212f4 | phase 3 and the final restore save files exactly as written, as A0 does | 2 of 88 accepted A0 files broken and 20 shifted by the reordering |
| 76f54bd | tests and fixture (below); `docs/ARCHITECTURE.md` | |

No prompt was changed, and nothing is specific to a task or a family.

## Tests

- `python3 tests/test_repair_verdicts.py` (new): the recorded false clean is not clean and the recorded linter-only proofs are clean (fixture `tests/fixtures/repair_verdicts/workflow_b1_snippets.json`: the recorded code and result with Lean's whole output); the verdict rules; the build digest; exploration commands; banking notes; reordering and verbatim saves on the queues-ring-b2 A0 file; the phase order of `orchestrate()`. With Lean: the recorded snippets through `Session.try_snippet` on the recorded candidate (the `req_effects` proof is refused with its errors, the `req_invalid_noop` proof is banked and `#print axioms` shows it proved), and the queues-ring-b2 file fails to compile reordered and compiles as written. All pass.
- Existing tests, all passing: `tests/test_topdown.py` (with Lean, including the two runs to a verified Passport), `tests/test_feedback.py` (with Lean), `tests/test_lean_feedback.py` (with Lean), `tests/test_muse_tools.py` (with Lean), `tests/test_muse_snippet_imports.py` (with Lean), `tests/test_model_failures.py`, `tests/test_budget_controls.py`, `tests/test_implement_mode.py --quick`, `tests/test_fin_integration.py --quick`, `tests/test_isolation.py`, `tests/test_judge_scan.py`, `tests/test_wins.py`. `tests/test_server_controls.py` does not start here (no `fastapi` module), as before these changes. Two expectations were updated on purpose: the linter test now expects a clean snippet in every loop, and the fast path's count of blocking warnings no longer counts a deprecation.

## What a measured run has to show

- On workflow-b1 and workflow-b3 the recovered proofs would have put 7 and 5 of 9 requirements in the file before phase 3, which is where the A1-only tasks were won; whether the remaining ones close within the budget is not established by replay.
- On permissions-acl-b2 none of these changes repairs the per-requirement phase. The run may still need A0's whole budget in phase 3, and the gain rests on the build digest and the verbatim saves making whole-file attempts converge faster than A0's, which is unmeasured.
- Accepting linter-only snippets banks more proofs earlier on every task; the snippet verdict now costs one file read per call. A file that compiled only because the reordering fixed the model's order in phase 3 now fails, as it would for A0.
- The persistent session's fast path, on by default in the current code but absent from the run that was diagnosed, already read whole diagnostics; it now applies the same linter rule.
