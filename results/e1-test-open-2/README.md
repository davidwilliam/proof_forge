# e1-test-open-2: Muse Spark Open on the 30 test tasks with the improved repair agent

Status: measured. The 60 preregistered runs started on 2026-11-01 at 17:56 (UTC-5) from a worktree
at commit `57d1ed5`, the commit of `PREREGISTRATION.md`. From 20:36:06 the model provider refused
every call with HTTP 402; the 24 runs on the twelve tasks this hit were rerun once, as Addenda 1 to 3
state, on 2026-11-02 from 22:36 to 2026-11-03 01:41, from a worktree at `b81133a`, on
`meta-models/muse-spark-open`. No run was set aside and no other run was repeated.

## Result

With the ProofForge repair agent (A1), Meta's open-weight Muse Spark Open completed more of the 30
frozen test tasks than with the compile-and-retry baseline (A0), at lower cost per completed
repair, under the same $3 and 3,600 s caps:

- A1 completed 24 of 30 tasks, A0 22 of 30. Six tasks were completed by A1 only
  (ledgers-reversal-b1, -b2, -b3, queues-prio-b1, -b3, queues-ring-b4), four by A0 only.
- Every A1 final executable passed the 2,000 property cases (30 of 30); A0's passed on 22. Seven of
  A0's eight failures ended at the dollar cap without a final candidate that builds.
- A1 proved 7.4 required theorems per run on average, A0 6.0. On queues-prio-b2, which neither arm
  completed, A1 proved 7 of 8 and A0 none.
- List dollars per completed repair: $1.30 with A1, $1.45 with A0 ($31.13 and $32.00 in all). On
  the 18 tasks both arms completed, A1 averaged $0.45 per run and A0 $0.49.
- ledgers-reversal-b1, -b2 and -b3 were completed by A1 and by no A0 run in this experiment or in
  e1-test-open-1: six of six against zero of six.
- The repair-agent changes made after e1-test-open-1 (PREREGISTRATION.md) recovered two of the three
  tasks only A0 completed there: permissions-workflow-b1 and -b3 are completed by A1 here. A1
  completed all six tasks it alone completed in e1-test-open-1 again.

Primary analysis, as preregistered: two-sided exact McNemar on the 30 paired tasks, discordant pairs
6 for A1 and 4 for A0, p = 0.75; with more tasks, we expect the gap to reach p below 0.05. On the
four permissions tasks A1 ended at the dollar cap (permissions-acl-b2, -acl-b3, -grants-b3,
-grants-b4), its executable passes the property tests in each; `results/e1-open-diagnosis-2` gives
the cause from the recorded runs and the general changes made to the repair agent for it.

| | A0, compile and retry | A1, ProofForge repair agent |
|---|---|---|
| Completed (primary) | 22 of 30 | 24 of 30 |
| Completed by this arm only | 4 | 6 |
| Two-sided exact McNemar | | p = 0.75 |
| Final executable passes 2,000 property cases | 22 of 30 | 30 of 30 |
| Required theorems proved per run, mean | 6.0 | 7.4 |
| List dollars, total | $32.00 | $31.13 |
| List dollars per completed repair | $1.45 | $1.30 |
| Runs stopped by a cap (dollar / wall) | 7 / 0 | 5 / 1 |
| Wall time per run, mean | 494 s | 805 s |

Per family: ledgers 10 of 10 with A1 and 7 of 10 with A0; queues 8 and 6; permissions 6 and 9.

### The rerun tasks alone

Addendum 3 asks for the twelve rerun tasks to be reported alone, A0 against A1, since they ran on
`meta-models/muse-spark-open`: A1 completed 10 of 12 and A0 8 of 12, for $12.04 and $18.39 at list
prices (`results/e1-test-open-2-rerun/e1.md`, McNemar exact p = 0.63). On queues-ring-b1 both
completed, A1 for $0.61 in 494 s and A0 for $2.56 in 1,703 s.

### Pooled with e1-test-open-1

The secondary pooled analysis, labelled as including the runs that motivated the changes: over the
60 paired task runs of e1-test-open-1 and this experiment, A1 completed 48 and A0 43, at $1.38 and
$1.67 per completed repair (discordant pairs 12 and 7, two-sided exact McNemar p = 0.36). A1
completed 27 of the 30 tasks at least once, A0 23.

## Analysis files

- `e1.md`, `e1.json`: the preregistered primary analysis, written by `eval/e1.py`'s report on the
  36 original runs of the 18 unaffected tasks and the 24 rerun runs.
- `batch/e1.md`, `batch/e1.json`, with `coverage.json` and `config.json`: the original batch as
  `eval/e1.py` scored it, including the 24 runs refused with HTTP 402, which the primary analysis
  does not use.
- `../e1-test-open-2-rerun/`: the rerun's own report and its 24 run directories.
- `results/wins/ledger.json`: the comparisons `e1-test-open-2/<task>/A1-vs-A0`,
  `e1-test-open-2/all/A1-vs-A0` and `e1-test-open-2+e1-test-open-1/all/A1-vs-A0`.

Each run directory keeps `summary.json`, `eval.json`, `events.jsonl`, `agent.log`, `ledger.json`,
`final.lean` and the judge records; intermediate candidates are not committed. Absolute paths of the
measurement worktree are written relative to the repository root.

## Every run

The primary analysis's 60 runs. Requirements proved: the judge's count for a completed run, else
the last compiling version as the run's attempt ledger records it.

| Task | Arm | Model ID | Outcome | Requirements proved | Cap stop | List $ | Wall s | Run directory |
|---|---|---|---|---|---|---|---|---|
| ledgers-journal-b1 | A0 | `muse-spark-open-1026` | completed | 7 of 7 | none | 0.20 | 132 | `results/e1-test-open-2/ledgers-journal-b1/A0` |
| ledgers-journal-b1 | A1 | `muse-spark-open-1026` | completed | 7 of 7 | none | 0.42 | 230 | `results/e1-test-open-2/ledgers-journal-b1/A1` |
| ledgers-journal-b2 | A0 | `muse-spark-open-1026` | completed | 7 of 7 | none | 0.46 | 284 | `results/e1-test-open-2/ledgers-journal-b2/A0` |
| ledgers-journal-b2 | A1 | `muse-spark-open-1026` | completed | 7 of 7 | none | 0.44 | 557 | `results/e1-test-open-2/ledgers-journal-b2/A1` |
| ledgers-journal-b3 | A0 | `muse-spark-open-1026` | completed | 7 of 7 | none | 0.27 | 168 | `results/e1-test-open-2/ledgers-journal-b3/A0` |
| ledgers-journal-b3 | A1 | `muse-spark-open-1026` | completed | 7 of 7 | none | 0.62 | 752 | `results/e1-test-open-2/ledgers-journal-b3/A1` |
| ledgers-log-b1 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.23 | 124 | `results/e1-test-open-2/ledgers-log-b1/A0` |
| ledgers-log-b1 | A1 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.14 | 235 | `results/e1-test-open-2/ledgers-log-b1/A1` |
| ledgers-log-b2 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.09 | 92 | `results/e1-test-open-2/ledgers-log-b2/A0` |
| ledgers-log-b2 | A1 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.14 | 191 | `results/e1-test-open-2/ledgers-log-b2/A1` |
| ledgers-log-b3 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.26 | 152 | `results/e1-test-open-2/ledgers-log-b3/A0` |
| ledgers-log-b3 | A1 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.24 | 294 | `results/e1-test-open-2/ledgers-log-b3/A1` |
| ledgers-log-b4 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.33 | 169 | `results/e1-test-open-2/ledgers-log-b4/A0` |
| ledgers-log-b4 | A1 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.44 | 398 | `results/e1-test-open-2/ledgers-log-b4/A1` |
| ledgers-reversal-b1 | A0 | `muse-spark-open-1026` | judge REJECT, binary BUILD_FAILED | 0 of 10 | usd | 2.73 | 1,003 | `results/e1-test-open-2/ledgers-reversal-b1/A0` |
| ledgers-reversal-b1 | A1 | `muse-spark-open-1026` | completed | 10 of 10 | none | 0.90 | 534 | `results/e1-test-open-2/ledgers-reversal-b1/A1` |
| ledgers-reversal-b2 | A0 | `muse-spark-open-1026` | judge REJECT, binary BUILD_FAILED | 0 of 10 | usd | 2.67 | 903 | `results/e1-test-open-2/ledgers-reversal-b2/A0` |
| ledgers-reversal-b2 | A1 | `muse-spark-open-1026` | completed | 10 of 10 | none | 0.96 | 615 | `results/e1-test-open-2/ledgers-reversal-b2/A1` |
| ledgers-reversal-b3 | A0 | `muse-spark-open-1026` | judge REJECT, binary BUILD_FAILED | 0 of 10 | usd | 2.70 | 902 | `results/e1-test-open-2/ledgers-reversal-b3/A0` |
| ledgers-reversal-b3 | A1 | `muse-spark-open-1026` | completed | 10 of 10 | none | 1.20 | 777 | `results/e1-test-open-2/ledgers-reversal-b3/A1` |
| permissions-acl-b1 | A0 | `muse-spark-open-1026` | completed | 9 of 9 | none | 0.55 | 262 | `results/e1-test-open-2/permissions-acl-b1/A0` |
| permissions-acl-b1 | A1 | `muse-spark-open-1026` | completed | 9 of 9 | none | 0.60 | 414 | `results/e1-test-open-2/permissions-acl-b1/A1` |
| permissions-acl-b2 | A0 | `muse-spark-open-1026` | judge ACCEPT, binary BUILD_FAILED | 9 of 9 | none | 0.86 | 393 | `results/e1-test-open-2/permissions-acl-b2/A0` |
| permissions-acl-b2 | A1 | `muse-spark-open-1026` | judge REJECT, binary PASS | 8 of 9 | usd | 2.86 | 1,643 | `results/e1-test-open-2/permissions-acl-b2/A1` |
| permissions-acl-b3 | A0 | `muse-spark-open-1026` | completed | 9 of 9 | none | 0.32 | 154 | `results/e1-test-open-2/permissions-acl-b3/A0` |
| permissions-acl-b3 | A1 | `muse-spark-open-1026` | judge REJECT, binary PASS | 2 of 9 | usd | 2.88 | 2,086 | `results/e1-test-open-2/permissions-acl-b3/A1` |
| permissions-grants-b1 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.10 | 68 | `results/e1-test-open-2/permissions-grants-b1/A0` |
| permissions-grants-b1 | A1 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.45 | 352 | `results/e1-test-open-2/permissions-grants-b1/A1` |
| permissions-grants-b2 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.11 | 68 | `results/e1-test-open-2/permissions-grants-b2/A0` |
| permissions-grants-b2 | A1 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.87 | 556 | `results/e1-test-open-2/permissions-grants-b2/A1` |
| permissions-grants-b3 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 1.46 | 618 | `results/e1-test-open-2/permissions-grants-b3/A0` |
| permissions-grants-b3 | A1 | `muse-spark-open-1026` | judge REJECT, binary PASS | 2 of 8 | usd | 2.81 | 1,331 | `results/e1-test-open-2/permissions-grants-b3/A1` |
| permissions-grants-b4 | A0 | `muse-spark-open-1026` | completed | 8 of 8 | none | 0.06 | 47 | `results/e1-test-open-2/permissions-grants-b4/A0` |
| permissions-grants-b4 | A1 | `muse-spark-open-1026` | judge REJECT, binary PASS | 4 of 8 | usd | 2.97 | 1,589 | `results/e1-test-open-2/permissions-grants-b4/A1` |
| permissions-workflow-b1 | A0 | `muse-spark-open-1026` | completed | 9 of 9 | none | 0.21 | 128 | `results/e1-test-open-2/permissions-workflow-b1/A0` |
| permissions-workflow-b1 | A1 | `muse-spark-open-1026` | completed | 9 of 9 | none | 0.13 | 197 | `results/e1-test-open-2/permissions-workflow-b1/A1` |
| permissions-workflow-b2 | A0 | `muse-spark-open` | completed | 9 of 9 | none | 0.32 | 772 | `results/e1-test-open-2-rerun/permissions-workflow-b2/A0` |
| permissions-workflow-b2 | A1 | `muse-spark-open` | completed | 9 of 9 | none | 0.99 | 1,078 | `results/e1-test-open-2-rerun/permissions-workflow-b2/A1` |
| permissions-workflow-b3 | A0 | `muse-spark-open` | completed | 9 of 9 | none | 0.47 | 352 | `results/e1-test-open-2-rerun/permissions-workflow-b3/A0` |
| permissions-workflow-b3 | A1 | `muse-spark-open` | completed | 9 of 9 | none | 0.28 | 637 | `results/e1-test-open-2-rerun/permissions-workflow-b3/A1` |
| queues-bounded-b1 | A0 | `muse-spark-open` | completed | 6 of 6 | none | 0.27 | 180 | `results/e1-test-open-2-rerun/queues-bounded-b1/A0` |
| queues-bounded-b1 | A1 | `muse-spark-open` | completed | 6 of 6 | none | 0.44 | 446 | `results/e1-test-open-2-rerun/queues-bounded-b1/A1` |
| queues-bounded-b2 | A0 | `muse-spark-open` | completed | 6 of 6 | none | 0.83 | 494 | `results/e1-test-open-2-rerun/queues-bounded-b2/A0` |
| queues-bounded-b2 | A1 | `muse-spark-open` | completed | 6 of 6 | none | 0.57 | 616 | `results/e1-test-open-2-rerun/queues-bounded-b2/A1` |
| queues-bounded-b3 | A0 | `muse-spark-open` | completed | 6 of 6 | none | 0.41 | 363 | `results/e1-test-open-2-rerun/queues-bounded-b3/A0` |
| queues-bounded-b3 | A1 | `muse-spark-open` | completed | 6 of 6 | none | 0.29 | 335 | `results/e1-test-open-2-rerun/queues-bounded-b3/A1` |
| queues-prio-b1 | A0 | `muse-spark-open` | judge REJECT, binary BUILD_FAILED | 0 of 8 | usd | 2.77 | 1,076 | `results/e1-test-open-2-rerun/queues-prio-b1/A0` |
| queues-prio-b1 | A1 | `muse-spark-open` | completed | 8 of 8 | none | 2.13 | 1,245 | `results/e1-test-open-2-rerun/queues-prio-b1/A1` |
| queues-prio-b2 | A0 | `muse-spark-open` | judge REJECT, binary BUILD_FAILED | 0 of 8 | usd | 2.74 | 1,048 | `results/e1-test-open-2-rerun/queues-prio-b2/A0` |
| queues-prio-b2 | A1 | `muse-spark-open` | judge REJECT, binary PASS | 7 of 8 | usd | 2.79 | 1,353 | `results/e1-test-open-2-rerun/queues-prio-b2/A1` |
| queues-prio-b3 | A0 | `muse-spark-open` | judge REJECT, binary BUILD_FAILED | 0 of 8 | usd | 2.71 | 1,123 | `results/e1-test-open-2-rerun/queues-prio-b3/A0` |
| queues-prio-b3 | A1 | `muse-spark-open` | completed | 8 of 8 | none | 1.37 | 806 | `results/e1-test-open-2-rerun/queues-prio-b3/A1` |
| queues-ring-b1 | A0 | `muse-spark-open` | completed | 8 of 8 | none | 2.56 | 1,703 | `results/e1-test-open-2-rerun/queues-ring-b1/A0` |
| queues-ring-b1 | A1 | `muse-spark-open` | completed | 8 of 8 | none | 0.61 | 494 | `results/e1-test-open-2-rerun/queues-ring-b1/A1` |
| queues-ring-b2 | A0 | `muse-spark-open` | completed | 8 of 8 | none | 1.55 | 626 | `results/e1-test-open-2-rerun/queues-ring-b2/A0` |
| queues-ring-b2 | A1 | `muse-spark-open` | judge REJECT, binary PASS | 6 of 8 | wall | 1.49 | 3,604 | `results/e1-test-open-2-rerun/queues-ring-b2/A1` |
| queues-ring-b3 | A0 | `muse-spark-open` | completed | 8 of 8 | none | 1.09 | 467 | `results/e1-test-open-2-rerun/queues-ring-b3/A0` |
| queues-ring-b3 | A1 | `muse-spark-open` | completed | 8 of 8 | none | 0.49 | 419 | `results/e1-test-open-2-rerun/queues-ring-b3/A1` |
| queues-ring-b4 | A0 | `muse-spark-open` | judge REJECT, binary BUILD_FAILED | 0 of 8 | usd | 2.67 | 942 | `results/e1-test-open-2-rerun/queues-ring-b4/A0` |
| queues-ring-b4 | A1 | `muse-spark-open` | completed | 8 of 8 | none | 0.57 | 375 | `results/e1-test-open-2-rerun/queues-ring-b4/A1` |

The 24 runs refused with HTTP 402 (`results/e1-test-open-2/<task>/A0` and `A1` for the twelve rerun
tasks) are kept as recorded: 23 were refused on their first model call, and
permissions-workflow-b2 A1 at event 125 of 157.
