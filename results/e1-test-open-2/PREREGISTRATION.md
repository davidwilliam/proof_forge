# e1-test-open-2: preregistration

Written on 2026-11-01 on `main`, before any run of this experiment. Later changes go into dated
addenda at the end and never rewrite the sections above them.

## Question

On the 30 frozen E1 test tasks, does Meta's open-weight Muse Spark Open verify more tasks with the
ProofForge repair agent (A1) than with the compile-and-retry baseline (A0), at equal caps, with the
repair agent as improved after `results/e1-test-open-1`?

## What changed since e1-test-open-1

`results/e1-test-open-1` (commit `36fc8d3`): A1 24 of 30, A0 21 of 30; 6 tasks verified only by
A1, 3 only by A0 (permissions-acl-b2, permissions-workflow-b1, permissions-workflow-b3). The build
team studied those three runs (`results/e1-open-diagnosis/README.md`) and changed the repair agent
(commits `dea92c4` to `8b212f4` as merged on `main`):

- snippet verdicts come from Lean's whole output and exit status, not a 4,000-character tail that
  could hide every error header;
- a snippet with only linter warnings is accepted in every loop (`sorry` still blocks);
- `try_snippet` states what it did not bank, and exploration commands are not banked;
- each compile reports every error with its location;
- the whole-file phase compiles each file as the model wrote it.

The changes are general: no task, family or prompt change. A0 (`agents/baseline.py`) behaves as
in e1-test-open-1. The changes were made knowing these test tasks and A1's failures on them; the
comparison measures the repair agent including that work.

## Arms and settings

- A0: `agents/baseline.py`; A1: `agents/repair.py --planner none`; both through `eval/e1.py`.
- Model `meta-models/muse-spark-open-1026` (Baseten Model APIs).
- Caps per run: $3 at list prices and 3,600 s, as in e1-test-open-1.
- Tasks: the 30 test tasks bound by `results/test-freeze.json` (unchanged).
- Code: the commit that adds this file, run from a worktree checked out at it.
- Command: `eval/e1.py --label test-open-2 --split test --arms A0,A1 --model
  meta-models/muse-spark-open-1026 --budget-usd 3 --budget-wall 3600 --parallel 2 --batch-usd 200
  --require-clean`, `PF_CONTAINER_SLOTS=1`.

## Runs

- One run per arm per task, 60 runs. Fixed; no extension, no early stopping.
- A run lost to infrastructure with no verdict (no `summary.json`) is rerun once and both are
  reported.
- `results/frontier-2` may run on the host at the same time; `results/hard-task-2` does not start
  before this experiment ends.

## Outcomes and analysis

- Primary outcome per task and arm: completed (judge accepts the final candidate and its rebuilt
  executable passes 2,000 property cases, seed 1), as `eval/e1.py` scores it.
- Primary analysis: exact McNemar test on the 30 paired tasks, two-sided, alpha 0.05, as in
  e1-test-open-1; the direction is stated with it.
- Secondary: list dollars per completed repair; mean list dollars; budget stops; the three tasks
  A0 alone verified in e1-test-open-1; the six A1 alone verified; e1-test-open-1 and this
  experiment pooled per task (labelled as including the runs that motivated the changes).

## Commitments

- No change to either arm, the tasks or the judge after this commit until the runs finish.
- Every run is reported in `results/e1-test-open-2/README.md`, whatever its outcome.

## Addendum 1, 2026-11-01

From 20:36:06 local time the Baseten Model API answered every call with HTTP 402 ("please check
your current payment status."): the account's credit ran out. The runs had already been scored
when this addendum was written. Twelve tasks lost both runs to it, 24 runs in all. In 23 of them
the first model call returned 402 and the model never answered; permissions-workflow-b2 A1 got
the 402 at event 125 of 157. The harness still wrote `summary.json` for each, so the
infrastructure rule under Runs does not apply to them as written; this addendum extends it to
runs whose model calls the provider refused for billing.

- Lost runs: A0 and A1 on permissions-workflow-b2, permissions-workflow-b3, queues-bounded-b1,
  -b2, -b3, queues-prio-b1, -b2, -b3, queues-ring-b1, -b2, -b3, -b4.
- Once the account is funded, each is rerun once from a worktree at this experiment's code
  commit (57d1ed5), arms, model and caps unchanged: `eval/e1.py --label test-open-2-rerun
  --tasks <the twelve> --arms A0,A1 --model meta-models/muse-spark-open-1026 --budget-usd 3
  --budget-wall 3600 --parallel 2 --batch-usd 100 --require-clean`, `PF_CONTAINER_SLOTS=1`.
- The primary analysis uses the rerun for these 24 runs and the original runs for the other 36.
  The original 24 stay in `results/e1-test-open-2` and are reported with it.
- The other 36 runs are unaffected: every model call they made returned before 20:36:06, apart
  from transient timeouts and one 502 that the client retried.
- `results/hard-task-2` does not start before the rerun ends.
