# vyper-replication-1: preregistration

Written on 2026-11-01, on `main` at `d1627c6`, before any run of this experiment. Later changes go
into dated addenda at the end and never rewrite the sections above them.

## Question

On `rw-vyper-sqrt` (Vyper's `sqrt()` builtin, CVE-2025-26622, repair mode), does Muse Code with
ProofForge produce a verified repair more often than Muse Code alone, at equal caps?

## Why this experiment, and what it does not confirm

`results/hard-task-1` measured 5 runs per arm on two tasks. On `rw-vyper-sqrt` the `proofforge` arm
verified 5 of 5 and the `alone` arm 2 of 5 (one-sided Fisher p = 0.083, not significant; that
preregistration needed a difference of four). On `rw-oz-sqrt` neither arm verified (0 of 5 each).

This experiment repeats the Vyper measurement with fresh runs only. The task was chosen after
seeing those results, so the hard-task-1 runs are not part of the primary analysis: the primary
test uses the 20 runs of this experiment alone. `rw-oz-sqrt` is not repeated, because no run of
either arm verified it and a repetition with the same caps would measure two zeros.

## Task

`realworld/tasks/rw-vyper-sqrt`, unchanged since `66bc340`: locked manifest sha256
`ea5b5e443d8f028f5bd161c67e95a1ff2046fec2de44a43f04a7936e51622fb1`, five requirements
(REQ-SQRT-NOT-ABOVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-TOTAL, REQ-SQRT-NEG-REVERTS, REQ-DEPLOYED-LOOP),
start candidate the v0.4.0 code. Repair mode only.

## Arms and settings

Identical to `results/hard-task-1/PREREGISTRATION.md`, Addendum 2. Nothing is changed or tuned.

- `alone`: `agents/muse_code.py --arm alone` (MCP profile `lean`: `lean_build` only, no library).
- `proofforge`: `agents/muse_code.py --arm proofforge-full` (MCP profile `full`, the skill
  `.agents/skills/proofforge/SKILL.md`, ProofForgeFin vendored). No planner model in either arm.
- Muse Code 1.4.14 (build 1.4.14-R7309.1), `MUSE_NO_AUTO_UPDATE=1`, model
  `muse-spark-1.3-contributor` at medium effort.
- Caps per run: $10 at standard list prices (`integrations/muse/meter.py`) and 14,400 s of wall time.
- Code: the commit that adds this file. Outside `web/` and `results/` its tree is identical to
  `baa38a0`, the frozen commit of hard-task-1 (`git diff baa38a0 d1627c6 -- . ':!web' ':!results'`
  is empty). `lib/ProofForgeFin` tree `c7361632d0a109c0a95626655b4b6699a06412ee`, the same at both
  commits. Runs execute from a worktree checked out at this commit.

## Runs

- 10 runs per arm, 20 in total. The number is fixed; no extension, no early stopping.
- Driver: `integrations/muse/measure.py --parallel 2 --budget-usd 10 --budget-wall 14400
  --results results/vyper-replication-1`, with `PF_CONTAINER_SLOTS=1`, items in the order
  `rw-vyper-sqrt:alone:1 rw-vyper-sqrt:proofforge-full:1 rw-vyper-sqrt:alone:2
  rw-vyper-sqrt:proofforge-full:2 ...` up to run 10, so each concurrent pair is one run of each arm.
- No other model experiment runs on the host during the measurement.
- A run is set aside only for an infrastructure failure that leaves no Lean verdict (the Docker
  daemon not answering, the meter failing, the model endpoint refusing every request), decided
  without looking at the arm; it is rerun, and both are reported.

## Outcomes and analysis

- Primary outcome per run: VERIFIED by `bin/proofforge check` on the run's final candidate, judged
  outside the budget from the frozen commit; every VERIFIED Passport is reproduced with
  `bin/proofforge verify`.
- Primary analysis: one-sided Fisher exact test of H1 "the `proofforge` arm verifies more often than
  the `alone` arm" on the 2 x 2 table of this experiment's 20 runs, alpha 0.05.
- Significance thresholds, computed in advance for 10 runs per arm (p of the one-sided test):

  | `proofforge` verified | largest `alone` count with p < 0.05 | p at that count |
  |---|---|---|
  | 10 of 10 | 6 | 0.043 |
  | 9 of 10 | 5 | 0.016 |
  | 8 of 10 | 3 | 0.035 |
  | 7 of 10 | 2 | 0.035 |
  | 6 of 10 | 1 | 0.029 |
  | 5 of 10 | 0 | 0.016 |

- Secondary, reported without a confirmatory claim:
  - list dollars per verified run (all list dollars of an arm divided by its verified runs);
  - one-sided Mann-Whitney U test of "the `proofforge` arm spends fewer list dollars per run";
  - runs stopped by a cap, dollars charged, wall time, wall time to the first VERIFIED check where
    the run's events record it;
  - for each unverified run, whether its final candidate is REFUTED, UNRESOLVED or does not build,
    and the requirements proved in its last compiling version;
  - the same Fisher test on the 15 runs per arm of this experiment and hard-task-1 together, labelled
    as including the runs that motivated this experiment.

## Commitments

- No model call on `rw-vyper-sqrt` outside the 20 measured runs before they finish; no change to
  either arm, the task, the library or the judge.
- Every run is reported in `results/vyper-replication-1/README.md`, whatever its outcome, with its
  Passport, check and verify output.
