# frontier-2: preregistration

Written on 2026-11-01 on `main` at `2ffad5b`, before any run of this experiment. Later changes go
into dated addenda at the end and never rewrite the sections above them.

## Question

On the two real-world tasks that no measured run of any arm has verified, `rw-oz-sqrt` (OpenZeppelin
`Math.sqrt` v4.9.6 and the Aerodrome first deposit) and `rw-compound-comp` (Compound Proposal 62),
does Muse Code with ProofForge in its current state produce verified repairs, and more often than
Muse Code alone, at equal caps?

## What changed since those runs, and how it was made

Both tasks were measured before: `rw-oz-sqrt` 0 of 5 in each arm (`results/hard-task-1`);
`rw-compound-comp` verified by no run of Muse Code alone, Muse Code with ProofForge, the repair agent
with the planner, or the feedback capabilities (`results/muse-code-1`, `results/compound-1`,
`results/library-1`, `results/frontier-1`). After those failures the build team studied the run
transcripts and the tasks' reference proofs and changed ProofForge:

- library modules `ProofForgeFin.SqrtIter`, `ProofForgeFin.WordBridge`, `ProofForgeFin.NatSqrt`
  (commit `eafe3fc`) and `ProofForgeFin.Accumulator` (commit `3e0895f`): general mathematics with no
  task, protocol or codebase name, which state neither task's requirements. The build team wrote
  solutions of both tasks with these modules (91 lines against a 354-line reference for
  `rw-oz-sqrt`; 720 against 1,650 for `rw-compound-comp`), both VERIFIED; those solutions are not in
  the repository and are never in a run's workspace;
- the `proofforge-full` arm keeps its best compiling version, reports the required theorems proved
  at each build, continues a session from its progress, imports the library modules a snippet uses,
  and names the core replacement of a Mathlib tactic (commits `cdd96ca` to `8159985`).

The library was therefore written knowing these two tasks and the points where provers stopped. A
gap between the arms measures ProofForge including that work, and is reported that way. The `alone`
arm has none of it, as in every earlier measurement.

## Arms and settings

- `alone`: `agents/muse_code.py --arm alone` (Lean through `lean_build`, no library).
- `proofforge`: `agents/muse_code.py --arm proofforge-full` (MCP profile `full`, the skill,
  ProofForgeFin vendored).
- Muse Code 1.4.14, `MUSE_NO_AUTO_UPDATE=1`, model `muse-spark-1.3-contributor` at medium effort.
- Caps per run: $10 at list prices and 14,400 s.
- Code: the commit that adds this file, run from a worktree checked out at it. Library source tree
  and the `git_commit` of every run are recorded in each run's `summary.json`.

## Runs

- Repair mode, 10 runs per arm per task, 40 in total. Fixed; no extension, no early stopping.
- Starts after `results/vyper-replication-1` has finished (its preregistration excludes other model
  experiments on the host while it runs).
- Driver: `integrations/muse/measure.py --parallel 2 --budget-usd 10 --budget-wall 14400
  --results results/frontier-2`, `PF_CONTAINER_SLOTS=1`, items in the order `rw-oz-sqrt:alone:1
  rw-oz-sqrt:proofforge-full:1 rw-compound-comp:alone:1 rw-compound-comp:proofforge-full:1`, then
  the same for runs 2 to 10.
- A run is set aside only for an infrastructure failure that leaves no Lean verdict, decided
  without looking at the arm; it is rerun and both are reported.

## Outcomes and analysis

- Primary outcome per run: VERIFIED by `bin/proofforge check` on the run's final candidate, judged
  outside the budget from the frozen commit; every VERIFIED Passport reproduced with
  `bin/proofforge verify`. The final candidate is the one each arm's code selects.
- Primary analysis, per task: one-sided Fisher exact test, `proofforge` verifies more often than
  `alone`, alpha 0.025 per task (two tasks). With 10 runs per arm and 0 verified alone, p < 0.025
  needs at least 5 verified with ProofForge (p = 0.016); with 1 alone, at least 7 (p = 0.010).
- Secondary, without a confirmatory claim: pooled Fisher test over both tasks; list dollars per
  verified run; dollars charged; wall time; runs stopped by a cap; requirements proved in the final
  candidate (for `rw-compound-comp`, the three sequence bounds separately); REFUTED, UNRESOLVED or
  not building for each unverified run; which library modules each `proofforge` run imported.

## Commitments

- No model call on either task outside these runs before they finish; no change to either arm, the
  tasks, the library or the judge after this commit.
- Every run is reported in `results/frontier-2/README.md`, whatever its outcome.
