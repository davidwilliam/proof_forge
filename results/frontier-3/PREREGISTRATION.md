# frontier-3: preregistration

Written on 2026-11-02 on `main` at `a736621`, before any run of this experiment. Later changes go
into dated addenda at the end and never rewrite the sections above them.

## Question

On `rw-compound-comp` (Compound Proposal 62), which no measured run of any arm has verified, does
Muse Code with ProofForge produce verified repairs once the library has
`ProofForgeFin.Accumulator.Market`, and more often than Muse Code on its own, at equal caps?

## What changed since frontier-2, and how it was made

In `results/frontier-2` every one of the 10 ProofForge runs proved the same 5 of 8 requirements and
stopped at the $10 cap without proving `req_rewards_bounded`, `req_account_bounded` and
`req_no_backdated`; the 10 runs on their own proved at most 5 of 8. The build team read those runs
and wrote `ProofForgeFin.Accumulator.Market` (commit `a7eece9`): general mathematics over states read
as two-sided reward markets, with no task, protocol or codebase name, that does not state the
task's requirements. A solution written by the build team with it is VERIFIED (337 lines against
1,138 in the reference); it is not in the repository and never in a run's workspace.

The module was therefore written knowing this task and the points where the frontier-2 runs
stopped. A gap between the arms measures ProofForge including that work, and is reported that way.
The `alone` arm has none of it, as in every earlier measurement. No other part of either arm
changed since `995ee6e`.

## Arms and settings

- `alone`: `agents/muse_code.py --arm alone` (Lean through `lean_build`, no library).
- `proofforge`: `agents/muse_code.py --arm proofforge-full` (MCP profile `full`, the skill,
  ProofForgeFin vendored).
- Muse Code 1.4.14, `MUSE_NO_AUTO_UPDATE=1`, model `muse-spark-1.3-contributor` at medium effort.
- Caps per run: $10 at list prices and 14,400 s.
- Code: the commit that adds this file, run from a worktree checked out at it. Library source tree
  and the `git_commit` of every run are recorded in each run's `summary.json`.

## Runs

- Repair mode, 10 runs per arm, 20 in total. Fixed; no extension, no early stopping.
- Driver: `integrations/muse/measure.py --parallel 2 --budget-usd 10 --budget-wall 14400
  --results results/frontier-3`, `PF_CONTAINER_SLOTS=1`, items in the order
  `rw-compound-comp:alone:1 rw-compound-comp:proofforge-full:1`, then the same for runs 2 to 10.
- `results/e1-test-open-2-rerun` (Muse Spark Open on Baseten) may run on the host at the same time;
  `results/hard-task-2` does not start before this experiment ends.
- A run is set aside only for an infrastructure failure that leaves no Lean verdict, decided
  without looking at the arm; it is rerun and both are reported.

## Outcomes and analysis

- Primary outcome per run: VERIFIED by `bin/proofforge check` on the run's final candidate, judged
  outside the budget from the frozen commit; every VERIFIED Passport reproduced with
  `bin/proofforge verify`. The final candidate is the one each arm's code selects.
- Primary analysis: one-sided Fisher exact test, `proofforge` verifies more often than `alone`,
  alpha 0.05. With 10 runs per arm and 0 verified alone, p < 0.05 needs at least 4 verified with
  ProofForge (p = 0.043).
- Secondary, without a confirmatory claim: list dollars per verified run; dollars charged; wall
  time; runs stopped by a cap; requirements proved in the final candidate, with the three sequence
  bounds separately; REFUTED, UNRESOLVED or not building for each unverified run; whether each
  `proofforge` run imported `ProofForgeFin.Accumulator.Market`; frontier-2 and this experiment's
  `alone` runs pooled (labelled as such).

## Commitments

- No model call on this task outside these runs before they finish; no change to either arm, the
  task, the library or the judge after this commit.
- Every run is reported in `results/frontier-3/README.md`, whatever its outcome.
