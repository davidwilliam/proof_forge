# frontier-4: preregistration

Written on 2026-11-02 on `main` at `d2c68f5`, before any run of this experiment. Later changes go
into dated addenda at the end and never rewrite the sections above them.

## Question

On `rw-compound-comp` (Compound Proposal 62), does Muse Code with ProofForge verify the repair more
often than Muse Code on its own, at equal caps, after the changes built from the frontier-3 runs?
And does it verify more often than the ProofForge arm of frontier-3 (2 of 10)?

## What changed since frontier-3, and how it was made

`results/library-compound-gaps-1` read the ten `proofforge-full` runs of `results/frontier-3` from
their committed records and built three changes (branch `compound-gaps-1`, merged at `d2c68f5`):

- `lean_build`, `try_snippet` and `check_candidate` of the `full` toolset read Lean's output whole
  and keep the first errors; from the third failed build in a row the result names the
  declarations with errors and the `check_snippet_fast` route. The `lean` toolset of the `alone`
  arm returns what it returned before.
- The skill: a new step 4 (write the fix in the specification's terms), a library module's recipe
  when one fits, a failed build fixed from its first error.
- `ProofForgeFin`: three list lemmas in `Ledger`; in `Accumulator.Market` a start where rewards
  begin on sides that never had any, its invariant and potential bounds, `simp` lemmas for clocks
  written by their fields and the module's recipe as templates. No task, protocol or codebase
  name; 12 theorems and 2 definitions, accepted by the six kernels and `leanchecker`.

The changes were written knowing this task and where the frontier-3 runs stopped. A gap between
the arms measures ProofForge including that work, and is reported that way. The `alone` arm has
none of it; no part of it changed since frontier-3.

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
  --results results/frontier-4`, `PF_CONTAINER_SLOTS=1`, items in the order
  `rw-compound-comp:alone:1 rw-compound-comp:proofforge-full:1`, then the same for runs 2 to 10.
- Starts after `results/hard-task-2` ends. `results/e1-test-open-2-rerun` (Muse Spark Open on
  Baseten) may run on the host at the same time.
- A run is set aside only for an infrastructure failure that leaves no Lean verdict, decided
  without looking at the arm; it is rerun and both are reported.

## Outcomes and analysis

- Primary outcome per run: VERIFIED by `bin/proofforge check` on the run's final candidate, judged
  outside the budget from the frozen commit; every VERIFIED Passport reproduced with
  `bin/proofforge verify`. The final candidate is the one each arm's code selects.
- Primary analysis: one-sided Fisher exact test, `proofforge` verifies more often than `alone`,
  alpha 0.05. With 0 verified alone, p < 0.05 needs at least 4 of 10 with ProofForge (p = 0.043).
- Secondary analysis: one-sided Fisher exact test, this experiment's `proofforge` arm verifies more
  often than the `proofforge` arm of frontier-3 (2 of 10), labelled as a comparison across two
  versions of ProofForge run at different times.
- Secondary, without a confirmatory claim: list dollars per verified run; dollars charged; wall
  time; runs stopped by a cap; requirements proved in the final candidate, with the three sequence
  bounds separately; REFUTED, UNRESOLVED or not building for each unverified run; minutes and list
  dollars to the five per-call requirements; failed builds and the longest streak of failed
  builds; whether each `proofforge` run imported `ProofForgeFin.Accumulator.Market` and used
  `Clock.reinit`; the `alone` runs of frontier-2, frontier-3 and this experiment pooled (labelled
  as such).

## Commitments

- No model call on this task outside these runs before they finish; no change to either arm, the
  task, the library or the judge after this commit.
- Every run is reported in `results/frontier-4/README.md`, whatever its outcome.
