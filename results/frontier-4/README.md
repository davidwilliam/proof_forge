# frontier-4: Muse Code on its own and with ProofForge on `rw-compound-comp`, after the frontier-3 changes

Status: measured. The 20 preregistered runs (10 per arm) ran from 2026-11-02 22:36 to 2026-11-03
03:25 (UTC-5) from a worktree at commit `dbc2c01`, the commit that adds `PREREGISTRATION.md`. No
run was set aside and none was rerun.

## Result

On `rw-compound-comp` (Compound Proposal 62), Muse Code with ProofForge verified 8 of 10 runs; on
its own it verified 0 of 10. Preregistered one-sided Fisher exact test: p = 0.00036 (alpha 0.05).
Every verified run ended by itself at an accepted check, at a median of $4.30 list dollars and
18 minutes, and proves the three sequence bounds (`req_rewards_bounded`, `req_account_bounded`,
`req_no_backdated`); no run on its own proved any of them.

Preregistered secondaries:

- Against the ProofForge arm of `results/frontier-3` (2 of 10): 8 of 10, one-sided Fisher exact
  p = 0.012. This compares two versions of ProofForge run at different times.
- The runs on its own of `frontier-2`, `frontier-3` and this experiment pooled: 0 of 30, against
  8 of 10 with ProofForge, one-sided Fisher exact p = 0.00000059.

| | On its own | With ProofForge |
|---|---|---|
| Verified (primary) | 0 of 10 | 8 of 10 |
| One-sided Fisher exact | | p = 0.00036 |
| List dollars, total | $91.74 | $55.76 |
| List dollars per verified run | | $6.97 |
| List dollars per run, median | $9.54 | $4.46 |
| Dollars charged, total | $2.54 | $1.79 |
| Wall time per run, median | 35 min | 22 min |
| Model calls per run, median | 424.5 | 270 |
| Runs stopped by a cap | 10 of 10 | 2 of 10 |
| Final candidates that build | 1 of 10 | 10 of 10 |
| Requirements proved in the last compiling version, per run (mean) | 3.8 of 8 | 7.3 of 8 |
| Sequence bounds proved, runs | 0 of 10 | 8 of 10 |
| Failed builds (`lean_build`), all runs | 366 of 560 | 85 of 175 |
| Longest streak of failed builds, median | 7.5 | 3 |
| Runs with a build that proves the five per-call requirements | 7 of 10 | 9 of 10 |
| Time and list dollars to that build, median | 19 min, $5.26 | 4 min, $1.15 |

List dollars are the meter's charge at standard list prices, the quantity the cap applies to; the
meter charges each request its worst case before sending it, so a run stops when the next request's
worst case would pass $10, which is why capped runs end below $10. Dollars charged are what the
contributor tier billed.

As the preregistration states, the changes measured here were built from the ten ProofForge runs of
`frontier-3` on this task (`results/library-compound-gaps-1`): build output read whole with the
declarations in error named, a skill step to write the fix in the specification's terms, and
additions to `ProofForgeFin.Accumulator.Market` and `ProofForgeFin.Ledger`. The gap measures
ProofForge including that work. The `alone` arm has none of it and is unchanged since `frontier-3`.

## Library modules imported

Nine of ten ProofForge runs import `ProofForgeFin.Accumulator.Market`, and all eight verified runs
use its `Clock.reinit` start; `proofforge-full-10` imports only `ProofForgeFin.Ledger`. Other
imports: `ProofForgeFin.Ledger` in runs 1, 5, 6, 7 and 10; `ProofForgeFin.DeFi.Rewards` in runs 5,
7 and 9. No unverified final candidate is REFUTED in either arm: each fails on proof (a `sorry`
left or a build error), not on a counterexample.

## Every run

Primary outcome: VERIFIED by `bin/proofforge check` on the run's final candidate, judged again
outside the budget from the frozen commit (`judged/<task>/<run>/passport.json`); every Passport
reproduced by `bin/proofforge verify` (`judged/<task>/<run>/verify.txt`). The judged status equals
the status recorded during the run for every run. "Proved in the last compiling version" counts the
required theorems proved without `sorry` in the last version of the run that built (`ledger.json`,
`best_candidate`).

| Run | Passport status | Final candidate | Proved in the last compiling version | List dollars | Dollars charged | Wall time | Ended by | Passport |
|---|---|---|---|---|---|---|---|---|
| alone-1 | UNRESOLVED | does not build | 5 of 8 | $9.54 | $0.24 | 36 min | $10 cap | `8ddefc7299f22621` |
| alone-2 | UNRESOLVED | does not build | 0 of 8 | $8.42 | $0.23 | 35 min | $10 cap | `6c6406de7598e846` |
| alone-3 | UNRESOLVED | does not build | 5 of 8 | $9.47 | $0.27 | 35 min | $10 cap | `ee27bf2f38bb187b` |
| alone-4 | UNRESOLVED | does not build | 4 of 8 | $6.95 | $0.22 | 41 min | $10 cap | `78228253eb89fd9c` |
| alone-5 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.57 | $0.28 | 18 min | $10 cap | `92e2e0af320bbe70` |
| alone-6 | UNRESOLVED | does not build | 5 of 8 | $9.53 | $0.25 | 35 min | $10 cap | `e0f167bdd675f785` |
| alone-7 | UNRESOLVED | does not build | 5 of 8 | $9.54 | $0.28 | 31 min | $10 cap | `ff05cecfda48ef0f` |
| alone-8 | UNRESOLVED | does not build | 0 of 8 | $9.56 | $0.25 | 33 min | $10 cap | `68b1dd97944b4c1f` |
| alone-9 | UNRESOLVED | does not build | 4 of 8 | $9.62 | $0.29 | 40 min | $10 cap | `158575a2fb16603f` |
| alone-10 | UNRESOLVED | does not build | 5 of 8 | $9.55 | $0.25 | 17 min | $10 cap | `335c78d6359d7a7f` |
| proofforge-full-1 | VERIFIED | VERIFIED | 8 of 8 | $4.29 | $0.13 | 15 min | accepted | `79450c41fd0ea77c` |
| proofforge-full-2 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $7.74 | $0.22 | 41 min | $10 cap | `62c6d4443c9c568e` |
| proofforge-full-3 | VERIFIED | VERIFIED | 8 of 8 | $5.17 | $0.22 | 26 min | accepted | `56fe74dd5031aa23` |
| proofforge-full-4 | VERIFIED | VERIFIED | 8 of 8 | $4.25 | $0.13 | 27 min | accepted | `dd8943d482bd33d6` |
| proofforge-full-5 | VERIFIED | VERIFIED | 8 of 8 | $4.63 | $0.15 | 11 min | accepted | `de111c83c26b493c` |
| proofforge-full-6 | VERIFIED | VERIFIED | 8 of 8 | $8.67 | $0.30 | 25 min | accepted | `d073ccf63cb75abf` |
| proofforge-full-7 | VERIFIED | VERIFIED | 8 of 8 | $3.94 | $0.12 | 16 min | accepted | `459f18db9b68f18b` |
| proofforge-full-8 | VERIFIED | VERIFIED | 8 of 8 | $3.13 | $0.11 | 10 min | accepted | `a381e7a35f97d951` |
| proofforge-full-9 | VERIFIED | VERIFIED | 8 of 8 | $4.30 | $0.14 | 19 min | accepted | `ad5c81f6774ea354` |
| proofforge-full-10 | UNRESOLVED | builds with `sorry` (4 of 8 proved) | 4 of 8 | $9.64 | $0.28 | 33 min | $10 cap | `9d5e1574cb487bf8` |

| Run | Sequence bounds proved | Failed builds | Longest streak of failed builds | First build proving the five per-call requirements | `Clock.reinit` |
|---|---|---|---|---|---|
| alone-1 | 0 of 3 | 45 of 70 | 7 | 24 min, $5.26 | no |
| alone-2 | 0 of 3 | 27 of 39 | 8 | not reached | no |
| alone-3 | 0 of 3 | 31 of 51 | 6 | 15 min, $2.72 | no |
| alone-4 | 0 of 3 | 29 of 36 | 16 | not reached | no |
| alone-5 | 0 of 3 | 37 of 53 | 8 | 13 min, $6.86 | no |
| alone-6 | 0 of 3 | 43 of 64 | 7 | 28 min, $6.76 | no |
| alone-7 | 0 of 3 | 37 of 65 | 6 | 19 min, $4.59 | no |
| alone-8 | 0 of 3 | 34 of 41 | 19 | not reached | no |
| alone-9 | 0 of 3 | 40 of 55 | 10 | 39 min, $9.40 | no |
| alone-10 | 0 of 3 | 43 of 86 | 5 | 9 min, $4.22 | no |
| proofforge-full-1 | 3 of 3 | 9 of 21 | 3 | 4 min, $1.36 | yes |
| proofforge-full-2 | 0 of 3 | 6 of 12 | 3 | 37 min, $6.70 | no |
| proofforge-full-3 | 3 of 3 | 8 of 16 | 4 | 4 min, $0.81 | yes |
| proofforge-full-4 | 3 of 3 | 4 of 16 | 2 | 4 min, $1.03 | yes |
| proofforge-full-5 | 3 of 3 | 8 of 23 | 1 | 3 min, $1.25 | yes |
| proofforge-full-6 | 3 of 3 | 18 of 25 | 6 | 10 min, $3.96 | yes |
| proofforge-full-7 | 3 of 3 | 13 of 19 | 5 | 4 min, $0.94 | yes |
| proofforge-full-8 | 3 of 3 | 8 of 12 | 3 | 3 min, $1.01 | yes |
| proofforge-full-9 | 3 of 3 | 6 of 14 | 3 | 5 min, $1.15 | yes |
| proofforge-full-10 | 0 of 3 | 5 of 17 | 2 | not reached | no |

Failed builds count the `lean_build` calls whose `lake build` exited non-zero (`mcp-calls.jsonl`);
the ProofForge arm also checks snippets with `check_snippet_fast` and `try_snippet`, which are not
counted. The first build proving the five per-call requirements (`req_calls_succeed`,
`req_supply_hook`, `req_borrow_hook`, `req_claim`, `req_set_speeds`) is the first `lean_build` that
exits 0 on a version whose five theorems contain no `sorry` and use no declaration Lean reported as
using `sorry`; time is from the run's first model call, list dollars are the meter's charges up to
that build.

## Files

- `runs/<task>/<run>/`: the run's configuration, prompts, final candidate, Passport during the run,
  attempt ledger, model requests with the meter's charges, tool calls and Muse Code events
  (`events.jsonl.gz`). Intermediate candidate versions are not committed. In two event logs
  (`alone-7`, `alone-8`), Muse Code listed a host directory outside the task; the 4 names of host
  accounts and local tools in each listing are replaced by `<redacted>`.
- `judged/<task>/<run>/`: Passport, `check` and `verify` output of the judgement from the frozen
  commit.
