# frontier-3: Muse Code on its own and with ProofForge on `rw-compound-comp`, with `ProofForgeFin.Accumulator.Market`

Status: measured. The 20 preregistered runs (10 per arm) ran from 2026-11-02 08:19 to 14:07
(UTC-5) from a worktree at commit `a3a1307`, the commit that adds `PREREGISTRATION.md`. No run was
set aside and none was rerun.

## Result

On `rw-compound-comp` (Compound Proposal 62), Muse Code with ProofForge verified 2 of 10 runs; on
its own it verified 0 of 10. These are the first verified repairs of this task in any measured run:
`results/frontier-2` (0 of 10 in each arm) and the earlier runs of `muse-code-1`,
`baseline-flagships-1`, `compound-1`, `library-1`, `frontier-1` and `feedback-measure-1` have
none (`results/wins/ledger.json`). Both verified runs ended by
themselves at an accepted check, at $6.70 and $7.41 list dollars, and both prove the three sequence
bounds (`req_rewards_bounded`, `req_account_bounded`, `req_no_backdated`) that no earlier run of
either arm proved.

Every ProofForge final candidate builds (10 of 10); 1 of 10 builds on its own. The last compiling
version proves 4.5 of 8 requirements per run on average with ProofForge and 2.2 of 8 on its own.

Preregistered one-sided Fisher exact test: p = 0.24 (alpha 0.05; p < 0.05 needs at least 4 of 10
with 0 of 10 on its own). Preregistered secondary, the runs on its own of `frontier-2` and this
experiment pooled: 2 of 10 with ProofForge against 0 of 20, one-sided Fisher exact p = 0.10.

| | On its own | With ProofForge |
|---|---|---|
| Verified (primary) | 0 of 10 | 2 of 10 |
| One-sided Fisher exact | | p = 0.24 |
| List dollars, total | $92.47 | $85.43 |
| List dollars per verified run | | $42.72 |
| List dollars per run, median | $9.56 | $8.84 |
| Dollars charged, total | $2.52 | $2.39 |
| Wall time per run, median | 34 min | 34 min |
| Model calls per run, median | 408.5 | 390.5 |
| Runs stopped by a cap | 10 of 10 | 8 of 10 |
| Final candidates that build | 1 of 10 | 10 of 10 |
| Requirements proved in the last compiling version, per run | 0, 0, 5, 2, 0, 4, 0, 4, 4, 3 of 8 | 4, 3, 5, 0, 8, 4, 5, 5, 8, 3 of 8 |

List dollars are the meter's charge at standard list prices, the quantity the cap applies to; the
meter charges each request its worst case before sending it, so a run stops when the next request's
worst case would pass $10, which is why capped runs end below $10. Dollars charged are what the
contributor tier billed.

As the preregistration states, `ProofForgeFin.Accumulator.Market` was written after the
`frontier-2` runs on this task stopped at 5 of 8 requirements; the gap measures ProofForge
including that library work. The `alone` arm has none of it.

## Library modules imported

Every ProofForge run imports `ProofForgeFin.Accumulator.Market`: seven by name and three
(`proofforge-full-2`, `-8`, `-10`) through all of `ProofForgeFin`. `proofforge-full-5` also imports
`ProofForgeFin.Ledger`; `proofforge-full-9` imports `ProofForgeFin.Accumulator.Market` alone.

## Every run

Primary outcome: VERIFIED by `bin/proofforge check` on the run's final candidate, judged again
outside the budget from the frozen commit (`judged/<task>/<run>/passport.json`); every Passport
reproduced by `bin/proofforge verify` (`judged/<task>/<run>/verify.txt`). The judged status equals
the status recorded during the run for every run. "Proved in the last compiling version" counts the
required theorems proved without `sorry` in the last version of the run that built (`ledger.json`,
`best_candidate`).

| Run | Passport status | Final candidate | Proved in the last compiling version | List dollars | Dollars charged | Wall time | Ended by | Passport |
|---|---|---|---|---|---|---|---|---|
| alone-1 | UNRESOLVED | does not build | 0 of 8 | $9.64 | $0.28 | 33 min | $10 cap | `a643a1818dd07883` |
| alone-2 | UNRESOLVED | does not build | 0 of 8 | $8.04 | $0.23 | 16 min | $10 cap | `40abb8f29e5fa9b1` |
| alone-3 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.64 | $0.24 | 20 min | $10 cap | `e28e47ea797f53ec` |
| alone-4 | UNRESOLVED | does not build | 2 of 8 | $8.31 | $0.25 | 54 min | $10 cap | `0f6770c0b8b38457` |
| alone-5 | UNRESOLVED | does not build | 0 of 8 | $9.30 | $0.24 | 47 min | $10 cap | `c89a69858d0dfb80` |
| alone-6 | UNRESOLVED | does not build | 4 of 8 | $9.58 | $0.25 | 30 min | $10 cap | `6a90c4392fb553a5` |
| alone-7 | UNRESOLVED | does not build | 0 of 8 | $9.63 | $0.27 | 37 min | $10 cap | `29cdd5bcdb32e4ef` |
| alone-8 | UNRESOLVED | does not build | 4 of 8 | $9.21 | $0.24 | 17 min | $10 cap | `e7515aa5361ae920` |
| alone-9 | UNRESOLVED | does not build | 4 of 8 | $9.54 | $0.27 | 50 min | $10 cap | `4d65fe570e4044a1` |
| alone-10 | UNRESOLVED | does not build | 3 of 8 | $9.59 | $0.26 | 34 min | $10 cap | `66c613e9ba235417` |
| proofforge-full-1 | UNRESOLVED | builds with `sorry` (4 of 8 proved) | 4 of 8 | $9.56 | $0.25 | 25 min | $10 cap | `65420f3ed61aa27f` |
| proofforge-full-2 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.58 | $0.23 | 27 min | $10 cap | `fd4da818b465203e` |
| proofforge-full-3 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $7.22 | $0.20 | 39 min | $10 cap | `c3e0c6364207af72` |
| proofforge-full-4 | UNRESOLVED | builds with `sorry` (0 of 8 proved) | 0 of 8 | $8.09 | $0.20 | 14 min | $10 cap | `6e284bdcc6b8104d` |
| proofforge-full-5 | VERIFIED | VERIFIED | 8 of 8 | $6.70 | $0.20 | 49 min | accepted | `b7aca6c04101c9fc` |
| proofforge-full-6 | UNRESOLVED | builds with `sorry` (4 of 8 proved) | 4 of 8 | $9.60 | $0.29 | 38 min | $10 cap | `37d2284d83f14b53` |
| proofforge-full-7 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $8.57 | $0.23 | 53 min | $10 cap | `00edac44ae1e8013` |
| proofforge-full-8 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.11 | $0.27 | 30 min | $10 cap | `70297ce23f34dfac` |
| proofforge-full-9 | VERIFIED | VERIFIED | 8 of 8 | $7.41 | $0.26 | 19 min | accepted | `4f7e8adfccefae85` |
| proofforge-full-10 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.59 | $0.26 | 40 min | $10 cap | `55fd0360e9dfc1f8` |

## Files

- `runs/<task>/<run>/`: the run's configuration, prompts, final candidate, Passport during the run,
  attempt ledger, model requests with the meter's charges, tool calls and Muse Code events
  (`events.jsonl.gz`). Intermediate candidate versions are not committed. In one event log
  (`proofforge-full-2`), Muse Code listed a host directory outside the task; the 6 names of host
  accounts and local tools in that listing are replaced by `<redacted>`.
- `judged/<task>/<run>/`: Passport, `check` and `verify` output of the judgement from the frozen
  commit.
