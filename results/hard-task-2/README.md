# hard-task-2: Muse Code on its own and with ProofForge on `rw-kyber-swapstep`

Status: measured. The 20 preregistered runs (10 per arm) ran on 2026-11-02 from 14:17 to 22:35
(UTC-5) from a worktree at commit `0b70403`, the commit of Addendum 2 of `PREREGISTRATION.md`. No
other model experiment ran on the host during the runs. No run was set aside and none was rerun.

## Result

On the swap step of KyberSwap Elastic, the code behind the exploit of 2023-11-22, Muse Code with
ProofForge proved more of the locked requirements than Muse Code on its own, at the same model and
caps:

- Every ProofForge final candidate builds (10 of 10); 5 of 10 build on its own.
- The last compiling version proves 3.1 of 8 requirements per run on average with ProofForge and
  1.9 of 8 on its own (secondary, one-sided Mann-Whitney exact p = 0.014, U = 78 of 100).
- With ProofForge, REQ-IN-WITHIN-TARGET, the requirement the exploit broke, is proved in one run,
  and REQ-OUT-FEE-LIQUIDITY in three; no run on its own proves either. REQ-IN-FEE-LIQUIDITY is
  proved in 8 ProofForge runs and 3 runs on its own.

Neither arm verified a run within the $10 cap (0 of 10 in each arm; preregistered one-sided Fisher
exact p = 1). Every run of both arms ended at the $10 cap. REQ-OUT-WITHIN-TARGET and
REQ-POOL-CROSSES are proved in no run of either arm; they are the next library work for this task.

| | On its own | With ProofForge |
|---|---|---|
| Verified (primary) | 0 of 10 | 0 of 10 |
| One-sided Fisher exact | | p = 1 |
| Final candidates that build | 5 of 10 | 10 of 10 |
| Requirements proved in the last compiling version, per run | 3, 1, 1, 2, 3, 2, 3, 3, 0, 1 of 8 (mean 1.9) | 4, 3, 2, 3, 3, 3, 3, 5, 3, 2 of 8 (mean 3.1) |
| List dollars, total | $94.66 | $90.61 |
| List dollars per run, median | $9.59 | $9.56 |
| Dollars charged, total | $3.08 | $2.91 |
| Wall time per run, median | 50 min | 47 min |
| Model calls per run, median | 374.5 | 368 |
| Runs stopped by a cap | 10 of 10 | 10 of 10 |

List dollars are the meter's charge at standard list prices, the quantity the cap applies to; the
meter charges each request its worst case before sending it, so a run stops when the next request's
worst case would pass $10, which is why capped runs end below $10. Dollars charged are what the
contributor tier billed. One-sided Mann-Whitney exact test on list dollars per run (preregistered
secondary): U = 60 of 100, p = 0.24.

## Requirements proved, by requirement

Runs whose last compiling version proves each requirement (`ledger.json`, `best_candidate`):

| Requirement | On its own | With ProofForge |
|---|---|---|
| REQ-DEPLOYED-STEP | 9 | 10 |
| REQ-IN-FEE-LIQUIDITY | 3 | 8 |
| REQ-STEP-REACH | 6 | 7 |
| REQ-OUT-FEE-LIQUIDITY | 0 | 3 |
| REQ-STEP-PAID | 1 | 2 |
| REQ-IN-WITHIN-TARGET | 0 | 1 |
| REQ-OUT-WITHIN-TARGET | 0 | 0 |
| REQ-POOL-CROSSES | 0 | 0 |

The final candidates of `proofforge-full-1`, `-5` and `-8` are REFUTED: their code still lets an
exact-input step end beyond the target on some input, and `bin/proofforge check` gives the input and
a kernel-checked counterexample to REQ-IN-WITHIN-TARGET (`judged/<task>/<run>/check.txt`).

## Library modules imported

Eight ProofForge runs import ProofForgeFin modules: `ProofForgeFin.QuadRoot` (written for this task,
see `PREREGISTRATION.md`) in seven, with `Rounding`, `RoundCompose`, `Word`, `WordBridge`,
`FixedPoint` and `Money` in some; `proofforge-full-1` and `-4` import none.

## Every run

Primary outcome: VERIFIED by `bin/proofforge check` on the run's final candidate, judged again
outside the budget from the frozen commit (`judged/<task>/<run>/passport.json`); every Passport
reproduced by `bin/proofforge verify` (`judged/<task>/<run>/verify.txt`). The judged status equals
the status recorded during the run for every run. "Proved in the last compiling version" counts the
required theorems proved without `sorry` in the last version of the run that built (`ledger.json`,
`best_candidate`).

| Run | Passport status | Final candidate | Proved in the last compiling version | List dollars | Dollars charged | Wall time | Ended by | Passport |
|---|---|---|---|---|---|---|---|---|
| alone-1 | UNRESOLVED | does not build | 3 of 8 | $9.10 | $0.24 | 20 min | $10 cap | `7df95b541027b594` |
| alone-2 | UNRESOLVED | does not build | 1 of 8 | $9.62 | $0.25 | 48 min | $10 cap | `777675eaf96b6f59` |
| alone-3 | UNRESOLVED | builds with `sorry` (1 of 8 proved) | 1 of 8 | $9.72 | $0.47 | 50 min | $10 cap | `f2d568afeaec8f33` |
| alone-4 | UNRESOLVED | builds with `sorry` (2 of 8 proved) | 2 of 8 | $9.68 | $0.34 | 56 min | $10 cap | `3bc230836870f455` |
| alone-5 | UNRESOLVED | does not build | 3 of 8 | $9.63 | $0.29 | 51 min | $10 cap | `4feb7d1709ec0d8e` |
| alone-6 | UNRESOLVED | does not build | 2 of 8 | $9.14 | $0.24 | 49 min | $10 cap | `2fb14217fa206f83` |
| alone-7 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.56 | $0.33 | 43 min | $10 cap | `39d21b3b370aeb73` |
| alone-8 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.90 | $0.34 | 55 min | $10 cap | `2b3f5f119ac056c5` |
| alone-9 | UNRESOLVED | does not build | 0 of 8 | $8.78 | $0.25 | 52 min | $10 cap | `5f06e6ce501000ea` |
| alone-10 | UNRESOLVED | builds; 7 required theorems missing | 1 of 8 | $9.54 | $0.34 | 68 min | $10 cap | `3c8558fe45b4511f` |
| proofforge-full-1 | REFUTED | builds with `sorry` (4 of 8 proved) | 4 of 8 | $8.10 | $0.30 | 55 min | $10 cap | `46dd1ff89dfd0b48` |
| proofforge-full-2 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.56 | $0.33 | 58 min | $10 cap | `d1fd3d1905402e23` |
| proofforge-full-3 | UNRESOLVED | builds with `sorry` (2 of 8 proved) | 2 of 8 | $9.58 | $0.25 | 28 min | $10 cap | `5648382757ca0d95` |
| proofforge-full-4 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.77 | $0.31 | 57 min | $10 cap | `c0f6003fdaaee39d` |
| proofforge-full-5 | REFUTED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.56 | $0.25 | 43 min | $10 cap | `0699a86d9d5e3689` |
| proofforge-full-6 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $9.82 | $0.36 | 48 min | $10 cap | `bb2574181d4c80a0` |
| proofforge-full-7 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $7.94 | $0.25 | 49 min | $10 cap | `5695b52706b28193` |
| proofforge-full-8 | REFUTED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $8.34 | $0.23 | 37 min | $10 cap | `a8a197ad5fa15902` |
| proofforge-full-9 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $8.07 | $0.22 | 46 min | $10 cap | `768bb39f97e04d6d` |
| proofforge-full-10 | UNRESOLVED | builds with `sorry` (2 of 8 proved) | 2 of 8 | $9.89 | $0.42 | 36 min | $10 cap | `8539ee61b6200ac5` |

## Files

- `runs/<task>/<run>/`: the run's configuration, prompts, final candidate, Passport during the run,
  attempt ledger, model requests with the meter's charges, tool calls and Muse Code events
  (`events.jsonl.gz`). Intermediate candidate versions are not committed. In three event logs
  (`alone-2`, `alone-5`, `alone-7`), Muse Code listed host directories outside the task; the 6
  occurrences of host account and local tool names in each listing are replaced by `<redacted>`.
- `judged/<task>/<run>/`: Passport, `check` and `verify` output of the judgement from the frozen
  commit.
- `passports/kyber-reference.json` and `passports/kyber-start.json` were generated again on
  2026-11-02 from the frozen commit with a neutral temporary directory, so that they record no host
  path: the reference is VERIFIED (Passport `10b5838e6a5a6b6f`) and the start candidate REFUTED
  (Passport `8e8a058699b3a851`), the same statuses as the Passports `8daa0235dbc0dc04` and
  `a73c8bd1e11cf770` cited in `PREREGISTRATION.md`.
