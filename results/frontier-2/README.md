# frontier-2: Muse Code on its own and with ProofForge on `rw-oz-sqrt` and `rw-compound-comp`

Status: measured. The 40 preregistered runs (10 per arm per task) ran from 2026-11-01 16:07 to
2026-11-02 07:05 (UTC-5) from a worktree at commit `995ee6e`, the commit that adds
`PREREGISTRATION.md`. No run was set aside and none was rerun.

## Result

On `rw-oz-sqrt`, Muse Code with ProofForge verified 10 of 10 runs; on its own it verified 0 of 10.
Preregistered one-sided Fisher exact test: p = 5.4e-6 (alpha 0.025 per task). Every ProofForge run
ended at an accepted check after a median of 12 minutes and $1.78 at list prices; every run on
its own ended at the $10 cap or Muse Code's session limit, after a median of 85 minutes. No measured
run of any arm had verified this task before (`results/hard-task-1`: 0 of 5 in each arm).

On `rw-compound-comp`, neither arm verified a run (p = 1). With ProofForge every final candidate
proves the same 5 of 8 requirements, `req_calls_succeed` among them; on its own the final candidate
proves 3 to 5 of 8 in five runs and does not build in the other five. The three sequence bounds
(`req_rewards_bounded`, `req_account_bounded`, `req_no_backdated`) are proved in no run of either
arm.

| | `rw-oz-sqrt` on its own | `rw-oz-sqrt` with ProofForge | `rw-compound-comp` on its own | `rw-compound-comp` with ProofForge |
|---|---|---|---|---|
| Verified (primary) | 0 of 10 | 10 of 10 | 0 of 10 | 0 of 10 |
| One-sided Fisher exact | | p = 5.4e-6 | | p = 1 |
| List dollars, total | $95.45 | $19.88 | $90.78 | $92.56 |
| List dollars per verified run | | $1.99 | | |
| List dollars per run, median | $9.63 | $1.78 | $9.46 | $9.66 |
| Dollars charged, total | $3.69 | $0.77 | $2.52 | $2.82 |
| Wall time per run, median | 85 min | 12 min | 36 min | 25 min |
| Model calls per run, median | 356 | 108 | 399 | 394.5 |
| Runs stopped by a cap or the session limit | 10 of 10 | 0 of 10 | 10 of 10 | 10 of 10 |
| Final candidates that build | 7 of 10 | 10 of 10 | 5 of 10 | 10 of 10 |
| Requirements proved in the final candidate, per run | 0, 2, 0, 2, 2, 2, 0, 0, 1, 4 of 8 | 8 of 8 in each | 4, 4, 0, 0, 3, 0, 5, 5, 0, 0 of 8 | 5 of 8 in each |

Secondary, without a confirmatory claim: both tasks pooled, 10 of 20 with ProofForge against 0 of
20 on its own, one-sided Fisher exact p = 2.2e-4. On `rw-oz-sqrt` every ProofForge run spent fewer
list dollars than every run on its own (Mann-Whitney U = 100 of 100, exact one-sided p = 5.4e-6).

List dollars are the meter's charge at standard list prices, the quantity the cap applies to; the
meter charges each request its worst case before sending it, so a run stops when the next request's
worst case would pass $10, which is why some capped runs end below $10. Dollars charged are what the
contributor tier billed.

As the preregistration states, the ProofForgeFin modules these runs import (`SqrtIter`,
`WordBridge`, `NatSqrt`, `Accumulator`) were written after earlier runs on these two tasks failed;
the gap measures ProofForge including that library work. The `alone` arm has none of it.

## Library modules imported

- `rw-oz-sqrt`: every ProofForge run imports `ProofForgeFin.SqrtIter`; nine import
  `ProofForgeFin.WordBridge` by name and one (`proofforge-full-6`) imports all of `ProofForgeFin`.
  Six also import `ProofForgeFin.NatSqrt`, five `ProofForgeFin.Sqrt`, one `ProofForgeFin.Evm.Bits`.
- `rw-compound-comp`: every ProofForge run imports `ProofForgeFin.Ledger` or all of `ProofForgeFin`,
  and nine import `ProofForgeFin.Accumulator` or its submodules (`Potential`, `Index`, `Runs`).

## Every run

Primary outcome: VERIFIED by `bin/proofforge check` on the run's final candidate, judged again
outside the budget from the frozen commit (`judged/<task>/<run>/passport.json`); every Passport
reproduced by `bin/proofforge verify` (`judged/<task>/<run>/verify.txt`). The judged status equals
the status recorded during the run for every run. "Proved in the last compiling version" counts the
required theorems proved without `sorry` in the last version of the run that built (`ledger.json`,
`best_candidate`).

### rw-oz-sqrt

| Run | Passport status | Final candidate | Proved in the last compiling version | List dollars | Dollars charged | Wall time | Ended by | Passport |
|---|---|---|---|---|---|---|---|---|
| alone-1 | UNRESOLVED | builds; no required theorem stated | 0 of 8 | $9.57 | $0.27 | 44 min | $10 cap | `9a9fbff45779029d` |
| alone-2 | UNRESOLVED | builds with `sorry` (2 of 8 proved) | 2 of 8 | $8.83 | $0.42 | 143 min | session limit | `521e272920952b5e` |
| alone-3 | UNRESOLVED | does not build | 0 of 8 | $9.50 | $0.49 | 182 min | session limit | `6c19a3662d49eac9` |
| alone-4 | UNRESOLVED | builds with `sorry` (2 of 8 proved) | 2 of 8 | $9.78 | $0.31 | 72 min | $10 cap | `d636518091d64bf7` |
| alone-5 | UNRESOLVED | builds with `sorry` (2 of 8 proved) | 2 of 8 | $9.49 | $0.39 | 95 min | $10 cap | `bd43aa056a4ab035` |
| alone-6 | UNRESOLVED | builds with `sorry` (2 of 8 proved) | 2 of 8 | $9.86 | $0.37 | 84 min | $10 cap | `6ae8d15105a31127` |
| alone-7 | UNRESOLVED | does not build | 1 of 8 | $8.88 | $0.26 | 55 min | $10 cap | `1f62685567dce037` |
| alone-8 | UNRESOLVED | does not build | 0 of 8 | $9.69 | $0.51 | 200 min | $10 cap | `5d7672afb952bb1e` |
| alone-9 | UNRESOLVED | builds with `sorry` (1 of 8 proved) | 1 of 8 | $9.89 | $0.34 | 86 min | $10 cap | `c87d07b41fbf9da1` |
| alone-10 | UNRESOLVED | builds with `sorry` (4 of 8 proved) | 4 of 8 | $9.95 | $0.33 | 49 min | $10 cap | `3190e459ef7823c6` |
| proofforge-full-1 | VERIFIED | VERIFIED | 8 of 8 | $1.29 | $0.05 | 12 min | accepted | `69b54ebdc50781ca` |
| proofforge-full-2 | VERIFIED | VERIFIED | 8 of 8 | $2.66 | $0.09 | 12 min | accepted | `e06e6988cc1986e8` |
| proofforge-full-3 | VERIFIED | VERIFIED | 8 of 8 | $2.40 | $0.08 | 15 min | accepted | `d0001e4be0e89505` |
| proofforge-full-4 | VERIFIED | VERIFIED | 8 of 8 | $1.70 | $0.06 | 5 min | accepted | `0a8d0747d92f57a2` |
| proofforge-full-5 | VERIFIED | VERIFIED | 8 of 8 | $1.64 | $0.06 | 12 min | accepted | `9e3f4a8aaf1a2f68` |
| proofforge-full-6 | VERIFIED | VERIFIED | 8 of 8 | $1.68 | $0.07 | 21 min | accepted | `55d944d0c660f787` |
| proofforge-full-7 | VERIFIED | VERIFIED | 8 of 8 | $3.08 | $0.12 | 12 min | accepted | `5c0a61ccd4b39191` |
| proofforge-full-8 | VERIFIED | VERIFIED | 8 of 8 | $1.85 | $0.08 | 16 min | accepted | `61ef109da82f042b` |
| proofforge-full-9 | VERIFIED | VERIFIED | 8 of 8 | $2.08 | $0.09 | 10 min | accepted | `156082ec798f2899` |
| proofforge-full-10 | VERIFIED | VERIFIED | 8 of 8 | $1.49 | $0.06 | 9 min | accepted | `5789521d90b4752e` |

### rw-compound-comp

| Run | Passport status | Final candidate | Proved in the last compiling version | List dollars | Dollars charged | Wall time | Ended by | Passport |
|---|---|---|---|---|---|---|---|---|
| alone-1 | UNRESOLVED | builds with `sorry` (4 of 8 proved) | 4 of 8 | $9.64 | $0.27 | 17 min | $10 cap | `626148d8ded476b4` |
| alone-2 | UNRESOLVED | builds with `sorry` (4 of 8 proved) | 4 of 8 | $9.37 | $0.27 | 38 min | $10 cap | `2856b2d58bb58845` |
| alone-3 | UNRESOLVED | does not build | 0 of 8 | $7.46 | $0.23 | 17 min | $10 cap | `072227d2a569bd74` |
| alone-4 | UNRESOLVED | does not build | 0 of 8 | $9.18 | $0.23 | 39 min | $10 cap | `fbe0c21f81186f4c` |
| alone-5 | UNRESOLVED | builds with `sorry` (3 of 8 proved) | 3 of 8 | $8.61 | $0.24 | 42 min | $10 cap | `b685e96cf8635c9b` |
| alone-6 | UNRESOLVED | does not build | 0 of 8 | $9.63 | $0.27 | 32 min | $10 cap | `563cb9b0bdfd4e9d` |
| alone-7 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.60 | $0.26 | 45 min | $10 cap | `9a0d8e2d6dca5feb` |
| alone-8 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $8.18 | $0.22 | 15 min | $10 cap | `5fbb236f1ce28444` |
| alone-9 | UNRESOLVED | does not build | 4 of 8 | $9.56 | $0.25 | 46 min | $10 cap | `89f567131d6a2106` |
| alone-10 | UNRESOLVED | does not build | 0 of 8 | $9.54 | $0.26 | 34 min | $10 cap | `ce21007984b35c6f` |
| proofforge-full-1 | UNRESOLVED | builds; 3 required theorems missing | 5 of 8 | $9.87 | $0.31 | 23 min | $10 cap | `dfa9412b3902ff88` |
| proofforge-full-2 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.84 | $0.32 | 31 min | $10 cap | `8e05bcfc32fd7fc0` |
| proofforge-full-3 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $7.25 | $0.21 | 19 min | $10 cap | `cae3d5e38502a735` |
| proofforge-full-4 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.79 | $0.33 | 78 min | $10 cap | `c32e79bb7dc5d6aa` |
| proofforge-full-5 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $8.23 | $0.26 | 17 min | $10 cap | `e8ba6739dc045766` |
| proofforge-full-6 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.56 | $0.26 | 36 min | $10 cap | `337a718f7144666c` |
| proofforge-full-7 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.56 | $0.24 | 41 min | $10 cap | `d1a0759ce8be7c5d` |
| proofforge-full-8 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $8.90 | $0.23 | 15 min | $10 cap | `9c6a2200026cb2a8` |
| proofforge-full-9 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.78 | $0.32 | 25 min | $10 cap | `faa20962030a65f4` |
| proofforge-full-10 | UNRESOLVED | builds with `sorry` (5 of 8 proved) | 5 of 8 | $9.76 | $0.33 | 25 min | $10 cap | `27084298d2bab899` |

## Files

- `runs/<task>/<run>/`: the run's configuration, prompts, final candidate, Passport during the run,
  attempt ledger, model requests with the meter's charges, tool calls and Muse Code events
  (`events.jsonl.gz`). Intermediate candidate versions are not committed. In eight event logs of
  runs on its own, Muse Code listed host directories outside the task; the 56 names of host
  accounts and local tools in those listings are replaced by `<redacted>`.
- `judged/<task>/<run>/`: Passport, `check` and `verify` output of the judgement from the frozen
  commit.
