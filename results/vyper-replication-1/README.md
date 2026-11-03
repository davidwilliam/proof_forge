# vyper-replication-1: Muse Code alone against Muse Code with ProofForge on `rw-vyper-sqrt`

Status: measured. The 20 preregistered runs (10 per arm) ran on 2026-11-01 from 07:46 to 16:07
(UTC-5) from a worktree at commit `b8fffb3`, whose tree outside `web/` and `results/` is that of
`baa38a0`, the frozen commit of `results/hard-task-1`. Plan: `PREREGISTRATION.md`, committed before
the first run. No run was set aside and none was rerun.

## Task

`realworld/tasks/rw-vyper-sqrt`: Vyper's `sqrt()` builtin on decimals, CVE-2025-26622, repair mode
from the v0.4.0 code (`sqrt(0.9999999998)` returns `0.9999999999`). Five requirements:
REQ-SQRT-NOT-ABOVE, REQ-SQRT-NOT-BELOW, REQ-SQRT-TOTAL, REQ-SQRT-NEG-REVERTS, REQ-DEPLOYED-LOOP.
Locked manifest sha256 `ea5b5e443d8f028f5bd161c67e95a1ff2046fec2de44a43f04a7936e51622fb1`.

## Results

Primary outcome: VERIFIED by `bin/proofforge check` on the run's final candidate, judged again
outside the budget from the frozen commit (`judged/rw-vyper-sqrt/<run>/passport.json`); all 20
Passports reproduced by `bin/proofforge verify` (`judged/rw-vyper-sqrt/<run>/verify.txt`). The judged
status equals the status recorded during the run for every run.

| | `alone` (Muse Code) | `proofforge` (Muse Code with ProofForge) | One-sided test |
|---|---|---|---|
| Verified (primary) | 8 of 10 | 9 of 10 | Fisher exact, p = 0.50 |
| List dollars per run, median (secondary) | $6.83 | $4.32 | Mann-Whitney U = 77 of 100, exact p = 0.022 |
| List dollars, total | $71.99 | $51.22 | |
| List dollars per verified run | $9.00 | $5.69 | |
| Dollars charged, total | $2.66 | $1.90 | |
| Wall time per run, median | 43 min | 25 min | |
| Wall time of a verified run, median | 41 min | 22 min | |
| Runs stopped by the $10 cap | 2 of 10 | 1 of 10 | |
| Pooled with `results/hard-task-1` (secondary, includes the runs that motivated this experiment) | 10 of 15 | 14 of 15 | Fisher exact, p = 0.084 |

With ProofForge, Muse Code verified 9 of 10 runs at $5.69 per verified run against $9.00, and a
verified run took a median of 22 minutes against 41. ProofForge runs spent fewer list dollars
(preregistered secondary, one-sided Mann-Whitney exact p = 0.022). Every run that verified ended at
its first accepted check, so its wall time is the time to a verified repair. Muse Code on its own is
strong on this task, 8 of 10; on the verification rate the primary Fisher exact test gives p = 0.50,
and pooled with `results/hard-task-1`, 14 of 15 against 10 of 15, p = 0.084. At the pooled rates,
17 runs per arm reach p below 0.05; with more runs, we expect the rate difference to get there.

List dollars are the meter's charge at standard list prices, the quantity the cap applies to;
dollars charged are what the contributor tier billed.

In `results/hard-task-1` the same arms verified 2 of 5 alone and 5 of 5 with ProofForge; this
experiment shows a higher rate for Muse Code alone (8 of 10) than those five runs did.

## Every run

"Proved in the last compiling version" counts the required theorems proved without `sorry` in the
last version of the run that built (`ledger.json`, `best_candidate`).

| Run | Passport status | Final candidate | Proved in the last compiling version | List dollars | Dollars charged | Wall time | Ended by | Passport |
|---|---|---|---|---|---|---|---|---|
| alone-1 | VERIFIED | VERIFIED | 5 of 5 | $8.99 | $0.34 | 73 min | accepted | `ee27293e5cbf2c28` |
| alone-2 | VERIFIED | VERIFIED | 5 of 5 | $6.36 | $0.23 | 53 min | accepted | `9e5c9985d850cdb5` |
| alone-3 | VERIFIED | VERIFIED | 5 of 5 | $5.67 | $0.19 | 47 min | accepted | `ccb4a885e09022cd` |
| alone-4 | VERIFIED | VERIFIED | 5 of 5 | $9.30 | $0.46 | 125 min | accepted | `6323bdbeb4e8c7df` |
| alone-5 | VERIFIED | VERIFIED | 5 of 5 | $7.29 | $0.22 | 33 min | accepted | `ec6bef7f3a45cac1` |
| alone-6 | UNRESOLVED | builds; no required theorem stated | 0 of 5 | $9.94 | $0.47 | 111 min | $10 cap | `bf0f83c2a8a99864` |
| alone-7 | UNRESOLVED | does not build (unknown identifier) | 2 of 5 | $9.57 | $0.26 | 39 min | $10 cap | `1987e685386faf99` |
| alone-8 | VERIFIED | VERIFIED | 5 of 5 | $5.38 | $0.19 | 17 min | accepted | `a01e910367ec2659` |
| alone-9 | VERIFIED | VERIFIED | 5 of 5 | $3.85 | $0.13 | 36 min | accepted | `fa74796048943b11` |
| alone-10 | VERIFIED | VERIFIED | 5 of 5 | $5.64 | $0.18 | 15 min | accepted | `6d8d4836f1949b7c` |
| proofforge-full-1 | VERIFIED | VERIFIED | 5 of 5 | $4.67 | $0.15 | 14 min | accepted | `d0ca2757f579ef7c` |
| proofforge-full-2 | VERIFIED | VERIFIED | 5 of 5 | $5.13 | $0.17 | 12 min | accepted | `36e55a8496fa2d7f` |
| proofforge-full-3 | VERIFIED | VERIFIED | 5 of 5 | $3.43 | $0.12 | 22 min | accepted | `00a72bde9bc226f4` |
| proofforge-full-4 | UNRESOLVED | builds with `sorry` | 2 of 5 | $9.68 | $0.48 | 161 min | $10 cap | `dc3744b206afb5d0` |
| proofforge-full-5 | VERIFIED | VERIFIED | 5 of 5 | $6.08 | $0.24 | 47 min | accepted | `fa8ab0badee5fa62` |
| proofforge-full-6 | VERIFIED | VERIFIED | 5 of 5 | $3.97 | $0.15 | 15 min | accepted | `5cd10b37b41c045c` |
| proofforge-full-7 | VERIFIED | VERIFIED | 5 of 5 | $2.72 | $0.11 | 33 min | accepted | `39516c945bd4e648` |
| proofforge-full-8 | VERIFIED | VERIFIED | 5 of 5 | $9.29 | $0.26 | 39 min | accepted | `f9a33e8aa6d497b3` |
| proofforge-full-9 | VERIFIED | VERIFIED | 5 of 5 | $3.30 | $0.11 | 20 min | accepted | `e7762f509728e828` |
| proofforge-full-10 | VERIFIED | VERIFIED | 5 of 5 | $2.94 | $0.11 | 29 min | accepted | `c60ae5a323136271` |

The three unverified runs:

- `alone-6`: the final file builds but states none of the five required theorems (28 helper
  declarations proved); the run reached the $10 cap.
- `alone-7`: the final file does not build (`Unknown identifier Znat_le_B`); its last compiling
  version proved 2 of 5; the run reached the $10 cap.
- `proofforge-full-4`: the final file builds with `sorry` in 3 of the 5 required theorems (2 of 5
  proved); the run reached the $10 cap after 161 minutes.

## Files

- `runs/rw-vyper-sqrt/<run>/`: the run's configuration, prompts, final candidate, Passport during
  the run, attempt ledger, model requests with the meter's charges, tool calls and Muse Code events
  (`events.jsonl.gz`). Intermediate candidate versions are not committed.
- `judged/rw-vyper-sqrt/<run>/`: Passport, `check` and `verify` output of the judgement from the
  frozen commit.
