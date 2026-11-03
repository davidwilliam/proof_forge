# feedback-measure-1: the feedback features of `results/feedback-1` and `results/feedback-2` on `rw-compound-comp`

Status: measured. Three runs of the repair harness on Compound Proposal 62 on 2026-10-31, from
18:42 to 23:20 (UTC-4), with Muse Spark 1.3 on the Contributor tier at $10 list and 14,400 s per
run, ProofForgeFin version `5552fae3`, the tactic portfolio, the goal tool and refutation by
sampling on, parallel variants off.

## Result

From a fresh start, A2 with every feedback feature (Muse Wonder 1.0 as lemma planner) proved 4 of 8
requirements in its last compiling version, against 2.5 per run for the two A0 runs of
`results/library-1` at the same caps (`results/wins/ledger.json`,
`feedback-measure-1+library-1/rw-compound-comp/A2-full-vs-A0`). Resumed from earlier candidates,
A0 and A2 each ended with the five per-call requirements proved (5 of 8).

| Run | Arm | Start | Requirements proved (last compiling version) | List $ | Charged $ | Ended by |
|---|---|---|---|---|---|---|
| `A2-full-1` | A2, every feedback feature | fresh | 4 of 8 | 9.81 | 2.08 | $10 cap |
| `A2-resume-1` | A2 | the five `library-1` A2 runs (4 of 8) | 5 of 8 | 9.24 | 1.08 | $10 cap |
| `A0-resume-1` | A0 | `library-1` A0-1 and A0-2 (5 of 8) | 5 of 8 | 9.78 | 0.50 | $10 cap |

The three sequence bounds (`req_rewards_bounded`, `req_account_bounded`, `req_no_backdated`) were the
open requirements of every run here. ProofForgeFin's `Accumulator.Market`, built next, supplies them:
Muse Code with ProofForge verified Compound in 2 of 10 runs of `results/frontier-3` and 8 of 10 of
`results/frontier-4`, against 0 of 10 on its own.

No Passport was issued for these runs; requirements proved are each run's `ledger.json` best
candidate.

## Files

`rw-compound-comp/<run>/`: `summary.json`, `events.jsonl`, `ledger.json`, `final.lean`,
`stdout.txt` and, for A2, the planner's plans (`plan_*.md`). Intermediate candidate versions are not
committed. Paths in the run records are relative to the repository root (`eval/normalize.py`).
