# baseline-flagships-1: Muse Spark alone on the real-world tasks

Arm A0 (`agents/baseline.py`): Muse Spark 1.3 on the Contributor tier (`muse-spark-1.3-contributor`) receives the task brief, the protected specification and the start candidate, replies with a complete `candidate/Solution.lean`, and gets back only what ordinary checking gives: Lean errors, or the axiom audit of each required theorem. No goal states, snippet tool, banked lemmas, tests or planner. Two attempts per task, decided in advance, each capped at $10 at list prices and 14,400 s, the same caps as the repair runs in `cetus-1`, `euler-1`, `vault-1`, `balancer-1`, `knight-1` and `compound-1`.

Every run whose session reported acceptance was then checked by `bin/proofforge check` (`passport.json`, `check.txt`) and reproduced by `bin/proofforge verify` (`verify.txt`).

| Task | Run | Session | Stop | Elapsed | List $ | Charged $ | Passport |
|---|---|---|---|---|---|---|---|
| rw-cetus-shlw | A0-1 | accepted | - | 328 s | 0.17 | 0.008 | VERIFIED `c448db9c559f7412` |
| rw-cetus-shlw | A0-2 | accepted | - | 167 s | 0.12 | 0.006 | VERIFIED `18aa3b25629ebabc` |
| rw-euler-donate | A0-1 | accepted | - | 1,284 s | 0.88 | 0.047 | VERIFIED `7b74e28e3db81ee9` |
| rw-euler-donate | A0-2 | accepted | - | 2,075 s | 3.12 | 0.187 | VERIFIED `58ed68fe9f630b34` |
| rw-hundred-vault | A0-1 | accepted | - | 1,730 s | 1.09 | 0.058 | VERIFIED `7029533ce17ca3f5` |
| rw-hundred-vault | A0-2 | accepted | - | 1,847 s | 1.91 | 0.101 | VERIFIED `f944514b448ac5fd` |
| rw-balancer-upscale | A0-1 | not accepted | dollar cap | 11,682 s | 9.61 | 0.557 | none |
| rw-balancer-upscale | A0-2 | accepted | - | 4,625 s | 7.29 | 0.440 | VERIFIED `bc317c4e817f0a1b` |
| rc-knight-router | A0-1 | accepted | - | 6,072 s | 6.79 | 0.408 | VERIFIED `dc1375e5f7262c88` |
| rc-knight-router | A0-2 | not accepted | dollar cap | 7,159 s | 9.43 | 0.556 | none |
| rw-compound-comp | A0-1 | not accepted | wall (see below) | 9,701 s | 5.94 | 0.301 | none |
| rw-compound-comp | A0-2 | not accepted | wall (see below) | 8,316 s | 4.27 | 0.225 | none |

Summary: accepted in 2 of 2 attempts on Cetus, Euler and Hundred, 1 of 2 on Balancer and Knight, 0 of 2 on Compound. All eight accepted runs were VERIFIED by the independent check and reproduced.

Both Compound runs ended before their wall cap. In `agents/repair.py` `Session.call`, which A0 shares, a single model call that reaches its per-attempt timeout (600 s) raises `DeadlineReached` and is treated as the run's wall stop, although the run deadline was hours away. The two runs are kept as measured; they did not use their full budget. The same defect ended `frontier-1`'s Compound run early. No other recorded run stopped on the wall clock before its cap.

Per run: `agent.log` (console), `events.jsonl`, `summary.json` (budget accounting), `final.lean`, and for accepted runs `passport.json`, `check.txt`, `verify.txt` and the judge record (`judge_v*.json`). Intermediate candidate versions are not committed. Text was normalized with `eval/normalize.py`.
