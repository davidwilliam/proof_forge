# E1 on the frozen test tasks with Muse Glimmer 30B (incomplete)

Command, from commit 5c1431f with a clean tree:

```
python3 eval/e1.py --label test-glimmer-1 --split test --arms A0,A1 --model glimmer/muse-glimmer-30b --budget-usd 3 --budget-wall 3600 --parallel 2 --require-clean
```

Model: `meta-models/Muse-Glimmer-30B` at revision `cec94fcfd6512f2cfe708138c32533b346ea4f69`, BF16, served by vLLM 0.32.0 on one Modal H100 with the DFlash drafter (`infra/modal/`), routed as `glimmer/muse-glimmer-30b`. The agents ran unchanged at reasoning effort medium, passed to the model as the chat template's `reasoning_strength`. Budget dollars use the GPU-cost price in `agents/budget.py` ($0.155 input, $6.37 output per 1M tokens, derived from `price-bench.json`), not a list price.

## Status

The run is not finished. It started at 03:59:11 UTC on 2026-10-30. At 12:33:13 UTC Modal drained the serving container and paused the workspace (`modal deploy` now fails with "Workspace ... is paused"), so no replacement container could start. The runner was stopped at 12:40 UTC. 31 of the 60 runs were scored, 2 were interrupted, and 27 never started: permissions-grants-b4 A1, both arms of the three permissions-workflow tasks and of all ten queues tasks.

Runs affected by the outage, kept here as recorded and excluded from the counts below:

| Run | What happened |
|---|---|
| `permissions-grants-b1/A1` | requests failed with HTTP 502 and 503 from 12:33:13; the worst-case charges of the failed attempts ended it with a usd stop |
| `permissions-grants-b2/A1` | 13 failed attempts with HTTP 503 "no upstreams available"; usd stop |
| `permissions-grants-b3/A1` | 15 failed attempts with HTTP 503; usd stop |
| `permissions-grants-b3/A0`, `permissions-grants-b4/A0` | stopped by the runner with no summary; `eval/e1.py` sets such runs aside as `interrupted-N` and runs them again when the batch resumes |

Before the outage, 6 runs each lost one attempt to a client connect timeout (`URLError [Errno 60]`); those runs are counted as measured.

## Results so far

`e1.md` is the evaluator's report over all 31 scored runs, outage runs included. Excluding the three outage runs:

| Arm | Completed | Judge accepts | Binary pass | Budget stops (usd / wall) | Mean $ (GPU-cost price) |
|---|---|---|---|---|---|
| A0 | 0/15 | 0 | 0 | 2 / 0 | 1.78 |
| A1 | 3/13 | 3 | 13 | 3 / 3 | 2.23 |

The completed A1 repairs are ledgers-journal-b3, ledgers-log-b1 and ledgers-log-b2. On the same tasks Muse Spark 1.3 (`results/e1-test-1`) completed 13 of the 15 A0 runs and all 13 A1 runs.

- **A0 never compiled.** No A0 version compiled in any run, so every A0 final candidate is the last attempt and the binary build fails. 13 of the 15 A0 runs ended at the baseline's 200-turn limit, between 737 s and 2,480 s, before either cap. Glimmer answers in tens of seconds, so it uses up the turns before the wall clock.
- **A1 kept passing tests but not the judge.** Every A1 final candidate passed the binary property check, but 10 of 13 were not accepted. Nine of them still had required theorems proved with `sorry` at the end. In ledgers-log-b3 the session reported every requirement proved, and the official judge still rejected the file.

## GPU cost

The container ran continuously from 03:20:39 to 12:33:13 UTC. Its measured price is $4.3963 per hour: H100 $3.95, CPU $0.189, memory $0.256 (Modal billing report, every full hour from 04:00 to 11:00). Modal's billing summary lists $40.88 for the deployed app over that time. This includes startup, the smoke test, the throughput benchmark and the dev A1 run before E1.

The E1 window from 03:59:11 to 12:33:13 is 30,842 s, so $37.66 at that rate. The scored runs charged $64.71 at the GPU-cost price, or $55.71 without the outage runs. Of the $64.71, $56.35 is reported token usage and $8.36 is worst-case charges for attempts whose response never arrived. The token price overstates the GPU cost: over the E1 window the server produced 7,711,008 completion tokens, 250 per second on aggregate, against the 191.6 per second the price was derived from. 248,223,232 of the 270,031,873 prompt tokens were prefix-cache hits.
