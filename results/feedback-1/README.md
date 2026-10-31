# feedback-1: tactic portfolio replayed on recorded goals

No model calls. `agents/portfolio_replay.py` took every goal a recorded run spent model turns on and compiled the tactic portfolio (`agents/portfolio.py`) on it exactly as the agent now does before the first turn: the goal removed from the candidate version on disk when its first dialog started, one renamed copy per tactic under `maxHeartbeats 50000`, `#print axioms` of each copy. A goal counts as closed only when a copy has no error and no `sorryAx` (it uses no open declaration). Turns and dollars are the recorded ones for that goal (all its dialogs, list prices, prover turns; planner calls are not attributed per goal in these recordings).

Command (one Lean container at a time, `LEAN_NUM_THREADS=2`, library source tree `34d63d5e…`, 2,394 s in total):

```
python3 agents/portfolio_replay.py <run dirs> --out results/feedback-1 --jobs 1 --threads 2
```

Files: `portfolio-replay.json` (per run, per goal, per tactic: closed, milliseconds, heartbeat limit, first error, suggestion), `portfolio-replay.log` (one line per goal).

## Result

| Goals the model spent turns on | goals | closed by the portfolio | their recorded turns | their recorded dollars |
|---|---|---|---|---|
| library-1, exact contexts (candidate version at the first dialog): rw-compound-comp A2-1, A2-2, A2-topdown-1, -2, -3; rc-knight-router A2-1, A2-2; rw-balancer-upscale A2-1, A2-2 | 372 | 91 (24%) | 276 of 2,700 (10%) | $6.15 of $52.93 (12%) |
| balancer-1 (no candidate versions on disk; final.lean as context, approximate): implement-1, implement-2, repair-A1-1, repair-A1-2, repair-A2-1 | 48 | 1 | 10 of 642 | $0.16 of $10.71 |
| All dialog goals | 420 | 92 (22%) | 286 of 3,342 | $6.31 of $63.65 |

Per run (exact contexts):

| Run | goals | closed | turns closed / all | dollars closed / all | portfolio Lean time |
|---|---|---|---|---|---|
| rw-compound-comp A2-1 | 50 | 19 | 60 / 410 | $1.31 / $8.25 | 475 s |
| rw-compound-comp A2-2 | 51 | 18 | 52 / 375 | $1.17 / $7.71 | 297 s |
| rw-compound-comp A2-topdown-1 | 43 | 9 | 34 / 375 | $0.79 / $8.20 | 255 s |
| rw-compound-comp A2-topdown-2 | 67 | 14 | 41 / 267 | $0.81 / $5.31 | 465 s |
| rw-compound-comp A2-topdown-3 | 46 | 11 | 26 / 465 | $0.59 / $7.58 | 192 s |
| rc-knight-router A2-1 | 39 | 4 | 20 / 267 | $0.54 / $5.35 | 123 s |
| rc-knight-router A2-2 | 35 | 5 | 12 / 241 | $0.28 / $4.74 | 113 s |
| rw-balancer-upscale A2-1 | 18 | 3 | 5 / 147 | $0.15 / $2.69 | 73 s |
| rw-balancer-upscale A2-2 | 23 | 8 | 26 / 153 | $0.50 / $3.10 | 129 s |

- Every closed goal is a helper: a planner lemma or skeleton helper. None of the 84 required-theorem goals of these runs (stated as a predicate of the implementation over every input or every sequence) is closed by any entry.
- The model had eventually proved 84 of the 92 closed goals; 8 closed goals were never proved by the model in the recording.
- 40 of the 92 closed goals cost the model one turn; the most expensive cost 17 turns.
- First closing entry: `exact?` 30, `unfold D at *; intros; grind` 29, `try?` 13, `grind` 13, `intros; grind [D]` 4, `simp_all` 2, `decide` 1. `omega`, `simp_all <;> omega` never closed a goal first; `omega` closed none. The unfolding entries (definitions the goal's own statement names) account for a third of the closures.
- `generalize_divs` and `machine_norm` were never tried: no recorded candidate imports a module that defines them (the compound candidates import `ProofForgeFin.DeFi`).
- A0 (whole-file turns, no goal dialogs): the required theorems left unproved by the final candidates of library-1 rw-compound-comp A0-1, A0-2, rw-balancer-upscale A0-1, A0-2 and baseline-flagships-1 rc-knight-router A0-2, rw-balancer-upscale A0-1, rw-compound-comp A0-1, A0-2 (57 goals, final.lean as context): 1 closed, `req_calls_succeed` of rw-compound-comp A0-2 by `unfold … at *; intros; grind`. The other baseline-flagships-1 A0 runs left nothing unproved.

## Cost

- Batches: 398, median 3.8 s, 90th percentile 6.9 s, longest 242 s (a batch stopped at its wall allowance and compiled again without `exact?` and `try?`; 5 goals). Over all runs 2,384 s of Lean, about 6 s per goal, against recorded runs of 2 to 4 hours each (compound A2-1: 475 s of portfolio against a 7,909 s run).
- Per attempt: the fixed tactics take tens of milliseconds (median `grind` 41 ms, `omega` 16 ms, unfolding entries 72 to 78 ms); `exact?` and `try?` take about a second (median 1.1 s, 90th percentile 3.5 s) and are the only entries the heartbeat limit does not stop: in the first replay with a 20 s per-attempt allowance one ran 516 s, which is why the allowance is now 60 s plus 5 s per attempt and a stopped batch is retried without them.
- No dollars.

## Limits of this measurement

- A closure here is "a renamed copy compiles with no error and no `sorryAx`". Banking re-compiles the whole candidate, which can still fail (placement); the live agent banks only what compiles.
- The saving is an upper bound on turns for each goal: once the portfolio closes a goal the model does not spend those turns, but a dialog on one goal sometimes banks other lemmas too, and a run with the portfolio would take a different path afterwards.
- The portfolio is tried again live when the file's set of complete declarations changes; the replay tries each goal once, at its first dialog, so it may undercount.
- balancer-1 and the A0 runs have no candidate versions on disk, so their context is the final candidate with the goal reopened (`sorry`), marked `approximate_context` in the JSON.

## Resume on recorded runs (no model calls)

`agents/repair.py --task rw-compound-comp --resume-from <library-1 A2-1>,<A2-2>,<A2-topdown-1>` with the loop replaced by a no-op (ledgers reconstructed from the run directories; git shows the task's lock unchanged since those runs): the base is A2-2's best candidate (4 of 8 required theorems proved, re-checked), 295 proved declarations of the three runs are carried after Lean checks, 3 are dropped by Lean (one declaration, `td0_setSpeeds_effect`, in three versions), 8 open goals are queued first, 42 s of Lean. The candidate grows from 107 KB to 234 KB; resumed runs therefore show prompts the compact view (117 KB). `agents/baseline.py --task rw-compound-comp --resume-from <library-1 A0-1>,<A0-2>` starts from A0-1's candidate with 5 of 8 required theorems proved.
