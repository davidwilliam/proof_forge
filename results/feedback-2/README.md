# feedback-2: goal tool, refutation by sampling, parallel variants

No model calls. Three measurements of the features in `docs/ARCHITECTURE.md` (Goal tool and persistent Lean session; Refutation of new helpers on concrete values; Parallel short variants), each on recorded runs of the main checkout (`results/library-1`, `results/balancer-1`, read only). Library source tree `34d63d5e…`, the pinned image `proofforge-lean:4.35.0`, `LEAN_NUM_THREADS=2`. The machine was shared with other Lean work throughout (load average 18 to 34), so absolute times are high; both paths of a comparison ran under the same load, one after the other.

Files: `goal-replay-rw-compound-comp-A2-2.json`, `refute-replay.json` and `refute-replay.log`, `variants-sim.json`.

## 4. Goal tool: latency and answer size against full-file compiles

```
python3 agents/goal_replay.py ../library-1/rw-compound-comp/A2-2 --out results/feedback-2 --snippets 40 --threads 2
```

40 consecutive `try_snippet` calls of rw-compound-comp A2-2 (calls 118 to 157 of 296, in dialogs on three required theorems and five planner lemmas; 19 candidate versions of 36 to 62 KB), each checked on the candidate version it was recorded against, first as the agent did then (`lake env lean Scratch.lean`, which elaborates the whole candidate again), then on the persistent session (the scratch text sent as one incremental edit). Times are Lean's, measured after a container slot is held.

| | snippets | compile path, median (mean, p90) | session, median (mean, p90) |
|---|---|---|---|
| failing (an error or a `sorry`) | 22 | 4.23 s (4.58 s, 6.65 s) | 0.50 s (0.64 s, 0.58 s) |
| clean (then compiled and banked as before) | 18 | 5.79 s | 0.47 s before the same compile |

- All 40 verdicts agree (failing or clean). The first replay found one disagreement: a snippet whose only warning was a deprecation, which the compile path does not show and the session counted; the session now applies the compile path's rule exactly (commit `leanserver: decide a snippet clean exactly as the compile path does`).
- The session elaborated the whole candidate once (3.85 s, its first use) and incrementally after that, across the 19 candidate versions of the window.
- Lean time for the 40 checks: 205 s on the compile path, 127 s with the session (failing snippets 101 s to 14 s; clean ones pay 0.47 s more each, 113 s instead of 104 s), 38% less.
- Per turn: in the recorded run a dialog turn with a snippet took 13.6 s (median, model call included) of which 4.1 s were snippet checks, and 151 of the 296 snippets failed (2.96 s median then). A turn whose snippet fails is about 3.7 s shorter with the session at the replay's times (4.2 s to 0.5 s), a quarter of the median turn.
- `goal_at` on the dialog's goal (40 calls): 0.41 s median, 217 bytes median (1,225 at most): hypotheses and goal at each `sorry` of the goal.

Tokens. There is no saving in the answers to failing snippets: the session's answers are the same Lean messages, complete where the compile path's `tail -c 9000` had cut long ones, plus the proof state at each `sorry`. Within the 6,000 characters `try_snippet` returns, the 22 failing snippets got 23.6 KB from the compile path and 41.8 KB from the session (16 without `sorry`: 18.6 KB and 24.8 KB; 6 with `sorry`: 5.0 KB and 17.0 KB, the difference being the proof states). What `goal_at` can replace is the snippet the model writes only to see a state: 32 of the run's 296 snippets contained `sorry`, 989 bytes of model output each on average (31.6 KB in all), against a call of about 60 bytes that returns 217. At list price (Spark: $1.25 per million input tokens, $4.25 output) these amounts are a fraction of a cent per turn; the measurable gain is latency.

## 6. Refutation of introduced lemmas on concrete values

```
python3 agents/refute_replay.py <library-1 A2 runs> <balancer-1 runs> --out results/feedback-2 --jobs 1 --threads 2
```

Every lemma the recorded runs introduced, sampled with the probe of this commit (64 instances, task generator values first) in the candidate version written when it was introduced, joined with the turns and list-price dollars the recording then spent on it: the library-1 A2 runs (nine) and balancer-1 repair-A2-1 (the other balancer-1 runs introduced no lemma: A1 and implement runs have no planner, and no model stated a helper with `sorry` through replace_declaration). 2,730 s of Lean, one probe at a time.

| | lemmas |
|---|---|
| introduced (planner lemmas 327, skeleton helpers 47) | 374 |
| sampled, no counterexample in 64 instances | 276 |
| shown false (counterexample, kernel-checked refutation) | **0** |
| unsupported: not decidable after unfolding (an `∀` over an unbounded type, an `∃`, equality of structures holding functions) | 70 |
| unsupported: no values (a binder of type `Acct → Prop`) | 1 |
| not run: the context does not build in the replay workspace (`Solution` missing) | 18 |
| not run: probe stopped at its wall allowance | 2 |
| already proved in its context | 7 |

- **Zero introduced lemmas would have been flagged false, so zero turns would have been saved.** The recordings agree: no model `refute_helper` call succeeded in these runs, and of the 276 sampled lemmas the model later proved 175; the other 101 (818 turns, $15.59) were never proved, and none has a counterexample among 64 instances, so they were hard or needed context, not false, as far as sampling can tell.
- The probe does catch false statements of this shape: `tests/test_lean_feedback.py` refutes `n - m + m = n`, the token-bucket capacity bound without its hypothesis, a step lemma whose post-state comes from the step equation (`step s r = (.ok, s')`) and a predicate without a `Decidable` instance; the earlier top-down test's planted false helper `td0_capacity_step` is rejected at skeleton acceptance.
- Coverage: the probe ran on 347 lemmas and sampled 276 of them (80%); every instance was decided for all but one of those. The rc-knight-router lemmas are mostly unsupported (44 of 62): they quantify over every event sequence or compare whole states that hold functions.
- Cost: 69 probes, 30 s median each, 5.9 s per statement median (each probe includes `lake build Solution`, which a live run has usually just done).
- The first version of the probe reached 259 lemmas (76 unsupported, 32 not run); binders fixed by a hypothesis equation, unfolding of predicates without an instance and fuel only for constructor nesting brought it to 276. The result was zero false in both.

## 7. Parallel short variants: can they win at list price?

`agents/variants_replay.py` (no model calls, no Lean) on the recorded token counts of the library-1 A2 runs and the balancer-1 runs. File: `variants-sim.json`.

```
python3 agents/variants_replay.py <library-1 A2 runs> <balancer-1 runs> --out results/feedback-2
```

What the recordings hold:

- 165 goals were still open after their first dialog (median 12 turns, the full allowance). After that first dialog the runs spent $56.65 at list price on them (later dialogs on the goal, planner calls for it, and the dialogs on its plan lemmas; mean $0.34, median $0.11 per goal), and 65 of them were proved in the end.
- 112 later dialogs on those goals exist; 64 of them came without a planner decomposition of their goal before them. Success within T turns: all later dialogs 28.6% (T=2), 39.3% (T=4), 46.4% (T=6); later dialogs without a decomposition 12.5%, 25.0%, 31.2%. A turn costs $0.016 (median).

A variant is simulated as a draw of one recorded later dialog: it succeeds at turn j if that dialog proved its goal by turn j <= T, and its turns cost what that dialog's turns cost. K variants run in lockstep, stop at the first success, and every turn any of them started is charged (a request in flight is charged). If none succeeds the run continues as recorded. Four models, from optimistic to conservative:

| model (draws from) | K=2, T=2 | K=2, T=4 | K=2, T=6 | K=3, T=2 | K=3, T=4 | K=3, T=6 |
|---|---|---|---|---|---|---|
| pooled: any later dialog of any goal | -$11.27 | -$13.83 | -$14.48 | -$12.67 | -$14.97 | -$15.63 |
| pooled, without a preceding decomposition | +$4.96 | +$1.97 | +$2.29 | +$8.06 | +$4.64 | +$5.28 |
| same goal: the goal's own later dialogs | -$7.31 | -$2.49 | +$2.85 | -$2.55 | +$6.08 | +$15.13 |
| same goal, without a preceding decomposition | +$12.90 | +$22.27 | +$30.73 | +$19.49 | +$33.90 | +$46.86 |

Change in list-price dollars against the $56.65 recorded (negative is a saving). The variants themselves cost $13 to $49 across the table.

Reading:

- Variants win at list price only in the models that credit them with help they would not have. The pooled models treat a short dialog on any goal as a draw for every goal (they also predict 88 to 150 proved goals where the recordings proved 65, which no harness change of this kind delivers); the "same goal" model uses later dialogs that, in A2, mostly came after a planner decomposition had proved helper lemmas for the goal.
- In the most conservative model, a variant is a later dialog on the same goal with no decomposition before it. Only 55 of the 165 goals have one, and variants win 8 goals (K=2, T=2) to 20 (K=3, T=6). Variants then cost more than they save in every configuration: +$12.90 (+23%) for K=2, T=2, up to +$46.86 for K=3, T=6.
- Break-even: with K=2, T=2 the variants cost $0.08 per stuck goal, so they must win at least 23% of stuck goals to pay for themselves at the mean recorded cost after a first dialog ($0.34). The recordings show 5% (8 of 165) for a direct retry without decomposition.
- So, plainly: on these recordings, parallel variants cannot be shown to win at list price; under the assumption closest to what a variant actually is (a fresh short retry of the same goal right after its first dialog), they lose. What they buy is wall-clock time when they win: the K variants of a stuck goal take about T turns of wall time, where the recorded path went on to a planner decomposition and lemma dialogs one after another.
- The default is the cheapest setting, K=2 with T=2 turns (`--variants 2 --variant-turns 2`): it has the smallest loss in the most conservative model (+$0.08 per stuck goal) and the largest saving in the same-goal model; it saves in two of the four models, as every setting with K=2 and T up to 4 does. For equal-budget comparisons until a live measurement exists, `--variants 0` turns them off.

## Limits of these measurements

- One recorded task for the goal tool, one window of 40 snippets; candidates of other tasks and sizes will give other times. The session's advantage grows with the time the compile path spends elaborating the unchanged candidate.
- The refutation replay samples each lemma in the context where it was introduced, with the probe of this commit; a live run samples the same statements at the same points. Lemmas whose context does not build in the replay workspace, or whose probe hit its wall allowance under the machine's load, are counted as not run.
- The variants simulation uses recorded dialogs as stand-ins for variants; no variant was run against a model. Its conservative and optimistic bounds differ by $60 on $57.
