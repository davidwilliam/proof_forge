# knight-1: Muse repairs of rc-knight-router

Repair runs of `agents/repair.py` on `realworld/tasks/rc-knight-router`, a child-order router reconstructed from the SEC findings in Release No. 34-70694 (Knight Capital Americas LLC, October 16, 2013); it is not Knight's code. The start candidate is the reconstructed Power Peg defect. Every run used Muse Spark 1.3 on the Contributor tier (`muse-spark-1.3-contributor`), a cap of $10 at standard list prices, and the orchestrated mode with default turn limits. A1 is `--planner none`; A2 adds `--planner muse-wonder-1.0`. The plan was A1 first, up to two attempts, then A2 if A1 failed, up to two attempts.

| Run | Planner | Wall cap | Stopped by | Elapsed | List $ | Charged $ | Required theorems proved | Passport |
|---|---|---|---|---|---|---|---|---|
| A1-1 | none | 7,200 s | wall cap | 7,202 s | 5.31 | 0.32 | 1 of 6 | UNRESOLVED, `4fddc1683956e92f` |
| A1-2 | none | 14,400 s | dollar cap | 8,147 s | 9.60 | 0.57 | 1 of 6 | UNRESOLVED, `27f4c83221ed220e` |
| A2-1 | Wonder 1.0 | 14,400 s | dollar cap | 5,933 s | 9.77 | 1.93 | 5 of 6 | UNRESOLVED, `edc4ec8cd40a2db0` |
| A2-2 | Wonder 1.0 | 14,400 s | accepted | 4,079 s | 4.96 | 0.98 | 6 of 6 | VERIFIED, `98cfed64ae1ec596` |

List $ is at standard list prices for every model (the budget scale); charged $ is at the tier actually used (Spark on the Contributor tier, Wonder at its standard price). Per model: A2-1 spent $8.30 list ($0.47 charged) on Spark and $1.46 on Wonder; A2-2 spent $4.22 list ($0.23 charged) on Spark and $0.74 on Wonder. The four runs together cost $29.64 at list prices and $3.80 charged.

A1-1 ran with a wall cap of 7,200 s and stopped there with $4.69 of its dollar cap unused; the later runs used 14,400 s so that the dollar cap is the binding limit. In every run the behavior phase produced an executable that passes the 2,001 property cases. The A1 runs proved only REQ-NORMAL-ORDER-ROUTED; A2-1 proved every requirement except REQ-FILL-ACCOUNTING.

## The accepted repair

`A2-2/final.lean` (1,616 lines) removes the Power Peg path: every code version and flag value route by the shares not yet sent, and every execution report advances the cumulative executed quantity by the shares it executes. The judge accepted it: Comparator in paranoid mode with the Lean paranoid, lean4lean, nanoda, con-leche, con-ron and Lean default kernels, leanchecker, and the axiom audit (each required theorem uses `propext` and, except REQ-NORMAL-ORDER-ROUTED, `Quot.sound`). Its executable passed 2,001 property cases.

```sh
bin/proofforge verify results/knight-1/A2-2/passport.json --candidate results/knight-1/A2-2/final.lean
```

reproduced every hash and status on the machine that issued it (`A2-2/verify.log`). The Passport's trust assumptions include the task's reconstruction note.

## The start candidate

`start/passport.json` (`ca3e7312fe7af22f`) is the Passport of the reconstructed defect, `realworld/tasks/rc-knight-router/candidate/Solution.lean`: REFUTED on all six requirements by its rebuilt executable. On the flagship case (a 300-share flagged order on the legacy build, three 100-share routing opportunities each followed by a full execution, then a fourth) it sends four child orders, 400 shares, and reports a cumulative quantity of 0. The kernel-checked refutation for every number of rounds is `realworld/tasks/rc-knight-router/witnesses/buggy_original.lean`.

## Files

Per run: `agent.log` (console), `events.jsonl` (every model turn and tool call), `summary.json` (budget accounting and final status), `final.lean`, `passport.json` and `check.log` (`bin/proofforge check` on `final.lean`), the judge record of an accepted version (`judge_v*.json`) and planner replies (`plan_*.md`) where they exist. Intermediate candidate versions are not committed. Text was normalized with `eval/normalize.py` as described in `results/README.md`.
