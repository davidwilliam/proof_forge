# library-1: Muse with ProofForgeFin versus Muse alone on three flagship tasks

Measured runs on `rw-compound-comp`, `rc-knight-router` and `rw-balancer-upscale`, October 30 to 31,
2026. Every run has the same caps: $10 at standard list prices (`agents/budget.py`) and 14,400 s of
wall time, with the model `muse-spark-1.3-contributor` at medium effort.

- A0 is `agents/baseline.py`, Muse Spark alone with compile-and-retry.
- A2 is `agents/repair.py` with the Muse Wonder planner (`--planner muse-wonder-1.0`) and the library (`--library on`).
- The A2 runs on Knight and Balancer, and the orchestrated A2 runs on Compound, use library version `f2fbb0d3610136fa`.
- The top-down runs used the `--loop topdown` code at the commit given in each row (see their `summary.json`).

| Task | Run | Loop | Outcome | Requirements proved | Time s | List $ | Charged $ | Stop |
|---|---|---|---|---|---|---|---|---|
| rc-knight-router | A2-1 | orchestrated | VERIFIED | 6/6 | 3,835 | 6.31 | 1.25 | |
| rc-knight-router | A2-2 | orchestrated | VERIFIED | 6/6 | 4,516 | 5.51 | 1.02 | |
| rw-balancer-upscale | A2-1 | orchestrated | VERIFIED | 8/8 | 2,717 | 3.07 | 0.46 | |
| rw-balancer-upscale | A2-2 | orchestrated | VERIFIED | 8/8 | 4,080 | 3.60 | 0.57 | |
| rw-balancer-upscale | A0-1 | | UNRESOLVED | 0/8 | 14,400 | 8.90 | 0.45 | wall |
| rw-balancer-upscale | A0-2 | | UNRESOLVED | 0/8 | 13,175 | 9.86 | 0.53 | dollars |
| rw-balancer-upscale | A0-3 | | VERIFIED | 8/8 | 6,613 | 4.38 | 0.23 | |
| rw-compound-comp | A0-1 | | UNRESOLVED | 5/8 | 14,402 | 9.68 | 0.50 | wall |
| rw-compound-comp | A0-2 | | UNRESOLVED | 0/8 | 14,400 | 8.25 | 0.42 | wall |
| rw-compound-comp | A2-1 | orchestrated | UNRESOLVED | 3/8 | 7,909 | 9.82 | 1.79 | dollars |
| rw-compound-comp | A2-2 | orchestrated | UNRESOLVED | 4/8 | 8,982 | 9.72 | 2.15 | dollars |
| rw-compound-comp | A2-topdown-1 | topdown at 2960943 | UNRESOLVED | 2/8 | 7,685 | 9.83 | 1.74 | dollars |
| rw-compound-comp | A2-topdown-2 | topdown at 17e31c1 | UNRESOLVED | 0/8 | 5,285 | 9.79 | 4.79 | dollars |
| rw-compound-comp | A2-topdown-3 | topdown at b581535 | UNRESOLVED | 0/8 | 6,311 | 9.49 | 2.02 | dollars |

"Requirements proved" is the final snapshot's status in the run's own check. The Passports in the
VERIFIED rows were issued by `bin/proofforge check` on `final.lean` (`passport.json`, `check.txt`) and
reproduced by `bin/proofforge verify` (`verify.txt`).

## Balancer across all measured runs

Earlier runs on the same task and caps are in `results/baseline-flagships-1/rw-balancer-upscale`
(A0-1 UNRESOLVED at $9.61, A0-2 VERIFIED at $7.29) and `results/balancer-1` (`repair-A2-1` VERIFIED at
$2.51, run before the library existed).

| Arm | Verified | List $ over all runs | List $ per verified run |
|---|---|---|---|
| Muse alone (A0) | 2 of 5 | 40.04 | 20.02 |
| Muse with ProofForge and the planner (A2, library on in 2 of the 3 runs) | 3 of 3 | 9.18 | 3.06 |

The three Muse-alone runs that did not verify (`library-1` A0-1 and A0-2, `baseline-flagships-1` A0-1)
were checked again with `bin/proofforge check` on their `final.lean` (`passport.json`, `check.txt` in each
run directory): each is UNRESOLVED, with all eight proofs `sorry` and its executable passing all 2,001
generated property cases. Each rewrote the given-out path to price the exact amount out rounded up and
to refuse it unless that amount is below the scaled balance; none is refuted.

With ProofForge, every run verified (3 of 3) at $3.06 per verified run, 6.5x cheaper than Muse
alone at $20.02 (2 of 5). One-sided Fisher exact test on the verification rate: p = 0.18 with 8 runs;
at the same rates, 10 runs per arm give p = 0.0054, and with more runs we expect the rate difference
to reach p below 0.05.

## Compound

Muse Code with ProofForge later verified Compound: 2 of 10 runs in `results/frontier-3` and 8 of 10
in `results/frontier-4`, against 0 of 10 on its own (p = 0.00036). In this experiment no run
verified it; the build team's proof showed the specification is provable with the library:
`results/library-live-1`, Passport `b654d456`.

- **Orchestrated loop (A2-1, A2-2):** it works through the requirements in listed order and spends the budget on the per-call requirements before it reaches the three sequence bounds.
- **A2-topdown-1:** Lean accepted the skeleton on the first try, and it proved 6 of its 15 helpers. A pruning step removed the one-step helpers, because nothing used them yet while the run-level helpers were still `sorry`. Fixed in 492a8ae.
- **A2-topdown-2:** a short first attempt for every helper (`--probe-turns 5`) with planner decomposition after it sent 45% of the dollars to Muse Wonder and closed no helper. That change was dropped. Its commit, 17e31c1, is kept under the tag `topdown-fill-probe`.
- **A2-topdown-3:** it proved 7 helpers below the bounds. Lean's record of the final file (web/generated/shapes, docs/SHAPES.md) shows 11 lemmas left `sorry` inside the guarantees' shapes: `td0_exec_inv` under all three sequence bounds, `td0_exec_potentialTo_le` under ACCOUNT-BOUNDED and NO-BACKDATED-REWARDS, four more under REWARDS-BOUNDED and NO-BACKDATED-REWARDS, and one under each per-call guarantee.

Some final files keep exploration artifacts: `#check` lines and throwaway lemmas, for example
`fooTest123` in A2-1. They do not affect the status of any requirement.

`candidate_v*.lean` snapshots are not tracked (see `.gitignore`). `events.jsonl` records every model
call, tool call and check.
