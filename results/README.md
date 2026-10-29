# Results

Each experiment directory holds the runner configuration, the generated report and, per task and arm, the agent's final candidate (`final.lean`), the shared evaluator's verdict (`eval.json`), the agent summary with budget accounting (`summary.json`), the event log (`events.jsonl`) and the console log (`agent.log`). Intermediate candidate versions are not committed.

Model-written text in these files is verbatim except that em dashes are replaced with semicolons and en dashes with hyphens, and absolute paths into the checkout that produced a run are written relative to the repository root (`eval/normalize.py`).

| Directory | What | Notes |
|---|---|---|
| `e1-dev-1` | E1 on the 23 dev tasks, arms A0, A1, A2, $3 list and 2700 s per run | before the harness fixes in commit f8e0e6d; two runs lost to network timeouts |
| `e1-dev-2` | the same, after those fixes | used to set the test-run caps |
| `e1-test-1` | E1 on the 30 frozen test tasks, arms A0, A1, A2, $3 list and 3600 s per run, Muse Spark 1.3 on the Contributor tier | run from an isolated checkout under `results/test-freeze.json`; all 90 runs completed, none set aside |
| `e2-dev-flagship` | E2 on the flagship task | before the complete-proof attacks were added |
| `e2-all-1` | E2 on all 59 tasks: 247 seeded bad cases (232 with complete proofs), 239 good cases (references, generated refactors, accepted model repairs) | ordinary checking vs ProofForge on the same artifacts |
| `natural-1` | every intermediate candidate the Muse agents saved in E1 and the flagship development runs (5,860 versions, 234 runs): behavior search on each distinct implementation, static integrity findings, the judge on flagged representatives | no model calls; candidate versions are not committed, `candidates.jsonl` records their hashes; see its README |
| `cetus-1` | rw-cetus-shlw (Cetus `checked_shlw`): Muse repair arm A1 (`repair-A1-1`, Muse Spark 1.3 on the Contributor tier, $10 list cap) with its Passport and `verify` output, Passports of the three Lean ports (`passports/`), and the real Move code at the pinned commits run with the Sui CLI against the proved component (`real-code/`, `eval/realworld_cetus.py`) | A1 was accepted on its first attempt, so A2 was not run |
| `euler-1` | real-world task `rw-euler-donate` (Euler Finance v1 donateToReserves): the A1 Muse repair with its Passport and reproduction, Passports of the port and the reference, and the real contracts at the pinned commit run in Foundry (`eval/realworld_euler.py`) | A1 succeeded in its first attempt, so A2 was not run |
