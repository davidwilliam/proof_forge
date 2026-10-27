# Results

Each experiment directory holds the runner configuration, the generated report and, per task and arm, the agent's final candidate (`final.lean`), the shared evaluator's verdict (`eval.json`), the agent summary with budget accounting (`summary.json`), the event log (`events.jsonl`) and the console log (`agent.log`). Intermediate candidate versions are not committed.

Model-written text in these files is verbatim except that em dashes are replaced with semicolons and en dashes with hyphens (`eval/normalize.py`).

| Directory | What | Notes |
|---|---|---|
| `e1-dev-1` | E1 on the 23 dev tasks, arms A0, A1, A2, $3 list and 2700 s per run | before the harness fixes in commit f8e0e6d; two runs lost to network timeouts |
| `e1-dev-2` | the same, after those fixes | used to set the test-run caps |
| `e2-dev-flagship` | E2 on the flagship task | before the complete-proof attacks were added |
