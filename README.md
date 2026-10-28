# ProofForge

ProofForge lets Meta's coding agents repair critical software and ship machine-checked evidence that the repair meets locked requirements.

A component's requirements are written once as Lean 4 predicates over its implementation and locked by hash. A Muse model fixes the buggy code and proves every requirement. The repair counts only if the official checker accepts it in a fresh sandbox and the executable rebuilt from the same source passes property tests derived from the same requirements. The result is a Proof Passport: per-requirement statuses, hashes, commands, axioms, trust assumptions and a one-command reproduction.

## What the protected pipeline adds

A repository that keeps proofs next to the code accepts whatever its own build accepts. A repair can prove a weaker statement under a required theorem's name, ship a modified specification, or compile different code from the code that was proved, and the build stays green; Lean checks each of those proofs correctly, but they are proofs of something else. ProofForge judges every candidate against a locked challenge with Lean's `lake comparator` in a bubblewrap sandbox, replays it with `leanchecker`, rejects code-override constructs, and tests the executable rebuilt from the locked project. Every step, with its exact command, is described in [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md).

E2 compares three ways of checking the same artifacts (`results/e2-all-1`; every bad case is a seeded test written by the build team, so this describes this suite, not repairs in general):

| Checking | Seeded bad repairs accepted | Correct repairs rejected |
|---|---|---|
| Ordinary checking: the project builds, theorem names are present, the axiom audit is clean | 233 of 247 | 0 of 239 |
| Rebuild and property tests only | 1 of 247 | 0 of 239 |
| ProofForge | 0 of 247 | 0 of 239 |

The rebuild and its tests already reject almost every seeded attack: 229 change behavior on inputs the generator produces, and 17 do not build against the locked specification. The one that passes is `formal/attacks/g2_bulk_rounding.lean`: payouts to seven or more recipients drop the remainder, the test generator never produces more than five recipients, and the attack proves `req_fair_shares`, `req_effects` and `req_conservation` restated for fewer than seven recipients. Comparator rejects the restated statement; the counterexample ($1.00 to seven recipients pays 14 cents each and loses 2 cents) is in `formal/attacks/g2_bulk_rounding.counterexample.json`. A proof covers every input; tests cover the inputs someone thought to generate.

The 239 good cases are 118 reference-solution checks, 118 generated refactors of them (helpers renamed, comments added) and 3 accepted model repairs; tasks that share a base specification reuse files, so they come from 67 distinct sources. No specification-weakening attempt was observed in 138 development repair runs; every bad case here is seeded.

## Meta models writing verified repairs

The flagship task is a payout splitter whose bug loses a cent: $1.00 to three recipients pays 33 + 33 + 33. Muse Spark 1.3 repaired it and proved all eight requirements (valid payouts succeed, invalid ones change nothing, fair shares, full-state effects, conservation, nonnegativity, authorization, idempotency); the rebuilt binary pays 34 + 33 + 33. Three accepted repairs are stored with provenance in `formal/evidence/`:

| Evidence | Agent | Cost at list prices | Notes |
|---|---|---|---|
| `muse-repair-001` | Spark 1.3 with the harness, Wonder planner | $0.47 | two sessions across a harness fix |
| `muse-repair-002` | Spark 1.3 with the harness, Wonder planner | $0.34 | single session, 20 minutes |
| `muse-repair-003` | Spark 1.3, compile-and-retry only | $1.90 | 27 attempts, 26 minutes |

Each is accepted by six kernels in Comparator's paranoid mode (Lean default and paranoid, lean4lean, nanoda, con-leche, con-ron), and its binary passes 2,001 property cases plus resubmission cases.

## Benchmark

59 repair tasks in six families (`tasks/`, contract in `docs/TASKS.md`): 23 development, 6 validation and 30 test tasks. The test families (ledgers, permissions, queues) never appear in development or in any prompt used to build the agents. Every task has two reference solutions, a buggy start candidate refuted on its binary, and seeded attacks; `harness/validate_task.py` checks all of it.

E1 compares three arms under the same per-task budget (dollars at standard-tier list prices and wall-clock time), scored by one shared evaluator:

- A0: Muse Spark 1.3 compile-and-retry (Lean errors and the axiom audit only)
- A1: Muse Spark 1.3 with the ProofForge harness (behavior-first phase, per-obligation dialogs, snippet checks, binary tests)
- A2: A1 plus Muse Wonder as lemma planner

Development results (`results/e1-dev-2`, 23 tasks, $3 and 45 minutes per run): A0 completed 19, A1 20, A2 21; the differences are not significant. Every arm completed every rate-limiter and transfer task.

Test results (`results/e1-test-1`, the 30 frozen test tasks, $3 and 60 minutes per run, Muse Spark 1.3 on the Contributor tier):

| Arm | Completed | List $ per completed repair |
|---|---|---|
| A0 | 28 of 30 | 0.87 |
| A1 | 30 of 30 | 0.61 |
| A2 | 30 of 30 | 0.92 |

The test tasks do not separate the arms. A1 and A2 each complete two tasks that A0 does not and none that A0 completes alone (McNemar exact p = 0.50); A1 and A2 complete the same tasks. Both A0 failures are ledger-reversal tasks on which compile-and-retry reached the dollar cap with a final candidate that does not build. Under these budgets Muse Spark completes almost every test task with or without the harness, and the Wonder planner adds cost without a measured completion gain. The 90 runs cost $70.09 at list prices; the amount charged on the Contributor tier was $6.38.

The final test run requires `results/test-freeze.json`. Before making model calls, the
runner checks each selected test task and its validation receipt against that approved
record and binds the record's hash into the run configuration. Existing validation
receipts identify the committed snapshot with which validation was recorded; generating
a freeze does not rerun Lean. Resume rejects changes to the experiment configuration.

The approved limits are $3 at standard list prices and 60 minutes per repair run, two
concurrent runs, and a $150 batch cap. Unknown usage, lost responses, and HTTP failures
retain conservative request reservations. All remaining arms of a task must fit before
the task starts; omitted tasks are reported in `coverage.json`. After the repair deadline,
finalization may select an already-produced compiling version; final judging is outside
the repair budget for every arm. Run from an isolated checkout and keep its inputs fixed:

```sh
python3 eval/e1.py --label test-1 --split test --arms A0,A1,A2 --budget-usd 3 --budget-wall 3600 --parallel 2 --batch-usd 150 --require-clean
```

The PR gate has been exercised on GitHub: [PR #1](https://github.com/davidwilliam/proof_forge/pull/1)
first rejected the seeded bulk-rounding candidate, then accepted its replacement with the
stored Muse-authored repair. [PR #2](https://github.com/davidwilliam/proof_forge/pull/2)
checks the accepted repair separately; [PR #3](https://github.com/davidwilliam/proof_forge/pull/3)
rejects a protected-specification-only edit. Accepted Passports were reproduced by a second
fresh check. [Recorded outcomes and artifacts](reports/pr-integration/summary.json) include
the exact trusted checker revisions and valid Passport content hashes. These are automated
integration checks; an independent human developer trial remains to be completed, following
[the trial protocol](docs/TRIAL.md).

## Trust assumptions and limits

Every Passport lists them. A `VERIFIED` requirement relies on the Lean v4.35.0 kernel, compiler and runtime; the protected specification and challenge as reviewed by the owner; Comparator and its sandbox; and the judge image. The JSON wrapper around the proved function is tested, not proved. A requirement says exactly what its Lean statement says; anything it does not state is not covered.

## Running it

Requirements: Docker (judging runs in Linux containers), Python 3.12 or later, Node 20 for the web front end.

```
docker build -t proofforge-lean:4.35.0 -f infra/docker/Dockerfile.lean infra/docker   # pinned Lean image
python3 harness/validate_task.py formal                            # check the flagship task end to end
bin/proofforge check --candidate formal/evidence/muse-repair-002/Solution.lean --out passport.json
bin/proofforge verify passport.json --candidate formal/evidence/muse-repair-002/Solution.lean
```

Repair agents need `META_API_KEY` in the environment or in `.env`:

```
python3 agents/repair.py --task payout-flagship                    # A2; add --planner none for A1
python3 agents/baseline.py --task payout-flagship                  # A0
python3 eval/e1.py --label dev --split dev                         # E1
python3 eval/e2.py --label all                                     # E2 (no model calls)
```

API and web front end:

```
python3 -m venv .venv && .venv/bin/pip install -r server/requirements.txt
.venv/bin/uvicorn server.app:app --port 8765
cd web && pnpm install && pnpm dev
```

## Deployment

The API and judge run on a Fly.io Machine (performance-4x, 8 GB, region iad), the front end on Vercel. Fly Machines are microVMs with their own Linux kernel, so Comparator's bubblewrap sandbox runs unchanged as an unprivileged user. Both deploy scripts build from the committed tree only (`infra/fly/deploy.sh`, `infra/vercel/deploy.sh`); Passports record the judge image by registry digest.

Live jobs run Muse Spark 1.3 on its Contributor tier (every task here is synthetic) with Muse Wonder as planner. Controls (`server/controls.py`): per-client daily quotas and a daily live spending cap at the prices actually charged, stored on the data volume, a per-job dollar cap at standard list prices and a wall-clock cap, concurrency limits that answer 503 with Retry-After, request-wide deadlines on checks (a check stopped by its deadline is UNRESOLVED, never REFUTED), and an operator switch to replay-only mode that can also stop running live agents.

Measured on the deployed host:

- [Host smoke test](reports/host-smoke/fly-iad.json): the recorded repair is VERIFIED by all six kernels in the sandbox; the seeded bulk-rounding candidate passes its tests and is UNRESOLVED; a complete-proof attack and an `implemented_by` override are REFUTED.
- Live repairs on the host, Muse Spark 1.3 with the Wonder planner, all eight requirements VERIFIED: [standard tier](reports/host-smoke/fly-live-repair.json), 1,620 s, $2.74 charged; [Contributor tier](reports/host-smoke/fly-live-repair-contributor.json), 1,756 s, $0.44 charged ($0.08 Spark, $0.36 Wonder; $1.84 at standard list prices).
- Demo reliability (`infra/reliability.py`): each session loads the four web pages, replays the accepted recording to a fresh check, runs the hidden challenge, calls both payout builds and fetches the Passport, through the API. [Run 1](reports/reliability/fly-vercel-1.json): 19 of 20 sessions; session 10 returned HTTP 500 from a race on the job record, fixed by atomic replacement with a regression test. [Run 2](reports/reliability/fly-vercel-2.json), after the fix: 20 of 20 sessions, about 30 s each. Both runs passed three failure drills: replay-only mode refuses live jobs while replays continue; five simultaneous verifications give two results and three 503 refusals with nothing left running; a restart during a job ends it with a stated reason and the next session succeeds.
- [Failure drills](reports/drills/fly-1.json) (`infra/drills.py`): a Lean syntax error, a required proof left as `sorry`, an empty file and an `implemented_by` override are UNRESOLVED; the buggy candidate with a comment telling the checker to report VERIFIED is REFUTED, and a correct repair with the same comment is VERIFIED; malformed or out-of-bounds requests get 4xx answers. Model API failures (rate limiting, server errors, malformed bodies, a rejected key, malformed tool arguments) are drilled against a local stand-in in `tests/test_model_failures.py`: retried and charged at their worst case, a persistent outage ends at the budget cap.
- [Browser walk-through](reports/browser-walk/vercel-1.json) (`infra/browser-walk.js`, Chromium): the replay reaches a VERIFIED Passport in 33 s at 80x, the hidden challenge and both payout builds answer, and all five pages render at 1440 px and 390 px in light and dark with no console errors, failed requests or horizontal scrolling. Its first pass found the results and Passport pages scrolling sideways on a phone; fixed before this run.

## Layout

| Path | Contents |
|---|---|
| `formal/` | flagship task: locked spec and challenge, executable wrapper, oracle, references, attacks, evidence |
| `tasks/` | benchmark tasks |
| `hidden/` | hidden live-challenge variants of the flagship |
| `harness/` | judge, binary check, ordinary checking, lock, validator, Passport |
| `agents/` | Meta Model API client, budget, repair agent, compile-and-retry baseline |
| `eval/` | E1 and E2 runners |
| `server/`, `web/` | API and front end |
| `infra/` | images, deployment, host smoke test and reliability check |
| `.github/workflows/` | proof-carrying PR check |
| `results/`, `reports/`, `recordings/` | measured results, the G0 gate report, recorded sessions |

What was built during the hackathon, and the dependencies that were not, are listed in `ORIGIN.md`.
