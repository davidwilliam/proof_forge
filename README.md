# ProofForge

ProofForge lets Meta's coding agents repair critical software and ship machine-checked evidence that the repair meets locked requirements.

A component's requirements are written once as Lean 4 predicates over its implementation and locked by hash. A Muse model fixes the buggy code and proves every requirement. The repair counts only if the official checker accepts it in a fresh sandbox and the executable rebuilt from the same source passes property tests derived from the same requirements. The result is a Proof Passport: per-requirement statuses, hashes, commands, axioms, trust assumptions and a one-command reproduction.

## What the protected pipeline adds

A repository that keeps proofs next to the code accepts whatever its own build accepts. A repair can prove a weaker statement under a required theorem's name, ship a modified specification, or compile different code from the code that was proved, and the build stays green; Lean checks each of those proofs correctly, but they are proofs of something else. ProofForge judges every candidate against a locked challenge with Lean's `lake comparator` in a bubblewrap sandbox, replays it with `leanchecker`, rejects code-override constructs, and tests the executable rebuilt from the locked project.

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

Development results (`results/e1-dev-2`, 23 tasks, $3 and 45 minutes per run): A0 completed 19, A1 20, A2 21; the differences are not significant. Every arm completed every rate-limiter and transfer task. Test-set results will be reported here as measured, including a null result.

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
| `.github/workflows/` | proof-carrying PR check |
| `results/`, `reports/`, `recordings/` | measured results, the G0 gate report, recorded sessions |

What was built during the hackathon, and the dependencies that were not, are listed in `ORIGIN.md`.
