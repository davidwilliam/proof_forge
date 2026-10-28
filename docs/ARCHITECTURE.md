# Architecture

This describes the system as built. Each section names the code that implements it.

## Components

| Component | Code | Role |
|---|---|---|
| Task | `formal/`, `tasks/<id>/`, `harness/task.py`, `harness/lock.py` | one locked Lean project: protected spec, challenge, executable wrapper, oracle |
| Judge | `harness/judge.py` | decides proof acceptance from exit codes only |
| Binary check | `harness/binary_check.py` | rebuilds the executable and runs requirement-derived property tests |
| Passport | `harness/passport.py`, `bin/proofforge` | assembles statuses, hashes and provenance; reproduces a Passport |
| Repair agents | `agents/repair.py`, `agents/baseline.py`, `agents/meta_client.py`, `agents/budget.py` | Meta models fix the code and write the proofs |
| Evaluation | `eval/e1.py`, `eval/e2.py`, `eval/freeze.py`, `harness/ordinary.py` | completion under equal budgets (E1); integrity of checking (E2) |
| PR gate | `.github/workflows/proofforge.yml` | judges a pull request's candidate from a trusted checkout |
| API and web | `server/app.py`, `server/controls.py`, `web/` | jobs, replays, checks, Passports, the payout sidecar, the hidden challenge |
| Images and hosting | `infra/docker/`, `infra/fly/`, `infra/vercel/` | pinned Lean image; Fly.io Machine for the API and judge; Vercel for the web |

## Task

A task is a self-contained Lake project (format in `docs/TASKS.md`). `spec/<Lib>/Spec.lean` defines the requirement predicates over the implementation; `spec/<Lib>/Challenge.lean` states the definition holes and the required theorems with `sorry`; `spec/comparator.json` names the challenge and solution modules, the theorems, the definitions under repair and the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`). `harness/lock.py` writes `spec/locked.json`: the SHA-256 of every protected file and a manifest hash over them. `oracle.py` is an independent Python model of the component used only by the binary check. The candidate is `candidate/Solution.lean` (and optionally `candidate/Lib/**`); it is the only input taken from an agent or a pull request.

## Judge

`judge.judge(candidate, task)` runs, in order:

1. Tree check. Every protected file present in the submitted workspace must be byte-identical to `spec/locked.json`; the lock must be internally consistent, cover exactly the protected files, and match the repository's copies.
2. Implementation scan. After stripping comments, the candidate must not contain `implemented_by`, `extern`, `unsafe`, `@[export]`, `macro`, `elab`, `syntax`, `initialize`, `#eval`, `run_cmd`, `run_elab`, `run_meta`, `native_decide`, `set_option`, `opaque`, `axiom` or `@[csimp]`, and may import only the task's `Spec` and `Lemmas`, `Init.*` and `Std.*`. This is defense in depth against code overrides and elaboration-time code; Comparator is the authority on statements.
3. Fresh project. A new temporary directory receives the locked project files from the repository (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `spec/`, `app/`) and the candidate files, nothing else. It has never been built.
4. Comparator: `lake comparator --paranoid --config spec/comparator.json`. Comparator builds the solution in its bubblewrap sandbox, checks that every required theorem has exactly the challenge's statement, with the definitions under repair supplied by the solution, checks that only the permitted axioms are used, and checks the declarations with six kernels: Lean's default and paranoid modes, lean4lean, nanoda, con-leche and con-ron. Any failure rejects the candidate.
5. leanchecker: `lake build Solution && lake env leanchecker Solution`, a kernel replay of the solution module's declarations. It runs without `--fresh`, so imported modules (the locked spec and Lean's core library) are loaded from their build outputs rather than replayed; Comparator's kernels above check the solution's declarations independently.
6. Axiom audit: `#print axioms` for every required theorem. The result is recorded per theorem in the Passport; enforcement of permitted axioms is Comparator's.

The candidate is accepted only if steps 1, 2, 4 and 5 succeed. Lean runs in the pinned image `proofforge-lean:4.35.0` (`infra/docker/Dockerfile.lean`: Lean v4.35.0 from the GitHub release, checked against its published SHA-256). Locally each run is a `docker run --network none --memory 4g --pids-limit 512` container with the namespaces bubblewrap needs; inside the image (the Fly host, `PF_IN_IMAGE=1`) commands run directly and Comparator's sandbox applies the same way. Concurrent Lean runs per host are bounded by file locks (`PF_CONTAINER_SLOTS`, default 2). Every run has a timeout; callers can impose a request-wide deadline (`judge.time_limit`), and a run stopped by it is marked as a timeout, never as a failure of the candidate.

## Binary check

`binary_check.check_binary` builds the task's executable (`lake build <exe>`) in another fresh project from the same locked files and candidate, records its SHA-256, and runs JSON-lines cases through it. Round 1 is the oracle's flagship case plus N generated cases (2,000 for Passports, seed 0; the E1 evaluator uses seed 1). Round 2 runs follow-up cases the oracle derives from round-1 outputs, such as resubmitting an applied transaction. `oracle.check` maps each output to requirement IDs it violates; the first witnesses (input, output, message) are kept. Status is `PASS`, `REFUTED`, `BUILD_FAILED` or `TIMEOUT`.

The executable wrapper `app/Main.lean` (JSON parsing and printing) is locked but not proved; the Passport labels it tested only.

## Passport

`passport.build` combines one judge record and one binary record:

| Requirement status | Condition |
|---|---|
| VERIFIED | the judge accepted and the binary passed every case |
| REFUTED | the binary violated this requirement on a concrete input (witness recorded) |
| UNRESOLVED | anything else, including a rejected proof without a witness and a check stopped by a time limit |

The component is VERIFIED only if every requirement is, REFUTED if any requirement is, and UNRESOLVED otherwise. The Passport records the task and manifest hashes, the statement of each requirement, the candidate and solution-tree hashes, the executable hash, the Lean toolchain and judge image digest, per-check exit codes and timings, the six kernel names, the axioms per theorem, the trust assumptions, model and budget provenance when an agent produced the candidate, and a reproduce command. `passport_sha256` is a hash of the canonical JSON without that field. `bin/proofforge verify passport.json --candidate PATH` re-runs the pipeline and compares every recorded hash and status.

## Repair agents

All agents call the Meta Model API through `agents/meta_client.py` (chat completions with tool calls; transient network errors are retried within the run's deadline).

- A0, compile-and-retry (`agents/baseline.py`): Muse Spark 1.3 receives the brief, the spec and the buggy file and returns a complete `Solution.lean`; the harness replies with Lean errors, or with the axiom audit and scan violations once it compiles. No tests, snippets or planner.
- A1, harness (`agents/repair.py --planner none`): Muse Spark 1.3 works through tools in a private copy of the task without reference solutions: `read_file`, `write_solution`, `replace_declaration`, `try_snippet` (compiles a snippet after the current file and banks its proved declarations), `check` (per-theorem PROVED, SORRY or ERROR with goal states) and `run_tests` (the binary check). Phase 0 fixes behavior until the tests pass; phase 1 runs one dialog per obligation; phase 2 retries what is left; phase 3 spends any remaining budget on whole-file repair. Banking a proved snippet is transactional, and the run's result is its last compiling version.
- A2, harness with planner (`--planner muse-wonder-1.0`): in phase 2 Muse Wonder proposes helper lemma statements for an obligation that resisted direct proof; they are installed as `sorry` targets and proved by Spark, recursively to depth 2. Helpers left unproved and unused are pruned.

`agents/budget.py` enforces a dollar cap and a wall-clock cap per run. Dollars are counted at standard-tier list prices for every model, including calls served by the Contributor tier, so arms compare on one scale; the amount actually charged is tracked separately. Each call is charged its worst case before it is sent and settled from reported usage. The agent never decides acceptance; its last compiling version is judged by the shared evaluator.

## Evaluation

E1 (`eval/e1.py`) runs every arm once per task under identical caps and scores each final candidate with the judge and the binary check, outside the budget. A test run requires the approved freeze (`results/test-freeze.json`, `eval/freeze.py`), which binds the selected tasks, their validation receipts and the experiment configuration by hash; resume rejects any change. E2 (`eval/e2.py`) checks the same artifacts three ways: ordinary checking (`harness/ordinary.py`: the candidate's own project, including any spec files it ships, builds; required theorem names exist; the axiom audit is clean), the rebuild and tests alone, and ProofForge.

## PR gate

`.github/workflows/proofforge.yml` checks out the base branch as the trusted checker and the pull request head as data, builds the pinned image, runs `bin/proofforge check` on the PR's candidate from the trusted checkout, reproduces an accepted Passport with `bin/proofforge verify`, comments the result on the PR, uploads the Passport with the trusted checker revision, and fails unless the result is VERIFIED.

## API and deployment

`server/app.py` (FastAPI) serves:

- Jobs (`POST /api/jobs`): a replay re-emits a recorded session's events with compressed timing, labeled "Recorded run", then checks the recorded final candidate fresh; a live job runs `agents/repair.py` as a separate process (Muse Spark 1.3 on the Contributor tier with the Wonder planner by default), then checks its final candidate fresh. Events stream over server-sent events. Only public tasks are reachable; hidden variants and paths are refused.
- Checks (`POST /api/verify`): the full Passport pipeline on a submitted candidate, under a request-wide deadline.
- The payout sidecar (`POST /api/payout`): the buggy and repaired executables, built once and run on a single request.
- The hidden challenge (`POST /api/challenge`): 300 property cases against the start candidate of a hidden flagship variant, returning a witness or UNRESOLVED.
- Operator controls (`/api/admin/*`): replay-only mode and stopping live jobs.

`server/controls.py` keeps per-client daily quotas, the live spending ledger (reserved at the per-job cap, settled at the amount charged) and the operating mode in SQLite on the data volume, and bounds concurrent jobs, live jobs, checks and challenges, answering 503 with Retry-After when full. Job records and Passports are replaced atomically; a restart marks unfinished jobs FAILED with the reason.

The API and judge run as one Fly.io Machine (performance-4x, 8 GB, a 10 GB volume) built from the committed tree by `infra/fly/deploy.sh`; the Machine is a microVM with its own kernel, so bubblewrap runs as an unprivileged user. Passports record the image by registry digest. The web front end (Next.js) is deployed to Vercel by `infra/vercel/deploy.sh`.

## Not covered

A VERIFIED requirement covers exactly its Lean statement. The JSON wrapper is tested, not proved. The judge trusts the Lean toolchain, Comparator and its sandbox, the judge image, and the owner's review of the protected spec. The pipeline does not check that the requirements describe what the owner intends; that review is the owner's.
