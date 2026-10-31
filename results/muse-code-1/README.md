# muse-code-1: Muse Code alone versus Muse Code with ProofForge

Measured runs of Meta's Muse Code (`muse exec`, version 1.4.14, build 1.4.14-R7309.1, stable channel,
auto-update off) on four real-world tasks, October 31, 2026. The runner is `agents/muse_code.py`.

## Arms

Both arms use the same model, prompt, caps and Muse Code flags.

- **Muse Code alone (`alone`).** The task's locked Lean project, the buggy candidate and the issue
  report (`ISSUE.md`), and Lean. Muse Code's shell sandbox cannot reach Docker, where the pinned Lean
  4.35 toolchain runs, so Lean comes from the MCP server `integrations/muse/proofforge_mcp.py` in
  its `lean` profile. That profile has one tool, `lean_build`, which returns Lean's own output for
  `lake build Solution` or `lake env lean <file>`. There is no judge, no property tests and no library.
- **Muse Code with ProofForge (`proofforge`).** The same workspace, plus:
  - the full MCP server: `lean_build`, `show_task`, `try_snippet`, `check_candidate` (the official
    `bin/proofforge check`, with witnesses, kernel-checked counterexamples and a Passport),
    `verify_passport`, `search_library` and `list_tasks`;
  - the skill `.agents/skills/proofforge/SKILL.md` and the workspace `AGENTS.md`;
  - ProofForgeFin, vendored into the workspace.

Settings for every run:

- Model `muse-spark-1.3-contributor` at medium reasoning effort.
- Caps: $10 at standard list prices and 14,400 s of wall time per run, as in `results/library-1`.
- Muse Code flags: `exec --json --no-foreign-personal-context --disable-web-tools
  --disable-request-user-input --trust-workspace --disable-approval --sandbox-network restricted
  --max-model-steps 400`, the `--base-url` of the meter, and one `--session-id` per run.
- Muse Code runs with its own `HOME` and settings file: the MCP server only, telemetry off.
- The workspace is a fresh copy of the task's project files. It never contains the reference
  solutions, attacks, witnesses, README or results.
- The MCP server runs with `--blind`, so `show_task` leaves out the README, which describes the
  known fixes.

The final candidate of every run is the file on disk when the run stops (`final.lean`). It is judged
outside the budget by `bin/proofforge check`, identical for both arms (`passport.json`, `check.txt`).
Every VERIFIED Passport was reproduced by `bin/proofforge verify` (`verify.txt`).

## Results

| Task | Run | Arm | Outcome | Requirements proved | Time s | List $ | Charged $ | Model calls (main agent) | Stop | Passport |
|---|---|---|---|---|---|---|---|---|---|---|
| rc-knight-router | alone-1 | Muse Code alone | VERIFIED | 6/6 | 1,549 | 6.05 | 0.24 | 265 (237) |  | `e341575dd4c952d5` |
| rc-knight-router | alone-2 | Muse Code alone | VERIFIED | 6/6 | 1,038 | 3.32 | 0.11 | 227 (200) |  | `8dbaee08850b059d` |
| rc-knight-router | proofforge-1 | Muse Code + ProofForge | VERIFIED | 6/6 | 1,153 | 6.83 | 0.29 | 327 (295) |  | `505bbd87ab666840` |
| rc-knight-router | proofforge-2 | Muse Code + ProofForge | VERIFIED | 6/6 | 2,871 | 6.11 | 0.18 | 314 (284) |  | `84357f923fdc0087` |
| rw-balancer-upscale | alone-1 | Muse Code alone | VERIFIED | 8/8 | 1,608 | 5.77 | 0.17 | 307 (274) |  | `b4fab63692eb7adb` |
| rw-balancer-upscale | alone-2 | Muse Code alone | UNRESOLVED | 6/8 last compiling | 2,451 | 7.52 | 0.20 | 342 (307) | dollars |  |
| rw-balancer-upscale | alone-3 | Muse Code alone | UNRESOLVED | 6/8 last compiling | 3,056 | 6.98 | 0.24 | 210 (188) | dollars |  |
| rw-balancer-upscale | proofforge-1 | Muse Code + ProofForge | VERIFIED | 8/8 | 1,547 | 2.97 | 0.10 | 162 (146) |  | `b6ed85f286b9cfe0` |
| rw-balancer-upscale | proofforge-2 | Muse Code + ProofForge | UNRESOLVED | 6/8 last compiling | 2,445 | 7.94 | 0.24 | 339 (306) | dollars |  |
| rw-balancer-upscale | proofforge-3 | Muse Code + ProofForge | VERIFIED | 8/8 | 2,261 | 3.76 | 0.13 | 183 (164) |  | `9b9bff34c26280d0` |
| rw-cetus-shlw | alone-1 | Muse Code alone | VERIFIED | 5/5 | 209 | 0.61 | 0.03 | 49 (42) |  | `ccf91a508964842d` |
| rw-cetus-shlw | proofforge-1 | Muse Code + ProofForge | VERIFIED | 5/5 | 852 | 0.39 | 0.02 | 35 (30) |  | `b925dcb7292bda51` |
| rw-compound-comp | alone-1 | Muse Code alone | UNRESOLVED | 5/8 | 2,445 | 7.72 | 0.21 | 400 (360) | dollars |  |
| rw-compound-comp | proofforge-1 | Muse Code + ProofForge | UNRESOLVED | 0/8 last compiling | 3,623 | 7.08 | 0.22 | 316 (287) | dollars |  |

How to read the columns:

- **Passport** is the first 16 hex digits of the `passport_sha256` of the VERIFIED Passport.
- **Requirements proved**, for a VERIFIED run, is the requirements in the Passport. For any other
  run it is the required theorems proved without `sorry` in the final file, if that file compiles.
  Otherwise it is the count in the newest snapshot of the run that compiles (`last_compiling.json`,
  `integrations/muse/last_compiling.py`), marked "last compiling". The A0 to A2 agents report the
  same quantity for their newest compiling version. The outcome is always the official check of
  `final.lean`.
- **Model calls** counts every call the meter forwarded. The count in parentheses is calls by the
  main agent; the rest are Muse Code's helper agents (goal reminder, verification and todo nudges).
- **Stop** is empty when the judge accepted the candidate.

Every measured run ended in one Muse Code session: the agent ended its turn with the candidate
accepted, or the dollar cap stopped it. The runner's continuation, used when a session ends with
the task unfinished, was never needed. No run reached the wall cap.

### By arm

| Task | Arm | Verified | List $ over all runs | List $ per verified run | Charged $ |
|---|---|---|---|---|---|
| rw-balancer-upscale | Muse Code alone | 1 of 3 | 20.27 | 20.27 | 0.61 |
| rw-balancer-upscale | Muse Code + ProofForge | 2 of 3 | 14.68 | 7.34 | 0.47 |
| rc-knight-router | Muse Code alone | 2 of 2 | 9.37 | 4.69 | 0.35 |
| rc-knight-router | Muse Code + ProofForge | 2 of 2 | 12.94 | 6.47 | 0.48 |
| rw-cetus-shlw | Muse Code alone | 1 of 1 | 0.61 | 0.61 | 0.03 |
| rw-cetus-shlw | Muse Code + ProofForge | 1 of 1 | 0.39 | 0.39 | 0.02 |
| rw-compound-comp | Muse Code alone | 0 of 1 | 7.72 | | 0.21 |
| rw-compound-comp | Muse Code + ProofForge | 0 of 1 | 7.08 | | 0.22 |
| all four | Muse Code alone | 4 of 7 | 37.98 | 9.50 | 1.21 |
| all four | Muse Code + ProofForge | 5 of 7 | 35.09 | 7.02 | 1.19 |

The sample is small and the difference in verification rate is not significant. On Balancer, the
one-sided Fisher exact test gives p = 0.50.

Measured here:

- **Muse Code alone is strong.** It verified Knight twice, Balancer once and Cetus. In
  `results/library-1`, compile-and-retry Muse alone (A0) verified Balancer in 1 of 3 runs, after
  6,613 s.
- **Balancer.** The ProofForge arm verified 2 of 3 runs, at $7.34 at list prices per verified run;
  Muse Code alone verified 1 of 3, at $20.27.
- **Knight.** Both arms verified both runs. Muse Code alone was cheaper there ($4.69 against $6.47
  per verified run).
- **Compound.** Neither arm verified it, as in every earlier run in this repository.
- **Time.** The ProofForge arm's in-run time includes its own official checks: each
  `check_candidate` and `verify_passport` runs the full pipeline, 50 to 236 s each on this host.
  Muse Code alone sees only Lean, so it ends its turn when Lean accepts the file; the runner then
  confirms with the judge.
- **How the arms used the tools.** In the ProofForge arm, Muse Code called `check_candidate` once or
  twice per run and `verify_passport` once per verified run (`mcp-calls.jsonl`). It called
  `try_snippet` 3 to 44 times and `search_library` 0 to 3 times. Both verified Balancer runs of
  that arm import ProofForgeFin, and their Passports bind the library version.

### What stopped the unverified runs

All five unverified runs stopped on the dollar rule with $2.06 to $3.02 of the $10 unspent. The
rule is the same for both arms and for the A0, A1 and A2 agents (`agents/budget.py`). Before a
call is sent, its worst case is reserved: every byte of the request counted as an uncached input
token at list price, plus the output allowance. A call that cannot fit is refused.

Muse Code keeps the whole session in context. By the end of these runs a request was 1.6 to 2.4 MB
(310,000 to 384,000 tokens, more than 98% of them cached), so its byte bound was $2.0 to $3.0. The
next call no longer fit, and the run stopped.

Four of the five final files do not compile: the run stopped between edits. Their newest compiling
snapshots prove:

- Balancer, all three unverified runs: 6 of 8. The six per-swap requirements are proved; the two
  value requirements are open, as in the unverified Balancer runs of `results/balancer-1`.
- Compound, ProofForge arm: 0 of 8.
- Compound, Muse Code alone (its final file compiles): 5 of 8. The three sequence bounds are open,
  as in every earlier Compound run.

## How cost was measured

Muse Code reports token usage in its JSONL stream once, at the end of a run (`run.usage`: input,
cached, output and reasoning tokens per model). That record:

- leaves out the calls of Muse Code's helper agents (`children_included: false`);
- in these runs counted about half of the main agent's calls (for example 156 of 274 on Balancer
  `alone-1`, 73 of 146 on `proofforge-1`);
- is absent when a run is stopped.

The cost here was therefore measured at the wire. Muse Code's model calls go to a local metering
proxy (`integrations/muse/meter.py`) through `--base-url`; the proxy forwards them to the Meta Model
API and reads each call's usage from its `response.completed` event. The prices and the budget rule
are those of `agents/budget.py`:

- Each call is priced at standard-tier list prices ($1.25 input, $0.15 cached input, $4.25 output
  per million tokens for Muse Spark 1.3), Contributor-tier calls included. The amount charged at the
  Contributor tier is tracked separately.
- Each call is reserved at its worst case before it is sent, and settled to its reported usage.
- The output allowance is at most 32,000 tokens per call, as for A0 to A2. Muse Code asks for
  128,000.
- A call that does not fit beside calls in flight waits for them to settle. A call that does not
  fit with none open is refused; the calls in flight settle and Muse Code is stopped.
- A call cut off by a stop stays charged at its worst case.

`calls.jsonl` records every call: role (main agent or helper), request size, output allowance,
usage, list and charged cost. It holds no keys and no message contents.

| Run | Muse Code's run.usage: calls, list $ | Meter: calls, list $ |
|---|---|---|
| rc-knight-router alone-1 | 132, 3.81 | 265, 6.05 |
| rc-knight-router proofforge-1 | 150, 3.75 | 327, 6.83 |
| rw-balancer-upscale alone-1 | 156, 4.54 | 307, 5.77 |
| rw-balancer-upscale proofforge-1 | 73, 2.32 | 162, 2.97 |
| rw-cetus-shlw alone-1 | 26, 0.35 | 49, 0.61 |

Muse Code's own `--max-model-steps 400` was a backstop and never reached. The caps were the dollars
and the wall time.

## Demonstration

`integrations/muse/demo/run.sh` runs the developer flow on Balancer in the ProofForge arm, with the
prompt `integrations/muse/demo/balancer-prompt.md`: the incident report, then "fix it with
ProofForge", "show me what ProofForge refutes", "check until VERIFIED", "reproduce the Passport",
"no proof, no merge".

- `demo-balancer-1`: UNRESOLVED, stopped on the dollar rule at $7.75 at list prices after 2,968 s.
  It called `check_candidate` first, which refuted the deployed port with the attack-shaped witness,
  then worked on the fix and proofs. Several of its builds ran out of memory in the 4 GB Lean
  container (exit 137).
- `demo-balancer-2`: **VERIFIED**.
  - **Session 1.** In 2,214 s and $5.12 at list prices ($0.20 charged), Muse Code:
    1. read the skill;
    2. called `show_task`, `search_library` and `check_candidate`, which refuted the port and
       gave its witness and three kernel-checked counterexamples;
    3. wrote the fix and the proofs;
    4. got `check_candidate` VERIFIED: all 8 requirements, six kernels, 2,001 property cases. Its
       in-session Passport is `.proofforge/passport-002.json`, sha256 `db2db9bb...`.
  - **`verify_passport` then failed.** The call hit Muse Code's MCP tool timeout while Docker had
    stopped answering on this host (next section). Muse Code then closed the server's connection
    for the rest of the session. It reported the VERIFIED check and the failed reproduction as a
    caveat, and ended its turn.
  - **Session 2.** The runner's own check between sessions got no verdict from Docker and reported
    it to the agent as a rejection. A second session followed. In it Muse Code:
    - confirmed its verified file was intact and made no edits;
    - looked outside the workspace for a Lean toolchain (`find / -maxdepth 4 -name "proofforge*"`,
      `ps aux`, `ls ~/.local/bin`; listed under integrity below);
    - was stopped by the dollar rule at $7.89.
  - **The record.** The runner then failed in its final status step, so `summary.json` is
    reconstructed from `calls.jsonl`, the runner log and the transcript, and says so. `final.lean`
    is the file of session 1. `bin/proofforge check` gives a VERIFIED Passport, sha256 `2cbc7c45...`,
    with ProofForgeFin vendored (`passport.json`, `check.txt`). `bin/proofforge verify` reproduces it
    (`verify.txt`).

`events.jsonl` in each directory is the Muse Code JSONL transcript (`muse exec --json`). For the two
demonstration runs it is kept as plain JSONL. `transcript.txt` is a readable rendering of it
(`integrations/muse/transcript.py`). `mcp-calls.jsonl` holds the ProofForge tool calls with their
results.

## Findings about the integration, and changes after the measured runs

- **MCP tool timeout.** Muse Code ends an MCP tool call at its tool timeout, and then reports "MCP
  stdio connection is closed" for that server for the rest of the session.
  - The default is about 300 s: a tool that sleeps 600 s failed 304 s into the run.
  - The timeout is set per server with `tool_timeout_sec` in `mcp_servers.<id>`. A 60 s tool fails
    at 20 s and succeeds at 90 s.
  - In the measured runs, at the default, `check_candidate` took up to 236 s and `verify_passport`
    up to 158 s without hitting it. The demonstration's `verify_passport` hit it while Docker was
    not answering.
  - The runner now sets `tool_timeout_sec` to 3,600 (commit 456be24). The measured runs used the
    default.
- **Docker outage.** From about 18:00 to 18:42 the Docker daemon on this host did not answer
  (`docker version` timed out). Lean runs during that time produced no verdict.
  - No measured run's result depends on that window: every measured run had ended, and its official
    check gave a real Lean verdict, before 18:00.
  - The runner had reported a judge run without a verdict as a rejection. It now retries once and
    stops with `judge_unavailable` (commit 547555b).
  - It also writes its record before the final Lean work, so a failure there no longer loses it
    (commit eedf266).
- **Usage reporting.** Muse Code's own usage record undercounts the model calls of a run (see "How
  cost was measured"). A dollar cap needs the meter.

## Integrity of the runs

- **Isolation.** `integrations/muse/audit.py` lists every shell command and file read in a
  transcript that names a path outside the workspace, the checkout, reference solutions, attacks,
  witnesses or results.
  - In the measured runs it flags one command, in `rw-balancer-upscale/proofforge-2`. By manual
    review that is the word `/tmp` in a Python comment, not an access.
  - Three measured runs and `demo-balancer-1` kept backup copies of their own candidate as named
    files in `/tmp`, the sandbox's writable temp directory. They read back only those copies.
  - `demo-balancer-2`, in the session started by the runner's mistaken rejection, listed `/tmp` and
    `~/.local/bin`, searched `/` to depth 4 for `proofforge*` and ran `ps aux`. It read no file of the
    checkout, and its candidate was already final.
  - One smoke run (`smoke/ring-alone`) listed `/tmp`.
- **Lean.** Lean runs only in the pinned image, with the workspace mounted and no network. The
  judge reads the locked files from the repository and takes only the candidate file from the run.
- **Host.** Up to four runs ran at once, interleaving the arms (`integrations/muse/measure.py`). They
  shared four Lean container slots with other work on the host, so wall times include waiting for a
  slot.
- **Code version.** The runs used commits 7e2876a and fae9443 (`config.json`). The two differ only
  in the queue driver and the audit script; the runner, meter and MCP server are the same.

## Smoke runs (`smoke/`)

Before the measured runs, smoke runs checked the plumbing.

- **`queues-ring-b1`, both arms, $2 caps.** The arms reached 5 of 8 (`ring-alone`) and 0 of 8
  (`ring-pf`) before the cap. Two meter rules changed after them:
  - The output allowance is now at most 32,000 tokens.
  - A dollar stop now lets the calls in flight settle.
  Before these changes, two calls cut off at the stop of `ring-pf` stayed charged at their worst
  case of $1.59.
- **Continuation path, `queues-ring-b1` alone, `ring-cont`.** Six model steps per session, three
  continuations. The fourth part ended when a call did not fit beside the calls in flight. After it,
  the meter makes such a call wait instead.
- **`rw-balancer-upscale` ProofForge arm, `balancer-pf`, $3 cap.** Stopped by hand after `show_task`,
  `check_candidate` (REFUTED in 225 s, with the attack-shaped witness) and `try_snippet` against the
  vendored library had worked.

Candidate snapshots (`candidate_v*.lean`) are not tracked (see `.gitignore`). Transcripts are
verbatim except for three changes. Machine paths are replaced by `<workspace>`, `<proofforge>` and
`~`. The normalization of `eval/normalize.py` is applied (see `results/README.md`). The listings of
the host's `/tmp` in `demo-balancer-2` and `smoke/ring-alone` are replaced by `[listing of /tmp on the
host redacted]`. `final.lean` and
`passport.json` are unchanged, so every Passport hash still matches.
