# ProofForge

ProofForge checks fixes to financial code against locked Lean 4 specifications. A task is a Lake
project (Lean v4.35.0, core library, no Mathlib) whose specification is locked by hash; the
candidate is `candidate/Solution.lean`; the judge accepts it only when every required theorem has
exactly the locked statement, is proved, passes six kernels, `leanchecker` and the axiom audit,
and the executable built from the same file passes the property tests. The result is a Passport.
No proof, no merge.

## Layout

| Path | Contents |
|---|---|
| `tasks/<id>/`, `realworld/tasks/<id>/`, `formal/` | tasks: `spec/<Lib>/Spec.lean`, `Challenge.lean`, `Lemmas.lean`, `spec/locked.json`, `app/Main.lean`, `oracle.py`, `candidate/Solution.lean` |
| `harness/` | judge, binary check, counterexample stage, Passport, ProofForgeFin integration |
| `bin/proofforge` | `check`, `verify`, `tasks`, `spec-strength` |
| `lib/` | ProofForgeFin, the Lean library candidates may import |
| `agents/` | model agents and budgets; `agents/muse_code.py` runs Muse Code on a task |
| `integrations/muse/` | ProofForge MCP server and the metering proxy for Muse Code |
| `.agents/skills/proofforge/` | the ProofForge skill: the fix, prove, check workflow |
| `results/` | measured runs with their Passports |

Never edit files under a task's `spec/` or `app/`, its Lake files or `spec/locked.json`; never
edit `reference/`, `attacks/` or `witnesses/` to make a candidate pass.

## Fixing a task

1. `bin/proofforge tasks` (or the MCP tool `list_tasks`) and the task's `task.json` issue report.
2. Read `spec/<Lib>/Spec.lean` and `spec/<Lib>/Challenge.lean`: the definitions under repair and
   the required theorems (`:= sorry`).
3. Work on a copy of the candidate. Fix the definition; prove each required theorem with the
   locked name and statement, helpers first.
4. `bin/proofforge check --task <id> --candidate <file> --out passport.json`. REFUTED requirements
   come with a witness input and a counterexample checked by the kernel; UNRESOLVED ones with the
   proof-check reasons.
5. Repeat until the status is VERIFIED, then `bin/proofforge verify passport.json --candidate <file>`.

The `proofforge` MCP server (`integrations/muse/proofforge_mcp.py`) exposes the same steps as
tools: `show_task`, `lean_build`, `try_snippet`, `search_library`, `check_candidate`,
`verify_passport`. Its `full` profile adds the harness's proof tools
(`integrations/muse/session_tools.py`): `goal_at` and `check_snippet_fast` on a persistent Lean
session, `try_tactics` (the tactic portfolio), `refute_statement` (sampling on concrete values),
`search_library` with a `goal`, and `prior_attempts` (the attempt ledger) in a resumed run. The
skill `.agents/skills/proofforge/SKILL.md` describes the loop in detail.

## Candidate rules

- Imports: the task's `Spec` and `Lemmas`, `Init.*`, `Std.*`, `ProofForgeFin.*`.
- Forbidden: `sorry`, `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`, `@[export]`,
  `@[csimp]`, `macro`, `elab`, `syntax`, `initialize`, `#eval`, `run_cmd`, `native_decide`,
  `set_option`, simprocs and other elaboration-time code.
- Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`.

## Commands

- Lean runs in the pinned image `proofforge-lean:4.35.0`: `python3 harness/lean.py <project-dir> [command]`.
- Library search: `python3 harness/fin_lib.py index <words>`.
- Tests are plain scripts without model calls: `python3 tests/test_<name>.py`.
