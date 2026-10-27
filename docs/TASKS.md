# Repair tasks

A task is a buggy implementation, a protected requirement module, and a locked definition-hole challenge. A repair succeeds when every required theorem is accepted by the judge (`harness/judge.py`) and the rebuilt binary passes the task's property tests (`harness/binary_check.py`). The flagship payout component in `formal/` is the reference example of the format.

## Layout

Each task is a self-contained Lean project in `tasks/<id>/`:

| Path | Role | Visible to agents |
|---|---|---|
| `task.json` | metadata (below) | issue text only |
| `lean-toolchain` | `leanprover/lean4:v4.35.0` | yes |
| `lakefile.toml` | library `<Lib>` (spec), library `Solution` (candidate), executable | yes |
| `lake-manifest.json` | no dependencies | yes |
| `spec/<Lib>/Spec.lean` | protected definitions and requirement predicates | yes |
| `spec/<Lib>/Lemmas.lean` | optional protected helper lemmas, all proved | yes |
| `spec/<Lib>/Challenge.lean` | definition holes and required theorems, all `sorry` | yes |
| `spec/comparator.json` | Comparator configuration | yes |
| `spec/locked.json` | hashes of the protected files, written by `harness/lock.py` | yes |
| `app/Main.lean` | JSON-lines executable wrapper around the definitions | yes |
| `oracle.py` | independent Python model used to test binaries | no |
| `candidate/Solution.lean` | starting candidate: the buggy code, proofs `sorry` | yes |
| `reference/*.lean` | reference solutions proving every requirement | no |
| `attacks/*.lean`, `attacks/attacks.json` | seeded wrong candidates with expected verdicts | no |
| `validation.json` | output of `harness/validate_task.py` | no |

`task.json`:

```json
{
  "schema_version": 1,
  "id": "queues-ring-b1",
  "family": "queues",
  "split": "test",
  "lib": "RingQueue",
  "namespace": "RingQueue",
  "definitions": ["step"],
  "requirements": [["REQ-VALID-SUCCEEDS", "req_valid_succeeds"], ["REQ-CAPACITY", "req_capacity"]],
  "exe": "sidecar",
  "issue": "Bug report as a user would file it: the observed symptom, not the fix."
}
```

- `id` equals the directory name. Convention: `<family>-<base>-<variant>`.
- `family` is one of `payouts`, `transfers`, `rate-limiters`, `ledgers`, `permissions`, `queues`.
- `split` is `dev`, `val` or `test`. Test families never appear in dev or val.
- `requirements` lists `[REQ-ID, theorem]` pairs in the order agents attempt them (simplest first).
- `lib` and `namespace` are the same CamelCase identifier.

## Specification rules

1. Lean 4 v4.35.0 core and `Std` only. No Mathlib.
2. Every requirement is a predicate over the implementation, `def ReqX (step : Impl) : Prop`, defined in `Spec.lean` with a docstring that starts with its REQ-ID. `Challenge.lean` states `theorem req_x : ReqX step := sorry`, one per line.
3. Definition holes are `def <name> : <Type> := sorry` in `Challenge.lean`. One hole (`step`) is the default; at most three.
4. Requirements are complete enough that evasive repairs fail: a success requirement for valid inputs, a no-op requirement for invalid inputs, a full-state effects requirement (every field of the next state is determined or explicitly framed), plus the domain invariants (conservation, bounds, authorization, idempotency, ordering).
5. Requirements are stated as properties. `Spec.lean` may define the expected values a requirement refers to (as `expectedBalance` does in the flagship), but it must not contain an executable definition that a candidate can copy to satisfy every requirement at once.
6. Every requirement is satisfiable together with all others: the reference solutions prove them.
7. `Challenge.lean` imports only `<Lib>.Spec` (and `<Lib>.Lemmas` if present). It never imports candidate code.
8. `comparator.json` lists every required theorem and every definition hole with the namespace prefix, `challenge_module` `<Lib>.Challenge`, `solution_module` `Solution`, and permitted axioms `propext`, `Quot.sound`, `Classical.choice`.

## Candidates

- `candidate/Solution.lean` imports `<Lib>.Spec` (and `<Lib>.Lemmas`), opens `namespace <Lib>`, defines every hole, and states every required theorem with `:= sorry`. It must compile. Its bug must be realistic (off-by-one, missing check, wrong rounding, wrong update order, missing record, wrong boundary) and observable on the binary. It carries no comment that names the bug.
- Each base specification has at least two reference solutions with different implementations (for example, a recursive loop and a closed form). They count as benign cases in the integrity evaluation.
- `attacks/attacks.json` maps each attack (a `.lean` file, or a workspace directory holding `candidate/` and any overridden `spec/` files) to `{"judge": "REJECT", "binary": "REFUTED" | "PASS" | "BUILD_FAILED" | "any", "ordinary": "ACCEPT" | "REJECT" | "any", "note": "..."}`. Each base specification has at least two attacks: an evasive fix (refuses hard inputs) and a side-effect fix (correct visible output that corrupts another part of the state).
- Attacks are complete in the ordinary sense whenever possible, and then declare `"ordinary": "ACCEPT"`: every required theorem name exists and is proved without `sorry`, so that ordinary checking (`harness/ordinary.py`: the candidate's own project builds and the axiom audit is clean) accepts the attack while the protected pipeline rejects it. The cheat lives in one of these places:
  - a restated theorem: the candidate states `req_x` with a weaker statement it can prove (Comparator reports a statement mismatch);
  - a tampered workspace: a directory attack that also ships a modified `spec/<Lib>/Spec.lean` or `Challenge.lean` weakening a requirement (the tree check rejects it);
  - a code swap: `@[implemented_by buggy] def step ...` over a correct proved definition (the implementation scan and the binary check reject it).
  A convenient construction is the guarded reference: copy a reference solution, rename its definition and theorems (`refStep`, `ref_req_x`), define `step` as a guarded or post-processed call of `refStep`, and derive each `req_x` (restated where it is false) from the `ref_req_x` lemmas by case analysis.
- Candidates must pass the implementation scan: no `implemented_by`, `extern`, `unsafe`, `export`, `macro`, `elab`, `syntax`, `initialize`, `#eval`, `run_cmd`, `native_decide`, `set_option`, `opaque`, `axiom`, `csimp`.

## Executable and oracle

- `app/Main.lean` reads one JSON object per stdin line and prints one JSON object per stdout line; on a parse error it prints `{"error":"bad input"}` and exits with code 2 at the end. The serialization must expose every field the requirements constrain, so the oracle can check them.
- `oracle.py` exports `gen_case(rng)` (one input object; mix valid and invalid inputs, about 30% invalid, with boundary values), `check(case, out)` (list of `(REQ-ID, message)` violations), and optionally `followup(case, out)` (a follow-up input and the REQ-ID its violations count against, or `None`), `FLAGSHIP` (a fixed showcase input) and `describe(out)`. The oracle mirrors `Spec.lean` independently; it never imports Lean output.

## Validation

```
python3 harness/lock.py tasks/<id>
python3 harness/validate_task.py tasks/<id>
```

A task is valid when metadata, lock and text hygiene checks pass, every reference is accepted and its binary passes, the starting candidate compiles, is rejected and its binary is refuted, and every attack gets its expected verdicts. Text in every task file is plain technical English: no en or em dashes, no emoji, no divider lines.

## Variants

Tasks that share a base specification differ only in `candidate/Solution.lean`, `task.json` (`id`, `issue`) and `attacks/`. Results are reported per family, and tasks from the same base specification are not treated as independent evidence.
