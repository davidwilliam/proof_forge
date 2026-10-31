# Specification strength gate

A Passport says that a candidate's code satisfies the locked requirements. That is worth as much as the requirements are strong: a vacuous or weak requirement is satisfied by wrong code as well. The specification strength gate (`harness/spec_strength.py`) measures each locked specification by the wrong implementations it rejects. It mutates the task's reference solution at one site at a time, builds every mutant in the judge image, and decides for each one whether the specification rejects it, with a failing property case and, where the task has a counterexample adapter, a refutation checked by the kernel. The result is a statement of the form "this specification rejects N of M non-equivalent mutants of its reference; K of the rejections are kernel-checked refutations", with every survivor listed with its diff.

```
bin/proofforge spec-strength --task rw-cetus-shlw --out results/x     # measure one task
bin/proofforge spec-strength --task rw-cetus-shlw --list              # list the mutants, no Lean
bin/proofforge spec-strength --verify results/x/report.json           # check a report without Lean
python3 eval/spec_strength.py                                         # one task per locked specification
```

No model is called at any point.

## Pipeline

1. Reference. The first file of the task's `reference/` directory (sorted by name; `SolutionA.lean` for every current task) is the known-good implementation. Its Passport-equivalent evidence is the task's `validation.json`: every reference was accepted by the judge and its executable passed the property tests.
2. Proof stripping. The body of every `theorem`, `lemma` and `example` is replaced by `sorry`. Definitions, instances and structures are kept byte for byte, so the stripped reference computes what the reference computes, and a mutant that changes a definition still compiles even though the reference proofs no longer apply to it. Statements that contain `let x := v` keep their statement; the body is the first `:=` at the declaration's bracket depth that does not belong to such a binding (or a `|` alternative that begins a line).
3. Mutation scope. Only the bodies of code declarations reachable from the task's definition holes (`task.json` `definitions`) through identifier references are mutated, plus every instance (instances are used implicitly, for example a `Decidable` instance that implements a validity test). Signatures, comments, string literals and `by` blocks inside code (proof terms) are never mutated.
4. Operators. Each mutant differs from the stripped reference at exactly one site. Mutants whose source equals the reference or another mutant are dropped.

| Operator | Change |
|---|---|
| `rounding` | `a / b` becomes ceiling division (a small helper `⌈/⌉` is inserted after the imports: `(a + b - 1) / b` on `Nat`, `-((-a) / b)` on `Int`); the ceiling idioms `(a + b - 1) / b` and `(a - 1) / b + 1` become floor division; an identifier ending in `Down`/`Up` or `floor`/`ceil` is swapped for its counterpart when that name is defined in the solution or the specification (for example `mulDown` and `mulUp`) |
| `boundary` | `<` and `≤`, `>` and `≥` swapped |
| `equality` | `=` and `≠`, `==` and `!=` swapped |
| `arith` | binary `+` and `-` swapped, `*` replaced by `/`, unary minus dropped |
| `logic` | `&&` and `||`, `∧` and `∨` swapped; `true` and `false` flipped |
| `drop-conjunct` | one operand of a `&&` or `∧` chain replaced by `true` (a missing check) |
| `guard` | the condition of an `if` replaced by `true` (guard dropped) or by `false` (branch removed) |
| `field` | one `f := v` dropped from a structure update `{ s with ... }` (state field not updated); a field read `x.f` replaced by `x.g` for another field `g` read from the same `x` in the declaration; a projection `(e).f` replaced by another projection used in the declaration |
| `swap` | the operands of a non-commutative operator swapped when both are atoms; two adjacent arguments of an application swapped; `min` and `max` swapped |
| `constant` | a numeric literal `n` replaced by `n + 1`, `n - 1`, and for `n ≥ 10` by `10 n` and `n / 10` (scale factors, fee basis points, masks and shift widths) |

Generation is deterministic. `--max-mutants N` keeps N mutants chosen round robin over the operators, each operator's sites in an order shuffled by a seed derived from the task id; the published results use every mutant.

5. Build. The stripped reference and all mutants are built one after the other in a single container of the judge image (`lake build <exe>` on the locked project with the mutant as `candidate/Solution.lean`), with `LEAN_NUM_THREADS=4`, `--cpus 4` and a 300 s limit per mutant. A mutant that does not compile is discarded and counted (`not_compiled`, with its first error).
6. Baseline. The stripped reference's executable must pass the property tests (2,001 cases with seed 0, as in a Passport) and the extended cases (10,001 cases with seed 1). Otherwise the task is reported as not measured.
7. Property tests. A mutant whose executable is byte-identical to the reference's is `equivalent`: the change did not reach the compiled code. Every other compiled mutant runs the judge's own property tests (`binary_check.property_tests`, round 1 and the oracle's follow-up round) with the same case count and seed as a Passport. A violation kills it (`killed`). A mutant that passes runs the extended cases; a violation there kills it as well (`killed_extended`). A run stopped by the 300 s limit counts as `killed_timeout`.
8. Kernel-checked counterexamples. For a task with a counterexample adapter (`docs/COUNTEREXAMPLES.md`), each killed mutant's witnesses become Lean theorems `cex_<req> : ¬ (<locked statement>)` about the mutant's definitions, generated by `counterexample.generate` and checked as the Passport stage checks them: `lake comparator --paranoid` against the locked challenge with the negated theorem appended (Lean default and paranoid kernels, lean4lean, nanoda, con-leche, con-ron), `leanchecker`, and the axiom audit (only `propext`, `Quot.sound`, `Classical.choice`). Requirements without a kernel-checked refutation in the task are tried first; one accepted refutation per mutant is enough, after at most two checked attempts. A second pass tries up to two more mutants for every requirement that some mutant violates but none has yet refuted in the kernel. The checks run sequentially in the task's project.
9. Survivors. A compiled, non-equivalent mutant that passes both rounds of tests survives. Its outputs are compared with the reference's on all 12,002 round-1 cases. `survived_same`: no output differs, so the mutant is possibly equivalent (equivalence is not proved). `survived_differs`: some output differs and the oracle accepts it; the first differing input and both outputs are recorded. For a task with an adapter, each such survivor is then probed: every requirement in turn is instantiated on the first differing case and the refutation is checked in the kernel. An accepted refutation means the locked specification does reject the mutant and only the property tests missed it (`killed_kernel`). A survivor that remains `survived_differs` after the probe is a specification gap candidate: either the specification allows that behaviour, or it forbids it on an input the tests and the probe did not reach.

## Vacuity and satisfiability

For every requirement the report lists the mutants whose executable violates it and the mutants refuted for it by a kernel-checked theorem. A kernel-checked refutation of `R` for some implementation proves that `R` is not trivially true (it is not a theorem about every implementation). `not_trivially_true` is `kernel-checked`, `tested` (violated on the executable, no kernel-checked refutation) or `not shown` (no mutant violates it; the requirement may still be strong, but this run gives no evidence of it). The conjunction of the requirements is satisfiable: the task's references are accepted by the judge with every requirement proved (`satisfiability` in the report, from `validation.json`), and the stripped reference passes the property tests in the baseline.

## Report

`report.json` holds the task and its locked manifest hash (and whether the manifest still matches the files), the reference file and hashes, the settings, the generator version (`tool_sha256`), the counterexample adapter and its hash, the judge image and platform, the baseline, and one record per mutant: operator, declaration, line and column, description, unified diff against the stripped reference, source hash, build result, executable hash, test results per requirement, status, the first differing case for survivors, and every counterexample attempt with its Lean source, kernels, axioms and hashes. `summary` and `vacuity` are derived from the mutant records. `report_sha256` is the SHA-256 of the canonical JSON (sorted keys) of every other field, as for Passports. `report.md` renders the same content.

`verify_report` (CLI `--verify`) checks a report without Lean: the content hash, that the task's locked manifest in the checkout is the one measured, that `summary` and `vacuity` follow from the mutant records, and, with the generator version the report records, that every mutant is regenerated from the reference with the same source hash and diff. It does not rebuild or retest; rerunning `spec-strength` on the same image reproduces the statuses.

## Passport field

The gate does not change existing Passports or their hashes. A new Passport may carry an optional field `spec_strength`, produced by `passport_record(report)`:

```json
"spec_strength": {
  "report_sha256": "...",
  "locked_manifest_sha256": "...",
  "reference_sha256": "...",
  "tool_sha256": "...",
  "mutants": {"generated": 25, "selected": 25, "compiled": 24, "equivalent": 1, "killed": 22,
              "killed_kernel": 22, "survived": 1},
  "kill_ratio": "22 of 23",
  "requirements_not_shown_nontrivial": []
}
```

The field is covered by the Passport's own content hash like every other field, so it only appears in Passports issued after it is added, and an old Passport without it still reproduces. `verify_passport_record(passport, report)` checks it when present: the record equals `passport_record(report)` for the named report, the report's content hash holds, and the record's locked manifest is the Passport's. A Passport without the field passes this check unchanged. The report itself is kept next to the Passport (or under `results/`), not inside it, because its mutant records are large.

## Resource bounds

Each task runs its containers one at a time: one build container for all mutants, one short container per property-test round, one per counterexample check. The tool takes its own container slots (`PF_SPEC_SLOTS`, default 2, in a slot directory separate from the judge's), so at most two of its containers run at once on a host and judge runs elsewhere on the host do not wait for them. `PF_SPEC_LEAN_THREADS` (default 4) sets `LEAN_NUM_THREADS` and the container CPU limit. `eval/spec_strength.py` runs at most two tasks at once.

## Limits

- The mutants are single-site changes of one reference. They measure the specification against plausible local mistakes, not against every wrong program; a high kill ratio does not prove the specification complete.
- Equivalence is not proved. A mutant is called equivalent only when its executable is byte-identical to the reference's; survivors with no observed difference are reported as possibly equivalent.
- A survivor whose behaviour differs is not proved to satisfy the specification: it passed the oracle (which mirrors `Spec.lean` independently) on 12,002 generated cases and the kernel probe on one case. Each one is a lead that a person reads against `Spec.lean`; `results/spec-strength-1/README.md` gives that reading for the published run.
- Kernel-checked counterexamples exist only for tasks with an adapter; for the other tasks kills rest on the property tests of the executable.
- The compiled wrapper (`app/Main.lean`) is TESTED_ONLY here as in the judge; a mutant that changes behaviour the wrapper does not serialize is invisible to the property tests (and is then probed in the kernel only if some output differs).
