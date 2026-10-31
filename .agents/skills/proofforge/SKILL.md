---
name: proofforge
description: Fix financial code in Lean 4 against a locked ProofForge specification and prove every requirement, checked by the ProofForge judge (six kernels, leanchecker, axiom audit, property tests) with a Passport as the result. Use when a task names a ProofForge task, a locked spec under spec/, candidate/Solution.lean, a requirement such as REQ-..., a Passport, or the proofforge MCP tools.
---

# ProofForge: fix, prove, check

A ProofForge task is a Lean 4 (v4.35, core library, no Mathlib) project with a locked
specification. The only file you change is `candidate/Solution.lean`. The task is done when
`check_candidate` returns `"status": "VERIFIED"`: every requirement proved, the proofs accepted
by six kernels, and the executable built from the same file passing the property tests. No proof,
no merge: a fix that compiles but leaves a requirement `sorry`, REFUTED or UNRESOLVED is not done.

## Tools (MCP server `proofforge`)

| Tool | Use |
|---|---|
| `show_task` | issue report, definitions under repair, every locked requirement (id, theorem, exact statement, plain-language text), the rules |
| `lean_build` | Lean's own output: `lake build Solution`, or `lake env lean <file>` for a scratch file |
| `try_snippet` | compile a lemma or proof attempt after the candidate without changing the file; errors and goals in the snippet |
| `search_library` | ProofForgeFin theorems, tactics and simp sets (rounding, fixed point, `ceilDiv`, shares, ledgers, runs of operations) |
| `check_candidate` | the official check (`bin/proofforge check`): VERIFIED / REFUTED / UNRESOLVED per requirement, witnesses, kernel-checked counterexamples, Lean errors, sorry status, Passport |
| `verify_passport` | reproduce a Passport (`bin/proofforge verify`) |
| `list_tasks` | the task catalog |

There is no local Lean installation in the shell; Lean runs through these tools.

## Workflow

1. **Read the locked spec.** Call `show_task`, then read `spec/<Lib>/Spec.lean` (the requirement
   predicates), `spec/<Lib>/Challenge.lean` (the definitions under repair and the required
   theorems, each `:= sorry`) and `spec/<Lib>/Lemmas.lean` if present. The theorem statements in
   `Challenge.lean` are what the judge compares, byte for byte after elaboration.
2. **Find the defect.** Run `check_candidate` on the starting file. Each REFUTED requirement comes
   with a witness (an input, the output, the violated requirement) and a counterexample: the
   negation of the locked statement proved about the current code by the kernel. That input is
   the bug. Fix the definition so the witness no longer violates the requirement; do not weaken
   behavior on valid inputs (requirements that demand success still have to hold).
3. **Prove.** State helper lemmas first and prove them with `try_snippet`; move each proved lemma
   into the file above the theorem that uses it. Keep the required theorems at the end of the
   file with exactly the locked names and statements. Search the library before proving a
   general fact about rounding, division, scaling or sequences: `import ProofForgeFin` (or one
   module) is allowed, and its declarations are checked by the same kernels.
4. **Compile.** `lean_build` until the file compiles. `#print axioms` in a scratch file that
   imports `Solution` shows which theorems still depend on `sorryAx`.
5. **Check.** `check_candidate`. Iterate on what it returns: a new witness means the behavior is
   still wrong; `lean_errors` and `theorem_status` show what is not proved; `proof_check.reasons`
   names scan violations or a Comparator rejection (a statement that differs from the lock, a
   forbidden axiom, a kernel that rejects a declaration).
6. **Done.** Stop only at `"status": "VERIFIED"`. Report the Passport path and `passport_sha256`;
   `verify_passport` reproduces it.

## Rules the judge enforces

- Files under `spec/`, `app/`, `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are
  locked; the judge uses the repository's copies and rejects a workspace whose copies differ.
- Imports: the task's `Spec` and `Lemmas`, `Init.*`, `Std.*`, `ProofForgeFin.*`.
- Forbidden in the candidate: `sorry`, `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`,
  `@[export]`, `@[csimp]`, `macro`, `elab`, `syntax`, `initialize`, `#eval`, `run_cmd`,
  `native_decide`, `set_option`, simprocs and any other elaboration-time code.
- Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`.
- At a literal scale such as `10 ^ 18` or `10 ^ 36`, prove arithmetic over a variable scale and
  instantiate it: two of the six kernels unfold literal powers in equations Lean's kernel accepts.

## Lean 4.35 notes

- `omega` handles linear arithmetic over `Nat` and `Int` with literals; it does not see through
  definitions: `simp only [f]` or `unfold f` first.
- Nonlinear facts (`a * b / c` bounds): `Nat.div_le_div_right`, `Nat.mul_le_mul`,
  `Nat.div_mul_le_self`, `Nat.lt_div_mul_add`, or the library's `ceilDiv` and fixed-point lemmas.
- `split`, `cases h : e`, `by_cases`, `match` on the shape of the definition keep goals small;
  `simp_all` on a large state is slow and brittle.
- `decide` is fine on small closed propositions; `native_decide` is rejected.
