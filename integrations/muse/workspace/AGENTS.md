# ProofForge task workspace

This directory is one ProofForge task: a Lean 4 (v4.35.0, core library, no Mathlib) Lake project
with a locked specification. The only file to change is `candidate/Solution.lean`.

- `spec/<Lib>/Spec.lean`: the requirement predicates. Locked.
- `spec/<Lib>/Challenge.lean`: the definitions under repair and the required theorems, each
  `:= sorry`. Locked; every theorem must be proved in the candidate with exactly this statement.
- `spec/<Lib>/Lemmas.lean` (when present): proved helper lemmas. Locked.
- `app/Main.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: locked.
- `ISSUE.md`: the issue report.

Lean is not installed in the shell. Use the `proofforge` MCP tools: `lean_build`, `try_snippet`,
`check_candidate`, `search_library`, `show_task`, `verify_passport`. Follow the `proofforge` skill:
read the locked spec, run `check_candidate` to see the defect (witnesses and kernel-checked
counterexamples), fix the definition, prove every requirement, and iterate on `check_candidate`
until it returns `"status": "VERIFIED"`. A requirement that is `sorry`, REFUTED or UNRESOLVED is
not done. Work only inside this directory.
