# ProofForge task workspace

This directory is one ProofForge task: a Lean 4 (v4.35.0, core library, no Mathlib) Lake project
with a locked specification. The only file to change is `candidate/Solution.lean`.

- `spec/<Lib>/Spec.lean`: the requirement predicates. Locked.
- `spec/<Lib>/Challenge.lean`: the definitions under repair and the required theorems, each
  `:= sorry`. Locked; every theorem must be proved in the candidate with exactly this statement.
- `spec/<Lib>/Lemmas.lean` (when present): proved helper lemmas. Locked.
- `app/Main.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: locked.
- `ISSUE.md`: the issue report.

Lean is not installed in the shell. Use the `proofforge` MCP tools and follow the `proofforge`
skill, in this order:

1. In a resumed run, `prior_attempts` first: the earlier attempts' proved declarations, re-checked
   by Lean against the current file, and their failure notes.
2. `show_task` and the locked spec; `check_candidate` to see the defect (witnesses and
   kernel-checked counterexamples); fix the definition.
3. Decompose each required theorem into helpers stated with `sorry`; `refute_statement` on any
   helper that might be false before proving it.
4. Prove the required theorems that follow directly from the definitions or from each other
   first (`try_tactics` on each), then the others: `try_tactics` first, then `goal_at` and
   `search_library` with `goal`, iterating with `check_snippet_fast` and confirming with
   `try_snippet`.
5. Keep the file compiling: move a proof into it once it compiles as a snippet, `lean_build` after
   every edit, and restore `.proofforge/best.lean` (the best compiling version, when `lean_build`
   keeps one) rather than editing a broken file further.
6. `lean_build` until the file compiles, then `check_candidate`; iterate on its counterexamples
   until it returns `"status": "VERIFIED"`, and `verify_passport`.

Each response, reasoning included, stops at 32,000 output tokens; a response cut there is lost, and
the session ends after a few in a row. Take one step per response, a tool call or an edit, and
write a long proof as `have` steps ending in `sorry`, checked one at a time.

The tools never edit the candidate; write every change yourself. A tool the server does not offer
is skipped. A requirement that is `sorry`, REFUTED or UNRESOLVED is not done. Work only inside this
directory.
