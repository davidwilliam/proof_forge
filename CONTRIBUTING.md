# Contributing

ProofForge accepts a change to a candidate only with a proof: no proof, no merge.

## Fixing or implementing a task

1. `bin/proofforge tasks` lists the tasks; each task's `task.json` holds its issue report.
2. Read `spec/<Lib>/Spec.lean` and `spec/<Lib>/Challenge.lean`: the definitions under repair and the
   required theorems.
3. Edit `candidate/Solution.lean` only. Never edit a task's `spec/`, `app/`, Lake files or
   `spec/locked.json`, and never edit `reference/`, `attacks/` or `witnesses/` to make a candidate
   pass.
4. `bin/proofforge check --task <id> --candidate <file> --out passport.json` until the status is
   VERIFIED, then `bin/proofforge verify passport.json --candidate <file>`.

Candidate rules (imports, forbidden constructs, permitted axioms) are in `AGENTS.md`. Lean runs in
the pinned image `proofforge-lean:4.35.0`; the README's "Reproduce the Passports" section builds it.

## Pull requests

The `proofforge` workflow judges a pull request's candidate files against the base branch's locked
specification and posts the verdict. A pull request from outside the repository is judged after a
maintainer adds the `proofforge-check` label. The `tests` workflow runs the stored-file tests and
the site's tests on every pull request.

## New tasks and library lemmas

Open an issue with the task proposal template first. A new task needs a locked specification, a
reference solution with a VERIFIED Passport, the vulnerable or starting candidate, an oracle for the
property tests, and a README that states the source of every figure and what is not modeled
(`docs/TASKS.md`). Library lemmas go in `lib/ProofForgeFin` with their kernel run (`lib/README.md`).

## Measured results

Results under `results/` are measured runs. An experiment's plan is committed before its runs, as
`PREREGISTRATION.md`, and changes after that are dated addenda. Run data is never edited.
