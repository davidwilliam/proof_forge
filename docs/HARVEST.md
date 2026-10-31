# Proof harvesting

`harness/harvest.py` turns the helper lemmas of verified candidates into ProofForgeFin library
code, in `lib/ProofForgeFin/Harvested/`. It makes no model call; Lean runs in the pinned image.
Measured numbers are in `results/harvest-1/README.md`.

## Sources

A source is a final candidate with verification evidence bound to its bytes:

* `results/**/final.lean` next to a `passport.json` with status VERIFIED, whose content hash
  checks and whose `solution.files` hash is the file's;
* `results/**/final.lean` next to an `eval.json` with judge `ACCEPT`, binary `PASS` and the
  file's `final_sha256` (the E1 runs, which have no Passport);
* `formal/evidence/*/Solution.lean` with a VERIFIED verification record and matching hash.

Tasks of the frozen test split (`tasks/*` with `split: test`) are held out: their candidates are
listed and not harvested, so a library built from the harvest does not carry solutions of the
test tasks into later test runs. They are used as held-out data in the measurement.

## Pipeline

1. Read. Every `theorem` of a source except the task's required theorems, with its namespace,
   `open` commands and attributes (`harvest.parse`, a reader of top-level commands that respects
   comments and strings).
2. Restate. Variants of each statement and proof: as written; over library definitions (a task
   definition whose text equals a library definition is replaced by the library's, for example
   the task `sumOver` by `ProofForgeFin.Ledger.sumOver`; a type alias such as `AccountId := Nat`
   by its type; a task lemma by the library lemma of the same name in the same namespace); with
   task structures abstracted (a binder `(s : State)` used only through fields of general types
   becomes one variable per used field). The rewriting is textual; Lean decides whether a variant
   holds.
3. Classify (pass 1). Each variant is elaborated with a `sorry` proof in a file that imports only
   `ProofForgeFin`, with `autoImplicit` off. A lemma with a variant that elaborates is general;
   the others are task-specific. Task-specific lemmas are not written anywhere: the library cannot
   import a task's specification, and giving them to a rerun of the same task would be
   task-specific tuning of the harness.
4. Check proofs (pass 2). The general lemmas of each source, with their own proofs, in source
   order, so that a proof may cite an earlier general lemma of the same source. A lemma is kept
   when Lean accepts it with no error and its axioms are within `propext`, `Classical.choice` and
   `Quot.sound`. Lean also reports a fingerprint of each statement (the type with universe levels
   set to zero; Lean's expression equality ignores binder names and binder annotations, so equal
   fingerprints are the same statement up to names) and the existing constants with the same
   statement.
5. Deduplicate (pass 3). Lemmas with equal fingerprints form one class; the representative comes
   from a Passport-backed source if there is one, then has the shortest proof. A class is
   rejected when an existing constant has the same statement, when `rfl`, `decide`, `omega`,
   `simp`, `simp_all`, `fin_simp` or `div_norm` closes it (trivial), or when `exact?` closes it
   from the library and the core library (already provable by `exact` of an existing lemma). The
   checks run in a file without any harvested lemma.
6. Write. Accepted representatives are renamed (prefixes such as `my_`, `planN_`, `tmp_`
   removed, clashes numbered) and written with a provenance doc string: task, original name,
   source file and its SHA-256, and the Passport SHA-256 or the `eval.json` SHA-256, plus the
   other candidates that prove the same statement. A lemma whose proof cites a lemma that was not
   accepted keeps that lemma as a support lemma, with a doc string that says why. Modules:
   `Harvested.Arith` (`Nat`, `Int`), `Harvested.List` (lists, options, sums),
   `Harvested.Fin` (statements about ProofForgeFin definitions); `ProofForgeFin.Harvested` imports
   them and `ProofForgeFin` imports it. No harvested lemma gets a `simp` attribute, so the
   behaviour of `simp` in existing proofs that import the library does not change.
7. Final check. The modules are compiled over the pre-harvest library as the library build
   compiles them (default options, `linter.missingDocs` on). Two warnings are corrected
   automatically because Lean names the fix: an unused simp argument (removed) and a deprecated
   name (replaced). Any other error or warning, a statement whose fingerprint differs from pass 2
   or an axiom outside the permitted three drops the lemma and every lemma that uses it; the check
   repeats until the modules compile without messages. `tests/test_fin_lib.py` requires a library
   build without warnings.
8. Kernels. `harvest.py kernels` runs `harness/fin_kernels.py` restricted to the harvested
   modules (`check(modules=["ProofForgeFin.Harvested"])`, also `fin_kernels.py --modules`): every
   harvested declaration, with everything it depends on, through the six kernels of
   `lake comparator --paranoid` and `leanchecker`, plus the library's axiom audit
   (`lib/Audit.lean`). `harvest.py kernels --all` checks the whole library and the demonstrations.

The kernel guidance of `lib/README.md` applies: a statement with a large literal next to a
variable can make con-leche and con-ron exhaust their fuel. Harvested statements keep their
literals (abstracting them breaks the `omega` proofs they come with); the kernel check decides,
and a rejected lemma would be removed with its dependents.

## Measurement

`harvest.py measure` compares the library before the harvest (the sources without
`ProofForgeFin/Harvested`, which are byte for byte the sources of the commit the harvest started
from) with the library after it. No model is called.

* Re-proving. Every general helper lemma whose own proof checks, from the harvested sources and
  from the held-out test split, is given to one `exact?` in each library. A closure by a harvested
  lemma whose only source is the lemma's own candidate is circular and not counted. The report
  gives the counts and, for lemmas closed only with the harvest, the size of the original proofs
  (non-whitespace characters) against the size of `exact <term>`.
* Open obligations. For every unresolved final candidate (Passport UNRESOLVED, or judge not
  ACCEPT with the executable passing the property cases; refuted and non-building candidates are
  left out), the obligations are its `sorry` sites and the theorems that fail to compile as
  judged. Each is replaced by one line of tactics (`rfl`, `decide`, `omega`, `simp`, `simp_all`,
  `fin_simp`, `div_norm`, then `exact?`) with trace markers, the candidate imports `ProofForgeFin`,
  and it is compiled once with each library in the same project (the vendored package is swapped
  between the two runs). The report counts the obligations each library closes. A site is "not
  reached" when an earlier error in the same proof stops elaboration before it.

## Library versions and Passports

Writing the harvest changes `lib/` and therefore the library `source_tree_sha256`. Passports
record the version they were judged with; `bin/proofforge verify` reproduces a Passport of
another version with that version's sources (`fin_lib.root_for`): from the commit the Passport
records, or, when it records none (the sources were not committed when it was issued), from the
commit in the history of `lib/` whose sources hash to the recorded version
(`fin_lib.find_commit`, which hashes each commit's library from `git archive` and caches the
result). The sources are extracted into the cache and built there; the judge then runs with them.
No committed Passport vendors the library, so none depends on this; the pre-harvest version stays
reproducible because the commit before the harvest has exactly those sources.
`tests/test_harvest.py` checks the lookup without Lean and, with Lean, issues a Passport for
`tests/fixtures/library/compound_lib.lean` against the pre-harvest library and reproduces it from
the harvested checkout.

## Commands

```
python3 harness/harvest.py sources    # sources, harvested and held out
python3 harness/harvest.py run        # passes 1 to 3, final check, writes lib/ and results/harvest-1/harvest.json
python3 harness/harvest.py kernels    # six kernels, leanchecker and the axiom audit on the harvested modules
python3 harness/harvest.py measure    # results/harvest-1/measure.json
python3 tests/test_harvest.py [--quick]
```

Lean runs one container at a time with 4 CPUs, `LEAN_NUM_THREADS=4` and 3 GB
(`PF_HARVEST_CPUS`, `PF_HARVEST_MEMORY`), outside the judge's container slots, so judged runs on
the same host keep their slots. Intermediate files are in `PF_HARVEST_WORK` (default
`<tmp>/proofforge-fin/harvest`).
