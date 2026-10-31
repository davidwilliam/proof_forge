# harvest-1: proof harvesting into ProofForgeFin

Helper lemmas of verified candidates harvested into `lib/ProofForgeFin/Harvested/` by
`harness/harvest.py` (method in `docs/HARVEST.md`), and the effect measured without model calls.
Files: `harvest.json` (every source and every helper theorem with its class, verdict and reason),
`kernels.json` (the harvested modules through the judge's kernels and the axiom audit),
`measure.json` (both measurements, per lemma and per obligation).

## Sources

| | candidates | helper theorems |
|---|---:|---:|
| Passport VERIFIED (real-world tasks) | 21 | |
| E1 `eval.json` judge ACCEPT, binary PASS (dev tasks) | 109 | |
| `formal/evidence` VERIFIED (flagship) | 1 | |
| harvested, total | 131 | 2,203 |
| E1 runs of the frozen test split (held out, not harvested) | 166 | 2,467 |

Required theorems are not counted as helper theorems. No candidate was skipped for a hash
mismatch.

## What was harvested

| class | helper theorems |
|---|---:|
| task-specific: the statement does not elaborate without the task | 1,484 |
| general: the statement elaborates with only the library | 719 |
| of which as written | 564 |
| of which restated over library definitions or type aliases | 147 |
| of which with a task structure abstracted into its fields | 8 |
| general, but the proof does not check without the task | 27 |
| general with a proof that checks | 692 |

The 692 checked lemmas state 324 distinct statements (equal up to binder names and
annotations); 368 occurrences repeat a statement proved elsewhere. Verdicts per distinct
statement:

| verdict | statements |
|---|---:|
| accepted and written | 86 |
| trivial: closed by `rfl`, `decide`, `omega`, `simp`, `simp_all`, `fin_simp` or `div_norm` | 123 |
| duplicate: same statement as a core library constant | 51 |
| duplicate: `exact?` proves it from the core library | 20 |
| duplicate: `exact?` proves it from ProofForgeFin | 16 |
| duplicate: `exact?` proves it from harvested lemmas written before it | 16 |
| duplicate: same statement as a ProofForgeFin constant | 10 |
| dropped at the final compile (one cites a lemma that was not written; one statement changed meaning in the library namespace) | 2 |

Written: 86 accepted lemmas (61 as written, 25 restated over library definitions, mostly over
`ProofForgeFin.Ledger.sumOver`) and 27 support lemmas that accepted proofs cite (their doc
strings say why they were not accepted on their own): 113 theorems, in `Harvested.Arith` (41, of
which 33 accepted), `Harvested.List` (44, 35) and `Harvested.Fin` (28, 18). Nine proofs were
corrected at the final compile for a warning whose fix Lean names (unused simp argument,
deprecated name, unused variable). The accepted lemmas come from `rw-spliit-balances` (25), `rw-gomoney-split`
(18), `payouts-flagship-b2` (10), `payouts-fee-b1` (8), `rw-balancer-upscale` (7),
`payout-flagship` (6), `rw-hundred-vault` (5), `payouts-flagship-b3` (5), `transfers-overdraft-b4`
(1) and `payouts-fee-b2` (1). No lemma from the struct abstraction survived deduplication.

Task-specific lemmas are not written anywhere (see `docs/HARVEST.md`).

## Checks

* Six kernels: the 226 declarations of `ProofForgeFin.Harvested` (113 theorems and the
  constants Lean generates for them), with everything they depend on, pass Lean default and
  paranoid, lean4lean, nanoda, con-leche and con-ron in one `lake comparator --paranoid` run;
  `leanchecker` accepts the three modules. This includes `t_add_floor` and `t_in_grow`, which
  keep the literal `10^18` next to variables.
* Axiom audit of the whole library and the demonstrations: 9,844 constants, 3,108 theorems,
  0 violations; axioms used: `propext`, `Classical.choice`, `Quot.sound`.
* The library builds without warnings; the library scan passes for `ProofForgeFin.Harvested`.

## Library version

`source_tree_sha256` before the harvest `f2fbb0d3610136faa01943f8aec8b34be8f6613277cef15d6f387f0b7ce1b453`
(commit `cda1275`), after `34d63d5e60d7027c0c3a6fea8171bd4238182ada1c9110a7a095398c885bfde3`.
No committed Passport vendors the library, so none is affected. A Passport issued against the
pre-harvest library reproduces from the harvested checkout: `bin/proofforge verify` extracts the
sources of the recorded commit or, when the Passport records none, of the commit whose library
sources have the recorded hash (`fin_lib.root_for`); `tests/test_harvest.py` checks this with a
Passport of `tests/fixtures/library/compound_lib.lean`.

## Effect, measured without model calls

### Re-proving helper lemmas with one `exact?`

Every general helper lemma whose own proof checks is given to one `exact?`, once with the
library before the harvest and once after.

| | lemmas (distinct statements) | closed before | closed after | closed only after |
|---|---:|---:|---:|---:|
| harvested sources | 692 (324) | 495 (186) | 531 (199) | 44 (19) |
| held-out test split | 589 (213) | 403 (111) | 403 (111) | 0 (0) |

For the harvested sources, a closure by a harvested lemma whose only source is the lemma's own
candidate is circular and is not counted (110 rows). The 44 lemmas closed only after the harvest
are closed by a harvested lemma proved in another candidate; for 38 of them that candidate is of
another task: between tasks of the payouts family (33), between `rw-balancer-upscale` and
`rw-hundred-vault` (ceiling bounds, 3), and from `rw-gomoney-split` to payouts tasks (2).
Their original proofs total 11,369 non-whitespace characters; the `exact <term>` replacements
total 2,429. Six statements closed before are closed after only by a harvested copy of
themselves (`exact?` stops at its first suggestion), which counts as circular, so the distinct
count after is 199 rather than 205.

On the held-out test split (ledgers, permissions and queues), the harvest closes nothing new: 19
lemmas are closed by a harvested lemma, and all 19 were already closed by the library before.

### Open obligations of unresolved runs

47 unresolved final candidates (10 with a Passport UNRESOLVED from `compound-1`, `knight-1` and
`frontier-1`; 37 E1 runs with judge REJECT and the executable passing) have 258 open
obligations: 153 `sorry` terms and 105 `sorry` tactics, no theorem failing to compile. Each is
replaced by `rfl`, `decide`, `omega`, `simp`, `simp_all`, `fin_simp`, `div_norm`, then `exact?`,
with the library before and after the harvest.

| | obligations | closed before | closed after | closed only after |
|---|---:|---:|---:|---:|
| real-world (Compound, Knight) | 96 | 5 | 5 | 0 |
| dev | 62 | 11 | 11 | 0 |
| test split (held out) | 100 | 0 | 0 | 0 |
| total | 258 | 16 | 16 | 0 |

All 16 closures cite lemmas the candidate itself proves elsewhere in the file, or are closed by
`exact?` from the task's own definitions; none uses a library lemma. 16 obligations (in three
Compound candidates) are not reached in either run: the tactics exceed Lean's maximum recursion
depth, which `first` does not catch, and elaboration of the declaration stops before the marker.
An earlier run of this measurement with all obligations of a candidate in one file was stopped by
the container's memory limit for one candidate (Lean printed no messages); obligations are now
compiled in groups of at most six and every run's exit code is recorded (no run stopped).

## Reading

The harvest adds 86 checked, deduplicated lemmas, and they shorten re-proofs of lemmas that
recur across the dev payouts tasks and the real-world tasks they came from. On held-out tasks and
on the open obligations of unresolved runs, a fixed tactic battery with `exact?` closes nothing
more with the harvest than without it. Whether the harvested lemmas help a prover that searches
the library (the repair agent's index includes them) needs model runs, which this measurement
does not make.
