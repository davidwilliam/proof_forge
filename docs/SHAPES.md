# The shape of a guarantee

Data for the site concept of the same name: for each flagship task with a verified Muse repair, which
declarations each guarantee rests on, and for runs that did not verify, where the proof stops.
Everything is extracted from committed files by `web/scripts/proof-shapes.mjs` and written to
`web/generated/shapes/`; `web/tests/shapes.test.ts` checks it without Lean.

## Definitions

- **Guarantee.** One locked requirement theorem of a task (`task.json`, `spec/<lib>/Challenge.lean`).
  Its plain-language statement is the doc comment of the property it asserts in the locked
  specification, quoted with line breaks joined by spaces. Where the task README's requirement table
  has a row naming it, that row's text is kept as `readme`.
- **Shape.** The set of declarations the guarantee uses, directly or through others, following the
  constants the Lean kernel records in each declaration's type and value. This is the rule of the
  home page graph (`web/scripts/proof-graph/ProofGraph.lean`): compiler-generated declarations are
  walked through, constructors, recursors and projections count as their type, and Lean's core
  library and ProofForgeFin are not nodes. The guarantee itself is not counted.
- **Size.** The number of declarations in the shape.
- **Depth.** The longest chain of uses from the guarantee down to a declaration that uses no other
  node (0 for such a declaration, else one more than its deepest dependency).
- **Width.** `width[d]` is the number of declarations of the shape whose own depth is `d`.
- **Load-bearing.** `loadBearing.every` lists the declarations in the shape of every guarantee of the
  task; `loadBearing.lemmas` gives, for each lemma, the number of guarantees whose shape contains it.
- **Hole.** A declaration whose type or value contains `sorryAx` as the kernel records it: `sorry`
  for an explicit `sorry`, `error` for one Lean inserted after an elaboration error. A required
  theorem left `sorry` is a hole. A `sorry` in a declaration that no guarantee reaches is listed
  under `build.sorryOutsideShapes` (from Lean's `declaration uses 'sorry'` warnings); no guarantee
  hangs from it.
- **Hangs from.** The holes in a guarantee's shape, plus the guarantee itself if it is a hole.
- **Complete.** A guarantee with no hole in its shape, that is not a hole itself, in a candidate that
  builds without errors.

The same definitions are stored in every JSON file under `definitions`.

## Runs

| File | Run | Role |
|---|---|---|
| `verified-balancer.json` | `results/balancer-1/repair-A2-1` | VERIFIED Passport (the home page graph) |
| `verified-cetus.json` | `results/cetus-1/repair-A1-1` | VERIFIED Passport |
| `verified-euler.json` | `results/euler-1/rw-euler-donate/repair-A1-1` | VERIFIED Passport |
| `verified-hundred.json` | `results/vault-1/repair-A1-1` | VERIFIED Passport |
| `verified-knight.json` | `results/knight-1/A2-2` | VERIFIED Passport |
| `holes-compound-A0-1.json` | `results/library-1/rw-compound-comp/A0-1` | Muse alone, 5 of 8 in its own check |
| `holes-compound-A2-2.json` | `results/library-1/rw-compound-comp/A2-2` | A2 with ProofForgeFin, 4 of 8 |
| `holes-compound-A2-topdown-3.json` | `results/library-1/rw-compound-comp/A2-topdown-3` | top-down loop, 0 of 8 |
| `holes-balancer-A0-1.json` | `results/library-1/rw-balancer-upscale/A0-1` | Muse alone, UNRESOLVED Passport |

Compound and the payout flagship have no Passport-backed Muse repair. No Muse run verifies Compound
(`results/library-live-1` is VERIFIED but written by the build team). The payout flagship's Muse runs
were scored by the E1 evaluator and have no Passport; its only Passport is the REFUTED start
candidate in `results/counterexamples-1`.

`summary.json` holds the headline measurements (deepest, largest and smallest guarantee per task,
the lemmas in every shape and the most shared ones, the holes of each attempt, and for Compound the
guarantees open in every run) and the sha256 of each file.

## Regenerating

```sh
cd web
node scripts/proof-shapes.mjs                 # all runs, in the proofforge-lean:4.35.0 image
node scripts/proof-shapes.mjs holes-compound-A0-1  # one run
PF_LEAN_HOME=/path/to/lean-4.35.0 node scripts/proof-shapes.mjs  # an unpacked Lean release instead of Docker
pnpm vitest run tests/shapes.test.ts
```

Each run is staged as the judge stages it: the task directory with the run's `final.lean` as
`candidate/Solution.lean`, and ProofForgeFin vendored at the version recorded in the run's
`summary.json` when the file imports it (`harness/fin_lib.py`). Each file records the Lean version
that built it (`lean`). The committed files were built with the Lean 4.35.0 release for
darwin_aarch64 (`lean-4.35.0-darwin_aarch64.tar.zst`, sha256
`c0c6f34f35ba1dcc5c4a5fd106fefab9eb5e8469712624dd2c868d51b63177c2`, commit `eb6cafb7`), the
toolchain the tasks pin; the test checks that the Balancer file has exactly the nodes, edges and
exclusions of `web/generated/proof-graph.json`, which was built in the image.

The test checks every file against the committed candidate, task files, run summary and Passport by
sha256, the statements against the specification and README text at the recorded lines, every
measurement against a recomputation from the nodes and edges, every hole against a `sorry` in the
source and Lean's warning inside it, and for each attempt that the complete guarantees are exactly
the ones the run's own final check marked PROVED.
