# Counterexamples checked by the kernel

Lean answers whether a proof of a requirement is accepted. A candidate whose proof is rejected is not thereby shown to be wrong: the proof may be missing, or the statement may be true and only hard to prove. ProofForge marks a requirement REFUTED when the executable rebuilt from the candidate violates it on a concrete input, as decided by the task's Python oracle. The counterexample stage (`harness/counterexample.py`) turns that test failure into a theorem: the negation of the locked requirement, proved about the candidate's own definitions and checked by the same kernels that check accepted proofs. A REFUTED Passport then records a disproof checked by the kernel, not only a failing test.

## What the stage proves

For a requirement `REQ-X` with locked challenge line `theorem req_x : ReqX step := sorry`, the stage proves

```lean
theorem cex_req_x : ¬ (ReqX step) := by ...
```

in the task's namespace, where `step` is the candidate's definition of each definition hole. The proof instantiates the requirement at the concrete input of the witness and decides the instance by evaluation in the kernel. For example, the original Cetus port is refuted on the attack deposit of 2025-05-22:

```lean
theorem cex_req_delta_a_covers : ¬ (DeltaACovers checkedShlw) := by
  intro h
  have hx := h (60257519765924248467716150) (60863087478126617965993239)
    (10365647984364446732462244378333008) _ (by first | decide | exact (Option.some_get (by decide)).symm | rfl)
  revert hx
  first | decide | ...
```

`h` is the requirement, `∀ sp0 sp1 liquidity amount, getDeltaA checkedShlw sp0 sp1 liquidity true = some amount → exact ≤ amount * denominator`; the amount the port charges is left to the kernel (`_`, fixed by the hypothesis `getDeltaA ... = some amount`), and `decide` evaluates the candidate's `checkedShlw` and `getDeltaA` on the three numbers and finds the inequality false. Every generated file is recorded in the Passport; `results/counterexamples-1/*/cex/` has them as files.

## Pipeline

`counterexample.run(task, candidate, binary_result)` runs after the binary check, for a REFUTED candidate:

1. Witnesses. The binary check keeps the first witness (input, output, oracle message) of every refuted requirement; a witness found on a follow-up case (a resubmission, a reordered access list) also keeps the round-1 case it was derived from (`origin`).
2. Statement. The locked statement of the requirement is read from `spec/<Lib>/Challenge.lean` and negated: `¬ (<statement>)`. Nothing else supplies the statement.
3. Instance. The task's adapter maps the witness to the Lean terms of the instance (see Adapters). Without an adapter, or when the adapter returns no instance, the requirement stays REFUTED by the test only, and the Passport says why.
4. Lean files, in a fresh project made like the judge's (the locked `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `spec/`, `app/` from the repository, and the candidate files):
   - `cex/Cex/C<k>.lean`, the challenge: the locked `Challenge.lean`, byte for byte, with `theorem cex_req_x : ¬ (<statement>) := sorry` appended in the task's namespace. The definition holes are the locked ones.
   - `cex/Cex/S<k>.lean`, the refutation: `import Solution` (the candidate), the challenge's imports, any further module of the task's specification library the adapter names, and the theorem with its proof.
   - a `lean_lib` named `Cex` appended to the project's `lakefile.toml` copy, and a Comparator configuration naming the challenge module, the refutation module, the one theorem, the task's definition holes and the permitted axioms `propext`, `Quot.sound`, `Classical.choice`.
5. Checks, each in its own container run of the pinned image (`judge.in_container`, the judge's container slots, network off):
   - `lake build Cex.S<k>`;
   - `lake comparator --paranoid --config cex/c<k>.json`: Comparator builds and exports both modules in its bubblewrap sandbox, checks that `cex_req_x` has exactly the challenge's statement with the solution's definitions in the holes, that it uses only the permitted axioms, and checks it with Lean's default and paranoid kernels, lean4lean, nanoda, con-leche and con-ron;
   - `lake env leanchecker Cex.S<k>`, a kernel replay of the refutation module;
   - `#print axioms <ns>.cex_req_x`, recorded.
   The refutation counts (`kernel_checked: true`) only if all four succeed and the axioms are a subset of the permitted ones.

`passport.run(..., counterexample=True)` runs the stage and adds the result to the Passport. `bin/proofforge check` does so by default for a REFUTED candidate (`--no-counterexample` skips it); the API server and the evaluators call `passport.run` without it and are unchanged. `python3 harness/counterexample.py CANDIDATE --task T` runs the binary check and the stage and prints the result.

## The default proof

```lean
intro h
have hx := h <args>
first
  | (revert hx; decide)
  | (revert hx; decide +kernel)
  | (simp -failIfUnchanged only [<the specification's Prop definitions>] at hx <;> (revert hx; decide))
  | (repeat (first | exact absurd hx (by decide) | exact absurd hx.1 (by decide) | replace hx := hx.2); done)
```

`<args>` are the adapter's terms for the requirement's leading binders. An argument `_` is left to unification; an argument `?` is a hypothesis, discharged by the first of `decide`, `(Option.some_get (by decide)).symm` (which proves `f x = some y` and fixes `y` to the value the kernel computes), `rfl`, the adapter's hint terms, and `decide` after unfolding the specification's propositions. After instantiation, `revert hx; decide` decides the remaining implication `H₁ → … → C`, which is false exactly when every hypothesis holds and the conclusion fails. The third alternative unfolds a requirement's proposition that has no `Decidable` instance. The last refutes one decidable part of a conjunction whose other parts are not decidable, such as a frame condition over every account. When the conclusion is an equation between states with function fields, which `decide` cannot compare, the adapter names observations (for example the balances of the accounts the executable reports) and the proof refutes the equation of one observed value: `congrArg <observation> hx`. An adapter can also supply a complete proof, for requirements that are existential (`∃ x, …`) or about reachable states, where the proof needs a helper lemma.

The generated file sets `maxRecDepth` and `maxHeartbeats` higher than the defaults. The judge's implementation scan forbids `set_option` in candidates; here it is in the harness's own file, and every alternative is still checked by the kernel. `native_decide` is never used.

## Adapters

How a JSON case becomes Lean terms depends on the task's types, so a task may provide an optional adapter, a Python module with

```python
def instance(task, requirement, case, out, origin=None) -> dict | None
```

It is looked up as `<task>/counterexample.py`, then `counterexamples/<task id>.py`, then `counterexamples/<base id>.py`, where the base id is the task id without its `-bN` suffix (variants share a specification and a wrapper). The adapters of existing tasks are in `counterexamples/`, outside the task directories: every file of a test task is bound by `results/test-freeze.json`, and adding one would change the frozen snapshot. A new task can carry its adapter as `counterexample.py`; it is not read by agents (`task.readable` lists the specification and the candidate only).

`instance` returns `None` or a dict with `args` (Lean terms for the leading binders, `_` and `?` as above), `hints` (proof terms for hypotheses that are not decidable, such as `constantProduct_wellBehaved` for Balancer), `observe` (observations for equations between states with function fields), `preamble` (declarations before the theorem, such as a `Decidable` instance or a reachability lemma; names start with `cex` so that they do not collide with the candidate's), `imports` (modules of the task's specification library only), `proof` (a complete tactic proof) and `note`. The module `counterexample` provides renderers (`nat`, `int_`, `boolean`, `lst`, `struct`, `table`, `string`) and `observing`.

The adapters mirror the task's JSON wrapper: a state is written as the wrapper's `toState` builds it (for example balances as `fun a => (pairs.lookup a).getD 0`), so the kernel evaluates the candidate on the same state the executable ran on. Outputs of the candidate (amounts, next states) are left to the kernel wherever the requirement fixes them by an equation, so most refutations do not depend on the executable's output at all; where an adapter uses the output, it uses it only to find the step or account at which the oracle saw the failure.

## Trust

A kernel-checked counterexample relies on:

- the Lean v4.35.0 kernel, and the five further kernels Comparator runs, all of which must accept;
- Comparator's statement comparison: the refutation proves exactly `¬ (<locked statement>)` with the candidate's definitions in the locked holes;
- the locked specification and challenge, as for every Passport;
- the harness code that writes the challenge: it appends one theorem, whose statement is the locked one negated, to the unchanged locked challenge.

It does not rely on the adapter, the task oracle, the JSON wrapper, the compiled executable or the binary check. A wrong adapter term, a wrong oracle verdict or a misreporting wrapper makes the proof fail, and the Passport then records the reason; it cannot produce an accepted refutation of a requirement the candidate meets, because the kernel evaluates the candidate's definitions itself. `tests/test_counterexample.py` checks that a false instance (an input on which the requirement holds) does not build and that a source proving a weaker statement under the counterexample's name is rejected. Adapter text is also scanned for the constructs the judge forbids in candidates (`axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, elaboration-time code), as defense in depth; Comparator's axiom check is the authority.

What a refutation covers: the candidate's definitions as the kernel sees them. The executable is compiled from the same source; a construct that makes compiled code differ from the kernel's definitions (`implemented_by`, `extern`) is rejected by the judge's implementation scan, but the stage itself does not depend on it. The requirement statuses of the Passport are unchanged by the stage: REFUTED still means the rebuilt executable violated the requirement on a witness. The stage adds, per refuted requirement, whether that refutation is also a theorem.

## Passport field

A REFUTED Passport issued with the stage has `counterexamples`, one entry per refuted requirement with a witness:

| Key | Content |
|---|---|
| `requirement`, `refutes`, `theorem` | the REQ-ID, the locked theorem it refutes, the name of the refutation (`<ns>.cex_<theorem>`) |
| `statement`, `statement_sha256` | `¬ (<locked statement>)` and its hash |
| `kernel_checked` | true when the build, Comparator, leanchecker and the axiom audit succeeded |
| `reason` | why not, otherwise null: no adapter, no instance, a Lean error, a Comparator rejection, an axiom outside the permitted set |
| `kernels`, `axioms` | the kernels Comparator reports as accepting, and the axioms of the theorem |
| `input`, `output`, `origin`, `message` | the witness: the case, the executable's output, the round-1 case of a follow-up witness, the oracle's message |
| `note`, `adapter`, `adapter_sha256` | the adapter's description of the instance, its path and hash |
| `lean_source`, `lean_file_sha256`, `challenge_sha256` | the refutation's source and hash, and the hash of the generated challenge |
| `checks` | exit codes, timings and output hashes of the four container runs |

The field is part of the content hash. Passports issued without the stage have no such field and hash, and verify, exactly as before.

## Verify

`bin/proofforge verify passport.json --candidate PATH` re-runs the pipeline as before. For a Passport with `counterexamples`, it then re-checks every recorded refutation: it regenerates the statement and the challenge from the locked files of the repository, writes the recorded `lean_source` as the refutation module, and runs the build, Comparator, leanchecker and the axiom audit in a fresh container. It compares, per entry, the statement, the source hash (recomputed from the recorded source), the challenge hash, `kernel_checked`, the kernels and the axioms. The re-check does not need the adapter: the recorded source is the certificate.

## Coverage

`eval/counterexamples.py` runs the stage on the real-world ports that have Passports and on the start candidates of every task with an adapter, and writes `results/counterexamples-1/` (Passports, sources, `summary.json`, `README.md` with the table).

Results on the arm64 machine that issued them (`results/counterexamples-1/README.md` has the table per candidate):

| Candidates | Refuted requirements | Refuted by a kernel-checked theorem | Not handled, and why |
|---|---|---|---|
| `cetus-original-port` | 2 | 2 | none |
| `cetus-pr6-port` | 1 | 1 | none |
| `euler-port` | 3 | 3 | none |
| `balancer-port` | 3 | 3 | none |
| `knight-start` | 6 | 6 | none |
| `compound-p62-port` | 5 | 5 | none |
| `rw-gomoney-split-start` | 1 | 1 | none |
| `rw-hundred-vault-start` | 5 | 2 | REQ-DEPOSIT-ROUNDS-DOWN, REQ-REDEEM-ROUNDS-DOWN, REQ-WITHDRAW-ROUNDS-UP: the hypothesis `Minted` or `Burned` includes a frame condition over every actor |
| `rw-moneyphp-allocate-start` | 4 | 4 | none |
| `rw-spliit-balances-start` | 1 | 1 | none |
| payout flagship: 3 start candidates | 4 | 4 | none |
| ledgers-journal: 3 start candidates | 6 | 6 | none |
| permissions-acl: 3 start candidates | 9 | 9 | none |
| queues-ring: 4 start candidates | 11 | 11 | none |
| rate-limiters-bucket: 5 start candidates | 15 | 15 | none |
| transfers-overdraft: 5 start candidates | 9 | 9 | none |

In total 82 of 85 refuted requirements over 33 candidates are refuted by a theorem accepted by all six kernels and `leanchecker`. Axioms used: none (24 refutations), `propext` (27), `propext` and `Quot.sound` (26), all three permitted axioms (5: the two Balancer value requirements, through `constantProduct_wellBehaved` of the locked `Sanity` module, and three refutations on `ledgers-journal-b2` and `permissions-acl-b1` whose proof terms reach `Classical.choice` through the definitions and lemmas they unfold; the axiom is permitted, as for the judge). The four container runs of one refutation took 6.6 s to 17.4 s, median 11.4 s; the largest generated source is 3.7 KB (Balancer: a pool and a swap with 18-decimal rates). The 36 tasks without an adapter were not run: `ledgers-log-b1`, `ledgers-log-b2`, `ledgers-log-b3`, `ledgers-log-b4`, `ledgers-reversal-b1`, `ledgers-reversal-b2`, `ledgers-reversal-b3`, `payouts-fee-b1`, `payouts-fee-b2`, `payouts-fee-b3`, `payouts-weighted-b1`, `payouts-weighted-b2`, `payouts-weighted-b3`, `permissions-grants-b1`, `permissions-grants-b2`, `permissions-grants-b3`, `permissions-grants-b4`, `permissions-workflow-b1`, `permissions-workflow-b2`, `permissions-workflow-b3`, `queues-bounded-b1`, `queues-bounded-b2`, `queues-bounded-b3`, `queues-prio-b1`, `queues-prio-b2`, `queues-prio-b3`, `rate-limiters-window-b1`, `rate-limiters-window-b2`, `rate-limiters-window-b3`, `rate-limiters-window-b4`, `rate-limiters-window-b5`, `transfers-batch-b1`, `transfers-batch-b2`, `transfers-batch-b3`, `transfers-batch-b4`, `transfers-batch-b5`.

## Limits

- Adapters are per specification. A task without one gets no kernel-checked counterexample; 14 of the 24 distinct specifications in `formal/`, `tasks/` and `realworld/tasks/` have one (variants of a base, and moneyphp and Spliit, share a specification).
- Decidability. `decide` needs a `Decidable` instance for the instantiated statement. Equality of states with function fields (balances, slots, authorization) is not decidable; the stage compares observations instead, which refutes the equation whenever the observed parts differ, and the observations are the parts the executable reports, so a difference the oracle saw is one they show. Quantifiers over an unbounded type (`∀ a, balance a = …`, `∀ x, x ∈ applied ↔ …`) are not decidable; the adapter tries each account or ID of the case in turn. Existential conclusions (`∃ x, …`) need a proof that names the witness (REQ-DEQUEUE-CONTENTS, REQ-CLAIM).
- Hypotheses that are not computations. A requirement whose hypothesis is a property of a parameter (Balancer's `WellBehaved m`) needs a lemma proving it for the instance (`constantProduct_wellBehaved`, in the locked `Sanity` module). A requirement over reachable states (Euler's REQ-NO-BAD-DEBT) needs a lemma that the states a run passes through are reachable; the Euler adapter proves one by induction. A hypothesis that includes a frame condition over every actor (Hundred's `Minted` and `Burned` in the effects and rounding requirements) would need a proof about the candidate's code, not an evaluation, and the Hundred adapter returns no instance for those requirements.
- Kernel evaluation. The kernel's natural-number arithmetic is accelerated (GMP), so 256-bit Cetus products, 1e36-scaled Compound indices and Euler's 1e18 fixed point are evaluated directly. The cost is the cost of running the candidate in the kernel: a sequence of operations is evaluated step by step, and every function field is a closure the kernel unfolds at each lookup. The largest instances here (Balancer's 12-swap batch, Compound's 3-step sequences with 1e36 indices, Knight's 8-event runs) check in seconds. The elaborator's `decide` can fail to synthesize the `Decidable` instance of a large tuple, so each equation is refuted through one observed component at a time, with `decide +kernel` as the fallback.
- The witness. The stage refutes the requirement on the first witness the binary check kept. If the adapter cannot express that witness (an input shape it does not handle), the stage does not try another one.
