# Specification strength of the locked tasks

`eval/spec_strength.py --vacuity-probe` ran the specification strength gate (`harness/spec_strength.py`, described in `docs/SPEC_STRENGTH.md`) on one task per locked specification: the payout flagship, the nine real-world tasks and the first variant of each of the 15 other benchmark base specifications. Variants of a base specification share its locked files, its reference solutions and its oracle (`shared_with` in each report), and `payouts-flagship-b2` and `-b3` share the payout flagship's, so the 25 runs cover all 68 tasks. Every mutant the operators generate was built; nothing was sampled. Settings: 2,001 property cases with seed 0 (as in a Passport), 10,001 extended cases with seed 1 for mutants that pass, `LEAN_NUM_THREADS=4`, at most two containers of this tool at once. No model was called.

Each `<task>/` directory holds `report.json` (with `report_sha256`), `report.md` (every mutant with its result, and every survivor with its diff and first differing case) and, for a task with a counterexample adapter, `vacuity-probe.json` (`harness/spec_vacuity.py`). `table.md` and `summary.json` are the aggregate. `bin/proofforge spec-strength --verify <task>/report.json` checks a report's hash, the locked manifest and the regeneration of every mutant without Lean; `tests/test_spec_strength.py` does this for every committed report and probe.

## Result

Over the 25 specifications, the operators generated 1,676 single-site mutants of the reference solutions, of which 1,114 compile. The specifications reject 999 of the 1,114: 985 fail the property tests on the standard 2,001 cases, 2 only on the extended cases, and 12 do not finish the 2,001 cases within the 300 s limit (a Passport for them would not be VERIFIED; they have no witness). For the 15 specifications with a counterexample adapter, 730 of the 808 rejected mutants also carry a refutation of a locked requirement accepted by all six kernels, `leanchecker` and the axiom audit. 115 mutants survive: 105 whose outputs equal the reference's on all 12,002 round-1 cases, and 10 whose outputs differ while the property tests accept them.

| Task | Mutants | Compiled | Equivalent (identical executable) | Killed by property tests | Killed by kernel only | Killed with kernel-checked counterexample | Survived, behaviour differs | Survived, no observed difference | Killed of non-equivalent | Requirements violated / kernel-refuted |
|---|---|---|---|---|---|---|---|---|---|---|
| `payout-flagship` | 47 | 32 | 0 | 32 | 0 | 32 | 0 | 0 | 32 of 32 | 8 / 8 of 8 |
| `rw-cetus-shlw` | 25 | 17 | 0 | 16 | 0 | 16 | 1 | 0 | 16 of 17 | 5 / 5 of 5 |
| `rw-euler-donate` | 257 | 160 | 0 | 121 | 0 | 110 | 0 | 39 | 121 of 160 | 6 / 6 of 6 |
| `rw-hundred-vault` | 130 | 96 | 0 | 93 | 0 | 57 | 0 | 3 | 93 of 96 | 10 / 4 of 10 |
| `rw-balancer-upscale` | 134 | 119 | 0 | 104 | 0 | 103 | 5 | 10 | 104 of 119 | 8 / 8 of 8 |
| `rw-compound-comp` | 184 | 154 | 0 | 126 | 0 | 123 | 0 | 28 | 126 of 154 | 8 / 8 of 8 |
| `rc-knight-router` | 238 | 109 | 0 | 96 | 0 | 92 | 0 | 13 | 96 of 109 | 6 / 6 of 6 |
| `rw-gomoney-split` | 19 | 16 | 0 | 16 | 0 | 16 | 0 | 0 | 16 of 16 | 5 / 5 of 6 |
| `rw-moneyphp-allocate` | 58 | 30 | 0 | 27 | 0 | 16 | 2 | 1 | 27 of 30 | 5 / 5 of 8 |
| `rw-spliit-balances` | 58 | 30 | 0 | 27 | 0 | 16 | 2 | 1 | 27 of 30 | 5 / 5 of 8 |
| `ledgers-journal-b1` | 17 | 8 | 0 | 8 | 0 | 8 | 0 | 0 | 8 of 8 | 7 / 7 of 7 |
| `ledgers-log-b1` | 16 | 11 | 0 | 11 | 0 | 0 | 0 | 0 | 11 of 11 | 6 / 0 of 8 |
| `ledgers-reversal-b1` | 29 | 13 | 0 | 13 | 0 | 0 | 0 | 0 | 13 of 13 | 10 / 0 of 10 |
| `payouts-fee-b1` | 50 | 28 | 0 | 28 | 0 | 0 | 0 | 0 | 28 of 28 | 8 / 0 of 9 |
| `payouts-weighted-b1` | 80 | 47 | 0 | 46 | 0 | 0 | 0 | 1 | 46 of 47 | 8 / 0 of 9 |
| `permissions-acl-b1` | 33 | 20 | 0 | 19 | 0 | 18 | 0 | 1 | 19 of 20 | 8 / 7 of 9 |
| `permissions-grants-b1` | 22 | 11 | 0 | 11 | 0 | 0 | 0 | 0 | 11 of 11 | 8 / 0 of 8 |
| `permissions-workflow-b1` | 9 | 5 | 0 | 5 | 0 | 0 | 0 | 0 | 5 of 5 | 7 / 0 of 9 |
| `queues-bounded-b1` | 14 | 9 | 0 | 8 | 0 | 0 | 0 | 1 | 8 of 9 | 6 / 0 of 6 |
| `queues-prio-b1` | 11 | 8 | 0 | 8 | 0 | 0 | 0 | 0 | 8 of 8 | 8 / 0 of 8 |
| `queues-ring-b1` | 34 | 26 | 0 | 26 | 0 | 26 | 0 | 0 | 26 of 26 | 8 / 8 of 8 |
| `rate-limiters-bucket-b1` | 10 | 8 | 0 | 8 | 0 | 8 | 0 | 0 | 8 of 8 | 7 / 7 of 7 |
| `rate-limiters-window-b1` | 20 | 8 | 0 | 8 | 0 | 0 | 0 | 0 | 8 of 8 | 6 / 0 of 6 |
| `transfers-batch-b1` | 71 | 56 | 0 | 53 | 0 | 0 | 0 | 3 | 53 of 56 | 7 / 0 of 7 |
| `transfers-overdraft-b1` | 110 | 93 | 0 | 89 | 0 | 89 | 0 | 4 | 89 of 93 | 8 / 8 of 8 |
| total | 1676 | 1114 | 0 | 999 | 0 | 730 | 10 | 105 | 999 of 1114 | |

"Killed by property tests" includes the extended-case and time-limit kills. The last column counts requirements violated by some mutant's executable (or refuted in the kernel) and requirements with a kernel-checked refutation, from the report and its vacuity probe. Specifications without an adapter (`ledgers-log`, `ledgers-reversal`, `payouts-fee`, `payouts-weighted`, `permissions-grants`, `permissions-workflow`, `queues-bounded`, `queues-prio`, `rate-limiters-window`, `transfers-batch`) have no kernel-checked counterexamples; their kills rest on the property tests of the executable.

By operator (compiled, killed, survived): `field` 347, 331, 16; `swap` 178, 156, 22; `guard` 160, 146, 14; `arith` 114, 106, 8; `constant` 103, 92, 11; `drop-conjunct` 56, 35, 21; `boundary` 46, 30, 16; `logic` 44, 41, 3; `equality` 37, 34, 3; `rounding` 29, 28, 1. Most non-compiling mutants are `field` and `swap` mutants that swap values of different types.

## Survivors whose behaviour differs: specification gaps

Ten mutants produce outputs that differ from the reference's and still pass the property tests. For each one, every requirement was also instantiated on the first differing case and checked in the kernel (where the adapter can express the case); none of these probes refutes a requirement. They fall into four findings. None of them requires a change to a locked task, and no locked task was modified.

1. `rw-moneyphp-allocate` and `rw-spliit-balances`, M002 and M050 (four mutants): the tie-break between equal remainders is not specified. M002 changes `if g k < g n then n else k` to `≤` in `argmaxTo`, M050 starts the search at index 1. For `{"amount": 100, "ratios": [1, 1, 1]}` the reference returns `[34, 33, 33]` and the mutants `[33, 33, 34]` and `[33, 34, 33]`; for `{"amount": 5, "ratios": [0, 7, 3]}` the reference returns `[0, 4, 1]` and M002 `[0, 3, 2]`. `REQ-LARGEST-REMAINDER` (`LargestRemainderOn`) only requires that no unit could move from a share rounded up to a share rounded down and bring both closer to exact, which every tie-break satisfies. The locked specifications therefore admit several allocations for the same input. This is a real gap in determinism: two implementations with Passports for this task can disagree on who receives the leftover unit. Pinning it needs an added requirement, for example that among equal remainders the lowest index is served first, if that is the upstream libraries' order.
2. `rw-balancer-upscale`, M011 and M048: a given-in swap in a pool whose fee exceeds 100% is unconstrained. M048 drops the guard `mulUp amount fee ≤ amount` of `subtractSwapFeeAmount`, M011 weakens it to `mulDown`; both differ from the reference only when the fee is above `1e18`. In the first differing case (fee `1e18 + 1`) the mutants accept a given-in swap of 1 raw unit and pay 0 out, where the reference refuses. Every requirement that could object either assumes `p.fee < ONE` (`REQ-GIVEN-IN-SUCCEEDS`) or holds trivially when the net amount in is 0 (`REQ-GIVEN-IN-PAYS-AT-MOST`, `REQ-SWAP-KEEPS-VALUE`). The gap is outside the configurations a Balancer pool accepts (Balancer pools cap the swap fee well below 100%), so it does not affect the incident the task reproduces.
3. `rw-balancer-upscale`, M044, M129 and M130: the charge of a given-out swap may be up to the stated rounding tolerance above the reference's. M044 and M129 remove the `a = 0` case of `divUp`, so a given-out swap of 0 tokens is charged 2 raw units where the reference charges 0; M130 adds 2 instead of 1 in `divUp` and overcharges on 4 of 12,002 cases. `REQ-GIVEN-OUT-CHARGES-AT-MOST` allows the charge to exceed the price by one raw unit for the conversion and one for the fee, by design, so these overcharges are within the specification. If the charge should equal Balancer's to the unit, the bound would need to be tightened.
4. `rw-cetus-shlw`, M021: the value `checkedShlw` returns together with the overflow flag is unconstrained. The mutant returns `(1, true)` instead of `(0, true)` on overflow. `REQ-SHLW-EXACT` constrains the value only when the flag is `false`, and `getDeltaA` aborts on the flag, so the value is never used: the locked caller is unaffected, and the freedom is deliberate.

## Survivors with no observed difference

105 mutants produce the reference's output on every one of the 12,002 round-1 cases. No mutant produced an executable byte-identical to the reference's (the "equivalent" check never fired: every source change changed the binary), so these are not counted as equivalent in the totals. Reading each diff against the code and the specification:

- 57 are equivalent to the reference: arguments of a commutative operation swapped (`min`, `max`, `mulDown`, `mulUp`, `mulDouble`; balancer 7, compound 2, euler 2, knight 6, permissions-acl 1), a default of `getD` or `headD` that no valid input reaches (moneyphp and spliit 1 each, payouts-weighted 1, queues-bounded 1), and guards whose two branches compute the same value at the boundary (balancer `complement` and `divDown`, 3; compound's index updates and grants when the elapsed blocks, the speed or the amount is zero, 25; knight's checks of parent or child ids past the end, whose quantities are zero, and its bookkeeping of `sent` and `done` once an order or child is complete, 7).
- 48 change behaviour that the property tests never reach, on states the generator does not produce; the universally quantified requirements constrain those states, but no refutation was produced here:
  - `rw-euler-donate`, 37: 22 are in the liquidation branch. In every state reachable from `genesis` with a correct step every account is healthy (that is `REQ-NO-BAD-DEBT`), so a liquidation never succeeds in a generated case. The other 15 change guards that held in every generated state (`x ≤ s.cash` of a withdrawal or borrow, the health check of a deposit, the receiver check of a transfer, the checks of a burn). `REQ-EFFECTS` and `REQ-ALLOWED-SUCCEEDS` quantify over every state, so a refutation needs a hand-built unhealthy state, which the task's adapter (operation sequences from `genesis`) cannot express.
  - `rw-hundred-vault`, 3: dropped conjuncts `t ≤ s.supply`, `sharesUp s x ≤ s.supply` and `x ≤ s.assets`, implied in reachable states by the invariant that a balance never exceeds the supply.
  - `rw-compound-comp`, 1 (M015): `amount ≤ s.reserve` became `<`; a grant equal to the whole reserve is not generated.
  - `transfers-overdraft-b1`, 4, and `transfers-batch-b1`, 3: dropped `Nodup` and membership checks. The JSON wrapper builds the account universe from the balance list, so it never produces duplicate accounts, and an account outside it has balance 0 and limit 0, so the overdraft check refuses it anyway; the requirements quantify over every `State`, including ones the wrapper cannot build.

These 48 measure the property tests and the adapters more than the specifications: they are the mutants a kernel refutation on arbitrary states would settle.

## Vacuity

Every requirement of the 15 specifications with an adapter is shown not trivially true by a kernel-checked refutation for some mutant, except: the six effects and rounding requirements of `rw-hundred-vault` (violated by 7 to 24 mutants each; the adapter declines them because their hypotheses contain a frame condition over every actor), `REQ-INVALID-NOOP` of `permissions-acl` (violated by one mutant; the refutation does not build), and `REQ-ONE-SHARE-EACH` of `rw-gomoney-split`, `REQ-ORDER-INDEPENDENT` of `permissions-acl`, and `REQ-VALID-SUCCEEDS`, `REQ-INVALID-FAILS` and `REQ-ONE-SHARE-EACH` of the two allocation tasks, which no mutant violates. The vacuity probe added kernel-checked refutations for `REQ-AUTHORIZATION` and `REQ-NONNEGATIVE` of the payout flagship, `REQ-AUTHORIZATION` of `transfers-overdraft` and `REQ-KNOWN-ACCOUNTS` and `REQ-TRIAL-BALANCE` of `ledgers-journal`, which the oracles charge to another requirement. For the specifications without an adapter, 74 of 80 requirements are violated by some mutant's executable; the 6 others are `REQ-AUTHORIZATION` of `payouts-fee` and `payouts-weighted` (the oracle charges unauthorized payouts to `REQ-INVALID-NOOP`), `REQ-APPEND-ONLY` and `REQ-UNIQUE-IDS` of `ledgers-log`, and `REQ-SINGLE-DOC` and `REQ-AUDIT-APPEND-ONLY` of `permissions-workflow`.

A requirement no mutant violates is not shown to be vacuous either: single-site mutants of these references do not happen to break it (the allocation tasks' validity and shape requirements are guaranteed by the structure of `allocate`, for example). The conjunction of each specification's requirements is satisfiable: the references are accepted by the judge with every requirement proved (`satisfiability` in each report, from the task's `validation.json`), and the stripped references pass the property tests in every baseline.

## What did not work

- 78 of the 808 rejected mutants of adapter tasks have no kernel-checked refutation: 35 in `rw-hundred-vault` whose refuted requirements the adapter declines (frame conditions), 12 in the allocation tasks that were stopped by the time limit and have no witness, 12 whose only violation is the wrapper's output count (allocation tasks and compound), 11 whose generated refutation does not build (euler 9, compound 1, permissions-acl 1), and 8 where the mutant file was read stale by the container (below).
- In 8 counterexample checks (knight 4, euler 2, balancer 1, vault 1) Lean reported a parse error in the mutant itself, which had built in the build stage: the file written on the host just before the container started was read stale through the Docker Desktop bind mount. Those attempts are recorded as failed; the vacuity probe retries such a check once. The rejection of these mutants by the property tests is unaffected.
- 12 mutants of the allocation tasks (6 each) made the executable so slow that the 2,001 cases did not finish in 300 s; they are counted as rejected, separately (`killed_timeout`), and carry no witness.
- The byte-identical-executable test for equivalence never fired. Equivalence above is a reading of the diffs, not a proof.

## Reproduce

```
python3 eval/spec_strength.py --force --vacuity-probe          # all 25 specifications
bin/proofforge spec-strength --task rw-cetus-shlw --out /tmp/cetus
bin/proofforge spec-strength --verify results/spec-strength-1/rw-cetus-shlw/report.json
```

The statuses depend on the judge image (digest in each report) and are reproduced by rerunning; `--verify` checks the records without Lean.
