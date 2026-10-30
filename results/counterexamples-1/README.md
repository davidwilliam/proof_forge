# Counterexamples checked by the kernel

`eval/counterexamples.py` runs the Passport pipeline with the counterexample stage
(`harness/counterexample.py`, described in `docs/COUNTEREXAMPLES.md`) on the vulnerable ports that
already have Passports and on the start candidate of every other task that has a counterexample
adapter: judge, binary check (2,000 generated cases, seed 0), then, for every refuted
requirement, a Lean theorem `cex_<req> : ¬ (<locked statement>)` about the candidate's
definitions, built from the binary check's witness and checked with `lake comparator --paranoid`
(Lean default and paranoid kernels, lean4lean, nanoda, con-leche, con-ron) against the locked
challenge with that theorem appended, then with `leanchecker` and the axiom audit.

Result: 82 of 85 refuted requirements over 33 candidates are refuted by a
kernel-checked theorem (20 of 20 on the 6 real-world ports with prior Passports; 8 of 11 on the 4 start candidates of the other real-world tasks; 54 of 54 on the 23 benchmark start candidates). Every accepted refutation was accepted by all six kernels and
`leanchecker`; the axioms used are `Classical.choice`, `Quot.sound`, `propext`. The four kernel-check
runs of one refutation (build, Comparator, leanchecker, axiom audit) took 6.6 s to
17.4 s, median 11.4 s, on the arm64 machine that issued these Passports.

The prior Passports of the ports are unchanged; these are new Passports of the same candidates,
with the `counterexamples` field. Each directory holds `passport.json` and the Lean source of
each refutation under `cex/`. Reproduce one with its `reproduce` command, for example
`bin/proofforge verify results/counterexamples-1/cetus-original-port/passport.json --candidate realworld/tasks/rw-cetus-shlw/attacks/buggy_original.lean`;
`verify` re-checks every recorded refutation in a fresh container (`verify.log`: eight of these Passports
reproduced; `verify-prior.log`: the prior Passports of the Cetus original port and the Knight start
candidate still reproduce, unchanged, with the harness that adds the stage).

### Real-world ports with prior Passports

| Target | Task | Status | Refuted requirements | Kernel-checked refutations | Not checked |
|---|---|---|---|---|---|
| `cetus-original-port` | `rw-cetus-shlw` | REFUTED | 2 | 2 of 2 | none |
| `cetus-pr6-port` | `rw-cetus-shlw` | REFUTED | 1 | 1 of 1 | none |
| `euler-port` | `rw-euler-donate` | REFUTED | 3 | 3 of 3 | none |
| `balancer-port` | `rw-balancer-upscale` | REFUTED | 3 | 3 of 3 | none |
| `knight-start` | `rc-knight-router` | REFUTED | 6 | 6 of 6 | none |
| `compound-p62-port` | `rw-compound-comp` | REFUTED | 5 | 5 of 5 | none |

### Start candidates of the other real-world tasks

| Target | Task | Status | Refuted requirements | Kernel-checked refutations | Not checked |
|---|---|---|---|---|---|
| `rw-gomoney-split-start` | `rw-gomoney-split` | REFUTED | 1 | 1 of 1 | none |
| `rw-hundred-vault-start` | `rw-hundred-vault` | REFUTED | 5 | 2 of 5 | REQ-DEPOSIT-ROUNDS-DOWN, REQ-REDEEM-ROUNDS-DOWN, REQ-WITHDRAW-ROUNDS-UP: not handled by the adapter: the requirement's hypothesis Minted or Burned includes a frame condition over every actor, which needs a proof about the candidate's code rather than an evaluation |
| `rw-moneyphp-allocate-start` | `rw-moneyphp-allocate` | REFUTED | 4 | 4 of 4 | none |
| `rw-spliit-balances-start` | `rw-spliit-balances` | REFUTED | 1 | 1 of 1 | none |

### Benchmark start candidates

| Target | Task | Status | Refuted requirements | Kernel-checked refutations | Not checked |
|---|---|---|---|---|---|
| `payout-flagship-start` | `payout-flagship` | REFUTED | 2 | 2 of 2 | none |
| `ledgers-journal-b1-start` | `ledgers-journal-b1` | REFUTED | 2 | 2 of 2 | none |
| `ledgers-journal-b2-start` | `ledgers-journal-b2` | REFUTED | 2 | 2 of 2 | none |
| `ledgers-journal-b3-start` | `ledgers-journal-b3` | REFUTED | 2 | 2 of 2 | none |
| `payouts-flagship-b2-start` | `payouts-flagship-b2` | REFUTED | 1 | 1 of 1 | none |
| `payouts-flagship-b3-start` | `payouts-flagship-b3` | REFUTED | 1 | 1 of 1 | none |
| `permissions-acl-b1-start` | `permissions-acl-b1` | REFUTED | 5 | 5 of 5 | none |
| `permissions-acl-b2-start` | `permissions-acl-b2` | REFUTED | 2 | 2 of 2 | none |
| `permissions-acl-b3-start` | `permissions-acl-b3` | REFUTED | 2 | 2 of 2 | none |
| `queues-ring-b1-start` | `queues-ring-b1` | REFUTED | 2 | 2 of 2 | none |
| `queues-ring-b2-start` | `queues-ring-b2` | REFUTED | 3 | 3 of 3 | none |
| `queues-ring-b3-start` | `queues-ring-b3` | REFUTED | 3 | 3 of 3 | none |
| `queues-ring-b4-start` | `queues-ring-b4` | REFUTED | 3 | 3 of 3 | none |
| `rate-limiters-bucket-b1-start` | `rate-limiters-bucket-b1` | REFUTED | 5 | 5 of 5 | none |
| `rate-limiters-bucket-b2-start` | `rate-limiters-bucket-b2` | REFUTED | 2 | 2 of 2 | none |
| `rate-limiters-bucket-b3-start` | `rate-limiters-bucket-b3` | REFUTED | 2 | 2 of 2 | none |
| `rate-limiters-bucket-b4-start` | `rate-limiters-bucket-b4` | REFUTED | 2 | 2 of 2 | none |
| `rate-limiters-bucket-b5-start` | `rate-limiters-bucket-b5` | REFUTED | 4 | 4 of 4 | none |
| `transfers-overdraft-b1-start` | `transfers-overdraft-b1` | REFUTED | 1 | 1 of 1 | none |
| `transfers-overdraft-b2-start` | `transfers-overdraft-b2` | REFUTED | 1 | 1 of 1 | none |
| `transfers-overdraft-b3-start` | `transfers-overdraft-b3` | REFUTED | 1 | 1 of 1 | none |
| `transfers-overdraft-b4-start` | `transfers-overdraft-b4` | REFUTED | 3 | 3 of 3 | none |
| `transfers-overdraft-b5-start` | `transfers-overdraft-b5` | REFUTED | 3 | 3 of 3 | none |

Tasks without an adapter, not run (36): `ledgers-log-b1`, `ledgers-log-b2`, `ledgers-log-b3`, `ledgers-log-b4`, `ledgers-reversal-b1`, `ledgers-reversal-b2`, `ledgers-reversal-b3`, `payouts-fee-b1`, `payouts-fee-b2`, `payouts-fee-b3`, `payouts-weighted-b1`, `payouts-weighted-b2`, `payouts-weighted-b3`, `permissions-grants-b1`, `permissions-grants-b2`, `permissions-grants-b3`, `permissions-grants-b4`, `permissions-workflow-b1`, `permissions-workflow-b2`, `permissions-workflow-b3`, `queues-bounded-b1`, `queues-bounded-b2`, `queues-bounded-b3`, `queues-prio-b1`, `queues-prio-b2`, `queues-prio-b3`, `rate-limiters-window-b1`, `rate-limiters-window-b2`, `rate-limiters-window-b3`, `rate-limiters-window-b4`, `rate-limiters-window-b5`, `transfers-batch-b1`, `transfers-batch-b2`, `transfers-batch-b3`, `transfers-batch-b4`, `transfers-batch-b5`.
