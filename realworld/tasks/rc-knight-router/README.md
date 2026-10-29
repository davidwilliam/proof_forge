# rc-knight-router: a child-order router reconstructed from the SEC findings

This task is reconstructed from the SEC findings in the order against Knight Capital Americas LLC (Securities Exchange Act of 1934 Release No. 70694, October 16, 2013). Knight's code is not public. Nothing in this directory is Knight's code, and no statement here is about Knight's system: every theorem is about the Lean model in `spec/OrderRouter/Spec.lean` and the routers written against it.

The `rc-` prefix marks a task reconstructed from a regulator's findings; `rw-` tasks port real public code at pinned commits. `task.json` records `"reconstructed": true` and the order, and every Passport for this task carries that statement in its trust assumptions.

## What the order says

Paragraph numbers refer to section III of the order. Figures below are the order's own.

| Paragraph | Finding | Where it is in the model |
|---|---|---|
| 12 | SMARS receives parent orders and, "as needed based on the available liquidity", sends one or more child orders to external venues for execution. | `Event.parent`, `Event.route id liq`, `Child`; a routing opportunity offers `liq` shares |
| 13 | The new RLP code replaced unused code formerly used for "Power Peg", which was "still present and callable", and "repurposed a flag that was formerly used to activate the Power Peg code". | `ParentRec.flag`; the start candidate sends flagged orders to the Power Peg path on a server without the new code |
| 14 | Power Peg's "cumulative quantity function counted the number of shares of the parent order that had been executed" and "instructed the code to stop routing child orders after the parent order had been filled completely". In 2005 Knight moved it "to an earlier point in the SMARS code sequence" and did not retest Power Peg. | `ParentRec.cum`; the Power Peg stop check; the port's execution-report handler |
| 15 | A technician "did not copy the new code to one of the eight SMARS computer servers". | `Build.legacy` versus `Build.rlp`; `aug1` in `witnesses/buggy_original.lean` |
| 16 | "Orders sent with the repurposed flag to the eighth server triggered the defective Power Peg code"; the server "continuously sent child orders, in rapid sequence, for each incoming parent order without regard to the number of share executions Knight had already received". "One part of Knight's order handling system recognized that the parent orders had been filled, this information was not communicated to SMARS." | the defect in the start candidate; the facts of a run (`Truth`) are kept apart from the router's own count (`ParentRec.cum`) |
| 17 | For 212 parent orders, "SMARS sent millions of child orders, resulting in 4 million executions in 154 stocks for more than 397 million shares in approximately 45 minutes"; an approximately $3.5 billion net long position in 80 stocks and an approximately $3.15 billion net short position in 74 stocks; "Knight realized a $460 million loss". | context only; not modeled |
| 23, 24 | The "33 Account" held "positions resulting from executions that Knight received back from the markets that its systems could not match to the unfilled quantity of a parent order"; "SMARS continued to send millions of child orders to the market despite the fact that the parent orders already had been completely filled". | REQ-NO-EXCESS-EXECUTION and REQ-STOP-WHEN-FILLED |
| 27 | Uninstalling the new RLP code from the seven correctly deployed servers caused additional parent orders "to activate the Power Peg code that was present on those servers". | every requirement quantifies over every code version, so it covers any number of servers on either build |

Section IV.C imposes a civil money penalty of $12,000,000.

## The model

A server runs one code version, `Build.rlp` (the new code) or `Build.legacy` (the new code was not copied). Events are new parent orders (`parent qty flag`, numbered 0, 1, 2, ... in arrival order), routing opportunities (`route id liq`), acknowledgements (`ack k`) and execution reports (`fill k q`: `q` shares of child order `k` executed). A router is `step : Build → State → Event → State × List Child`: it returns its next state and the child orders it sends.

The quantities the requirements talk about are computed by the specification from the events and the child orders the router emitted (`Truth`), never from the router's own state. An execution report executes at most the unexecuted shares of the child order it names, and a report for a child order that was never sent executes nothing, so the requirements hold over every sequence of events, including duplicate, oversized and unknown reports.

## Requirements

Each one quantifies over every code version, every flag value, every parent order and every sequence of events from the empty router.

| Requirement | Statement |
|---|---|
| REQ-NORMAL-ORDER-ROUTED | a 300-share order with three routing opportunities of 100 shares, each child order executed, is sent as exactly three 100-share child orders, 300 shares are executed, and a fourth routing opportunity sends nothing (the non-vacuity check: a router that never sends fails it) |
| REQ-ROUTES-AVAILABLE | a routing opportunity for an existing parent sends exactly one child order for the available liquidity capped at the shares not yet sent, and nothing when that is zero or the parent does not exist |
| REQ-NEVER-OVERROUTE | the cumulative shares sent in child orders for a parent never exceed its quantity |
| REQ-STOP-WHEN-FILLED | once a parent is executed in full, no event makes the router send another child order for it |
| REQ-NO-EXCESS-EXECUTION | the shares executed for a parent never exceed its quantity |
| REQ-FILL-ACCOUNTING | the router's cumulative executed quantity for every parent equals the shares actually executed in its child orders |

The Lean statements are in `spec/OrderRouter/Spec.lean`; `spec/OrderRouter/Challenge.lean` applies them to the definition hole `OrderRouter.step`. `spec/OrderRouter/Lemmas.lean` holds proved helper lemmas that hold for every router, among them `exec_le_sent` (the venue model never executes more than was sent).

## What was proved

- Both reference solutions are accepted by the judge (Comparator in paranoid mode with six kernels, leanchecker, axiom audit with only `propext`, `Quot.sound` and `Classical.choice`) and their executables pass the property tests (`validation.json`). `reference/SolutionA.lean` routes every build and flag on one path; `reference/SolutionB.lean` keeps the Power Peg path and repairs it.
- The start candidate `candidate/Solution.lean` is the reconstructed defect. `witnesses/buggy_original.lean` refutes it in the Lean kernel, with no `sorry` and only `propext` and `Quot.sound`:
  - `legacy_unbounded n`: one flagged 100-share parent order on the legacy build, then `n` rounds of a 100-share routing opportunity and an execution report that fills the child order just sent, gives `n` child orders, `100 * n` shares sent and `100 * n` shares executed, for every `n` (proved by induction);
  - `child_orders_unbounded N`: for every bound `N` there is an event sequence with more than `N` child orders for that single parent;
  - `rlp_one_child n`: the same events on the rlp build send exactly one 100-share child order;
  - `aug1_seven_servers` and `aug1_eighth_server`: with the new code on seven of eight servers, as in paragraph 15, the seven send one child order and the eighth sends `n`;
  - `refutes_*`: the start candidate violates each of the six requirements.
- `witnesses/restore_cum_count.lean` refutes the obvious repair (`attacks/restore_cum_count.lean`): if execution reports advance the Power Peg count again but Power Peg still decides from executions, two routing opportunities before any report send 200 shares for a 100-share order. Counting executions bounds what is executed only after it is reported; the shares sent are bounded only by counting what was sent.
- `attacks/rlp_only_proof.lean` proves every requirement for the rlp build only. Ordinary checking accepts it (every theorem name exists, no `sorry`, clean axioms); the judge rejects it because the statements differ from the locked ones, and its executable is refuted on the legacy build.

## Muse repairs

`results/knight-1` holds four runs of `agents/repair.py` with Muse Spark 1.3 on the Contributor tier and a $10 cap at list prices per run. Without a planner (A1), two runs proved only REQ-NORMAL-ORDER-ROUTED. With Muse Wonder 1.0 as planner (A2), the first run proved five of the six requirements before reaching its dollar cap, and the second was VERIFIED: $4.96 at list prices, $0.98 charged, Passport `98cfed64ae1ec596e517299b422a5fb0beac571cdce89c18ea2e5660845bc178`, reproduced with `bin/proofforge verify`. The accepted repair removes the Power Peg path. The results README has the per-run figures.

## What is not claimed

- The order does not describe Knight's code. How the cumulative quantity function was moved and why Power Peg stopped seeing executions is not stated; the start candidate models the outcome the order reports (paragraph 16) with one choice of mechanism: execution reports do not advance the count that the Power Peg stop check reads. Other mechanisms with the same outcome are possible.
- Nothing is claimed about Power Peg as it ran before 2005, about Knight's other systems, or about the controls the order finds missing (Rule 15c3-5). Prices, venues, order types, timing, cancellations and the 9.5 percent price collar of paragraph 21 are not modeled.
- The eight-server deployment appears only in the witness file; the requirements quantify over each server's code version, which covers every deployment because servers do not share state in the model.
- The executable wrapper `app/Main.lean` is tested, not proved.

## Sources

- SEC, In the Matter of Knight Capital Americas LLC, Order Instituting Administrative and Cease-and-Desist Proceedings, Release No. 34-70694, File No. 3-15570, October 16, 2013: https://www.sec.gov/files/litigation/admin/2013/34-70694.pdf. An automated request without a contact header was refused (HTTP 403) on 2026-10-29.
- The same 18-page PDF from the Internet Archive, used for every quotation here: https://web.archive.org/web/20201212052325/https://www.sec.gov/litigation/admin/2013/34-70694.pdf, SHA-256 `40e89727336e4adc3ecbe3800faabe2ca7c9daaed6858a4b3a7dcc518d3ba2b5` (PDF metadata: "Release No. 34-70694; File No. 3-15570; Date: 2013-10-16", created 2013-10-16).

## Reproduce

```sh
python3 harness/validate_task.py realworld/tasks/rc-knight-router
bin/proofforge check --task realworld/tasks/rc-knight-router --candidate realworld/tasks/rc-knight-router/reference/SolutionA.lean --out passport.json
bin/proofforge verify passport.json --candidate realworld/tasks/rc-knight-router/reference/SolutionA.lean
```
