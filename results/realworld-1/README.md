# Real-world bugs: realworld-1

Four money routines from open-source projects, each with a documented bug that was reported and fixed upstream. For three of them (Spliit, go-money, moneyphp) a ProofForge task under `realworld/tasks/` locks the requirements as Lean predicates. Its start candidate and attacks are Lean ports of the buggy releases. Then each project's real code is run, unmodified, at the exact commit of every listed release and checked input by input against the same requirements and against a proved component. RubyMoney is checked as real code only, against the allocation requirements.

What is proved: the Lean component accepted by the judge (Comparator with six kernels, `leanchecker`, the implementation scan, 2,001 property cases on the rebuilt executable) meets every requirement for every input. What is tested: the real libraries, on 2,000 generated inputs from each routine's own domain plus the inputs documented in their issues, against the same requirements, with each output also compared to the proved component's output. The real libraries are not proved. A Lean port models a release's logic in exact arithmetic; it does not model floating point.

Every violation recorded for real code is restated as a `decide` goal over the specification's per-input predicates and checked in the Lean kernel (`*/real-code/Confirm.lean`; 35 goals, all checked). Every port's refutation on its documented input is a kernel-checked theorem (`realworld/tasks/*/witnesses/`; 6 ports, all checked).

Reproduce: `python3 eval/realworld.py --cases 2000 --seed 0` (needs Docker with the pinned Lean image, git, node and npm, go, ruby, and the pinned PHP image; sources are fetched at run time and not copied into this repository).

## Results

| Project (stars, license) | Release | Real code on 2,000+ inputs | Requirements broken |
|---|---|---|---|
| [Spliit](https://github.com/spliit-app/spliit) (3,030, MIT), `getBalances` | 1.21.0 | 977 inputs break a requirement: 439 lose cents, 538 create cents, up to 5 cents | REQ-CONSERVATION |
| | 1.22.0 (fix) | every requirement met on 2,001 inputs; 1,498 identical to the proved component, 503 break ties differently | none |
| [go-money](https://github.com/Rhymond/go-money) (1,912, MIT), `Money.Split` | v1.0.3 | panics on 750 valid inputs (index out of range) | REQ-VALID-SUCCEEDS |
| | v1.0.5 | 110 inputs get shares of the wrong sign that do not add up | REQ-CONSERVATION, REQ-SIGN, REQ-WITHIN-ONE-UNIT |
| | v1.0.6 (fix) | identical to the proved component on all 2,002 inputs | none |
| [moneyphp/money](https://github.com/moneyphp/money) (4,872, MIT), `Money::allocate` | v3.0.9 | 1,344 inputs: cents to zero-ratio parties, shares of the wrong sign, leftovers in list order | REQ-ZERO-RATIO, REQ-SIGN, REQ-WITHIN-ONE-UNIT, REQ-LARGEST-REMAINDER |
| | v3.1.0 | throws "Undefined offset" on 8 valid inputs; leftovers in list order on 1,306 | REQ-VALID-SUCCEEDS, REQ-WITHIN-ONE-UNIT, REQ-LARGEST-REMAINDER |
| | v3.2.0 | leftovers in list order on 1,312 inputs | REQ-WITHIN-ONE-UNIT, REQ-LARGEST-REMAINDER |
| | v3.2.1 (fix) | every requirement met on 2,003 inputs; 1,999 identical to the proved component, 4 break ties differently | none |
| [RubyMoney](https://github.com/RubyMoney/money) (2,883, MIT), `Allocation.generate` | v6.18.0 | loses a cent on the documented input and on 41 of 1,013 generated inputs with decimal ratios | REQ-CONSERVATION (and see below) |
| | v6.19.0 (fix) | conserves on every input | REQ-WITHIN-ONE-UNIT, REQ-LARGEST-REMAINDER (see below) |

The documented inputs, each confirmed on the real release:

- Spliit 1.21.0, [issue #374](https://github.com/spliit-app/spliit/issues/374): 100 cents split evenly three ways gives 33 + 33 + 33 = 99. The proved component gives 34 + 33 + 33. Issue #374 is still open; the fix shipped in 1.22.0 ([pull request #562](https://github.com/spliit-app/spliit/pull/562)).
- go-money v1.0.3, [pull request #94](https://github.com/Rhymond/go-money/pull/94): `Split(-101, 4)` panics with "index out of range [4] with length 4". v1.0.5, [issue #106](https://github.com/Rhymond/go-money/issues/106): `Split(-2, 3)` returns [1, 1, 0], which adds up to +2; the proved component returns [-1, -1, 0]. The fix shipped in v1.0.6 ([pull request #107](https://github.com/Rhymond/go-money/pull/107)).
- moneyphp v3.0.9, [issue #436](https://github.com/moneyphp/money/issues/436): allocating 5 with ratios [0, 7, 3] gives [1, 3, 1]; the proved component gives [0, 4, 1]. v3.1.0, the fix for #436, [issue #466](https://github.com/moneyphp/money/issues/466): allocating 1 with ratios [1, 1] throws "Undefined offset: 2"; the proved component gives [1, 0]. v3.2.0, [pull request #492](https://github.com/moneyphp/money/pull/492): 9999 with ratios [75, 25] gives [7500, 2499]; the proved component gives [7499, 2500], which v3.2.1 also returns ([pull request #526](https://github.com/moneyphp/money/pull/526)).
- RubyMoney v6.18.0, [issue #1033](https://github.com/RubyMoney/money/issues/1033): 700273 with the issue's decimal ratios gives shares that add up to 700272. Fixed in v6.19.0 ([pull request #1034](https://github.com/RubyMoney/money/pull/1034)).

RubyMoney, read with care: both releases allocate sequentially (each part takes a truncated share of what remains), so a share can be more than one cent away from its exact proportional share. For example, 128 cents with ratios [3, 7, 4, 0, 6, 8] gives the first party 15 cents where its exact share is 13.71. Our allocation requirements REQ-WITHIN-ONE-UNIT and REQ-LARGEST-REMAINDER rule this out; RubyMoney's documentation does not promise either property. This is a difference from our requirements, not a reported bug. The documented bug, a lost cent, breaks REQ-CONSERVATION, and v6.19.0 fixes it on every input tested.

## Muse repairs

The repairs were written by `agents/repair.py` with Muse Spark 1.3 on the Contributor tier and the Muse Wonder 1.0 planner (arm A2). Costs are at standard list prices, and charged.

| Task | Run | Caps | Outcome | List $ | Charged $ | Wall |
|---|---|---|---|---|---|---|
| rw-gomoney-split | repair-A2-1 | $3, 3600 s (E1 caps) | accepted: all 6 requirements VERIFIED, Passport `b336a739207fe2d6` | 0.97 | 0.22 | 1613 s |
| rw-spliit-balances | repair-A2-1 | $3, 3600 s | wall cap; 3 of 8 proved | 2.09 | 0.38 | 3600 s |
| | repair-A2-2 | $10, 10800 s | dollar cap; 7 of 8 proved (REQ-LARGEST-REMAINDER open) | 9.73 | 2.14 | 9109 s |
| | repair-A2-3 | $5, 7200 s, started from repair-A2-2's final candidate | accepted: all 8 requirements VERIFIED, Passport `6ae5595df2f580ad` | 2.44 | 0.39 | 1807 s |
| rw-moneyphp-allocate | repair-A2-1 | $3, 3600 s | wall cap; 3 of 8 proved | 2.01 | 0.44 | 3592 s |
| | repair-A2-2 | $10, 10800 s | dollar cap; 3 of 8 proved | 9.80 | 2.35 | 10208 s |

- **go-money:** Muse completed the repair within the E1 caps. Its `split` divides the magnitude and gives the leftover units, with the amount's sign, to the first parties. That is the behavior of the fixed v1.0.6, which matches it on all 2,002 inputs.
- **Spliit:** the repair took a second and a third run, $12.17 at list price across repair-A2-2 and repair-A2-3 ($2.53 charged). The accepted file is Muse's: a greedy largest-remainder allocation with 2,858 lines of proof. It still contains one unproved helper lemma, which no required theorem uses: the axiom audit shows only `propext`, `Quot.sound` and `Classical.choice`.
- **moneyphp:** Muse did not complete the repair.
- **Proved components used as references:**
  - go-money and Spliit: Muse's accepted repairs.
  - moneyphp and RubyMoney: the build-team reference (`realworld/tasks/rw-moneyphp-allocate/reference/SolutionA.lean`). It was written by the build team, not by a model, and is accepted by the same judge. It checks the same locked allocation specification as the Spliit task (manifest `32bf7261d904341e`).

## Files

- `summary.json`: run settings (image, seed, pinned PHP image, node packages, tool versions) and the per-project reports below.
- `<task or project>/real-code/`:
  - `cases.jsonl`: the inputs, documented ones first.
  - `<release>/outputs.jsonl`: the real code's outputs.
  - `report.json`: per release, counts, every documented witness and the first generated witness per requirement, each with the proved component's output and its Lean confirmation. It also records the ports' judge, binary and kernel-refutation results.
  - `Confirm.lean`: the witness goals checked in the kernel.
- `<task>/repair-*/`: the agent's final candidate (`final.lean`), budget summary (`summary.json`), event log (`events.jsonl`) and console log (`agent.log`). Accepted repairs also have their Passport (`passport.json`).
- The adapters that call the real code are in `realworld/adapters/`. Each project is fetched at the commit its tag pointed to when this ran; `eval/realworld.py` refuses to run if a tag has moved.
