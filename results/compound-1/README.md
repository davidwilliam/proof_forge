# Compound results: COMP reward distribution after Proposal 62

Task: `realworld/tasks/rw-compound-comp` (locked manifest
`1490fbf459091f4ea9d0717f912178a6e85597172a7bcd24ab3ce44678192e96`). Its README states what is
specified, proved and tested.

## Muse runs

Muse Spark 1.3 on the Contributor tier (`muse-spark-1.3-contributor`), `agents/repair.py`, each
run capped at $10 at standard list prices and 14,400 s. Repair mode starts from the port of the
Proposal 62 code with the issue report; implement mode starts from a stub generated from the
locked challenge, without the port, the issue report or the reference. Arm A2 adds Muse Wonder
1.0 as lemma planner. A2 was started after the first A1 attempt failed, and ran alongside the
second A1 attempt.

| Run | Mode, arm | Stop | Proved in the final version | Time | List $ | Charged $ | Passport |
|---|---|---|---|---|---|---|---|
| `repair-A1-1` | repair, A1 | dollar cap | 0 of 8 | 13,492 s | 9.83 | 0.52 | REFUTED |
| `repair-A1-2` | repair, A1 | wall-clock cap | 0 of 8 | 14,401 s | 8.20 | 0.43 | UNRESOLVED |
| `repair-A2-1` | repair, A2 | dollar cap | 5 of 8 | 10,483 s | 9.68 | 1.93 | UNRESOLVED |
| `repair-A2-2` | repair, A2 | dollar cap | 5 of 8 | 12,708 s | 9.69 | 1.78 | UNRESOLVED |
| `implement-1` | implement, A1 | dollar cap | 3 of 8 | 12,420 s | 9.77 | 0.54 | UNRESOLVED |
| `implement-2` | implement, A1 | wall-clock cap | 4 of 8 | 14,401 s | 7.38 | 0.38 | UNRESOLVED |

No run proved all eight requirements, so the outcome is UNRESOLVED for every arm and for
implement mode. The six runs cost $54.55 at list prices and $5.58 charged. In the A2 runs, Muse
Wonder accounted for $1.49 and $1.32 of the charged amount (it is charged at list price).

What happened in the runs, from `events.jsonl` and `agent.log`:

- In both A1 repair runs, the behavior-first phase changed the port so that the binary tests
  passed. The per-requirement dialogs then proved none of the eight requirements. The
  compile-and-retry fallback rewrote the file, and the run ended on the last version that
  compiled. In `repair-A1-1` that version's executable is refuted on REQ-SUPPLY-HOOK,
  REQ-BORROW-HOOK, REQ-CLAIM and REQ-SET-SPEEDS (its index updates are wrong); in
  `repair-A1-2` it is refuted as well.
- Both A2 runs proved the five per-call requirements (REQ-CALLS-SUCCEED, REQ-SUPPLY-HOOK,
  REQ-BORROW-HOOK, REQ-CLAIM, REQ-SET-SPEEDS), several through lemmas the planner proposed.
  Their final executables pass all 2,001 property cases. REQ-REWARDS-BOUNDED,
  REQ-ACCOUNT-BOUNDED and REQ-NO-BACKDATED-REWARDS stayed unproved. In `repair-A2-2` the
  planner decomposed REQ-REWARDS-BOUNDED into a potential that does not grow per operation
  (`plan6_exec_potF_le` in `agent.log`); the decomposition was not completed.
- The implement runs wrote a correct implementation (their final executables pass all 2,001
  cases) and proved three and four of the per-call requirements. Neither proved a sequence
  requirement.

The three unproved requirements are the ones that quantify over every pre-upgrade state and
every sequence of operations. The reference proves them with a potential function over the
account list (`reference/SolutionA.lean`, about 1,600 lines).

Each run directory holds `final.lean` (the version the run ended on), `summary.json`,
`events.jsonl`, `agent.log`, `passport.json` and `check.txt` (from `bin/proofforge check`), and
`verify.txt` (from `bin/proofforge verify`, which reproduced every Passport).

Passport hashes (sha256): `repair-A1-1` `498bdf4350258dd2f9db25434ef4697a206aa44a9909982b0ed4e0047f5cdc99`,
`repair-A1-2` `c1f371e8ce18fa91e3a148b9f305b38a863b80a4886d0316046a1e06ec786411`,
`repair-A2-1` `bcc8f7807df120a66156e809a45ceffd70dfea8722ae3a7bc7ac054326af3c36`,
`repair-A2-2` `94d7c2ecbe0c5eb9c9e55fca828da4163164e13bc0afc667e6800fd99c2c6653`,
`implement-1` `9215a10735f62866656aff73339f3972e6fba028f14565fa7cf8951d8a885d84`,
`implement-2` `890911e6d188ca1cb36a5ed76adecf26f0409581f80ceaa3704503ea3ba2738f`. A requirement
proved in a run but not accepted by the judge is UNRESOLVED in its Passport: the judge accepts a
candidate only when every required theorem is proved.

## Proved component and port

`passports/reference.json`: `bin/proofforge check --task rw-compound-comp --candidate
realworld/tasks/rw-compound-comp/reference/SolutionA.lean` returned VERIFIED for all eight
requirements (Comparator in paranoid mode with six kernels, `leanchecker`, axioms `propext`,
`Classical.choice`, `Quot.sound`; executable `comp-sidecar`, linux/arm64, 2,001 property cases).
Passport sha256 `7ccce9a2ebe8bffb61198e010b595f3126fb0ac5aa21c9906fe73593b2528d4a`.
`passports/port.json`: the Proposal 62 port is REFUTED (Passport
`3ac121be0f5748feeb430e95637d409048441b55a91e009b2253f3ded07693a3`); its first witness is the
cSUSHI claim. Both reproduce with `bin/proofforge verify` (`passports/*-verify.txt`).

## Deployed code

`real-code/report.json` comes from `python3 eval/realworld_compound.py --cases 500 --out
results/compound-1 --scan` (log in `real-code.log`). No Muse repair was accepted, so the
proved component in the comparison is the build-team reference.

| Check | Result |
|---|---|
| compiled Comptroller vs deployed runtime code (metadata hash excluded) | identical for Proposals 62, 64 and 65 |
| Proposal 62 build identical to the Lean port, every operation | 503 of 503 sequences |
| Proposal 64 build identical to the Lean port of Proposal 64 | 503 of 503 |
| Proposal 65 build identical to the proved component | 503 of 503 |
| Proposal 62 build breaks a requirement | 279 sequences: REQ-ACCOUNT-BOUNDED 252, REQ-REWARDS-BOUNDED 229, REQ-CLAIM 182, REQ-SUPPLY-HOOK 99, REQ-BORROW-HOOK 74 |
| Proposal 64 build breaks a requirement | 104 sequences, REQ-CLAIM only |
| Proposal 65 build breaks a requirement | 0 |
| violations restated as `decide` goals and checked in the kernel | 8 of 8 (`real-code/Confirm.lean`) |
| fork replay of the cSUSHI claim at block 13322936 | Proposal 62: 18977306140567618322762 credited and paid; Proposals 64 and 65: 0 |
| port refutations, unit tests, Compound's regression test | checked; the 14 unit tests pass on the port and on the reference; the regression test fails on the port and passes on the reference |
| mainnet credits at index 1e36, blocks 13322798 to 13382884 | 86 credits to 74 accounts (`real-code/onchain-credits.jsonl`) |

Outputs are in `real-code/real-p62-outputs.jsonl`, `real-p64-outputs.jsonl` and
`real-p65-outputs.jsonl`, with the inputs in `cases.jsonl`. The Lean outputs equal them; the
report records their SHA-256 (`lean_outputs`).
