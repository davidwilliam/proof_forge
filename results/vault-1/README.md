# Vault results: Hundred Finance share accounting

Task: `realworld/tasks/rw-hundred-vault` (locked manifest
`37515f0be09213bb191e9cee58a4036496e2a0b253ff025a2a8c2fdafb79e077`). Its README states what is
specified, proved and tested.

## Muse repair

| Run | Arm | Model | Caps | Outcome | Time | List $ | Charged $ |
|---|---|---|---|---|---|---|---|
| `repair-A1-1` | A1 (`--planner none`) | muse-spark-1.3-contributor | $10 list, 7,200 s | all 10 requirements VERIFIED | 1,200 s | 0.65 | 0.037 |

The run starts from the port of the hToken (`candidate/Solution.lean`). In the
behavior-first phase, Muse replaced the truncated exchange rate with exact `assets / supply`
pricing: deposits round down, redemptions round down, and withdrawals burn
`(x * supply + assets - 1) / assets`. The binary tests passed after that phase. The first
pass of per-obligation dialogs proved eight requirements. `req_withdraw_succeeds` and
`req_share_value` were proved in the second phase without a planner, the latter through
helper lemmas for one-step monotonicity and transitivity of `ValueNotBelow`. The session's
check reported ACCEPTED at 1,190 s. The run made 67 model calls with 551,293 prompt tokens
(354,224 cached) and 82,784 completion tokens. Attempt 2 and the A2 arm were not run,
because A1 succeeded on its first attempt.

Files in `repair-A1-1`:

- `final.lean`: the accepted candidate.
- `summary.json` and `events.jsonl`: the budget and the event log.
- `judge_v039.json`: the in-session judge record of the accepted version.
- `passport.json` and `passport.md`: the Passport from `bin/proofforge check`.
- `verify.txt`: the output of `bin/proofforge verify`.

## Passport

`bin/proofforge check --task realworld/tasks/rw-hundred-vault --candidate results/vault-1/repair-A1-1/final.lean`
returned VERIFIED for all ten requirements. The candidate was accepted by Comparator in
paranoid mode with six kernels and replayed by `leanchecker`. The executable `vault-sidecar`
(linux/arm64, sha256 `1fa3777b174b8aac...`) passed 2,001 property cases.

- Passport sha256: `08fe86f17f27c49d60bda786d1498200d333c1c8d63d2f858ab668cd4f7fe7c4`
- Solution tree sha256: `19f2cc72c049ff5aa785e37c266a4d6701791053dbcaee1d547cf023ee8a77a1`

`bin/proofforge verify results/vault-1/repair-A1-1/passport.json --candidate results/vault-1/repair-A1-1/final.lean`
reproduced every hash and status, including the executable hash on the same platform.

## Deployed contract

`real-code/report.json` comes from `python3 eval/vault.py --cases 500 --out results/vault-1`.
The run forks Optimism at block 90761917 and empties the hWBTC market as the attacker did.
The admin then withdraws the 377 satoshi of reserves, which leaves 1 satoshi of cash and no
shares. 501 sequences (the documented attack plus 500 generated) then ran on the deployed
`CErc20Delegate` bytecode, on the Lean port, and on the executable of the Muse repair above.

| Check | Result |
|---|---|
| deployed contract identical to the port, every operation | 501 of 501 sequences |
| deployed contract meets every requirement | 209 of 501 sequences |
| sequences where the deployed contract breaks a requirement | 292: REQ-WITHDRAW-ROUNDS-UP 291, REQ-SHARE-VALUE 289, REQ-REDEEM-ROUNDS-DOWN 2 |
| Muse repair breaks a requirement | 0 of 501 |
| witnesses restated as `decide` goals and checked in the kernel | 5 of 5 (`real-code/Confirm.lean`) |
| port refutations (`witnesses/*.lean`) and unit tests (`tests/PortUnitTests.lean`) | checked; the 12 unit tests pass on the port |

The outputs are in `real-code/real-outputs.jsonl`, `port-outputs.jsonl`,
`proved-outputs.jsonl` and `cases.jsonl`.
