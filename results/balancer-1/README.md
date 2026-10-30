# Balancer results: swap rounding in the V2 Composable Stable Pool

Task: `realworld/tasks/rw-balancer-upscale` (locked manifest
`57787df38ed76a28b1ef04d5eb7de74e6ec85c41873ee6f074ee7e0ceec052eb`). Its README states what is
specified, proved and tested.

## Muse runs

Muse Spark 1.3 on the Contributor tier (`muse-spark-1.3-contributor`), `agents/repair.py`, with a $10
cap at standard list prices and 14,400 s per run, at most two attempts per arm. Repair mode starts
from the port (`candidate/Solution.lean`) with the issue report; implement mode starts from a stub
generated from the locked challenge (`onSwap := fun _ _ _ => none`, every theorem `sorry`) and sees
neither the port nor the issue report.

| Run | Mode, arm | Outcome | Time | List $ | Charged $ |
|---|---|---|---|---|---|
| `repair-A1-1` | repair, A1 (`--planner none`) | UNRESOLVED: stopped at the dollar cap; best version in session proved 6 of 8 (REQ-SWAP-KEEPS-VALUE and REQ-BATCH-KEEPS-VALUE open); the final snapshot proves none | 11,666 s | 9.73 | 0.56 |
| `repair-A1-2` | repair, A1, second attempt | all 8 requirements VERIFIED | 3,212 s | 3.03 | 0.16 |
| `repair-A2-1` | repair, A2 (`--planner muse-wonder-1.0`) | all 8 requirements VERIFIED | 2,344 s | 2.51 | 0.41 |
| `implement-1` | implement, A1 | UNRESOLVED: stopped at the dollar cap; best version in session proved 6 of 8 (the same two open) | 9,316 s | 9.67 | 0.58 |
| `implement-2` | implement, A1, second attempt | all 8 requirements VERIFIED | 4,444 s | 3.81 | 0.21 |

Costs by model: `repair-A2-1` spent $2.22 list ($0.12 charged) on Muse Spark (149 calls) and $0.29
list ($0.29 charged) on Muse Wonder (2 planner calls). The other runs used Muse Spark only:
`repair-A1-1` 166 calls, `repair-A1-2` 178, `implement-1` 180, `implement-2` 119. A1 attempt 1
failed, so A2 was run as specified; A1 attempt 2 was started at the same time as A2 and also
succeeded.

`repair-A2-1` changes the port in one place: `swapGivenOut` upscales the amount out with a new
`upscaleUp` (`(amount * scalingFactor + (ONE - 1)) / ONE`, rounding up) instead of `upscale`
(`mulDown`), and goes on only when that amount is below the scaled balance; everything else is the
port. This is the fix of `reference/SolutionA.lean`. `repair-A1-2` makes the same change, writing
the rounded-up amount with the specification's `scaleUp`. `implement-2` writes the wrapper from the
specification: a given-in swap prices `netInDown` (the exact net amount in, rounded down) and pays
out `outGivenIn * ONE / rate` rounded down; a given-out swap prices the amount out rounded up and
charges it rounded up twice, for the conversion to raw units and for the fee.

The two runs that reached the cap had proved the six per-swap requirements in session but not
REQ-SWAP-KEEPS-VALUE, from which their proofs of REQ-BATCH-KEEPS-VALUE follow. In each, the final
snapshot is the session's last compiling version, not its best one: `repair-A1-1/final.lean` proves
none of the eight, `implement-1/final.lean` proves five.

Files in each run directory: `final.lean` (the selected candidate), `summary.json` and
`events.jsonl` (budget and event log), `stdout.txt`, and for the accepted runs `judge_v*.json`
(the in-session judge record), `passport.json`, `check.txt` and `verify.txt`.

## Passports

`bin/proofforge check --task realworld/tasks/rw-balancer-upscale --candidate <file> --out <passport>`;
each VERIFIED Passport was reproduced with `bin/proofforge verify <passport> --candidate <file>`
(every hash and status, including the executable hash on the same platform; `verify.txt`).

| Candidate | Status | Passport sha256 |
|---|---|---|
| `repair-A2-1/final.lean` | VERIFIED, 8 of 8, six kernels, 2,001 binary cases | `48930efdd4d67460bfd22bb15dfa9625caafc36cd6fca3a8fee444d5f3b204ba` |
| `repair-A1-2/final.lean` | VERIFIED, 8 of 8, six kernels, 2,001 binary cases | `eb1adce9d7aa20d3373ac6a1b0787e08c84aa284e31ec29cec796c8098ce7a19` |
| `implement-2/final.lean` | VERIFIED, 8 of 8, six kernels, 2,001 binary cases | `65d5a81fef2352eb67a72f032ade091fd051b30ebf44c310b1d0c6dcb1b84d3d` |
| `reference/SolutionA.lean` (`passports/reference.json`) | VERIFIED | `1ce4b1668c0861c51fb6e3e5ff6c9a0c18f85bb1f8ce39a3fcc42924aa9b0b76` |
| the port, `attacks/balancer_port.lean` (`passports/port.json`) | REFUTED: REQ-GIVEN-OUT-CHARGES-AT-LEAST, REQ-SWAP-KEEPS-VALUE and REQ-BATCH-KEEPS-VALUE by binary witnesses, the rest UNRESOLVED (proofs `sorry`) | `d65bd405a13bfd4feaef838e4cc60dea2560bc47ff78cad8dfda591aaf26cb71` |

## Deployed contracts

`real-code/report.json` comes from `python3 eval/realworld_balancer.py --cases 500 --out results/balancer-1`
(forge 1.4.4, public archive RPC `https://eth.drpc.org`, no credentials). The run forks Ethereum at
the state just before transaction `0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742`,
runs the attack's first 22 swaps as one `batchSwap`, which leaves the osETH/WETH pool with 67,000
wei of each token, and runs 501 batches through the deployed Vault's `swap`: the attack's 90 swaps
and 500 generated batches (10,385 swaps in all), from that state or from the state before the
transaction. The fork reports scaling factors 1e18 and 1058132408689971699, fee 1e14 and
amplification 200000. The same batches run on the executables of the port and of the accepted repair
`repair-A2-1` (the only accepted repair when this run was made), with the StableMath port as the
pool math.

| Check | Result |
|---|---|
| deployed code identical to the port (success flag, amount and balances of every swap) | 501 of 501 batches |
| the attack's 90 swaps on the deployed code | every amount equals the transaction's Swap event; D 137,893 to 2,445; `getRate()` 1029274992349090474 to 18250218330832792 |
| deployed code identical to the proved component | 194 of 501 batches |
| given-out swaps the deployed code charged less than the proved component | 546 |
| batches from the 67,000-wei state that go through on the deployed code | 85 of 344; D and `getRate()` fall in the same 56 |
| batches from the state before the transaction that go through | 88 of 157; D falls in none; `getRate()` falls in 25, by at most 0.022% (not investigated) |
| batches that go through on the proved component | 119 of 501; D falls in none (tested: StableMath is not proved well behaved) |
| falls of D on the deployed code's balances checked in the Lean kernel | 6 of 6 (`real-code/Confirm.lean`) |
| `witnesses/attack_batch.lean` on the port, `tests/PortUnitTests.lean` on the port and on the proved component | checked; the 11 unit tests pass on both |

The outputs are in `real-code/real-outputs.jsonl`, `port-outputs.jsonl`, `proved-outputs.jsonl` and
`cases.jsonl`; `real-code.log` is the run's console output.
