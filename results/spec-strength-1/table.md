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

Surviving mutants whose behaviour differs from the reference:

- `rw-cetus-shlw` M021 (constant, `checkedShlw` line 25): constant `0` replaced by `1`; outputs differ on 4055 cases, first input `{"n": 6277101735386683105903941386108044688699448269690241981769, "op": "shlw"}`
- `rw-balancer-upscale` M011 (rounding, `subtractSwapFeeAmount` line 39): `mulUp` replaced by `mulDown`; outputs differ on 64 cases, first input `{"math": "product", "pool": {"balances": [434312381500305329691818, 1], "fee": 1000000000000000001, "rates": [1776791408642453381, 1100000000000000000]}, "swaps": [{"amount": 1, "in": 0, "kind": "in",`
- `rw-balancer-upscale` M044 (guard, `divUp` line 20): condition `a = 0` replaced by `false`; outputs differ on 126 cases, first input `{"math": "product", "pool": {"balances": [27419, 87191], "fee": 50000000000000000, "rates": [1000000000000000000, 1058132408689971699]}, "swaps": [{"amount": 0, "in": 1, "kind": "out", "out": 0}, {"am`
- `rw-balancer-upscale` M048 (guard, `subtractSwapFeeAmount` line 39): condition `mulUp amount fee ≤ amount` replaced by `true`; outputs differ on 92 cases, first input `{"math": "product", "pool": {"balances": [434312381500305329691818, 1], "fee": 1000000000000000001, "rates": [1776791408642453381, 1100000000000000000]}, "swaps": [{"amount": 1, "in": 0, "kind": "in",`
- `rw-balancer-upscale` M129 (constant, `divUp` line 20): constant `0` replaced by `1`; outputs differ on 126 cases, first input `{"math": "product", "pool": {"balances": [27419, 87191], "fee": 50000000000000000, "rates": [1000000000000000000, 1058132408689971699]}, "swaps": [{"amount": 0, "in": 1, "kind": "out", "out": 0}, {"am`
- `rw-balancer-upscale` M130 (constant, `divUp` line 20): constant `1` replaced by `2`; outputs differ on 4 cases, first input `{"math": "product", "pool": {"balances": [1, 580380105682104817724422], "fee": 1000000000000, "rates": [1999999999999999999, 1058132408689971699]}, "swaps": [{"amount": 1, "in": 1, "kind": "in", "out"`
- `rw-moneyphp-allocate` M002 (boundary, `argmaxTo` line 20): `<` replaced by `≤`; outputs differ on 2195 cases, first input `{"amount": 5, "ratios": [0, 7, 3]}`
- `rw-moneyphp-allocate` M050 (constant, `argmaxTo` line 19): constant `0` replaced by `1`; outputs differ on 672 cases, first input `{"amount": -111, "ratios": [1, 1, 1, 1, 1, 1, 1, 1]}`
- `rw-spliit-balances` M002 (boundary, `argmaxTo` line 20): `<` replaced by `≤`; outputs differ on 2195 cases, first input `{"amount": 100, "ratios": [1, 1, 1]}`
- `rw-spliit-balances` M050 (constant, `argmaxTo` line 19): constant `0` replaced by `1`; outputs differ on 674 cases, first input `{"amount": 100, "ratios": [1, 1, 1]}`
