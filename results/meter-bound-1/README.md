# meter-bound-1: the meter's input bound, replayed on the calls of results/muse-code-1

No model calls. `integrations/muse/meter_replay.py` replays the `calls.jsonl` of the 14 measured runs of
`results/muse-code-1` through `integrations/muse/meter.py` under two input bounds, with the $10 cap at list prices
and the 32,000-token output cap:

- **byte bound** (the rule the runs were measured with): every byte of the request is at most one input token,
  plus 64 tokens per input item and 2,048 fixed;
- **prefix bound** (now the meter's rule, for every arm): for a request that extends an earlier settled request of
  the same conversation, that request's reported `prompt_tokens` plus the byte length of the new items, with the
  same overheads; the smaller of the two bounds is used. Anything else falls back to the byte bound.

A call log has no message contents, so the replay infers the prefix relation: a call extends the previous settled
call of the same caller (role, opening of its instructions, reasoning effort, model) when it has more input items
and at least as many bytes, and its new items carry the byte difference. The live meter compares the actual items.
Calls are replayed one at a time in the order they settled.

Command: `python3 integrations/muse/meter_replay.py results/muse-code-1/*/*-[0-9] --out results/meter-bound-1/replay.json`

## Result

Under both bounds, in all 14 runs: no reservation held more than the $10 cap, and no call reported more input tokens
than the bound used for it (`input_bound_violations` 0). Under the prefix bound every recorded call is admitted. Per
byte the requests grew, the reported input grew by at most 0.80 tokens (requests run 3.1 to 4.6 bytes per token).

The five runs the dollar rule stopped. The request each run's stop refused, its input bound under each rule, and how
much of the $10 the run could use before that request no longer fits (the cap minus the request's worst case with
the minimum output allowance of 1,024 tokens):

| Run | Spent at the stop ($ list) | Byte bound (tokens) | Usable under it ($) | Prefix bound (tokens) | Usable under it ($) |
|---|---|---|---|---|---|
| rw-balancer-upscale/alone-2 | 7.52 | 2,005,192 | 7.49 | 350,526 | 9.56 |
| rw-balancer-upscale/alone-3 | 6.98 | 2,423,282 | 6.97 | 372,644 | 9.53 |
| rw-balancer-upscale/proofforge-2 | 7.94 | 1,656,943 | 7.92 | 396,508 | 9.50 |
| rw-compound-comp/alone-1 | 7.72 | 1,862,010 | 7.67 | 315,672 | 9.60 |
| rw-compound-comp/proofforge-1 | 7.08 | 2,355,441 | 7.05 | 378,527 | 9.52 |

The byte bound's usable amount matches each run's recorded spend at its stop to within $0.06, so the replay
reproduces the stops. Under the prefix bound those runs could have used $9.50 to $9.60 of the $10. What they would
have done with the rest is not measured here.

For the 9 runs that the judge accepted, the usable amount at their final request goes from $9.51 to $9.94 under
the byte bound to $9.84 to $9.98 under the prefix bound.

`replay.json` has, per run and rule: calls admitted, where the replay was refused (none), the largest reservation
held, reservations by bound, violations, and the final request's bound, worst case and usable amount.
`tests/test_muse_meter.py` checks these properties on every run.
