# rw-cetus-shlw: the Cetus overflow check

On 2025-05-22 an attacker drained the concentrated-liquidity pools of Cetus, a DEX on Sui. The Block reports, from Cetus's incident report, that about $223 million was taken, that the core pools were disabled within 30 minutes, and that addresses holding about $162 million were frozen. The cause was `checked_shlw` in Cetus's open-source Move library integer-mate, which "incorrectly validated inputs against a 256-bit limit instead of a 192-bit limit". Dedaub gives the attack deposit: tick range [300000, 300200], sqrt prices 60257519765924248467716150 and 60863087478126617965993239, liquidity 10365647984364446732462244378333008, and 1 unit of token A paid.

Cetus merged two fixes that day. Pull request 6 (merged 14:37 UTC) changed the mask to `1 << 192` and kept `n > mask`. Pull request 7 (merged 16:09 UTC) changed the test to `n >= mask`.

## What is proved

The task proves properties of a Lean 4 port of `checked_shlw` together with its caller `get_delta_a`, for all inputs: every 256-bit `n`, and every `u128` pair of sqrt prices and `u128` liquidity. Move's `u128` and `u256` are `BitVec 128` and `BitVec 256`; Move's `<<` drops the bits shifted out, exactly like `BitVec`'s `<<<`; a Move abort (an overflow flag, a division by zero, a `u64` cast that does not fit) is `none`. The statements are in `spec/ClmmMath/Spec.lean` and `spec/ClmmMath/Challenge.lean`; `checkedShlw` is the definition hole and `getDeltaA` is the protected caller, parameterized by the shift routine.

| Requirement | Lean statement (`spec/ClmmMath/Spec.lean`) |
|---|---|
| REQ-SHLW-EXACT | `∀ n, (shlw n).2 = false → (shlw n).1.toNat = n.toNat * 2 ^ 64`: when no overflow is reported, no bit is lost |
| REQ-SHLW-COMPLETE | `∀ n, n.toNat * 2 ^ 64 < 2 ^ 256 → (shlw n).2 = false`: no false overflow |
| REQ-DELTA-A-COVERS | rounding up, `getDeltaA shlw sp0 sp1 L true = some a → L * \|sp1 - sp0\| * 2 ^ 64 ≤ a * (sp0 * sp1)`: the depositor pays at least the exact amount for the liquidity received |
| REQ-DELTA-A-TIGHT | rounding up, `0 < a → (a - 1) * (sp0 * sp1) < L * \|sp1 - sp0\| * 2 ^ 64`: less than one unit over |
| REQ-DELTA-A-FLOOR | rounding down, `a * (sp0 * sp1) ≤ L * \|sp1 - sp0\| * 2 ^ 64`: the pool never pays more than the exact amount |

The returned amount is a `BitVec 64`, so it always fits a `u64`; a larger quotient aborts, as Move's cast does.

Sanity theorems, proved in `spec/ClmmMath/Lemmas.lean` for every shift routine:

- `attack_rejected`: any routine meeting REQ-SHLW-EXACT makes `getDeltaA` abort on the attack deposit (rounding up or down).
- `nonvacuous`: any routine meeting REQ-SHLW-EXACT and REQ-SHLW-COMPLETE makes `getDeltaA` return 3045910951 units for liquidity 10^18 over the attack's price range, so COVERS and TIGHT bind a real output and cannot be met by aborting.

Results:

| Lean port | Move source | Verdict |
|---|---|---|
| `attacks/buggy_original.lean` | `checked_shlw` at integer-mate commit `4d09c8ba0527274983c6664a5d5def2e784d4692`, `sui/sources/math_u256.move` lines 18 to 25 (the same function as lines 19 to 26 of commit `585f17eb3085c283e06ca229c6b6fc4fc2939e57`, which Dedaub links): `mask = 0xffffffffffffffff << 192`, `n > mask` | REFUTED |
| `attacks/pr6_mask_only.lean` | merge commit of pull request 6, `fc84a51c29fabfbfbdb8ed76506b61a07493d492`, lines 18 to 25: `mask = 1 << 192`, `n > mask` | REFUTED |
| `reference/SolutionA.lean` | merge commit of pull request 7, `06660f704c4ac1d443ab62346a46b5b60d49df33`, lines 18 to 25: `mask = 1 << 192`, `n >= mask` | VERIFIED |
| `reference/SolutionB.lean` | independent rewrite (tests `n >> 192 == 0`) | VERIFIED |
| `getDeltaA` in `Spec.lean` (protected) | `get_delta_a` in CetusProtocol/cetus-clmm-interface commit `5f1872c9e629050928b2b7c4605828e9203f5a98` (2025-05-15, the last change to the file before the incident), `sui/cetus_clmm/sources/math/clmm_math.move` lines 68 to 98, with `full_mul` and `div_round` from integer-mate | not a candidate |

Kernel-checked counterexamples (`decide`, standard axioms only):

- Original, `witnesses/buggy_original.lean`: on the attack deposit `liquidity * diff = 2^192 + 491983144293873864340816` (193 bits) is below the original mask, no overflow is reported, the shifted value is 9075487151368008912317032979326758767558656, and `getDeltaA` returns `some 1`. The exact amount, rounded up, is 31572840708638430117170542 units. This refutes REQ-SHLW-EXACT and REQ-DELTA-A-COVERS.
- Pull request 6, `witnesses/pr6_mask_only.lean`: `checkedShlw (2^192) = (0, false)`, refuting REQ-SHLW-EXACT. At the caller, liquidity 2^113 over sqrt prices 60257519765924248467716150 and 60257519765924248467716150 + 2^79 (so `liquidity * diff = 2^192`) is charged 0 units, refuting REQ-DELTA-A-COVERS. Pull request 6 does refuse the attack deposit itself; its only lossy input is `n = 2^192`, and `attacks/pr6_restated.lean` proves the other three requirements as stated and the two failing ones restated with `n ≠ 2^192`. Comparator rejects the restated statements.

Repair by Muse (`results/cetus-1/repair-A1-1`): arm A1, Muse Spark 1.3 on the Contributor tier with the ProofForge harness and no planner, started from the original port with a $10 list cap. It was accepted on its first attempt in 428 s, at $0.19 at standard list prices and $0.011 charged; arm A2 was therefore not run. Its fix tests `n.toNat * 2 ^ 64 < 2 ^ 256` directly; `results/cetus-1/repair-A1-1/Equivalence.lean` proves that it returns the same value and flag as the pull request 7 port on every 256-bit input. `bin/proofforge check` gives a VERIFIED Passport (all five requirements, six kernels, 2001 binary cases), Passport sha256 `9131dfdfd3e27da8145cd70972c65748a5447585ce2c625dee404b1506239852`, and `bin/proofforge verify` reproduces every hash and status (`verify.txt`).

Real Move code (`results/cetus-1/real-code`, `eval/realworld_cetus.py`): the real `checked_shlw` and `get_delta_a`, from the pinned commits and unmodified, were run with Sui CLI 1.83.0 (`sui move test`) on 2007 inputs, the 7 documented values plus 2000 generated by the task oracle (which includes 2^192 among its boundary values):

| Version | Real output equals its Lean port | Real output equals the proved component | Inputs that break a requirement |
|---|---|---|---|
| original (4d09c8b) | 2007 of 2007 | 1317 | 658: REQ-SHLW-EXACT 636, REQ-DELTA-A-COVERS 22; the attack deposit returns 1 |
| pull request 6 (fc84a51) | 2007 of 2007 | 1974 | 33: REQ-SHLW-EXACT 32 (all at n = 2^192), REQ-DELTA-A-COVERS 1 (the deposit with `liquidity * diff = 2^192`, which returns 0) |
| pull request 7 (06660f7) | 2007 of 2007 | 2007 | 0 |

For the original, 32 further outputs differ from the proved component but meet every requirement. Each recorded violation is restated as a Lean goal over the protected definitions and checked in the kernel (`real-code/Confirm.lean`, 9 of 9).

## What is not proved

- The Move code itself is not proved. The real code is run on 2007 inputs and compared with the Lean ports and the proved component; agreement on those inputs is tested, not proved.
- The ports are hand translations. The translation of Move integer semantics into `BitVec` and `Option` is reviewed, not machine-checked.
- `get_delta_a` is taken from the public interface repository, whose math modules have full bodies. The deployed package bytecode is not compared.
- `get_delta_b`, `get_liquidity_from_a`, the tick math and the rest of the pool (positions, swaps, fees) are not specified.
- Whether a deposit with `liquidity * diff = 2^192` was reachable through the pool's entry points under pull request 6 is not claimed; the requirement is stated over all `u128` inputs.
- REQ-SHLW-COMPLETE says that no valid shift is refused. A deposit whose exact amount fits a `u64` but whose `liquidity * diff * 2^64` does not fit 256 bits still aborts in the fixed code; the requirements do not claim otherwise.
- The JSON wrapper `app/Main.lean` is tested, not proved.

## Sources

- Dedaub, technical analysis with the attack inputs and the vulnerable commit link: https://dedaub.com/blog/the-cetus-amm-200m-hack-how-a-flawed-overflow-check-led-to-catastrophic-loss/
- The Block, summary of Cetus's incident report (amount taken, freeze, root cause wording): https://www.theblock.co/post/355795/sui-dex-cetus-open-source-library-flaw-smart-contract-223-million-usd-exploit
- integer-mate at the pinned commits: https://github.com/CetusProtocol/integer-mate/blob/4d09c8ba0527274983c6664a5d5def2e784d4692/sui/sources/math_u256.move, https://github.com/CetusProtocol/integer-mate/blob/585f17eb3085c283e06ca229c6b6fc4fc2939e57/sui/sources/math_u256.move
- Pull request 6: https://github.com/CetusProtocol/integer-mate/pull/6 (merged 2025-05-22T14:37:30Z, merge commit fc84a51c29fabfbfbdb8ed76506b61a07493d492)
- Pull request 7: https://github.com/CetusProtocol/integer-mate/pull/7 (merged 2025-05-22T16:09:27Z, merge commit 06660f704c4ac1d443ab62346a46b5b60d49df33)
- Caller: https://github.com/CetusProtocol/cetus-clmm-interface/blob/5f1872c9e629050928b2b7c4605828e9203f5a98/sui/cetus_clmm/sources/math/clmm_math.move
