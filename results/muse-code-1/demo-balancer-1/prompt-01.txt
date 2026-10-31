Incident report for the swap wrapper in candidate/Solution.lean (also in ISSUE.md):

The swap wrapper `BalancerSwap.onSwap` (a port of the regular-swap path of Balancer V2's BaseGeneralPool, as deployed for the osETH/WETH Composable Stable Pool 0xDACf5Fa19b1f720111609043ac67A9818262850c on Ethereum) lets a batch of small given-out swaps drain the pool. In transaction 0x6ed07db1a9fe5c0794d44cd36081d6a6df103fab868cdd75d581e3bd23bc9742 (2025-11-03) the pool held 67,000 wei of WETH and 67,000 wei of osETH (scaling factor 1058132408689971699, fee 0.01%), and 30 rounds of three given-out swaps (osETH out down to 18 wei, then 17 wei of osETH out, then WETH out paid with osETH) took its invariant from 137,893 to 2,445. A request for 17 wei of osETH is worth 17.988 of the pool's 18-decimal units, but the pool math is asked to price 17 units: the first such swap was charged 625,492 wei of WETH, while 18 units cost 1,041,412. With the constant-product math of the specification, four rounds of this shape take the pool's WETH from 67,000 to 4,193 wei.

Fix it with ProofForge. This workspace is the ProofForge task rw-balancer-upscale; the requirements in spec/BalancerSwap/ are locked. Use the proofforge skill and the proofforge MCP tools:

1. Run check_candidate on the current file first and show me what ProofForge refutes, with the witness and the kernel-checked counterexample.
2. Fix `BalancerSwap.onSwap` in candidate/Solution.lean.
3. Prove all eight locked requirements of spec/BalancerSwap/Challenge.lean in candidate/Solution.lean, with the same names and statements and no `sorry`.
4. Check the fix with check_candidate until it is VERIFIED, then reproduce the Passport with verify_passport.

No proof, no merge. When you are done, give me the Passport path and its sha256, and one paragraph on what the fix changes.
