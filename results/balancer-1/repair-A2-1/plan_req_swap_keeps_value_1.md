(1) **Proof plan.** For a successful swap, unpack `step`, `onSwap`, and `settle`. In the given-in case, the fee-netted scaled input is at most the raw amount credited, and `downscaleDown` ensures the raw output scaled is at most the math's scaled output; these give a pointwise bound between the post-trade scaled balances used by `OutGivenInSound` and the settled pool's scaled balances. In the given-out case, the analogous bounds follow from `divUp`/`addSwapFeeAmount` charging at least the math's scaled input and from scaling the exact output up. Applying `InvariantMonotone` to those pointwise bounds, chained with the appropriate soundness property, proves each case; `req_swap_keeps_value` then follows by cases on `s.kind`.

(2)
```lean
theorem plan1_givenIn_pointwise : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool) (amt x o c : Nat),
    Valid p s → s.kind = .givenIn →
    subtractSwapFeeAmount s.amount p.fee = some amt →
    x = upscale amt (p.rate s.tokenIn) →
    o = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x →
    downscaleDown o (p.rate s.tokenOut) = some c →
    settle p s c = some p' →
    ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + x)
        s.tokenOut (scaledBalances p s.tokenOut - o) k ≤ scaledBalances p' k := by sorry

theorem plan1_givenOut_pointwise : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool) (P ai c : Nat),
    Valid p s → s.kind = .givenOut →
    P = m.inGivenOut (scaledBalances p) s.tokenIn s.tokenOut
      (scaleUp s.amount (p.rate s.tokenOut)) →
    downscaleUp P (p.rate s.tokenIn) = some ai →
    addSwapFeeAmount ai p.fee = some c →
    settle p s c = some p' →
    ∀ k, k < p.n →
      update2 (scaledBalances p) s.tokenIn (scaledBalances p s.tokenIn + P)
        s.tokenOut (scaledBalances p s.tokenOut -
          scaleUp s.amount (p.rate s.tokenOut)) k ≤ scaledBalances p' k := by sorry

theorem plan1_givenIn_value : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool),
    WellBehaved m p.n → s.kind = .givenIn →
    step onSwap m p s = some p' → value m p ≤ value m p' := by sorry

theorem plan1_givenOut_value : ∀ (m : PoolMath) (p : Pool) (s : Swap) (p' : Pool),
    WellBehaved m p.n → s.kind = .givenOut →
    step onSwap m p s = some p' → value m p ≤ value m p' := by sorry
```