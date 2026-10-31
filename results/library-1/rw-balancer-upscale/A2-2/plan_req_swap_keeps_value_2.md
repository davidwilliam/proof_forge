(1) Proof plan: Split on the swap kind and on whether `onSwap` returns a value. For given-in, the math's soundness gives invariance for adding `netInDown` and subtracting the scaled output; the raw output satisfies `y * rateOut ≤ outScaled * ONE`, so the settled scaled balances dominate that updated balance pointwise, and invariant monotonicity finishes. For given-out, use the ceiling charge to get `ONE*ONE*price ≤ c*(ONE-fee)*rateIn`, together with `amount * rateOut ≤ scaleUp amount rateOut * ONE`; again the settled scaled balances dominate the math's updated balance, so in-given-out soundness plus monotonicity finishes. Settlement/`Valid` only identify the settled pool's balances with the corresponding `update2`.

(2)
```lean
theorem plan2_div_mul_le : ∀ (out r : Nat), out * ONE / r * r ≤ out * ONE := by sorry

theorem plan2_ceil_charge_ge : ∀ (price fee rate c : Nat),
    0 < (ONE - fee) * rate →
    c = (ONE * ONE * price + ((ONE - fee) * rate) - 1) / ((ONE - fee) * rate) →
    ONE * ONE * price ≤ c * (ONE - fee) * rate := by sorry

theorem plan2_invariant_mono_of_update2_le : ∀ (m : PoolMath) (n : Nat)
    (b b' : Nat → Nat) (i j xi yj : Nat),
    InvariantMonotone m n →
    (∀ k, k < n → update2 b i xi j yj k ≤ b' k) →
    m.invariant (update2 b i xi j yj) ≤ m.invariant b' := by sorry

theorem plan2_scaled_givenIn_dom : ∀ (p : Pool) (s : Swap) (y outS : Nat),
    s.tokenIn ≠ s.tokenOut →
    y * p.rate s.tokenOut ≤ outS * ONE →
    ∀ k, update2 (scaledBalances p) s.tokenIn
          ((scaledBalances p) s.tokenIn + netInDown p s)
          s.tokenOut ((scaledBalances p) s.tokenOut - outS) k ≤
        scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + s.amount)
          s.tokenOut (p.balance s.tokenOut - y) k) (p.rate k) := by sorry

theorem plan2_scaled_givenOut_dom : ∀ (p : Pool) (s : Swap) (c price : Nat),
    s.tokenIn ≠ s.tokenOut →
    ONE * ONE * price ≤ c * (ONE - p.fee) * p.rate s.tokenIn →
    s.amount * p.rate s.tokenOut ≤ scaleUp s.amount (p.rate s.tokenOut) * ONE →
    ∀ k, update2 (scaledBalances p) s.tokenIn
          ((scaledBalances p) s.tokenIn + price)
          s.tokenOut ((scaledBalances p) s.tokenOut - scaleUp s.amount (p.rate s.tokenOut)) k ≤
        scaleDown (update2 p.balance s.tokenIn (p.balance s.tokenIn + c)
          s.tokenOut (p.balance s.tokenOut - s.amount) k) (p.rate k) := by sorry
```