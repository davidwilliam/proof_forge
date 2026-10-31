**Proof plan.** Split the successful swap by kind and unfold `step`/`settle`, so the new pool’s balances are `p.balance` updated at `tokenIn`/`tokenOut`. For given-in, use `WellBehaved.outGivenIn` at `netInDown`; for given-out, use `WellBehaved.inGivenOut` at the guarded `scaleUp` amount. It remains to compare the math-updated scaled balances pointwise with the settled pool’s scaled balances: the in-side uses superadditivity of `scaleDown` plus the two rounding chains below, the out-side uses the two subtraction estimates. `InvariantMonotone` then lifts that pointwise comparison through the invariant, chaining with soundness. Batch value preservation follows from the single-swap result as already proved.

```lean
theorem plan0_scaleDown_add_le (a b r : Nat) :
    scaleDown a r + scaleDown b r ≤ scaleDown (a + b) r := by sorry

theorem plan0_netInDown_le_scaleDown (p : Pool) (s : Swap) :
    netInDown p s ≤ scaleDown s.amount (p.rate s.tokenIn) := by sorry

theorem plan0_scaleDown_sub_le_of_mul_le (b out y r : Nat)
    (hy : y * r ≤ out * ONE) (hout : out ≤ scaleDown b r) :
    scaleDown b r - out ≤ scaleDown (b - y) r := by sorry

theorem plan0_scaleDown_sub_scaleUp_le (b t r : Nat) :
    scaleDown b r - scaleUp t r ≤ scaleDown (b - t) r := by sorry

theorem plan0_scaleDown_charge_le_of_divUp_chain (P rin fee r0 c : Nat)
    (h1 : divUp P rin = some r0) (h2 : addSwapFeeAmount r0 fee = some c) :
    P ≤ scaleDown c rin := by sorry

theorem plan0_update2_le_of_parts (b b' : Nat → Nat) (i j x y : Nat)
    (hij : i ≠ j) (hi : b i + x ≤ b' i) (hj : b j - y ≤ b' j)
    (hother : ∀ k, k ≠ i → k ≠ j → b k ≤ b' k) :
    ∀ k, update2 b i (b i + x) j (b j - y) k ≤ b' k := by sorry
```