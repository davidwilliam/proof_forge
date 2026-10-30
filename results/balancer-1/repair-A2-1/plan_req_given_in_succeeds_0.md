(1) Proof plan: For a given-in swap, fee subtraction succeeds when `fee < ONE` because the fee rounds up to at most the amount. Downscaling succeeds when the output rate is positive. By well-behavedness, the pool math returns at most the scaled output balance `balance * rate / ONE`; dividing that bound back down by the positive rate returns at most the raw balance. Hence settlement cannot fail for insufficient output balance, so `step` is `some`.

(2)
```lean
theorem plan0_div_le_of_le_scaled : ∀ (o B r : Nat), 0 < r → o ≤ B * r / ONE → o * ONE / r ≤ B := by sorry
theorem plan0_swapGivenIn_isSome : ∀ (m : PoolMath) (p : Pool) (s : Swap), p.fee < ONE → 0 < p.rate s.tokenOut → ∃ y, swapGivenIn m p s = some y := by sorry
theorem plan0_swapGivenIn_decomp : ∀ (m : PoolMath) (p : Pool) (s : Swap) (y : Nat), swapGivenIn m p s = some y → ∃ x o, o = m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x ∧ downscaleDown o (p.rate s.tokenOut) = some y := by sorry
theorem plan0_outGivenIn_le_scaled : ∀ (m : PoolMath) (p : Pool) (s : Swap) (x : Nat), WellBehaved m p.n → Valid p s → m.outGivenIn (scaledBalances p) s.tokenIn s.tokenOut x ≤ scaledBalances p s.tokenOut := by sorry
theorem plan0_downscaleDown_le_balance : ∀ (o y B r : Nat), downscaleDown o r = some y → 0 < r → o ≤ B * r / ONE → y ≤ B := by sorry
theorem plan0_step_givenIn_isSome : ∀ (m : PoolMath) (p : Pool) (s : Swap) (y : Nat), s.kind = .givenIn → Valid p s → onSwap m p s = some y → y ≤ p.balance s.tokenOut → (step onSwap m p s).isSome := by sorry
```