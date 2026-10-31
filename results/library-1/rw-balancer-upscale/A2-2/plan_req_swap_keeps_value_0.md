Short proof plan: For given-in, use `OutGivenInSound` at `netInDown`, then show the settled pool's scaled balances pointwise dominate that ideal trade: the in-token by a floor-addition/fee bound, the out-token because the paid raw amount times its rate is at most the scaled amount times `ONE`, and all other tokens unchanged; conclude by invariant monotonicity. For given-out, use `InGivenOutSound` at `scaleUp amount`, then similarly dominate the ideal trade: the in-token because the ceiling charge, after the fee factor, covers `ONE*ONE*price`, and the out-token because `amount*rate ≤ scaleUp amount * ONE`; conclude again by monotonicity. The lemmas below isolate exactly these ceiling, scaled-subtraction, and scaled-addition arithmetic facts.

```lean
theorem plan0_ceil_mul_ge : ∀ (N d : Nat), 0 < d → N ≤ (N + d - 1) / d * d := by sorry

theorem plan0_scaleUp_mul_ge : ∀ (a r : Nat), a * r ≤ scaleUp a r * ONE := by sorry

theorem plan0_scaleDown_sub_ge : ∀ (B y out r : Nat), y * r ≤ out * ONE → scaleDown B r - out ≤ scaleDown (B - y) r := by sorry

theorem plan0_scaleDown_add_net_ge : ∀ (B A r g : Nat), g ≤ ONE → scaleDown B r + A * g * r / (ONE * ONE) ≤ scaleDown (B + A) r := by sorry

theorem plan0_scaleDown_add_price_ge : ∀ (B c r g price : Nat), g ≤ ONE → ONE * ONE * price ≤ c * g * r → scaleDown B r + price ≤ scaleDown (B + c) r := by sorry
```