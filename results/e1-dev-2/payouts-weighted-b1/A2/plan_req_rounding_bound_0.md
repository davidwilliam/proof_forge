**Proof plan:** On success, reuse the pro-rata equality to replace the balance difference by `weightedShare r.amount r.weights i`. Validity gives positive weights with nonzero total weight `W`. The floor share `amount * w / W` satisfies ` (amount*w/W)*W ≤ amount*w < (amount*w/W)*W + W`; adding the possible one-cent leftover bonus preserves both required bounds. Casting these natural-number bounds to `Int` then gives exactly `RoundingBound`.

```lean
theorem plan0_div_mul_le (x W : Nat) : x / W * W ≤ x := by sorry

theorem plan0_lt_div_mul_add (x W : Nat) (hW : 0 < W) : x < x / W * W + W := by sorry

theorem plan0_natSum_pos (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) : 0 < natSum ws := by sorry

theorem plan0_weighted_share_nat_bounds (amount : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    weightedShare amount ws i * natSum ws ≤ amount * ws.getD i 0 + natSum ws ∧
    amount * ws.getD i 0 < weightedShare amount ws i * natSum ws + natSum ws := by sorry

theorem plan0_weighted_share_int_bounds (amount : Nat) (ws : List Nat) (i : Nat) (hW : 0 < natSum ws) :
    (weightedShare amount ws i : Int) * (natSum ws : Int) ≤ ((amount * ws.getD i 0 : Nat) : Int) + (natSum ws : Int) ∧
    ((amount * ws.getD i 0 : Nat) : Int) < (weightedShare amount ws i : Int) * (natSum ws : Int) + (natSum ws : Int) := by sorry
```