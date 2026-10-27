**Proof plan.** Write `W = natSum ws` and decompose each `amount * w` via division by `W`: summing over `ws` gives `amount * W = W * (sum of floor shares) + (sum of remainders)`. Each remainder is `< W`, so the remainder sum is at most `ws.length * W`. Since `leftover amount ws = amount - (sum of floor shares)`, multiplying the leftover by `W` therefore gives at most `ws.length * W`, and cancelling the positive factor `W` yields the goal.

```lean
theorem plan2_natSum_map_amount_mul (amount : Nat) (l : List Nat) :
    natSum (l.map (fun w => amount * w)) = amount * natSum l := by sorry

theorem plan2_div_mod_decomp (amount : Nat) (l : List Nat) (W : Nat) :
    natSum (l.map (fun w => amount * w)) =
      W * natSum (l.map (fun w => amount * w / W)) +
        natSum (l.map (fun w => (amount * w) % W)) := by sorry

theorem plan2_remainder_sum_le (amount : Nat) (l : List Nat) (W : Nat) (hW : 0 < W) :
    natSum (l.map (fun w => (amount * w) % W)) ≤ l.length * W := by sorry

theorem plan2_mul_sub_add (W amount F : Nat) (hF : F ≤ amount) :
    W * (amount - F) + W * F = amount * W := by sorry

theorem plan2_key_eq (amount : Nat) (ws : List Nat) :
    natSum ws * natSum (ws.map (floorShare amount (natSum ws))) +
        natSum (ws.map (fun w => (amount * w) % natSum ws)) =
      amount * natSum ws := by sorry

theorem plan2_mul_leftover_le (amount : Nat) (ws : List Nat)
    (hW : 0 < natSum ws)
    (hF : natSum (ws.map (floorShare amount (natSum ws))) ≤ amount) :
    natSum ws * leftover amount ws ≤ ws.length * natSum ws := by sorry
```