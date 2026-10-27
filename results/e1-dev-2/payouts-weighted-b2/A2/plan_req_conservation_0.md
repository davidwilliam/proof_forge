(1) Proof plan: In the valid case, `step` keeps `accounts` and replaces balances by `expectedBalance`. Using the supplied `sumOver` lemmas, the new total is the old total minus `amount` (the source is in the duplicate-free account list) plus the sum of all `shareOf` values. Shares vanish outside `recipients`; on recipients, `indexOf?_getElem` identifies them with the indexed `weightedShare`s. Thus conservation reduces to the pure natural-number fact that the range-sum of `weightedShare amount ws` is `amount`: each term is a floor share plus possibly one leftover cent, the floor shares sum to at most `amount`, and the number of leftover cents is at most the length, with floor-sum + leftover = `amount`.

(2)
```lean
theorem plan0_range_succ_map (n : Nat) (g : Nat → Nat) :
    (List.range (n + 1)).map g = g 0 :: (List.range n).map (fun i => g (i + 1)) := by sorry

theorem plan0_floor_sum_mul_le (amount W : Nat) (ws : List Nat) :
    natSum (ws.map (floorShare amount W)) * W ≤ amount * natSum ws := by sorry

theorem plan0_amount_mul_le_floor_sum_add_length (amount W : Nat) (ws : List Nat) (hW : 0 < W) :
    amount * natSum ws ≤ (natSum (ws.map (floorShare amount W)) + ws.length) * W := by sorry

theorem plan0_range_floor_add_indicator_sum (amount W L : Nat) (ws : List Nat) :
    natSum ((List.range ws.length).map (fun i => floorShare amount W (ws.getD i 0) + if i < L then 1 else 0))
      = natSum (ws.map (floorShare amount W)) + Nat.min L ws.length := by sorry

theorem plan0_floor_sum_add_leftover (amount : Nat) (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws = amount ∧ leftover amount ws ≤ ws.length := by sorry

theorem plan0_weighted_range_sum (amount : Nat) (ws : List Nat) (hne : ws ≠ []) (hpos : ∀ w ∈ ws, 0 < w) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) = amount := by sorry
```