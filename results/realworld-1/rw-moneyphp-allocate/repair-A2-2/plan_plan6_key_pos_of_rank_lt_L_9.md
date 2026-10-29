(1) Proof plan: Assume the key at `i` is not positive. The key bounds give that it must be `0`. Then the number of positive keys is at most `rankOf keys n i`, hence strictly below `L`. The sum of all keys is at most `(S-1)` times that positive-key count, by the pointwise bound `key < S`. But the sum of keys also equals `S * L`, via the sum-of-keys identity, the factorisation `S * (x-y)`, and the `toNat` cast for `L`. This contradicts the arithmetic fact that `S * L ≤ (S-1) * C` is impossible when `0 < S` and `0 ≤ C < L`.

(2)
```lean
theorem plan9_key_bounds_getD (amount : Int) (ratios : List Nat) (i : Nat)
    (hS : 0 < ratios.sum) (hi : i < ratios.length) :
    0 ≤ (ratios.map (keyAt amount ratios.sum)).getD i 0 ∧
    (ratios.map (keyAt amount ratios.sum)).getD i 0 < (ratios.sum : Int) := by sorry

theorem plan9_count_pos_lt_of_key_zero (keys : List Int) (n i L : Nat)
    (h0 : keys.getD i 0 = 0) (hr : rankOf keys n i < L) :
    ((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length < L := by sorry

theorem plan9_keys_sum_le_count_pos (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (keyAt amount ratios.sum)).sum ≤
      ((ratios.sum : Int) - 1) *
        (((List.range ratios.length).filter
          (fun j => decide (0 < (ratios.map (keyAt amount ratios.sum)).getD j 0))).length : Int) := by sorry

theorem plan9_mul_sub_factor (S x y : Int) :
    S * (x - y) = x * S - S * y := by sorry

theorem plan9_Lnat_cast (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (((if 0 ≤ amount then
        (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
       else
        ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat) : Nat) : Int) =
      (if 0 ≤ amount then
        amount - (ratios.map (baseAt amount ratios.sum)).sum
       else
        (ratios.map (baseAt amount ratios.sum)).sum - amount) := by sorry

theorem plan9_keys_sum_eq_mul_Lnat (amount : Int) (ratios : List Nat)
    (hS : 0 < ratios.sum) :
    (ratios.map (keyAt amount ratios.sum)).sum =
      (ratios.sum : Int) *
        (((if 0 ≤ amount then
            (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
           else
            ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat) : Nat) : Int) := by sorry
```