Proof plan: Unpack a successful `allocate` call to get the shares as the range-map of bumped bases. For each index, the base excess is `-key` in the nonnegative case and `key` in the negative case, with `0 ≤ key < S`, so an unbumped share is already within one unit. A bumped share needs `key > 0`: this follows because `S * L` is the sum of all keys, each key is at most `S - 1` when positive, so `L` is below the number of positive keys, while a zero-key index has all positive-key indices ranked ahead of it. The lemmas below isolate the key/excess identity, the total-key identity, the positive-count/rank comparison, the sum bound, the resulting positivity of bumped keys, and the final pointwise excess bound.

```lean
theorem plan6_key_excess_base (amount : Int) (S : Nat) (r : Nat) (hS : 0 < S) :
    0 ≤ keyAt amount S r ∧ keyAt amount S r < (S : Int) ∧
    excess amount S (baseAt amount S r) r =
      if 0 ≤ amount then - keyAt amount S r else keyAt amount S r := by sorry

theorem plan6_sum_keys_general (amount : Int) (S : Nat) (ratios : List Nat) :
    (ratios.map (keyAt amount S)).sum =
      if 0 ≤ amount then
        amount * (ratios.sum : Int) - (S : Int) * (ratios.map (baseAt amount S)).sum
      else
        (S : Int) * (ratios.map (baseAt amount S)).sum - amount * (ratios.sum : Int) := by sorry

theorem plan6_count_pos_le_rankOf (keys : List Int) (n i : Nat)
    (hkey : keys.getD i 0 = 0) :
    ((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length ≤
      rankOf keys n i := by sorry

theorem plan6_sum_range_le_count_pos (keys : List Int) (n : Nat) (S : Int)
    (hS : 0 < S)
    (hkeys : ∀ j, j < n → 0 ≤ keys.getD j 0 ∧ keys.getD j 0 < S) :
    ((List.range n).map (fun j => keys.getD j 0)).sum ≤
      (S - 1) * (((List.range n).filter (fun j => decide (0 < keys.getD j 0))).length : Int) := by sorry

theorem plan6_key_pos_of_rank_lt_L (amount : Int) (ratios : List Nat) (i : Nat)
    (hS : 0 < ratios.sum) (hi : i < ratios.length)
    (hrank : rankOf (ratios.map (keyAt amount ratios.sum)) ratios.length i <
      (if 0 ≤ amount then
        (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat
       else
        ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat)) :
    0 < (ratios.map (keyAt amount ratios.sum)).getD i 0 := by sorry

theorem plan6_excess_share_of_allocate (amount : Int) (ratios : List Nat)
    (shares : List Int) (hS : 0 < ratios.sum) (hne : ratios ≠ [])
    (halloc : allocate amount ratios = some shares)
    (i : Nat) (hx : i < shares.length) (hr : i < ratios.length) :
    -(ratios.sum : Int) < excess amount ratios.sum shares[i] ratios[i] ∧
    excess amount ratios.sum shares[i] ratios[i] < (ratios.sum : Int) := by sorry
```