Split on the sign of `amount`. For nonnegative amounts, the bases are floor shares and exactly `L = amount - bases.sum` indices are bumped by `+1`, where `L ≤ length`. For nonpositive amounts the symmetric statement holds with `-1`. The bumped indices are those whose `rankOf`; an injective ranking of the keys into `range n`; is below `L`, so exactly `L` entries are bumped. A general “sum of a list bumped at a Boolean predicate” lemma then rewrites the total as `bases.sum ± L = amount`.

```lean
theorem plan0_baseAt_bounds (amount : Int) (S r : Nat) (hS : 0 < S) :
    -(S : Int) < amount * (r : Int) - baseAt amount S r * (S : Int) ∧
    amount * (r : Int) - baseAt amount S r * (S : Int) < (S : Int) ∧
    (0 ≤ amount → 0 ≤ amount * (r : Int) - baseAt amount S r * (S : Int)) ∧
    (amount ≤ 0 → amount * (r : Int) - baseAt amount S r * (S : Int) ≤ 0) := by sorry

theorem plan0_bases_diff_bounds (amount : Int) (ratios : List Nat) (hS : 0 < ratios.sum) :
    (0 ≤ amount →
      ((amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat : Int) =
        amount - (ratios.map (baseAt amount ratios.sum)).sum ∧
      (amount - (ratios.map (baseAt amount ratios.sum)).sum).toNat ≤ ratios.length) ∧
    (amount ≤ 0 →
      (((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat : Int) =
        (ratios.map (baseAt amount ratios.sum)).sum - amount ∧
      ((ratios.map (baseAt amount ratios.sum)).sum - amount).toNat ≤ ratios.length) := by sorry

theorem plan0_rankOf_lt (keys : List Int) (n i : Nat) (hi : i < n) :
    rankOf keys n i < n := by sorry

theorem plan0_rankOf_inj (keys : List Int) (n i j : Nat) (hi : i < n) (hj : j < n)
    (h : rankOf keys n i = rankOf keys n j) : i = j := by sorry

theorem plan0_count_rankOf_lt (keys : List Int) (n L : Nat) (hL : L ≤ n) :
    ((List.range n).filter (fun i => decide (rankOf keys n i < L))).length = L := by sorry

theorem plan0_sum_range_bump (bs : List Int) (p : Nat → Bool) (e : Int)
    (he : e = 1 ∨ e = -1) :
    ((List.range bs.length).map (fun i => bs.getD i 0 + if p i then e else 0)).sum =
      bs.sum + e * (((List.range bs.length).filter p).length : Int) := by sorry
```