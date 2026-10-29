Short proof plan: First isolate the sign facts for the nonnegative allocation: every entry is nonnegative, and for absolute value `0` every entry must actually be `0` by conservation plus the existing sum-of-nonnegatives lemma. Then handle the two branches of `allocate` separately. In the nonnegative branch, the only overlapping case for the opposite sign condition is `amount = 0`, where entries are `0`. In the negative branch, shares are negations of nonnegative shares. Finally, `req_sign` unfolds `allocate`, discharges the impossible `none` case, splits on `0 ≤ amount`, and applies the corresponding branch lemma.

```lean
theorem plan8_mem_map_neg_le_zero (l : List Int) (x : Int)
    (hx : x ∈ l.map (fun y => -y)) (hnn : ∀ y ∈ l, 0 ≤ y) :
    x ≤ 0 := by sorry

theorem plan8_allocateNonneg_zero_mem_eq_zero (ratios : List Nat) (x : Int)
    (hS : 0 < ratios.sum) (hx : x ∈ allocateNonneg 0 ratios ratios.sum) :
    x = 0 := by sorry

theorem plan8_signOn_of_allocateNonneg (amount : Int) (ratios : List Nat)
    (shares : List Int) (hS : 0 < ratios.sum) (hamt : 0 ≤ amount)
    (hshares : shares = allocateNonneg amount.natAbs ratios ratios.sum) :
    SignOn amount shares := by sorry

theorem plan8_signOn_of_allocateNonneg_map_neg (amount : Int) (ratios : List Nat)
    (shares : List Int) (hamt : amount < 0)
    (hshares : shares =
      (allocateNonneg amount.natAbs ratios ratios.sum).map (fun x => -x)) :
    SignOn amount shares := by sorry
```