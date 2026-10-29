**Proof plan:** Show that lengths are preserved at each stage of the construction: `chooseIter` only updates entries of its boolean mask via `List.set`, so the mask keeps its length; starting from `List.replicate rems.length false`, the chosen mask therefore has the same length as `rems`, hence as `ratios`. The floors list is a `map` over `ratios`, so `zipWith` of floors and mask has length `ratios.length`. Finally, `allocate` returns either these shares or their negations via `map`, neither of which changes length, which gives `OneShareEach`.

```lean
theorem plan0_chooseIter_length (rems : List Nat) (mask : List Bool) (k : Nat) :
    (chooseIter rems mask k).length = mask.length := by sorry

theorem plan0_choose_length (rems : List Nat) (k : Nat) :
    (choose rems k).length = rems.length := by sorry

theorem plan0_allocateNonneg_length (A : Nat) (ratios : List Nat) (S : Nat) :
    (allocateNonneg A ratios S).length = ratios.length := by sorry

theorem plan0_length_of_allocate_some (amount : Int) (ratios : List Nat) (shares : List Int)
    (h : allocate amount ratios = some shares) :
    shares.length = ratios.length := by sorry

theorem plan0_one_share_each : OneShareEach allocate := by sorry
```