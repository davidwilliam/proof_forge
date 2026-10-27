Short proof plan: prove the identity by induction on the duplicate-free list. For the head element, `indexOf?` gives `0`; for elements of the tail, membership gives an index in the tail, and consing shifts that index by one. This rewrites `sumOver` over `x :: xs` as the `k`-th share plus the corresponding sum over `xs` starting at `k + 1`. Separately decompose `List.range (n + 1)` into its head and shifted tail, cast the resulting natural addition to `Int`, and apply the induction hypothesis.

```lean
theorem plan2_indexOf_exists_of_mem (l : List Nat) (a : Nat) (h : a ∈ l) :
    ∃ i, indexOf? l a = some i := by sorry

theorem plan2_indexOf_cons_getD (x : Nat) (xs : List Nat) (a : Nat)
    (hne : x ≠ a) (hmem : a ∈ xs) :
    (indexOf? (x :: xs) a).getD 0 = (indexOf? xs a).getD 0 + 1 := by sorry

theorem plan2_sumOver_cons_indexOf (x : Nat) (xs : List Nat)
    (amount : Nat) (ws : List Nat) (k : Nat) (hl : (x :: xs).Nodup) :
    sumOver (x :: xs)
        (fun a => (weightedShare amount ws (k + (indexOf? (x :: xs) a).getD 0) : Int)) =
      (weightedShare amount ws k : Int) +
        sumOver xs
          (fun a => (weightedShare amount ws ((k + 1) + (indexOf? xs a).getD 0) : Int)) := by sorry

theorem plan2_natSum_range_succ (f : Nat → Nat) (n k : Nat) :
    natSum ((List.range (n + 1)).map (fun i => f (k + i))) =
      f k + natSum ((List.range n).map (fun i => f ((k + 1) + i))) := by sorry
```