**Proof plan.** Prove the target by induction on `l`, generalizing `offset`. For the head of `x :: xs`, `indexOf?` returns `some 0`. For elements of the tail, nodup gives `x ∉ xs`, so their indices in `x :: xs` are exactly their indices in `xs` shifted by `1`; this is transferred through `sumOver` by congruence. Finally, split `List.range (xs.length + 1)` into its first element and the shifted remaining range, then apply the induction hypothesis with `offset + 1`.

```lean
theorem plan2_indexOf_cons_self (x : Nat) (xs : List Nat) :
    indexOf? (x :: xs) x = some 0 := by sorry

theorem plan2_indexOf_cons_ne (x a : Nat) (xs : List Nat) (h : x ≠ a) :
    indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by sorry

theorem plan2_match_map_add_one (o : Option Nat) (g : Nat → Int) :
    (match o.map (· + 1) with
     | some i => g i
     | none => (0 : Int))
      =
    (match o with
     | some i => g (i + 1)
     | none => (0 : Int)) := by sorry

theorem plan2_sumOver_tail_index_shift (x : Nat) (xs : List Nat)
    (amount n offset : Nat) (h : x ∉ xs) :
    sumOver xs (fun a => match indexOf? (x :: xs) a with
      | some i => (fairShare amount n (offset + i) : Int)
      | none => 0)
      =
    sumOver xs (fun a => match indexOf? xs a with
      | some i => (fairShare amount n ((offset + 1) + i) : Int)
      | none => 0) := by sorry

theorem plan2_range_sum_shift (f : Nat → Int) (m : Nat) :
    sumOver (List.range (m + 1)) f
      = f 0 + sumOver (List.range m) (fun i => f (i + 1)) := by sorry
```