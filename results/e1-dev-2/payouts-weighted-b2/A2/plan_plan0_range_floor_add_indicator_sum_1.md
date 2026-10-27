**Proof plan:** Split the sum over the range into a floor-share part and a one-cent indicator part. Prove the floor-share range sum equals the floor-share sum over `ws` by shifting a `range (n+1)` map to expose the head element, prove additivity of `natSum` over pointwise-added maps, and evaluate the indicator range sum to `Nat.min L ws.length` by induction using the append formula for `natSum`. Combining these rewrites gives the target equality.

```lean
theorem plan1_range_succ_map_shift (n : Nat) (g : Nat → Nat) :
    (List.range (n + 1)).map g = g 0 :: (List.range n).map (fun i => g (i + 1)) := by sorry

theorem plan1_range_getD_map (ws : List Nat) (f : Nat → Nat) :
    (List.range ws.length).map (fun i => f (ws.getD i 0)) = ws.map f := by sorry

theorem plan1_natSum_map_add (l : List Nat) (f g : Nat → Nat) :
    natSum (l.map (fun i => f i + g i)) = natSum (l.map f) + natSum (l.map g) := by sorry

theorem plan1_natSum_append (l1 l2 : List Nat) :
    natSum (l1 ++ l2) = natSum l1 + natSum l2 := by sorry

theorem plan1_natSum_range_indicator (n L : Nat) :
    natSum ((List.range n).map (fun i => if i < L then 1 else 0)) = Nat.min L n := by sorry
```