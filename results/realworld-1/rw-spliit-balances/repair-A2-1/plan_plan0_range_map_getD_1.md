Prove by induction on the list. For a cons list, decompose `range (length + 1)` into `0` followed by successor indices, use `getD` at `0` for the head, cancel the successor against `getD` on a cons for the tail, and then apply the induction hypothesis.

```lean
theorem plan1_getD_cons_zero (a : Nat) (l : List Nat) (d : Nat) :
    (a :: l).getD 0 d = a := by sorry

theorem plan1_getD_cons_succ (a : Nat) (l : List Nat) (i d : Nat) :
    (a :: l).getD (i + 1) d = l.getD i d := by sorry

theorem plan1_range_succ_cons_map_succ (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) := by sorry

theorem plan1_map_range_getD_cons_succ (f : Nat → Nat) (a : Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f ((a :: l).getD (i + 1) 0))
      = (List.range l.length).map (fun i => f (l.getD i 0)) := by sorry

theorem plan1_range_map_getD (f : Nat → Nat) (l : List Nat) :
    (List.range l.length).map (fun i => f (l.getD i 0)) = l.map f := by sorry
```