(1) Proof plan: Split the summand into the base share and the bump. First handle the shifted `getD` on a cons list, then show summing `getD` over `List.range bs.length` recovers `bs.sum` by induction on `bs` using the successor decomposition of `range`. Separately, prove additivity of sums over a range by induction on the range length, and compute a constant-if sum as `e` times the filtered count by induction using `range_succ`/`filter_append`. The target then follows by rewriting its map as a sum of these two maps and applying the three computation lemmas; the hypothesis `e = 1 ∨ e = -1` is not needed.

(2)
```lean
theorem plan5_getD_cons_succ (a : Int) (tl : List Int) (i : Nat) :
    (a :: tl).getD (i + 1) 0 = tl.getD i 0 := by sorry

theorem plan5_sum_range_getD (bs : List Int) :
    ((List.range bs.length).map (fun i => bs.getD i 0)).sum = bs.sum := by sorry

theorem plan5_sum_map_add_range (n : Nat) (f g : Nat → Int) :
    ((List.range n).map (fun i => f i + g i)).sum =
      ((List.range n).map f).sum + ((List.range n).map g).sum := by sorry

theorem plan5_sum_range_ite_eq_mul_filter_length (n : Nat) (p : Nat → Bool) (e : Int) :
    ((List.range n).map (fun i => if p i then e else 0)).sum =
      e * (((List.range n).filter p).length : Int) := by sorry
```