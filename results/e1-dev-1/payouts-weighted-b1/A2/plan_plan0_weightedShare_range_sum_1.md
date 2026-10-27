(1) **Proof plan.** Split each `weightedShare` term into its floor share plus its indicator for the first `leftover` positions. Sum the floor parts over `List.range ws.length` by reindexing them as `ws.map (floorShare …)`, and sum the indicators to `leftover amount ws` (using `leftover ≤ ws.length` from the existing `plan0_leftover_add_floor`). The total is then exactly `floorSum + leftover = amount` by that same lemma.

(2)

```lean
theorem plan1_natSum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    natSum (l.map (fun a => f a + g a)) = natSum (l.map f) + natSum (l.map g) := by
  sorry

theorem plan1_natSum_range_indicator (k n : Nat) (hkn : k ≤ n) :
    natSum ((List.range n).map (fun i => if i < k then 1 else 0)) = k := by
  sorry

theorem plan1_map_range_getD_cons (x : Nat) (xs : List Nat) (f : Nat → Nat) :
    (List.range (x :: xs).length).map (fun i => f ((x :: xs).getD i 0)) =
      f x :: (List.range xs.length).map (fun i => f (xs.getD i 0)) := by
  sorry

theorem plan1_natSum_range_getD (ws : List Nat) (f : Nat → Nat) :
    natSum ((List.range ws.length).map (fun i => f (ws.getD i 0))) =
      natSum (ws.map f) := by
  sorry

theorem plan1_weightedShare_range_decomp (amount : Nat) (ws : List Nat)
    (hlo : leftover amount ws ≤ ws.length) :
    natSum ((List.range ws.length).map (weightedShare amount ws)) =
      natSum (ws.map (floorShare amount (natSum ws))) + leftover amount ws := by
  sorry
```