Induction on `l`, generalizing `k`: split a cons into its head, whose index is `0`, and its tail, whose indices shift by `1`. The tail shift and the corresponding decomposition of `List.range (m + 1)` reduce the goal to the induction hypothesis at `k + 1`.

```lean
theorem plan1_indexOf?_cons_map : ∀ (x a : AccountId) (xs : List AccountId),
    a ≠ x → indexOf? (x :: xs) a = (indexOf? xs a).map (· + 1) := by sorry

theorem plan1_match_map_add : ∀ (o : Option Nat) (F : Nat → Int) (k : Nat),
    (match o.map (· + 1) with
      | some i => F (k + i)
      | none => 0) =
    (match o with
      | some i => F (k + 1 + i)
      | none => 0) := by sorry

theorem plan1_sumOver_tail_indexOf : ∀ (F : Nat → Int) (k : Nat) (x : AccountId)
    (xs : List AccountId), (x :: xs).Nodup →
    sumOver xs (fun a => match indexOf? (x :: xs) a with
      | some i => F (k + i)
      | none => 0) =
    sumOver xs (fun a => match indexOf? xs a with
      | some i => F (k + 1 + i)
      | none => 0) := by sorry

theorem plan1_sumOver_range_succ_shift : ∀ (F : Nat → Int) (k m : Nat),
    F k + sumOver (List.range m) (fun i => F (k + 1 + i)) =
      sumOver (List.range (m + 1)) (fun i => F (k + i)) := by sorry
```