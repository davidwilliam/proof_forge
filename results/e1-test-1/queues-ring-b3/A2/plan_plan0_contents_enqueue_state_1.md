**Proof plan:** Expand `contents` of the updated state using `List.range_succ`: the last entry is at `slot s s.count`, so it becomes `x`, while earlier entries use the updated buffer at old slots. For an earlier index `i < s.count`, `(head + i) % capacity` differs from `(head + s.count) % capacity`; prove this by writing any `a % cap` with `a < cap + cap` as either `a` or `a - cap`, then finishing by arithmetic. Hence the update is invisible at old slots, and a range-map congruence lemma identifies the prefix with `contents s`.

```lean
theorem plan1_map_range_ext_lt : ∀ (f g : Nat → Nat) (n : Nat),
    (∀ i : Nat, i < n → f i = g i) →
    (List.range n).map f = (List.range n).map g := by sorry

theorem plan1_mod_eq_if_lt_two : ∀ (a cap : Nat), 0 < cap → a < cap + cap →
    a % cap = if a < cap then a else a - cap := by sorry

theorem plan1_add_mod_ne_of_lt : ∀ (cap head i j : Nat),
    head < cap → i < j → j < cap →
    (head + i) % cap ≠ (head + j) % cap := by sorry

theorem plan1_buf_update_at_slot_of_lt : ∀ (s : State) (x i : Nat),
    s.head < s.capacity → i < s.count → s.count < s.capacity →
    (fun k => if k = slot s s.count then x else s.buf k) (slot s i)
      = s.buf (slot s i) := by sorry

theorem plan1_contents_enqueue_expand : ∀ (s : State) (x : Nat),
    contents { s with
      buf := fun k => if k = slot s s.count then x else s.buf k,
      count := s.count + 1 }
    = (List.range s.count).map
        (fun i => (fun k => if k = slot s s.count then x else s.buf k) (slot s i))
      ++ [x] := by sorry
```