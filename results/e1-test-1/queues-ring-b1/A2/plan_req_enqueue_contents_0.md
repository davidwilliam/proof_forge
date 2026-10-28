If enqueue is not rejected, its guard must hold, so `count < capacity` and the new buffer only differs at `slot s s.count`. Expand `contents` at `count+1` via `range (n+1)`, show all earlier slots are distinct from the tail slot (so their values are unchanged), and note the final term is exactly `x`.

```lean
theorem plan0_range_succ_map (f : Nat → Nat) (n : Nat) :
    (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by sorry

theorem plan0_mod_ne_of_lt_add (a b cap : Nat) (h1 : a < b) (h2 : b < a + cap) :
    a % cap ≠ b % cap := by sorry

theorem plan0_slot_ne_of_lt (s : State) (i : Nat)
    (hcount : s.count < s.capacity) (hi : i < s.count) :
    slot s i ≠ slot s s.count := by sorry

theorem plan0_map_range_ext (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by sorry

theorem plan0_contents_enqueue_update (s : State) (x : Nat)
    (hcount : s.count < s.capacity) :
    contents { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 } = contents s ++ [x] := by sorry
```