(1) Proof plan: From non-rejection of `step s (.enqueue x)`, extract `0 < s.capacity` and `s.count < s.capacity` exactly as in `req_enqueue_effects`, and rewrite the resulting state to the explicit buffer update at `slot s s.count`. The contents then split at `List.range (s.count + 1)` into the old range plus the last slot. Earlier slots are unchanged because, for `i < s.count`, the slot `(head + i) % capacity` differs from `(head + count) % capacity`: their difference is a positive amount smaller than `capacity`, so taking the remainder cannot return the earlier slot. A pointwise range-map congruence rewrites all earlier values to the original buffer values, while the final value is `x`, yielding `contents s ++ [x]`.

(2)
```lean
theorem plan0_range_map_succ (n : Nat) (f : Nat → Nat) :
    (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by sorry

theorem plan0_mod_add_ne (r d cap : Nat) (hr : r < cap) (hd : 0 < d) (hdc : d < cap) :
    (r + d) % cap ≠ r := by sorry

theorem plan0_slot_tail_eq (head i count cap : Nat) (h : i ≤ count) :
    (head + count) % cap = ((head + i) % cap + (count - i)) % cap := by sorry

theorem plan0_slot_ne_of_lt (head i count cap : Nat) (hcap : 0 < cap)
    (hi : i < count) (hcount : count < cap) :
    (head + i) % cap ≠ (head + count) % cap := by sorry

theorem plan0_map_range_eq_of_forall_lt (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by sorry

theorem plan0_contents_enqueue_update (s : State) (x : Nat)
    (hcap : 0 < s.capacity) (hcount : s.count < s.capacity) :
    contents { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 } = contents s ++ [x] := by sorry
```