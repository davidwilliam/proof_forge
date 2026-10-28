(1) Proof plan: From non-rejection of an enqueue, extract the capacity/head/count conditions and rewrite `step` to its successful branch. Its tail slot is `slot s s.count`. For indices before `count`, that slot differs from the tail slot, so the updated buffer agrees with the old buffer on all previously stored positions. Expanding `contents` at `count + 1` therefore gives the old contents followed by the newly written value `x`.

(2)
```lean
theorem plan0_mod_eq_of_lt_two : ∀ (a cap : Nat), 0 < cap → a < cap + cap →
    a % cap = if a < cap then a else a - cap := by sorry

theorem plan0_add_mod_ne_of_lt : ∀ (cap head i j : Nat), head < cap → i < j → j < cap →
    (head + i) % cap ≠ (head + j) % cap := by sorry

theorem plan0_map_range_ext_lt : ∀ (f g : Nat → Nat) (n : Nat),
    (∀ i : Nat, i < n → f i = g i) →
    (List.range n).map f = (List.range n).map g := by sorry

theorem plan0_contents_enqueue_state : ∀ (s : State) (x : Nat),
    0 < s.capacity → s.head < s.capacity → s.count < s.capacity →
    contents ({ s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 }) = contents s ++ [x] := by sorry

theorem plan0_step_enqueue_of_not_rejected : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    0 < s.capacity ∧ s.head < s.capacity ∧ s.count < s.capacity ∧
    step s (.enqueue x) = (.ok, { s with
      buf := fun i => if i = slot s s.count then x else s.buf i,
      count := s.count + 1 }) := by sorry
```