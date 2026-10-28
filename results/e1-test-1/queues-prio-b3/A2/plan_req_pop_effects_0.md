**Proof plan:** A non-rejected pop must be valid, so its sorted stored list is nonempty and can be written as a head entry followed by its tail. The implementation then returns that head and leaves the tail, with capacity unchanged. Taking `l₁ = []`, `e` as the head, and `l₂` as the tail gives the required decomposition; sortedness supplies that the head's priority is at most every priority in the tail.

```lean
theorem plan0_valid_pop_exists_cons (s : State) (hV : Valid s .pop) :
    ∃ x xs, s.items = x :: xs ∧ Sorted (x :: xs) := by sorry

theorem plan0_sorted_head_le (x : Entry) (xs : List Entry)
    (hS : Sorted (x :: xs)) :
    ∀ y ∈ xs, x.prio ≤ y.prio := by sorry

theorem plan0_step_pop_eq_of_valid_cons (s : State) (x : Entry) (xs : List Entry)
    (hV : Valid s .pop) (hItems : s.items = x :: xs) :
    step s .pop = (.got x, { s with items := xs }) := by sorry

theorem plan0_valid_pop_of_not_rejected (s : State)
    (hNe : (step s .pop).1 ≠ .rejected) :
    Valid s .pop := by sorry

theorem plan0_pop_effects_of_head (s : State) (e : Entry) (xs : List Entry)
    (hItems : s.items = e :: xs)
    (hCap : (step s .pop).2.capacity = s.capacity)
    (hGot : (step s .pop).1 = .got e)
    (hTail : (step s .pop).2.items = xs)
    (hLe : ∀ y ∈ xs, e.prio ≤ y.prio) :
    (step s .pop).2.capacity = s.capacity ∧
      ∃ l₁ e' l₂, s.items = l₁ ++ e' :: l₂ ∧
        (step s .pop).1 = .got e' ∧
        (step s .pop).2.items = l₁ ++ l₂ ∧
        (∀ x ∈ l₁, e'.prio < x.prio) ∧
        (∀ x ∈ l₂, e'.prio ≤ x.prio) := by sorry
```