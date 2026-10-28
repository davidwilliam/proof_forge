**Proof plan.** Split the single step by operation. For an enqueue, either the guard fails; the step is `rejected` with the state unchanged and both flows empty; or it succeeds, in which case `plan0_contents_enqueue_update` gives `contents' = contents ++ [x]`, inflow `[x]` and outflow `[]`. For a dequeue, either the guard fails similarly, or it succeeds returning `s.buf s.head`; then the contents decompose as the head value followed by the tail contents, obtained by shifting slot indices with `dq_slot_shift2` pointwise over `List.range`. Case-splitting `op` and applying the two step lemmas proves `plan1_step_fifo`.

```lean
theorem plan2_range_map_shift (buf : Nat → Nat) (head cap n : Nat) :
    (List.range n).map (fun i => buf (((head + 1) % cap + i) % cap))
      = (List.range n).map (fun i => buf ((head + (i + 1)) % cap)) := by sorry

theorem plan2_contents_dequeue (s : State) (hcap : 0 < s.capacity)
    (hhead : s.head < s.capacity) (hpos : 0 < s.count) :
    contents s
      = s.buf s.head
        :: contents { s with head := (s.head + 1) % s.capacity, count := s.count - 1 } := by sorry

theorem plan2_step_enqueue_fifo (s : State) (x : Nat) :
    contents s ++ inflowOf (.enqueue x, (step s (.enqueue x)).1)
      = outflowOf (.enqueue x, (step s (.enqueue x)).1)
        ++ contents (step s (.enqueue x)).2 := by sorry

theorem plan2_step_dequeue_fifo (s : State) :
    contents s ++ inflowOf (.dequeue, (step s .dequeue).1)
      = outflowOf (.dequeue, (step s .dequeue).1)
        ++ contents (step s .dequeue).2 := by sorry
```