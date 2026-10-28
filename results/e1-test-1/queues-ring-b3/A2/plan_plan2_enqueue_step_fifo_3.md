Split the enqueue step by whether its outcome is `.rejected`. In the rejected case the step is a no-op and both flows are empty, so both sides reduce to `contents s`. In the accepted case the outcome is `.ok`, the inflow is `[x]`, the outflow is empty, and the stored contents gain exactly `x` at the end, so both sides reduce to `contents s ++ [x]`.

```lean
theorem plan3_enq_rejected_state : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 = .rejected →
    (step s (.enqueue x)).2 = s := by sorry

theorem plan3_enq_rejected_flows : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 = .rejected →
    inflowOf (.enqueue x, (step s (.enqueue x)).1) = [] ∧
    outflowOf (.enqueue x, (step s (.enqueue x)).1) = [] := by sorry

theorem plan3_enq_accepted_flows : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    (step s (.enqueue x)).1 = .ok ∧
    inflowOf (.enqueue x, (step s (.enqueue x)).1) = [x] ∧
    outflowOf (.enqueue x, (step s (.enqueue x)).1) = [] := by sorry

theorem plan3_enq_accepted_contents : ∀ (s : State) (x : Nat),
    (step s (.enqueue x)).1 ≠ .rejected →
    contents (step s (.enqueue x)).2 = contents s ++ [x] := by sorry
```