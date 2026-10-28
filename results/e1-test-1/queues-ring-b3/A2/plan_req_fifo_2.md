**Proof plan.** Prove a one-step FIFO identity separately for enqueue and dequeue: if the step is rejected, use `req_valid_succeeds` contrapositively with `req_invalid_noop` to get no inflow, outflow, or contents change; if it succeeds, use `req_enqueue_contents` or `req_dequeue_contents`. Combine the cases into a single-step lemma, extend it across the head operation of `run` using associativity of list append, and finish by induction on the operation list.

```lean
theorem plan2_enqueue_step_fifo : ∀ (s : State) (x : Nat),
    contents s ++ inflowOf (.enqueue x, (step s (.enqueue x)).1)
      = outflowOf (.enqueue x, (step s (.enqueue x)).1)
        ++ contents (step s (.enqueue x)).2 := by sorry

theorem plan2_dequeue_step_fifo : ∀ (s : State),
    contents s ++ inflowOf (.dequeue, (step s .dequeue).1)
      = outflowOf (.dequeue, (step s .dequeue).1)
        ++ contents (step s .dequeue).2 := by sorry

theorem plan2_step_fifo : ∀ (s : State) (op : Op),
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by sorry

theorem plan2_fifo_cons_step : ∀ (s : State) (op : Op) (ops : List Op),
    (∀ (t : State), contents t ++ inflow (run step t ops).1
      = outflow (run step t ops).1 ++ contents (run step t ops).2) →
    contents s ++ inflow (run step s (op :: ops)).1
      = outflow (run step s (op :: ops)).1
        ++ contents (run step s (op :: ops)).2 := by sorry

theorem plan2_fifo_run : ∀ (ops : List Op) (s : State),
    contents s ++ inflow (run step s ops).1
      = outflow (run step s ops).1 ++ contents (run step s ops).2 := by sorry
```