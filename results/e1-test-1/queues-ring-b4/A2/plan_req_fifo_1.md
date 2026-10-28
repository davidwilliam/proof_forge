Proof plan: Prove conservation for one step by splitting on whether the operation is rejected. A rejected operation contributes no inflow or outflow and leaves the state unchanged; a successful enqueue uses `req_enqueue_contents`, while a successful dequeue uses `req_dequeue_contents`. Then decompose `run` on `op :: ops`, rewrite `inflow`/`outflow` of the head entry, combine the one-step equation with the induction hypothesis using list-append associativity, and finish by induction on the operation list generalizing the state.

```lean
theorem plan1_inflowOf_rejected (op : Op) : inflowOf (op, .rejected) = [] := by sorry

theorem plan1_outflowOf_rejected (op : Op) : outflowOf (op, .rejected) = [] := by sorry

theorem plan1_step_fifo (s : State) (op : Op) :
    contents s ++ inflowOf (op, (step s op).1)
      = outflowOf (op, (step s op).1) ++ contents (step s op).2 := by sorry

theorem plan1_fifo_cons (s : State) (op : Op) (ops : List Op)
    (ih : contents (step s op).2 ++ inflow (run step (step s op).2 ops).1
          = outflow (run step (step s op).2 ops).1
            ++ contents (run step (step s op).2 ops).2) :
    contents s ++ inflow (run step s (op :: ops)).1
      = outflow (run step s (op :: ops)).1
        ++ contents (run step s (op :: ops)).2 := by sorry

theorem plan1_fifo_all (ops : List Op) (s : State) :
    contents s ++ inflow (run step s ops).1
      = outflow (run step s ops).1 ++ contents (run step s ops).2 := by sorry
```