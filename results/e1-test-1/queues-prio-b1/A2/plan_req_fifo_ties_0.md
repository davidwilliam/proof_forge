**Proof plan.** Prove a one-step conservation law for each priority class: a rejected step contributes nothing and leaves the state unchanged, a valid insert contributes `classOf p [e]` and uses `ins_classOf_stable2`, and a valid pop moves the head entry to the outflow. Then distribute `classOf p` over the `inflow`/`outflow` of a cons-run using `classOf_append2` and the cons equations for `run`, `inflow`, and `outflow`. Finally induct on `ops`, generalizing the state, and combine the one-step law with the induction hypothesis by list-append associativity.

```lean
theorem plan0_step_classOf (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by sorry

theorem plan0_classOf_inflow_run_cons (s : State) (op : Op) (ops : List Op) (p : Nat) :
    classOf p (inflow (run step s (op :: ops)).1) =
      classOf p (inflowOf (op, (step s op).1)) ++
        classOf p (inflow (run step (step s op).2 ops).1) := by sorry

theorem plan0_classOf_outflow_run_cons (s : State) (op : Op) (ops : List Op) (p : Nat) :
    classOf p (outflow (run step s (op :: ops)).1) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (outflow (run step (step s op).2 ops).1) := by sorry

theorem plan0_fifo_ties_by_ind (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1) =
      classOf p (outflow (run step s ops).1) ++
        classOf p (run step s ops).2.items := by sorry
```