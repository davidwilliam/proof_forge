**Proof plan.** Prove per-priority conservation for a single step, split according to whether the operation is an invalid operation, a valid insert, or a valid pop. The invalid case uses `req_invalid_noop`; the insert case rewrites the step with the inserted list and uses the existing fact that `classOf p (ins e l) = classOf p l ++ classOf p [e]` for sorted `l`; the pop case uses that a valid queue is a cons and that `classOf` splits over a cons. Combining these gives a uniform one-step conservation equation. The full `FifoTies` statement then follows by induction on the operation list, generalizing the state, unfolding `run` at a cons, splitting `inflow`/`outflow`/`classOf` over appends, and rewriting with the one-step equation and the induction hypothesis using associativity of list append.

```lean
theorem plan1_step_class_invalid (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by sorry

theorem plan1_step_class_insert (s : State) (e : Entry) (p : Nat)
    (hV : Valid s (.insert e)) :
    classOf p s.items ++
        classOf p (inflowOf (.insert e, (step s (.insert e)).1)) =
      classOf p (outflowOf (.insert e, (step s (.insert e)).1)) ++
        classOf p (step s (.insert e)).2.items := by sorry

theorem plan1_step_class_pop (s : State) (p : Nat)
    (hV : Valid s .pop) :
    classOf p s.items ++ classOf p (inflowOf (.pop, (step s .pop).1)) =
      classOf p (outflowOf (.pop, (step s .pop).1)) ++
        classOf p (step s .pop).2.items := by sorry

theorem plan1_step_class (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by sorry

theorem plan1_run_class (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1) =
      classOf p (outflow (run step s ops).1) ++
        classOf p (run step s ops).2.items := by sorry
```