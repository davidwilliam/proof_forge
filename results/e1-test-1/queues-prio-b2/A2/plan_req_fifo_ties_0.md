(1) Proof plan: Prove a per-priority, single-step conservation law: a successful stable insert appends the inserted entry to its priority class, a successful pop removes the head entry from its class, and invalid operations change nothing. Then induct on the operation list, rewriting `classOf` over appends and reassociating lists to combine the invariant for the first step with the invariant for the remaining run.

(2)
```lean
theorem plan0_classOf_append (p : Nat) (l₁ l₂ : List Entry) :
    classOf p (l₁ ++ l₂) = classOf p l₁ ++ classOf p l₂ := by sorry

theorem plan0_classOf_cons_singleton (p : Nat) (e : Entry) (l : List Entry) :
    classOf p (e :: l) = classOf p [e] ++ classOf p l := by sorry

theorem plan0_classOf_ins_sorted (p : Nat) (e : Entry) (l : List Entry) (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by sorry

theorem plan0_step_classOf (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by sorry

theorem plan0_run_classOf (ops : List Op) (s : State) (p : Nat) :
    classOf p s.items ++ classOf p (inflow (run step s ops).1)
      = classOf p (outflow (run step s ops).1) ++ classOf p (run step s ops).2.items := by sorry
```