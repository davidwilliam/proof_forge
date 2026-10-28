(1) Separate the one-step class-preservation equation by validity and operation. For a pop, the head is removed, so its class list splits as a singleton followed by the tail's class list. For a valid insert, sorted insertion preserves each priority class except for appending the new entry's singleton class at the end, which matches FIFO order among equal priorities. Invalid operations are rejected with no inflow, outflow, or state change. A final case split combines these facts.

(2)
```lean
theorem plan1_classOf_cons_singleton (p : Nat) (e : Entry) (l : List Entry) :
    classOf p (e :: l) = classOf p [e] ++ classOf p l := by sorry

theorem plan1_classOf_ins_sorted (p : Nat) (e : Entry) (l : List Entry)
    (h : Sorted l) :
    classOf p (ins e l) = classOf p l ++ classOf p [e] := by sorry

theorem plan1_step_classOf_not_valid (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by sorry

theorem plan1_step_classOf_insert_valid (s : State) (e : Entry) (p : Nat)
    (h : Valid s (Op.insert e)) :
    classOf p s.items ++ classOf p (inflowOf (Op.insert e, (step s (Op.insert e)).1))
      = classOf p (outflowOf (Op.insert e, (step s (Op.insert e)).1))
        ++ classOf p (step s (Op.insert e)).2.items := by sorry

theorem plan1_step_classOf_pop_valid (s : State) (p : Nat)
    (h : Valid s Op.pop) :
    classOf p s.items ++ classOf p (inflowOf (Op.pop, (step s Op.pop).1))
      = classOf p (outflowOf (Op.pop, (step s Op.pop).1))
        ++ classOf p (step s Op.pop).2.items := by sorry

theorem plan1_step_classOf (s : State) (op : Op) (p : Nat) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1))
      = classOf p (outflowOf (op, (step s op).1)) ++ classOf p (step s op).2.items := by sorry
```