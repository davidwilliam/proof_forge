**Proof plan:** Show that an invalid operation is exactly the rejected no-op step. Then the rejected outcome contributes no inflow and no outflow, and filtering an empty list is empty, reducing the class equation to `classOf p s.items = classOf p s.items`.

```lean
theorem plan2_step_rejected_eq (s : State) (op : Op) (h : ¬ Valid s op) :
    step s op = (.rejected, s) := by sorry

theorem plan2_inflowOf_rejected (op : Op) :
    inflowOf (op, .rejected) = ([] : List Entry) := by sorry

theorem plan2_outflowOf_rejected (op : Op) :
    outflowOf (op, .rejected) = ([] : List Entry) := by sorry

theorem plan2_classOf_nil_eq (p : Nat) :
    classOf p ([] : List Entry) = ([] : List Entry) := by sorry

theorem plan2_step_class_of_invalid (s : State) (op : Op) (p : Nat)
    (h : ¬ Valid s op) :
    classOf p s.items ++ classOf p (inflowOf (op, (step s op).1)) =
      classOf p (outflowOf (op, (step s op).1)) ++
        classOf p (step s op).2.items := by sorry
```