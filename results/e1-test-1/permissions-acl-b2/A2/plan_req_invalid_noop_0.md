**Proof plan:** To prove `InvalidNoop`, show the Boolean guard in `step` characterizes `ValidQuery`: guard `= true` implies membership and `r.user ≠ 0`, hence the guard must be `false` when the query is invalid. With the guard false, unfolding `step` immediately yields `(.rejected, s)`, and chaining these facts gives the requirement by a direct application.

```lean
theorem plan0_cond_true_imp_valid (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = true) : ValidQuery s r := by sorry

theorem plan0_cond_false_of_not_valid (s : State) (r : Request)
    (h : ¬ ValidQuery s r) : (s.users.contains r.user && r.user != 0) = false := by sorry

theorem plan0_step_rejected_of_cond_false (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = false) : step s r = (.rejected, s) := by sorry

theorem plan0_step_rejected_of_not_valid (s : State) (r : Request)
    (h : ¬ ValidQuery s r) : step s r = (.rejected, s) := by sorry
```