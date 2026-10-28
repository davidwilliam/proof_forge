**Proof plan.** A valid query gives `r.user ∈ s.users` and `r.user ≠ 0`. Convert these facts to the Boolean guard used by `step`: membership gives `contains = true`, and nonzeroness gives the Boolean inequality test. With the guard true, `step` takes its answered branch and returns either `.granted` or `.denied` according to `decision`, never `.rejected`.

```lean
theorem plan0_contains_true_of_mem (users : List UserId) (u : UserId)
    (h : u ∈ users) : users.contains u = true := by sorry

theorem plan0_bne_true_of_ne (u : UserId) (h : u ≠ 0) :
    (u != 0) = true := by sorry

theorem plan0_valid_guard_true (s : State) (r : Request)
    (h : ValidQuery s r) :
    (s.users.contains r.user && r.user != 0) = true := by sorry

theorem plan0_step_fst_granted_or_denied (s : State) (r : Request)
    (h : (s.users.contains r.user && r.user != 0) = true) :
    (step s r).1 = .granted ∨ (step s r).1 = .denied := by sorry

theorem plan0_valid_answered_step : ValidAnswered step := by sorry
```