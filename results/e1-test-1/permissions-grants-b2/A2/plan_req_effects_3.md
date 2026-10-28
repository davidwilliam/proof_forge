Short proof plan: For `Effects`, the user list is already unchanged by `step_users_eq_all3`, so the main work is the `has` function. Split on `r.op`: in the grant case, both the successful step branch and `expectedHas` reduce to the same conditional `if u == r.target && q == r.role then true else s.has u q`; in the revoke case they both reduce to the same conditional with `false`. Proving these two reductions separately for `expectedHas` and for a successful `step`, then combining them by cases on `r.op`, makes `req_effects` a direct pairing of `step_users_eq_all3` with the combined `has` equation.

```lean
theorem plan3_expected_grant (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .grant) :
    expectedHas s r u q = (if u == r.target && q == r.role then true else s.has u q) := by sorry

theorem plan3_expected_revoke (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .revoke) :
    expectedHas s r u q = (if u == r.target && q == r.role then false else s.has u q) := by sorry

theorem plan3_grant_step_has (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .grant) (h : (step s r).1 = .ok) :
    (step s r).2.has u q = (if u == r.target && q == r.role then true else s.has u q) := by sorry

theorem plan3_revoke_step_has (s : State) (r : Request) (u : UserId) (q : Role)
    (hop : r.op = .revoke) (h : (step s r).1 = .ok) :
    (step s r).2.has u q = (if u == r.target && q == r.role then false else s.has u q) := by sorry

theorem plan3_step_has_expected (s : State) (r : Request)
    (h : (step s r).1 = .ok) (u : UserId) (q : Role) :
    (step s r).2.has u q = expectedHas s r u q := by sorry
```