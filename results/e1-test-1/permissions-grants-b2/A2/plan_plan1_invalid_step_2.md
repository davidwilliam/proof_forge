Short proof plan: analyse a successful step by operation. First extract the Boolean guard that must hold for a successful grant and for a successful revoke. From those guards, together with membership from a successful step, reconstruct `ValidCommand` in each case, hence for every successful step. Finally, a step whose first component is not `.ok` must be the rejected no-op case by unfolding `step`; combining this with success-implies-valid proves that an invalid command is rejected unchanged.

```lean
theorem plan2_grant_ok_cond (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) :
    (isAdmin s r.actor && r.actor != r.target && !s.has r.target r.role) = true := by sorry

theorem plan2_revoke_ok_cond (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) :
    (isAdmin s r.actor && s.has r.target r.role &&
      (r.role != .admin || hasOtherAdmin s r.target)) = true := by sorry

theorem plan2_grant_ok_valid (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) : ValidCommand s r := by sorry

theorem plan2_revoke_ok_valid (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) : ValidCommand s r := by sorry

theorem plan2_ok_valid (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidCommand s r := by sorry

theorem plan2_not_ok_step (s : State) (r : Request)
    (h : (step s r).1 ≠ .ok) : step s r = (.rejected, s) := by sorry
```