**Proof plan:** Split a hypothetical successful step by `r.op`. In the grant case, extract membership, admin, self-target, and absent-role facts from the Boolean guards; in the revoke case, additionally convert `hasOtherAdmin` back to `OtherAdmin`. Hence success implies `ValidCommand`, so an invalid command cannot succeed. Since every non-`ok` branch of `step` returns `(.rejected, s)`, invalid commands are no-ops.

```lean
theorem plan1_grant_ok_valid (s : State) (r : Request) (hop : r.op = .grant)
    (h : (step s r).1 = .ok) : ValidCommand s r := by sorry

theorem plan1_revoke_ok_valid (s : State) (r : Request) (hop : r.op = .revoke)
    (h : (step s r).1 = .ok) : ValidCommand s r := by sorry

theorem plan1_ok_valid (s : State) (r : Request)
    (h : (step s r).1 = .ok) : ValidCommand s r := by sorry

theorem plan1_step_eq_of_not_ok (s : State) (r : Request)
    (h : (step s r).1 ≠ .ok) : step s r = (.rejected, s) := by sorry

theorem plan1_invalid_step (s : State) (r : Request)
    (h : ¬ ValidCommand s r) : step s r = (.rejected, s) := by sorry
```