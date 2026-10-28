Short proof plan: Unfold `ValidCommand` to obtain membership, admin status, and the grant/revoke side conditions. Convert these propositional facts into the Boolean tests used by `step`: list membership becomes `contains`, membership plus admin status becomes `isAdmin`, `OtherAdmin` becomes `hasOtherAdmin`, inequality becomes `bne`, and the missing/held role becomes the corresponding Boolean test. Then case-split on `r.op`, rewrite the outer membership guard in `step` to false, and rewrite each branch guard to true, so both branches return `.ok`.

```lean
theorem plan0_valid_contains (s : State) (r : Request) (h : ValidCommand s r) :
    (s.users.contains r.actor && s.users.contains r.target) = true := by sorry

theorem plan0_valid_isAdmin (s : State) (r : Request) (h : ValidCommand s r) :
    isAdmin s r.actor = true := by sorry

theorem plan0_hasOtherAdmin_of_otherAdmin (s : State) (u : UserId)
    (h : OtherAdmin s u) : hasOtherAdmin s u = true := by sorry

theorem plan0_valid_grant_extra (s : State) (r : Request) (h : ValidCommand s r)
    (hop : r.op = .grant) :
    (r.actor != r.target && !s.has r.target r.role) = true := by sorry

theorem plan0_valid_revoke_extra (s : State) (r : Request) (h : ValidCommand s r)
    (hop : r.op = .revoke) :
    (s.has r.target r.role && (r.role != .admin || hasOtherAdmin s r.target)) = true := by sorry
```