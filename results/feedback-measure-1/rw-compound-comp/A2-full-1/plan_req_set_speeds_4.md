**Proof plan.** Unfold `comptroller` on `.setSpeeds` to expose `setCompSpeedInternal` as a bind of `setSupplySpeed` followed by `setBorrowSpeed`, extracting the intermediate state `mid`. Apply the existing single-side specifications `setSupply_mid_spec4` and `setBorrow_mid_spec4` to the two steps. The supply step touches only `supplyState`, so `mid` agrees with `s` on `borrowState`, `blockNumber`, accounts, and both totals; rewriting the borrow-step specification along these equalities turns it into a statement about `s`, and collapsing the two nested record updates yields exactly the final state in `SpeedsSet`. Composing the two block-preconditions gives both implications required by `SpeedsSet`.

```lean
theorem plan4_setSpeeds_extract (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ mid, setSupplySpeed s a = some mid ∧ setBorrowSpeed mid b = some s' := by sorry

theorem plan4_supply_mid_invariants (s mid : St) (sup : Nat)
    (hmid : mid = { s with supplyState := if s.supplyState.speed = sup then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } }) :
    mid.borrowState = s.borrowState ∧ mid.blockNumber = s.blockNumber ∧
    mid.accts = s.accts ∧ totalBorrows mid = totalBorrows s ∧
    totalSupply mid = totalSupply s := by sorry

theorem plan4_compose_speedsSet (s mid s' : St) (a b : Nat)
    (hsup : (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
      mid = { s with supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hbor : (mid.borrowState.speed ≠ b → mid.borrowState.block ≤ mid.blockNumber) ∧
      s' = { mid with borrowState := if mid.borrowState.speed = b then mid.borrowState
        else { accrueSide mid.borrowState mid.blockNumber (totalBorrows mid) with speed := b } }) :
    SpeedsSet s a b s' := by sorry

theorem plan4_setSpeeds_effects : SetSpeedsEffects comptroller := by sorry
```