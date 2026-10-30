**Proof plan.** Decompose `setCompSpeedInternal` into its supply and borrow steps. Specify each step separately: its revert precondition, the resulting side equation, and preservation of the other side, block number, accounts, and reserve. Translate the borrow precondition and `accrueSide` arguments back through the supply step’s preservation facts, then combine the field equations into the record equality required by `SpeedsSet`.

```lean
theorem plan6_setSpeeds_decomp (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ s1, setSupplySpeed s a = some s1 ∧ setBorrowSpeed s1 b = some s' := by
  sorry

theorem plan6_supply_step_spec (s s1 : St) (a : Nat)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1.supplyState =
      (if s.supplyState.speed = a then s.supplyState
       else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) ∧
    s1.borrowState = s.borrowState ∧
    s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧
    s1.reserve = s.reserve := by
  sorry

theorem plan6_borrow_step_spec (s s' : St) (b : Nat)
    (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s'.borrowState =
      (if s.borrowState.speed = b then s.borrowState
       else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) ∧
    s'.supplyState = s.supplyState ∧
    s'.blockNumber = s.blockNumber ∧
    s'.accts = s.accts ∧
    s'.reserve = s.reserve := by
  sorry

theorem plan6_borrow_precond_of_steps (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1)
    (h2 : setBorrowSpeed s1 b = some s') :
    s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber := by
  sorry

theorem plan6_setSpeeds_state_eq_of_steps (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1)
    (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by
  sorry
```