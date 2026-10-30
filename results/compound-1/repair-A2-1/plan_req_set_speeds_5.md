Short plan: decompose `setCompSpeedInternal` into its supply-then-borrow steps, characterize each step using the existing `setSup_cases`/`setBor_cases` and preservation lemmas, rewrite the borrow accrual from the intermediate state back to the original state (accounts, block number, and borrow side are unchanged by the supply step), then combine the two characterizations into the record equality and block inequalities required by `SpeedsSet`.

```lean
theorem plan5_setSupplySpeed_spec (s s1 : St) (a : Nat)
    (h : setSupplySpeed s a = some s1) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    s1.supplyState = (if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a }) ∧
    s1.borrowState = s.borrowState ∧ s1.blockNumber = s.blockNumber ∧
    s1.accts = s.accts ∧ s1.reserve = s.reserve := by sorry

theorem plan5_setBorrowSpeed_spec (s s' : St) (b : Nat)
    (h : setBorrowSpeed s b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s'.borrowState = (if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b }) ∧
    s'.supplyState = s.supplyState ∧ s'.blockNumber = s.blockNumber ∧
    s'.accts = s.accts ∧ s'.reserve = s.reserve := by sorry

theorem plan5_setSpeeds_decomp (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ s1, setSupplySpeed s a = some s1 ∧ setBorrowSpeed s1 b = some s' := by sorry

theorem plan5_setSpeeds_state_eq (s s1 s' : St) (a b : Nat)
    (h1 : setSupplySpeed s a = some s1) (h2 : setBorrowSpeed s1 b = some s') :
    s' = { s with
      supplyState := if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState := if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by sorry

theorem plan5_setSpeeds_effect (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    SpeedsSet s a b s' := by sorry
```