Short proof plan: decompose the `setSpeeds` bind into a supply-speed step followed by a borrow-speed step. Characterize the intermediate state from the supply step, recording that it preserves the borrow side, accounts, and block number. Translate the borrow-step characterization back to the original state using those equalities, then combine the two nested state updates into the single update required by `SpeedsSet`.

```lean
theorem plan5_setSpeeds_decomp (s : St) (a b : Nat) (s' : St)
    (h : comptroller s (.setSpeeds a b) = some s') :
    ∃ m, setSupplySpeed s a = some m ∧ setBorrowSpeed m b = some s' := by sorry

theorem plan5_supply_form (s : St) (a : Nat) (m : St)
    (h : setSupplySpeed s a = some m) :
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } ∧
    m.borrowState = s.borrowState ∧
    m.accts = s.accts ∧
    m.blockNumber = s.blockNumber := by sorry

theorem plan5_borrow_form_translated (s : St) (b : Nat) (m s' : St)
    (hmBorrow : m.borrowState = s.borrowState)
    (hmAccts : m.accts = s.accts)
    (hmBlock : m.blockNumber = s.blockNumber)
    (h : setBorrowSpeed m b = some s') :
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by sorry

theorem plan5_combine_updates (s : St) (a b : Nat) (m s' : St)
    (hm : m = { s with supplyState :=
      if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } })
    (hs' : s' = { m with borrowState :=
      if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } }) :
    s' = { s with
      supplyState :=
        if s.supplyState.speed = a then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a },
      borrowState :=
        if s.borrowState.speed = b then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by sorry

theorem plan5_speedsSet_of_steps (s : St) (a b : Nat) (m s' : St)
    (hSup : setSupplySpeed s a = some m)
    (hBor : setBorrowSpeed m b = some s') :
    SpeedsSet s a b s' := by sorry
```