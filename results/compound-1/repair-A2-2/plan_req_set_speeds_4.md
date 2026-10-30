Short proof plan: split `_setCompSpeeds` into its supply and borrow phases. For each phase, prove (a) when the speed actually changes, success forces the old side's block to be at or before the current block, because the underlying index update must not underflow, and (b) the whole resulting state is exactly the original state with only that side replaced by either itself, if the speed is unchanged, or by `accrueSide` at the old speed with the new speed installed. The supply phase preserves the borrow side, block number, reserves, accounts, and hence `totalBorrows`, and symmetrically for the borrow phase; composing the two state equations therefore gives the two-field update and both block conditions in `SpeedsSet`, after which `req_set_speeds` is just unfolding `comptroller` to `setCompSpeedInternal`.

```lean
theorem plan4_setSupplySpeed_block (s : St) (sup : Nat) (sI : St)
    (h : setSupplySpeed s sup = some sI) (hne : s.supplyState.speed ≠ sup) :
    s.supplyState.block ≤ s.blockNumber := by sorry

theorem plan4_setBorrowSpeed_block (s : St) (bor : Nat) (s' : St)
    (h : setBorrowSpeed s bor = some s') (hne : s.borrowState.speed ≠ bor) :
    s.borrowState.block ≤ s.blockNumber := by sorry

theorem plan4_setSupplySpeed_state (s : St) (sup : Nat) (sI : St)
    (h : setSupplySpeed s sup = some sI) :
    sI = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by sorry

theorem plan4_setBorrowSpeed_state (s : St) (bor : Nat) (s' : St)
    (h : setBorrowSpeed s bor = some s') :
    s' = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by sorry

theorem plan4_setCompSpeedInternal_speedsSet (s : St) (sup bor : Nat) (s' : St)
    (h : setCompSpeedInternal s sup bor = some s') :
    SpeedsSet s sup bor s' := by sorry
```