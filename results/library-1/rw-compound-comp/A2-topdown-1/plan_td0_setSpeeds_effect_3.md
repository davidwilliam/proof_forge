Short proof plan: First characterize each index-update operation as exactly `accrueSide`, independently of whether the delta, speed, or total is zero. From that, characterize each one-sided speed setter: it either leaves its side unchanged or replaces it by the accrued side with the new speed, and success in the changing case forces the side's block to be no later than the current block. Finally, compose the supply and borrow setters; the supply step does not affect the borrow side, block number, accounts, or total borrows, so the borrow characterization transfers back to the original state, yielding `SpeedsSet`.

```lean
theorem plan3_updateSupplyIndex_accrue (s : St) (t : St)
    (h : updateCompSupplyIndex s = some t) :
    t = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by sorry

theorem plan3_updateBorrowIndex_accrue (s : St) (t : St)
    (h : updateCompBorrowIndex s = some t) :
    t = { s with
      borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan3_setSupplySpeed_spec (s : St) (sup : Nat) (t : St)
    (h : setSupplySpeed s sup = some t) :
    (s.supplyState.speed ≠ sup → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with
      supplyState := if s.supplyState.speed = sup then s.supplyState
        else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := sup } } := by sorry

theorem plan3_setBorrowSpeed_spec (s : St) (bor : Nat) (t : St)
    (h : setBorrowSpeed s bor = some t) :
    (s.borrowState.speed ≠ bor → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with
      borrowState := if s.borrowState.speed = bor then s.borrowState
        else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := bor } } := by sorry

theorem plan3_setCompSpeedInternal_spec (s : St) (a b : Nat) (t : St)
    (h : setCompSpeedInternal s a b = some t) :
    SpeedsSet s a b t := by sorry
```