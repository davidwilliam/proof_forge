**Proof plan.** First characterize each index update as exactly `accrueSide` (the `subChecked` success gives `block ≤ blockNumber`, and the arithmetic in `fraction` is the same ratio, with the zero-delta, zero-speed, and zero-total cases all collapsing to setting `block := now`). Then lift those characterizations through the two conditional speed setters, which either do nothing (speed unchanged) or accrue then overwrite `speed`. Finally, sequencing the supply setter before the borrow setter preserves the other side, the accounts (hence both totals), and `blockNumber`, so the borrow accrual computed after the supply step is the one `SpeedsSet` specifies on the original state, giving `SpeedsSet` for `setCompSpeedInternal` and hence for `comptroller (.setSpeeds a b)`.

```lean
theorem plan3_updateSupply_accrue (s : St) (t : St) :
    updateCompSupplyIndex s = some t →
    s.supplyState.block ≤ s.blockNumber ∧
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by sorry

theorem plan3_updateBorrow_accrue (s : St) (t : St) :
    updateCompBorrowIndex s = some t →
    s.borrowState.block ≤ s.blockNumber ∧
    t = { s with borrowState := accrueSide s.borrowState s.blockNumber (totalBorrows s) } := by sorry

theorem plan3_setSupplySpeed_spec (s : St) (a : Nat) (t : St) :
    setSupplySpeed s a = some t →
    (s.supplyState.speed ≠ a → s.supplyState.block ≤ s.blockNumber) ∧
    t = { s with supplyState := if s.supplyState.speed = a then s.supplyState
      else { accrueSide s.supplyState s.blockNumber (totalSupply s) with speed := a } } := by sorry

theorem plan3_setBorrowSpeed_spec (s : St) (b : Nat) (t : St) :
    setBorrowSpeed s b = some t →
    (s.borrowState.speed ≠ b → s.borrowState.block ≤ s.blockNumber) ∧
    t = { s with borrowState := if s.borrowState.speed = b then s.borrowState
      else { accrueSide s.borrowState s.blockNumber (totalBorrows s) with speed := b } } := by sorry

theorem plan3_setCompSpeedInternal_spec (s : St) (a b : Nat) (s' : St) :
    setCompSpeedInternal s a b = some s' → SpeedsSet s a b s' := by sorry
```