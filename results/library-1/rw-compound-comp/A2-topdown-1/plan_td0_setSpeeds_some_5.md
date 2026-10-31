(1) Proof plan: First show both index-update functions succeed whenever the relevant side's block is not ahead of the current block, by unfolding `subChecked` and splitting the update branches. Also show a supply-index update preserves `blockNumber` and `borrowState`. Lift these facts through `setSupplySpeed` (success and preservation) and through `setBorrowSpeed` (success). For `setSpeeds`, obtain the intermediate state from the supply step, use preservation to keep the borrow-block hypothesis, then apply borrow-step success in the `Option.bind` defining `setCompSpeedInternal`.

(2)
```lean
theorem plan5_updateSupply_some (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (updateCompSupplyIndex s).isSome = true := by sorry

theorem plan5_updateBorrow_some (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (updateCompBorrowIndex s).isSome = true := by sorry

theorem plan5_updateSupply_preserve (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    t.blockNumber = s.blockNumber ∧ t.borrowState = s.borrowState := by sorry

theorem plan5_setSupply_some (s : St) (a : Nat)
    (h : s.supplyState.block ≤ s.blockNumber) :
    (setSupplySpeed s a).isSome = true := by sorry

theorem plan5_setSupply_preserve (s : St) (a : Nat) (mid : St)
    (h : setSupplySpeed s a = some mid) :
    mid.blockNumber = s.blockNumber ∧ mid.borrowState = s.borrowState := by sorry

theorem plan5_setBorrow_some (s : St) (b : Nat)
    (h : s.borrowState.block ≤ s.blockNumber) :
    (setBorrowSpeed s b).isSome = true := by sorry
```