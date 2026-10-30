Short proof plan: `Consistent` supplies the two block inequalities needed for the index updates and the recorded-index inequalities needed for distribution. Updates succeed, do not change accounts or the block number, and do not decrease their market index, so distribution after an update succeeds. Repeating this reasoning through borrow distribution, supply update, and supply distribution proves claims; speed changes are either no-ops or successful updates. Case analysis on the call then gives `CallsSucceed`.

```lean
theorem plan0_updateSupply_spec (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ m, updateCompSupplyIndex s = some m ∧ m.accts = s.accts ∧
      m.blockNumber = s.blockNumber ∧ m.borrowState = s.borrowState ∧
      s.supplyState.index ≤ m.supplyState.index := by sorry

theorem plan0_updateBorrow_spec (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ m, updateCompBorrowIndex s = some m ∧ m.accts = s.accts ∧
      m.blockNumber = s.blockNumber ∧ m.supplyState = s.supplyState ∧
      s.borrowState.index ≤ m.borrowState.index := by sorry

theorem plan0_distributeSupplier_isSome (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome = true := by sorry

theorem plan0_distributeBorrower_isSome (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome = true := by sorry

theorem plan0_claimComp_isSome (s : St) (who : Account)
    (h : Consistent s) :
    (claimComp s who).isSome = true := by sorry

theorem plan0_setCompSpeedInternal_isSome (s : St) (a b : Nat)
    (hs : s.supplyState.block ≤ s.blockNumber)
    (hb : s.borrowState.block ≤ s.blockNumber) :
    (setCompSpeedInternal s a b).isSome = true := by sorry
```