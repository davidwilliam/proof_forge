Short proof plan: split `CallsSucceed` on the call. Consistency gives both side blocks are not ahead of `blockNumber` and every recorded account index is either absent (`0`) or bounded by the corresponding market index. The two update operations therefore always succeed, do not change accounts or the other side, and never decrease their own index. The two distribute operations then succeed because the account start index is bounded by the current market index. A claim is the sequential composition of the borrow update/distribution and supply update/distribution, with the borrower distribution preserving the supplier index; speed changes are conditional applications of the same always-succeeding updates.

```lean
theorem plan0_consistent_acct_bounds (s : St) (who : Account) (h : Consistent s) :
    ((s.acct who).supplierIndex = 0 ∨ (s.acct who).supplierIndex ≤ s.supplyState.index) ∧
      ((s.acct who).borrowerIndex = 0 ∨ (s.acct who).borrowerIndex ≤ s.borrowState.index) := by
  sorry

theorem plan0_updateSupply_exists (s : St) (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' ∧
      s.supplyState.index ≤ s'.supplyState.index ∧
      s'.accts = s.accts ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  sorry

theorem plan0_updateBorrow_exists (s : St) (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' ∧
      s.borrowState.index ≤ s'.borrowState.index ∧
      s'.accts = s.accts ∧ s'.supplyState = s.supplyState ∧
      s'.blockNumber = s.blockNumber := by
  sorry

theorem plan0_distributeSupplier_exists (s : St) (who : Account)
    (h : (s.acct who).supplierIndex = 0 ∨
      (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' ∧
      s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  sorry

theorem plan0_distributeBorrower_exists (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' ∧
      (s'.acct who).supplierIndex = (s.acct who).supplierIndex ∧
      s'.supplyState = s.supplyState ∧ s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber := by
  sorry
```