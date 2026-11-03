(1) Proof plan: Split `CallsSucceed` by the call. `Consistent` supplies both side-block bounds and every recorded account index bound. An update succeeds whenever its side block is not ahead of the current block, and `accrueSide` never lowers an index. After such an update, the account is unchanged and its recorded index is therefore still bounded by the updated index, so supplier/borrower distribution cannot fail in `subChecked`: the checked start is either the recorded index, `0`, or `compInitialIndex` under the guard `compInitialIndex ≤ index`. A claim is the borrow step followed by the supply step followed by the always-defined grant; speed setting is, on each side, either `some s` or the `Option.map` of a successful update, with the supply update leaving the borrow side and block number unchanged via the explicit `accrueSide` form. The lemmas below isolate exactly the account-bound extraction, index monotonicity, and the two update/distribute success facts needed for this case split.

(2)
```lean
theorem plan0_consistent_acct_indices (s : St) (who : Account) (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
    (s.acct who).borrowerIndex ≤ s.borrowState.index := by sorry

theorem plan0_accrueSide_index_ge (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index := by sorry

theorem plan0_updateSupply_some (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    ∃ s', updateCompSupplyIndex s = some s' := by sorry

theorem plan0_updateBorrow_some (s : St)
    (h : s.borrowState.block ≤ s.blockNumber) :
    ∃ s', updateCompBorrowIndex s = some s' := by sorry

theorem plan0_distributeSupplier_some (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    ∃ s', distributeSupplierComp s who = some s' := by sorry

theorem plan0_distributeBorrower_some (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    ∃ s', distributeBorrowerComp s who = some s' := by sorry
```