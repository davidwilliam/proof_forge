Short proof plan: For `CallsSucceed`, split on the call. Consistency gives each account’s recorded index is below the corresponding market index, even for accounts obtained via `getD`. The update functions are therefore successful and only increase their side’s index while preserving accounts, the block number, and the other side. Hence the subsequent distribution can succeed by the existing `subChecked` lemmas. For claims, borrower distribution must additionally preserve the supplier index and supply state so the following supply distribution can succeed. For speed changes, each update preserves the other side’s block condition.

```lean
theorem plan0_getD_supplier_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.supplierIndex ≤ idx) :
    (l.getD who noAcct).supplierIndex ≤ idx := by sorry

theorem plan0_getD_borrower_le (l : List Acct) (who idx : Nat)
    (h : ∀ a ∈ l, a.borrowerIndex ≤ idx) :
    (l.getD who noAcct).borrowerIndex ≤ idx := by sorry

theorem plan0_updateSupplyIndex_props (s s' : St)
    (hblock : s.supplyState.block ≤ s.blockNumber)
    (h : updateCompSupplyIndex s = some s') :
    s.supplyState.index ≤ s'.supplyState.index ∧
    s'.accts = s.accts ∧
    s'.blockNumber = s.blockNumber ∧
    s'.borrowState = s.borrowState := by sorry

theorem plan0_updateBorrowIndex_props (s s' : St)
    (hblock : s.borrowState.block ≤ s.blockNumber)
    (h : updateCompBorrowIndex s = some s') :
    s.borrowState.index ≤ s'.borrowState.index ∧
    s'.accts = s.accts ∧
    s'.blockNumber = s.blockNumber ∧
    s'.supplyState = s.supplyState := by sorry

theorem plan0_getD_modify_supplierIndex (l : List Acct) (n : Nat)
    (f : Acct → Acct) (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD n noAcct).supplierIndex =
      (l.getD n noAcct).supplierIndex := by sorry

theorem plan0_distributeBorrowerComp_preserves (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    s'.supplyState = s.supplyState ∧
    s'.blockNumber = s.blockNumber ∧
    (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by sorry
```