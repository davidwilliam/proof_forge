(1) Proof plan:

- Split `Consistent s` into both block bounds and, for the named account, both recorded-index bounds.
- Show the two `distribute*Comp` calls succeed whenever the relevant recorded index is below the current market index; the effective starting index is either the recorded index, `compInitialIndex` in the initialized case, or `0`.
- Characterize successful index updates: accounts and the opposite side are unchanged, the updated index does not decrease, and the updated side’s block is no later than the current block.
- Prove the supply hook directly from the supply update and supplier distribution; prove the borrow hook symmetrically.
- For a claim, run the borrow update and distribution, preserve the supplier information across the account-only borrower update, then run the supply update and distribution. `grantCompInternal` is total, so the claim succeeds.
- For speed changes, each branch is either unchanged or applies a successful index update, using the consistent block bounds.
- Finally, case-split on the four calls and combine these facts.

(2)

```lean
theorem plan0_acct_indices_le_of_consistent (s : St) (who : Account)
    (h : Consistent s) :
    (s.acct who).supplierIndex ≤ s.supplyState.index ∧
      (s.acct who).borrowerIndex ≤ s.borrowState.index := by
  sorry

theorem plan0_distributeSupplierComp_isSome_of_le (s : St) (who : Account)
    (h : (s.acct who).supplierIndex ≤ s.supplyState.index) :
    (distributeSupplierComp s who).isSome := by
  sorry

theorem plan0_distributeBorrowerComp_isSome_of_le (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (distributeBorrowerComp s who).isSome := by
  sorry

theorem plan0_updateSupply_shape (s s' : St)
    (hupd : updateCompSupplyIndex s = some s') :
    s'.accts = s.accts ∧
      s'.borrowState = s.borrowState ∧
      s'.blockNumber = s.blockNumber ∧
      s.supplyState.index ≤ s'.supplyState.index ∧
      s'.supplyState.block ≤ s'.blockNumber := by
  sorry

theorem plan0_updateBorrow_shape (s s' : St)
    (hupd : updateCompBorrowIndex s = some s') :
    s'.accts = s.accts ∧
      s'.supplyState = s.supplyState ∧
      s'.blockNumber = s.blockNumber ∧
      s.borrowState.index ≤ s'.borrowState.index ∧
      s'.borrowState.block ≤ s'.blockNumber := by
  sorry

theorem plan0_withAcct_supplierIndex (s : St) (who : Account)
    (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex =
        (s.acct who).supplierIndex ∧
      (s.withAcct who f).supplyState = s.supplyState ∧
      (s.withAcct who f).blockNumber = s.blockNumber := by
  sorry
```