Short proof plan: first isolate the checked-subtraction success for the adjusted borrower start index. Then prove that `List.modify`/`getD` and hence `St.withAcct` preserve `supplierIndex` when the update function does, and transport that preservation through `distributeBorrowerComp`. The main proof can then unfold the distributor, rewrite the subtraction using the start bound, use the resulting `withAcct` state, and discharge the remaining state fields by `rfl`.

```lean
theorem plan1_subChecked_of_le (a b : Nat) (h : b ≤ a) :
    subChecked a b = some (a - b) := by sorry

theorem plan1_borrower_adjusted_le (s : St) (who : Account)
    (h : (s.acct who).borrowerIndex = 0 ∨
      (s.acct who).borrowerIndex ≤ s.borrowState.index) :
    (if (s.acct who).borrowerIndex = 0 ∧ compInitialIndex ≤ s.borrowState.index
      then compInitialIndex else (s.acct who).borrowerIndex) ≤ s.borrowState.index := by sorry

theorem plan1_modify_getD_supplierIndex (l : List Acct) (n : Nat) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((l.modify n f).getD n noAcct).supplierIndex = (l.getD n noAcct).supplierIndex := by sorry

theorem plan1_withAcct_supplierIndex (s : St) (who : Account) (f : Acct → Acct)
    (hf : ∀ a, (f a).supplierIndex = a.supplierIndex) :
    ((s.withAcct who f).acct who).supplierIndex = (s.acct who).supplierIndex := by sorry

theorem plan1_distributeBorrower_supplierIndex (s : St) (who : Account) (s' : St)
    (h : distributeBorrowerComp s who = some s') :
    (s'.acct who).supplierIndex = (s.acct who).supplierIndex := by sorry
```