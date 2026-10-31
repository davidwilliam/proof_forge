If the entry is in bounds, `List.getD` returns that account, so `WellFormed` gives both index bounds. If it is out of bounds, `List.getD` returns `noAcct`, whose recorded indices are both `0`.

```lean
theorem plan7_getD_mem_or_default (l : List Acct) (who : Nat) :
    l.getD who noAcct ∈ l ∨ l.getD who noAcct = noAcct := by
  sorry

theorem plan7_wellformed_apply (L : Legacy) (a : Acct)
    (hWF : L.WellFormed) (ha : a ∈ L.accts) :
    a.supplierIndex ≤ L.supplyIndex ∧ a.borrowerIndex ≤ L.borrowIndex := by
  sorry

theorem plan7_noAcct_supplierIndex : noAcct.supplierIndex = 0 := rfl

theorem plan7_noAcct_borrowerIndex : noAcct.borrowerIndex = 0 := rfl

theorem plan6_acct_bounds (L : Legacy) (who : Account) (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  cases plan7_getD_mem_or_default L.accts who with
  | inl hmem =>
    exact plan7_wellformed_apply L (L.accts.getD who noAcct) hWF hmem
  | inr heq =>
    rw [heq]
    exact ⟨by rw [plan7_noAcct_supplierIndex]; exact Nat.zero_le _,
           by rw [plan7_noAcct_borrowerIndex]; exact Nat.zero_le _⟩
```