Short proof plan: characterize `accrualStart` as the implementation's effective supplier index, prove that `List.modify` only depends on the function value at the modified account, and use those facts to rewrite a successful `distributeSupplierComp` call into the specification's exact `creditFor` form. Combine this with the existing characterization of `updateCompSupplyIndex` in terms of `accrueSide`; success of the subsequent distribution also supplies the required `accrualStart ≤ index` inequality. The resulting supply-hook characterization is exactly `SupplyDistributed`.

```lean
theorem plan2_accrualStart_eq_effective (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) := by
  sorry

theorem plan2_modify_ext_getD (l : List Acct) (n : Nat) (f g : Acct → Acct)
    (h : f (l.getD n noAcct) = g (l.getD n noAcct)) :
    l.modify n f = l.modify n g := by
  sorry

theorem plan2_accrualStart_le_of_distributeSupplierComp_some
    (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index := by
  sorry

theorem plan2_distributeSupplierComp_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
      s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with
        accts := s.accts.modify who fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex s.supplyState.index)
              s.supplyState.index } } := by
  sorry

theorem plan2_supplyHook_eq (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    s.supplyState.block ≤ s.blockNumber ∧
    accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ∧
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex :=
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  sorry
```