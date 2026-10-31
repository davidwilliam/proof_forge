**Proof plan.** Unfold the supply hook as an `Option.bind` of `updateCompSupplyIndex` followed by `distributeSupplierComp`. First identify the inline supplier start in `distributeSupplierComp` with `accrualStart`. Next, characterize `updateCompSupplyIndex` as replacing the supply side by `accrueSide` and leaving accounts unchanged, and characterize `distributeSupplierComp` as crediting exactly `creditFor` from `accrualStart` while recording the current index. Finally, compose these two characterizations: the intermediate account record is the original one, the intermediate index is the accrued index, and `s.withAcct` on the intermediate state is exactly the record update required by `SupplyDistributed`.

```lean
theorem plan4_accrualStart_eq (recorded index : Nat) :
    (if recorded = 0 ∧ index ≥ compInitialIndex then compInitialIndex else recorded) =
      accrualStart recorded index := by sorry

theorem plan4_updateCompSupplyIndex_spec (s s1 : St)
    (h : updateCompSupplyIndex s = some s1) :
    s.supplyState.block ≤ s.blockNumber ∧
    s1 = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } ∧
    s1.accts = s.accts := by sorry

theorem plan4_distributeSupplierComp_spec (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
        s.supplyState.index ∧
    s' = s.withAcct who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s.supplyState.index)
          s.supplyState.index } := by sorry

theorem plan4_supplyDistributed_of_steps (s s1 s' : St) (who : Account)
    (hU : updateCompSupplyIndex s = some s1)
    (hD : distributeSupplierComp s1 who = some s') :
    SupplyDistributed s who s' := by sorry
```