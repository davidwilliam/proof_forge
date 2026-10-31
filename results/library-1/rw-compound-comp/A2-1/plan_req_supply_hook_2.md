**Proof plan.** Decompose the supply hook into `updateCompSupplyIndex` followed by `distributeSupplierComp`. First identify the implementation's adjusted supplier index with `accrualStart`. Then show that a successful supply-index update is exactly `accrueSide` applied to the original state, preserving accounts and total supply. Next characterize a successful supplier distribution as updating that account's index to the current index and adding the corresponding `creditFor` amount. Finally, compose these two characterizations, rewriting the intermediate state's index, account, and total supply back to the original state's `accrueSide` values to obtain `SupplyDistributed`.

```lean
theorem plan2_accrualStart_adjusted (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by
  sorry

theorem plan2_updateSupply_accrueSide (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  sorry

theorem plan2_distributeSupplier_char (mid : St) (who : Account) (s' : St)
    (h : distributeSupplierComp mid who = some s') :
    accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤
        mid.supplyState.index ∧
      s' = { mid with
        accts := mid.accts.modify who fun a =>
          { a with
            supplierIndex := mid.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex mid.supplyState.index)
              mid.supplyState.index } } := by
  sorry

theorem plan2_supplyDistributed_of_steps (s : St) (who : Account) (mid s' : St)
    (hup : updateCompSupplyIndex s = some mid)
    (hdist : distributeSupplierComp mid who = some s') :
    SupplyDistributed s who s' := by
  sorry
```