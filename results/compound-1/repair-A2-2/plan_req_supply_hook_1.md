**Proof plan.** Decompose the supply hook into its two steps. First show `updateCompSupplyIndex` is exactly the specification's `accrueSide` update once it does not revert. Then show `distributeSupplierComp` cannot succeed unless the account's `accrualStart` is below the (updated) index, and that when it does succeed it rewrites the account list exactly as `SupplyDistributed` requires (the supplier start computed by the candidate is `accrualStart`, and `mulDouble` on the index difference is `creditFor`). Substituting the first equality into the second and into the success bound gives all three conjuncts of `SupplyDistributed` directly.

```lean
theorem plan1_accrualStart_eq_if (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by sorry

theorem plan1_updateCompSupplyIndex_eq (s : St)
    (h : s.supplyState.block ≤ s.blockNumber) :
    updateCompSupplyIndex s =
      some { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by sorry

theorem plan1_distributeSupplierComp_le (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index := by sorry

theorem plan1_distributeSupplierComp_eq (s : St) (who : Account)
    (h : accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index) :
    distributeSupplierComp s who =
      some { s with accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := s.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex s.supplyState.index) s.supplyState.index } } := by sorry
```