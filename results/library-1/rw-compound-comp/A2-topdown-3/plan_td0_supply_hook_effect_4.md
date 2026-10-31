The supply hook first updates the supply index, then distributes supplier rewards. The missing reasoning is to identify the implementation's conditional supplier start with `accrualStart`, convert `mulDouble` on the account at `who` into the specification's `creditFor` expression under `List.modify`, characterize `distributeSupplierComp`, and transport that characterization across the index-update state.

```lean
theorem plan4_modify_congr_at (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by sorry

theorem plan4_supplier_start_eq (recorded index : Nat) :
    (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) =
      accrualStart recorded index := by sorry

theorem plan4_distributeSupplierComp_spec (s : St) (who : Account) (s' : St) :
    distributeSupplierComp s who = some s' →
      accrualStart (s.acct who).supplierIndex s.supplyState.index ≤
          s.supplyState.index ∧
        s' = s.withAcct who fun a =>
          { a with
            supplierIndex := s.supplyState.index,
            accrued := a.accrued + creditFor a.supply
              (accrualStart a.supplierIndex s.supplyState.index)
              s.supplyState.index } := by sorry

theorem plan4_supplyHook_decomp (s : St) (who : Account) (s' : St) :
    comptroller s (.supplyHook who) = some s' →
      ∃ t, updateCompSupplyIndex s = some t ∧
        distributeSupplierComp t who = some s' := by sorry

theorem plan4_supplyDistributed_of_steps (s : St) (who : Account) (t s' : St) :
    s.supplyState.block ≤ s.blockNumber →
      t = { s with
        supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } →
        distributeSupplierComp t who = some s' →
          SupplyDistributed s who s' := by sorry
```