**Proof plan.** For a supply hook, destruct the `Option.bind` into an intermediate state after `updateCompSupplyIndex` and a final state after `distributeSupplierComp`. Rewrite the update as the specification’s `accrueSide`, rewrite the distribution using the candidate’s supplier-start expression, `accrualStart`, and `creditFor`, and use a congruence lemma for `List.modify` to identify the two account-update functions at the affected account. These facts assemble directly into `SupplyDistributed`.

```lean
theorem plan2_creditFor_eq (units start index : Nat) :
    creditFor units start index = mulDouble units (index - start) := by sorry

theorem plan2_accrualStart_eq (recorded index : Nat) :
    accrualStart recorded index =
      (if recorded = 0 ∧ compInitialIndex ≤ index then compInitialIndex else recorded) := by sorry

theorem plan2_modify_congr_getD (xs : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (xs.getD who noAcct) = g (xs.getD who noAcct)) :
    xs.modify who f = xs.modify who g := by sorry

theorem plan2_updateSupply_eq (s t : St)
    (h : updateCompSupplyIndex s = some t) :
    s.supplyState.block ≤ s.blockNumber ∧
      t = { s with
            supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by sorry

theorem plan2_distributeSupplier_eq (s : St) (who : Account) (u : St)
    (h : distributeSupplierComp s who = some u) :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
      u = { s with
            accts := s.accts.modify who fun a =>
              { a with
                supplierIndex := s.supplyState.index,
                accrued := a.accrued + creditFor a.supply
                  (accrualStart a.supplierIndex s.supplyState.index)
                  s.supplyState.index } } := by sorry

theorem plan2_supply_hook_effect (s : St) (who : Account) (t u : St)
    (ht : updateCompSupplyIndex s = some t)
    (hu : distributeSupplierComp t who = some u) :
    SupplyDistributed s who u := by sorry
```