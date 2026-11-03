Short proof plan: extract the intermediate state from the `Option.bind` in the supply hook, characterize the supply-index update as `accrueSide` using the existing update lemma, and characterize distribution using the existing supplier-distribution lemma. The remaining difficulty is only rewriting projections and nested structure updates after substituting the intermediate state; the following projection, nested-update, and unfolding lemmas make that final rewriting a routine `simp`/`exact` step.

```lean
theorem plan2_update_supply_acct (s : St) (who : Account) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).acct who =
      s.acct who := by
  sorry

theorem plan2_update_supply_index (s : St) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).supplyState.index =
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
  sorry

theorem plan2_update_supply_accts (s : St) :
    ({ s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } : St).accts =
      s.accts := by
  sorry

theorem plan2_nested_supply_accts_update (s : St) (x : Side) (l : List Acct) :
    ({ ({ s with supplyState := x } : St) with accts := l } : St) =
      ({ s with supplyState := x, accts := l } : St) := by
  sorry

theorem plan2_supply_hook_unfold (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    ∃ s1, updateCompSupplyIndex s = some s1 ∧
      distributeSupplierComp s1 who = some s' := by
  sorry
```