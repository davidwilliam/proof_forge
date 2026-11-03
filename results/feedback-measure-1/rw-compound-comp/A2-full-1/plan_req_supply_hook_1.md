(1) Proof plan: Unfold the `do` notation for a supply hook to expose the intermediate state after `updateCompSupplyIndex`. Characterize that update as exactly replacing the supply side by `accrueSide`, which also recovers the block inequality required by `SupplyDistributed`. Characterize `distributeSupplierComp` in the specification’s `List.modify`/`creditFor`/`accrualStart` form; the key arithmetic point is that the implementation’s constant supplier delta agrees with `creditFor` on the account actually modified, so a general `List.modify` congruence lemma at the `getD` position suffices. Finally compose the two characterizations, using that the update does not change accounts or `totalSupply`, to obtain precisely `SupplyDistributed`.

(2)
```lean
theorem plan1_modify_congr_getD (l : List Acct) (who : Nat) (f g : Acct → Acct)
    (h : f (l.getD who noAcct) = g (l.getD who noAcct)) :
    l.modify who f = l.modify who g := by sorry

theorem plan1_updateSupply_eq_accrue (s : St) (s₁ : St)
    (h : updateCompSupplyIndex s = some s₁) :
    s.supplyState.block ≤ s.blockNumber ∧
    s₁ = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by sorry

theorem plan1_distributeSupplier_spec_form (s : St) (who : Account) (s' : St)
    (h : distributeSupplierComp s who = some s') :
    accrualStart (s.acct who).supplierIndex s.supplyState.index ≤ s.supplyState.index ∧
    s' = { s with accts := s.accts.modify who fun a =>
      { a with
        supplierIndex := s.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex s.supplyState.index)
          s.supplyState.index } } := by sorry

theorem plan1_supplyHook_distributed (s : St) (who : Account) (s' : St)
    (h : comptroller s (.supplyHook who) = some s') :
    SupplyDistributed s who s' := by sorry
```