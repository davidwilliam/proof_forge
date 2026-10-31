A supply hook is an `Option.bind` of two steps: first `updateCompSupplyIndex` brings the supply side to `accrueSide`, then `distributeSupplierComp` records that new index for the account and credits it using `accrualStart` and `creditFor`. So I isolate a generic bind-elimination lemma, one specification lemma for each of the two steps in exactly the vocabulary of `SupplyDistributed`, and one pure rewriting lemma that merges the intermediate state back into a single update of the original state. The main proof then just chains the three.

```lean
theorem plan12_bind_some {α β : Type} (m : Option α) (f : α → Option β) (y : β) :
    m.bind f = some y → ∃ x, m = some x ∧ f x = some y := by
  intro h
  cases m with
  | none => simp at h
  | some x => exact ⟨x, rfl, h⟩

theorem plan12_update_supply_spec (s : St) (t : St) :
    updateCompSupplyIndex s = some t →
    s.supplyState.block ≤ s.blockNumber ∧
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } := by
  sorry

theorem plan12_distribute_supply_spec (t : St) (who : Account) (s' : St) :
    distributeSupplierComp t who = some s' →
    accrualStart (t.acct who).supplierIndex t.supplyState.index ≤ t.supplyState.index ∧
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        supplierIndex := t.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex t.supplyState.index) t.supplyState.index } } := by
  sorry

theorem plan12_combine_supply (s t s' : St) (who : Account) :
    t = { s with supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) } →
    s' = { t with accts := t.accts.modify who fun a =>
      { a with
        supplierIndex := t.supplyState.index,
        accrued := a.accrued + creditFor a.supply
          (accrualStart a.supplierIndex t.supplyState.index) t.supplyState.index } } →
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by
  sorry

theorem td0_supply_hook_effect : ∀ (s : St) (who : Account) (s' : St),
    comptroller s (.supplyHook who) = some s' → SupplyDistributed s who s' := by
  intro s who s' h
  have hbind : (updateCompSupplyIndex s).bind (fun t => distributeSupplierComp t who) = some s' := h
  obtain ⟨t, ht_update, ht_dist⟩ := plan12_bind_some _ _ _ hbind
  obtain ⟨hblock, ht_eq⟩ := plan12_update_supply_spec s t ht_update
  obtain ⟨hstart, hs'_eq⟩ := plan12_distribute_supply_spec t who s' ht_dist
  have hstart' : accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by
    rw [ht_eq] at hstart
    exact hstart
  unfold SupplyDistributed
  exact ⟨hblock, hstart', plan12_combine_supply s t s' who ht_eq hs'_eq⟩
```