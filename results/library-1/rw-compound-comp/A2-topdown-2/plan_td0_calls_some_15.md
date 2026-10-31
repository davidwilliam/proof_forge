Short plan: preserve `Consistent` through each primitive index update and each distribution step. A supply or borrow hook is then an update followed by a distribution, a claim is borrow update/distribution followed by supply update/distribution, and speed-setting is treated as its own primitive step. Reassembling these successful `Option` steps gives success for every call.

```lean
theorem plan15_updateSupply_pres (s : St) :
    Consistent s →
    ∃ t, updateCompSupplyIndex s = some t ∧ Consistent t := by
  sorry

theorem plan15_updateBorrow_pres (s : St) :
    Consistent s →
    ∃ t, updateCompBorrowIndex s = some t ∧ Consistent t := by
  sorry

theorem plan15_distributeSupplier_pres (s : St) (who : Account) :
    Consistent s →
    ∃ s', distributeSupplierComp s who = some s' ∧ Consistent s' := by
  sorry

theorem plan15_distributeBorrower_pres (s : St) (who : Account) :
    Consistent s →
    ∃ s', distributeBorrowerComp s who = some s' ∧ Consistent s' := by
  sorry

theorem plan15_setSpeeds_some (s : St) (a b : Nat) :
    Consistent s → (comptroller s (.setSpeeds a b)).isSome := by
  sorry

theorem td0_calls_some : ∀ (s : St) (c : Call), Consistent s → (comptroller s c).isSome := by
  intro s c hs
  cases c with
  | supplyHook who =>
      obtain ⟨t, ht, htCons⟩ := plan15_updateSupply_pres s hs
      obtain ⟨s', hs', _hsCons⟩ := plan15_distributeSupplier_pres t who htCons
      simp [comptroller, ht, hs']
  | borrowHook who =>
      obtain ⟨t, ht, htCons⟩ := plan15_updateBorrow_pres s hs
      obtain ⟨s', hs', _hsCons⟩ := plan15_distributeBorrower_pres t who htCons
      simp [comptroller, ht, hs']
  | claim who =>
      obtain ⟨t1, ht1, h1⟩ := plan15_updateBorrow_pres s hs
      obtain ⟨t2, ht2, h2⟩ := plan15_distributeBorrower_pres t1 who h1
      obtain ⟨t3, ht3, h3⟩ := plan15_updateSupply_pres t2 h2
      obtain ⟨t4, ht4, _h4⟩ := plan15_distributeSupplier_pres t3 who h3
      simp [comptroller, claimComp, ht1, ht2, ht3, ht4]
  | setSpeeds a b =>
      exact plan15_setSpeeds_some s a b hs
```