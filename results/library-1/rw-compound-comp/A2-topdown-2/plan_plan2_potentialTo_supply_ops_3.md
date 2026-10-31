Supply hooks cannot increase the per-account potential: the credited amount is bounded by the pending amount released plus the previously unindexed emissions. After a hook, the acting account is synchronized with the supply index and the supply side is current, so merely increasing, decreasing, or transferring its supply creates no new pending rewards. Rejected operations leave the state unchanged.

```lean
theorem plan3_supply_hook_potentialTo_le (sp : Nat × Nat) (s : St)
    (a who : Account) (s' : St) :
    td0_Inv sp s →
    comptroller s (.supplyHook a) = some s' →
    td0_potentialTo s' who ≤ td0_potentialTo s who := by
  sorry

theorem plan3_supply_hook_synced (s : St) (a : Account) (s' : St)
    (ha : a < s.accts.length) :
    comptroller s (.supplyHook a) = some s' →
    (s'.acct a).supplierIndex = s'.supplyState.index ∧
      s'.supplyState.block = s'.blockNumber := by
  sorry

theorem plan3_add_supply_potentialTo_le (s : St) (a who x : Nat) :
    (s.acct a).supplierIndex = s.supplyState.index →
    s.supplyState.block = s.blockNumber →
    td0_potentialTo
        (s.withAcct a fun acct => { acct with supply := acct.supply + x }) who ≤
      td0_potentialTo s who := by
  sorry

theorem plan3_sub_supply_potentialTo_le (s : St) (a who x : Nat) :
    (s.acct a).supplierIndex = s.supplyState.index →
    s.supplyState.block = s.blockNumber →
    td0_potentialTo
        (s.withAcct a fun acct => { acct with supply := acct.supply - x }) who ≤
      td0_potentialTo s who := by
  sorry

theorem plan3_transfer_move_potentialTo_le (s s1 s2 : St)
    (src dst who x : Nat) :
    src < s.accts.length →
    dst < s.accts.length →
    comptroller s (.supplyHook src) = some s1 →
    comptroller s1 (.supplyHook dst) = some s2 →
    td0_potentialTo
        ((s2.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst
          fun a => { a with supply := a.supply + x }) who ≤
      td0_potentialTo s2 who := by
  sorry

theorem plan2_potentialTo_supply_ops (sp : Nat × Nat) (s : St) (who : Account) :
    td0_Inv sp s →
    (∀ a x, td0_potentialTo (exec comptroller s (.mint a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.mint a x)) ∧
    (∀ a x, td0_potentialTo (exec comptroller s (.redeem a x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.redeem a x)) ∧
    (∀ src dst x, td0_potentialTo (exec comptroller s (.transfer src dst x)) who ≤
      td0_potentialTo s who + doubleScale * emittedBy sp (.transfer src dst x)) := by
  intro hInv
  refine ⟨?_, ?_, ?_⟩
  · intro a x
    simp only [emittedBy, Nat.mul_zero, Nat.add_zero]
    by_cases ha : a < s.accts.length
    · cases hcall : comptroller s (.supplyHook a) with
      | none =>
          have key : exec comptroller s (.mint a x) = s := by
            simp [exec, ha, hcall]
          rw [key]
          exact Nat.le_refl _
      | some s' =>
          have key : exec comptroller s (.mint a x) =
              s'.withAcct a fun acct => { acct with supply := acct.supply + x } := by
            simp [exec, ha, hcall]
          rw [key]
          exact Nat.le_trans
            (plan3_add_supply_potentialTo_le s' a who x
              (plan3_supply_hook_synced s a s' ha hcall).1
              (plan3_supply_hook_synced s a s' ha hcall).2)
            (plan3_supply_hook_potentialTo_le sp s a who s' hInv hcall)
    · have key : exec comptroller s (.mint a x) = s := by
        simp [exec, ha]
      rw [key]
      exact Nat.le_refl _
  · intro a x
    simp only [emittedBy, Nat.mul_zero, Nat.add_zero]
    by_cases ha : a < s.accts.length
    · cases hcall : comptroller s (.supplyHook a) with
      | none =>
          have key : exec comptroller s (.redeem a x) = s := by
            simp [exec, ha, hcall]
          rw [key]
          exact Nat.le_refl _
      | some s' =>
          by_cases hx : x ≤ (s'.acct a).supply
          · have key : exec comptroller s (.redeem a x) =
                s'.withAcct a fun acct => { acct with supply := acct.supply - x } := by
              simp [exec, ha, hcall, hx]
            rw [key]
            exact Nat.le_trans
              (plan3_sub_supply_potentialTo_le s' a who x
                (plan3_supply_hook_synced s a s' ha hcall).1
                (plan3_supply_hook_synced s a s' ha hcall).2)
              (plan3_supply_hook_potentialTo_le sp s a who s' hInv hcall)
          · have key : exec comptroller s (.redeem a x) = s := by
              simp [exec, ha, hcall, hx]
            rw [key]
            exact Nat.le_refl _
    · have key : exec comptroller s (.redeem a x) = s := by
        simp [exec, ha]
      rw [key]
      exact Nat.le_refl _
  · intro src dst x
    simp only [emittedBy, Nat.mul_zero, Nat.add_zero]
    by_cases hg : src < s.accts.length ∧ dst < s.accts.length ∧ src ≠ dst
    · cases hcall1 : comptroller s (.supplyHook src) with
      | none =>
          have key : exec comptroller s (.transfer src dst x) = s := by
            simp [exec, hg, hcall1]
          rw [key]
          exact Nat.le_refl _
      | some s1 =>
          have hInv1 : td0_Inv sp s1 :=
            plan0_supply_inv sp s src s1 hcall1 hInv
          cases hcall2 : comptroller s1 (.supplyHook dst) with
          | none =>
              have key : exec comptroller s (.transfer src dst x) = s := by
                simp [exec, hg, hcall1, hcall2]
              rw [key]
              exact Nat.le_refl _
          | some s2 =>
              by_cases hx : x ≤ (s2.acct src).supply
              · have key : exec comptroller s (.transfer src dst x) =
                    (s2.withAcct src fun a => { a with supply := a.supply - x }).withAcct dst
                      fun a => { a with supply := a.supply + x } := by
                  simp [exec, hg, hcall1, hcall2, hx]
                rw [key]
                exact Nat.le_trans
                  (plan3_transfer_move_potentialTo_le s s1 s2 src dst who x
                    hg.1 hg.2.1 hcall1 hcall2)
                  (Nat.le_trans
                    (plan3_supply_hook_potentialTo_le sp s1 dst who s2 hInv1 hcall2)
                    (plan3_supply_hook_potentialTo_le sp s src who s1 hInv hcall1))
              · have key : exec comptroller s (.transfer src dst x) = s := by
                  simp [exec, hg, hcall1, hcall2, hx]
                rw [key]
                exact Nat.le_refl _
    · have key : exec comptroller s (.transfer src dst x) = s := by
        simp [exec, hg]
      rw [key]
      exact Nat.le_refl _
```