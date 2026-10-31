**Proof plan.** For the account `a = L.accts.getD who noAcct`, the upgraded account is the same account, so the goal reduces to bounding the pending and unindexed terms separately for each side. Well-formedness gives `a`'s recorded indices are at most the legacy market indices; together with `supplyStart`/`borrowStart` being `0` or `compInitialIndex`, this shows the post-upgrade `accrualStart` is never below the legacy `legacyStart`, so each side's pending term does not grow. The post-upgrade unindexed term on each side is either `0` (when the index was `0` and got initialized at the current block) or exactly the legacy unindexed amount. Adding the two sides and the unchanged `doubleScale * creditedTo` term yields the bound.

```lean
theorem plan6_acct_bounds (L : Legacy) (who : Account) (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by
  sorry

theorem plan6_supply_pending_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  sorry

theorem plan6_borrow_pending_le (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hstartle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
  sorry

theorem plan6_supply_unindexed_le (L : Legacy) (a : Acct) :
    (if 0 < a.supply then
       ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
         (upgrade L).supplyState.speed
     else 0) ≤
      (if 0 < a.supply then L.unindexedSupply else 0) := by
  sorry

theorem plan6_borrow_unindexed_le (L : Legacy) (a : Acct) :
    (if 0 < a.borrow then
       ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
         (upgrade L).borrowState.speed
     else 0) ≤
      (if 0 < a.borrow then L.unindexedBorrow else 0) := by
  sorry

theorem td0_upgrade_potentialTo_le : ∀ (L : Legacy) (who : Account), L.WellFormed →
    td0_potentialTo (upgrade L) who ≤
      doubleScale * (upgrade L).creditedTo who +
        L.pendingScaled (L.accts.getD who noAcct) +
        doubleScale * ((if 0 < (L.accts.getD who noAcct).supply
                        then L.unindexedSupply else 0) +
                       (if 0 < (L.accts.getD who noAcct).borrow
                        then L.unindexedBorrow else 0)) := by
  intro L who hWF
  obtain ⟨hsb, hbb⟩ := plan6_acct_bounds L who hWF
  have hsp := plan6_supply_pending_le L (L.accts.getD who noAcct)
    hWF.1 hWF.2.1 hsb
  have hbp := plan6_borrow_pending_le L (L.accts.getD who noAcct)
    hWF.2.2.1 hWF.2.2.2.1 hbb
  have hsu := plan6_supply_unindexed_le L (L.accts.getD who noAcct)
  have hbu := plan6_borrow_unindexed_le L (L.accts.getD who noAcct)
  have ha : (upgrade L).acct who = L.accts.getD who noAcct := rfl
  have hpend : td0_pendingTo (upgrade L) who ≤
      L.pendingScaled (L.accts.getD who noAcct) := by
    unfold td0_pendingTo td0_pendingAcct Legacy.pendingScaled
    rw [ha]
    exact Nat.add_le_add hsp hbp
  have hun : td0_unindexedTo (upgrade L) who ≤
      (if 0 < (L.accts.getD who noAcct).supply then L.unindexedSupply else 0) +
      (if 0 < (L.accts.getD who noAcct).borrow then L.unindexedBorrow else 0) := by
    unfold td0_unindexedTo
    rw [ha]
    exact Nat.add_le_add hsu hbu
  unfold td0_potentialTo
  exact Nat.add_le_add (Nat.add_le_add_left hpend _)
    (Nat.mul_le_mul_left doubleScale hun)
```