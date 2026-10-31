Bound the potential by cancelling the common `doubleScale * credited` term: bound each account's upgraded pending rewards supply-side and borrow-side by its legacy pending term, sum those bounds, bound each side's unindexed emission, and combine the resulting inequalities.

```lean
theorem plan9_supply_pending_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hstartle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  sorry

theorem plan9_borrow_pending_le (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hstartle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
  sorry

theorem plan9_pending_sum_le (L : Legacy)
    (h : ∀ a ∈ L.accts, td0_pendingAcct (upgrade L) a ≤ L.pendingScaled a) :
    td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by
  sorry

theorem plan9_supply_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed ≤
      L.unindexedSupply := by
  sorry

theorem plan9_borrow_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed ≤
      L.unindexedBorrow := by
  sorry

theorem plan9_combine (L : Legacy)
    (hp : td0_pending (upgrade L) ≤ (L.accts.map L.pendingScaled).sum)
    (hu : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow) :
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  show doubleScale * (upgrade L).credited + td0_pending (upgrade L) +
      doubleScale * td0_unindexed (upgrade L) ≤ _
  exact Nat.add_le_add (Nat.add_le_add_left hp _) (Nat.mul_le_mul_left _ hu)

theorem td0_upgrade_potential_le : ∀ (L : Legacy), L.WellFormed →
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by
  intro L hWF
  have hsStart := hWF.1
  have hsLe := hWF.2.1
  have hbStart := hWF.2.2.1
  have hbLe := hWF.2.2.2.1
  have hacct := hWF.2.2.2.2.2.2
  have hpoint : ∀ a ∈ L.accts, td0_pendingAcct (upgrade L) a ≤ L.pendingScaled a := by
    intro a ha
    have hbnd := hacct a ha
    have hs := plan9_supply_pending_le L a hsStart hsLe hbnd.1
    have hb := plan9_borrow_pending_le L a hbStart hbLe hbnd.2
    unfold td0_pendingAcct Legacy.pendingScaled
    exact Nat.add_le_add hs hb
  have hp := plan9_pending_sum_le L hpoint
  have hu : td0_unindexed (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by
    unfold td0_unindexed
    exact Nat.add_le_add (plan9_supply_unindexed_le L) (plan9_borrow_unindexed_le L)
  exact plan9_combine L hp hu
```