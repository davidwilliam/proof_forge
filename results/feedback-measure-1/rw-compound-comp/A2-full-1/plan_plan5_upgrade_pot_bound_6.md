**Proof plan**

Split the potential of the upgraded state into credited COMP, pending supply and borrow rewards, and unindexed emission. For every legacy account, the upgraded pending reward on each side is at most the corresponding legacy scaled term: if the legacy index is positive the upgraded index is unchanged and `accrualStart` is at least `legacyStart`; if it is zero, well-formedness forces the legacy start and the account's recorded index to be zero, and initialization makes the upgraded pending term zero. Summing these pointwise bounds bounds total pending rewards by the sum defining `Legacy.pendingScaled`. Initialization also makes unindexed emission after the upgrade no larger than the legacy unindexed emission. Finally, use the division-remainder bound for the rounded-down legacy pending total and combine the pieces arithmetically in `Pot`.

```lean
theorem plan6_pendSupply_upgrade_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    pendSupply (upgrade L) a ≤
      a.supply * (L.supplyIndex - legacyStart L.supplyStart a.supplierIndex) := by
  sorry

theorem plan6_pendBorrow_upgrade_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    pendBorrow (upgrade L) a ≤
      a.borrow * (L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex) := by
  sorry

theorem plan6_sumPend_upgrade_le (L : Legacy) (hL : L.WellFormed) :
    sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum := by
  sorry

theorem plan6_unindexed_upgrade_le (L : Legacy) :
    unindexedSupply (upgrade L) + unindexedBorrow (upgrade L) ≤
      L.unindexedSupply + L.unindexedBorrow := by
  sorry

theorem plan6_div_add_bound (n : Nat) :
    n ≤ doubleScale * (n / doubleScale) + (doubleScale - 1) := by
  sorry

theorem plan6_pot_bound_of_bounds (L : Legacy)
    (hsum : sumPendSupply (upgrade L) + sumPendBorrow (upgrade L) ≤
      (L.accts.map L.pendingScaled).sum)
    (hun : unindexedSupply (upgrade L) + unindexedBorrow (upgrade L) ≤
      L.unindexedSupply + L.unindexedBorrow) :
    Pot (upgrade L) ≤
      doubleScale * ((upgrade L).credited + L.owed) + (doubleScale - 1) := by
  sorry
```