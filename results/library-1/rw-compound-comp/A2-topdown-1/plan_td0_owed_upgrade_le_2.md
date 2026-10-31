(1) Proof plan: Analyze each side separately. For an account, upgrading either preserves its index or initializes a zero index to `compInitialIndex`; comparing `accrualStart` with `legacyStart`, using that the legacy start is `0` or `compInitialIndex`, shows that the upgraded pending amount is no larger. Summing preserves this inequality. For unindexed rewards, an initialized side has its block moved to the current block, contributing `0`, while an uninitialized side keeps its block and speed, contributing exactly the legacy amount. Finally, division by `doubleScale` is monotone and the three parts combine.

(2)

```lean
theorem plan2_start_diff_le (S r I : Nat)
    (hS : S = 0 ∨ S = compInitialIndex) (hSI : S ≤ I) (hrI : r ≤ I) :
    (if I = 0 then compInitialIndex else I) -
        accrualStart r (if I = 0 then compInitialIndex else I) ≤
      I - legacyStart S r := by sorry

theorem plan2_pending_upgrade_le (L : Legacy) (hWF : L.WellFormed)
    (a : Acct) (ha : a ∈ L.accts) :
    td0_pendingScaled (upgrade L) a ≤ Legacy.pendingScaled L a := by sorry

theorem plan2_unindexedSupply_upgrade_le (L : Legacy) :
    td0_unindexedSupply (upgrade L) ≤ L.unindexedSupply := by sorry

theorem plan2_unindexedBorrow_upgrade_le (L : Legacy) :
    td0_unindexedBorrow (upgrade L) ≤ L.unindexedBorrow := by sorry

theorem plan2_sum_pending_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    ((upgrade L).accts.map (td0_pendingScaled (upgrade L))).sum ≤
      (L.accts.map L.pendingScaled).sum := by sorry

theorem plan2_owed_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    td0_owed (upgrade L) ≤ L.owed := by sorry
```