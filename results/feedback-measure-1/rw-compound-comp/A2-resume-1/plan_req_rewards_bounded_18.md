**Proof plan.** Use the already-defined scaled potential `td0_potential s = doubleScale * s.credited + pending + doubleScale * unindexed`. First show the potential of any run from `upgrade L` grows by at most `doubleScale * emitted` since the upgrade (via the existing run-potential lemma, after rewriting `Pot = td0_potential` and using consistency of the upgrade). Second, bound the upgrade's own potential by its credited amount plus the legacy pending sum and the two unindexed emissions; each account's upgraded pending is at most its legacy pending, and an initialized side contributes no unindexed emission. Third, drop the nonnegative pending/unindexed terms from the run's potential to get a purely scaled bound on `credited`. Finally apply the existing scaled-to-unscaled conclusion (`td0_rewards_bound_of_scaled`, which absorbs the division rounding in `L.owed`) to obtain `RewardsBounded`.

```lean
theorem plan18_run_potential_le (L : Legacy) (ops : List Op) (hL : L.WellFormed) :
    td0_potential (run comptroller (upgrade L) ops) ≤
      td0_potential (upgrade L) + doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by sorry

theorem plan18_upgrade_potential_le (L : Legacy) (hL : L.WellFormed) :
    td0_potential (upgrade L) ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) := by sorry

theorem plan18_scaled_credited_le (L : Legacy) (ops : List Op) (hL : L.WellFormed) :
    doubleScale * (run comptroller (upgrade L) ops).credited ≤
      doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
        doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by sorry

theorem plan18_rewards_bounded : RewardsBounded comptroller := by sorry
```