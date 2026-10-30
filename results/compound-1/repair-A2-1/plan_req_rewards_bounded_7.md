**Proof plan.** Use `measure` as the potential: scaled credited COMP, plus pending index rewards, plus the scaled not-yet-indexed emission. At the upgrade, pending rewards are bounded by the legacy `pendingScaled` sum and unindexed emission by `Legacy.unindexedSupply/Borrow`; this bounds the initial measure by the claimed COMP, up to the division remainder in `Legacy.owed`. Each `exec` step increases the measure by at most the COMP emitted in that step: index updates move unindexed emission into pending rewards without creating COMP, distribution moves pending rewards into `accrued`, grants preserve `accrued + wallet`, and balance changes occur only after the relevant account has been brought up to date. Inducting over the operations bounds the final measure by the initial measure plus all emitted COMP, and dropping the nonnegative pending/unindexed terms gives `RewardsBounded`.

```lean
theorem plan7_pendSum_upgrade_le (L : Legacy) (hL : L.WellFormed) :
    pendSum (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by sorry

theorem plan7_unidx_upgrade_le (L : Legacy) :
    unidx (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by sorry

theorem plan7_measure_upgrade_le (L : Legacy) (hL : L.WellFormed) :
    measure (upgrade L) ≤
      ((upgrade L).credited + L.owed) * doubleScale +
        (L.accts.map L.pendingScaled).sum % doubleScale := by sorry

theorem plan7_measure_exec_le (s : St) (op : Op) (hC : Consistent s) :
    measure (exec comptroller s op) ≤
      measure s +
        emittedBy (s.supplyState.speed, s.borrowState.speed) op * doubleScale := by sorry

theorem plan7_measure_run_le (L : Legacy) (ops : List Op) (hL : L.WellFormed) :
    measure (run comptroller (upgrade L) ops) ≤
      measure (upgrade L) +
        emitted (L.compSpeed, L.compSpeed) ops * doubleScale := by sorry

theorem plan7_credited_of_measure_le (s : St) (K r : Nat)
    (hr : r < doubleScale) (h : measure s ≤ K * doubleScale + r) :
    s.credited ≤ K := by sorry
```