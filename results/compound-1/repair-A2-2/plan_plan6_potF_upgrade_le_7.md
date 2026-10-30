Short proof plan: bound the upgraded pending rewards account-by-account. For each side, replacing the legacy start by `accrualStart` at the upgraded index (which is `compInitialIndex` exactly when the legacy index was `0`) cannot increase the credited units times index-gain; summing gives `pendSum (upgrade L) ≤ ∑ pendingScaled`. The upgraded un-indexed emission is at most the legacy un-indexed supply plus borrow emission. Finally, division slack `S ≤ S / doubleScale * doubleScale + (doubleScale - 1)` turns the summed scaled pending amount into `L.owed`, and unfolding `potF` combines these bounds linearly.

```lean
theorem plan7_term_le (idx start recorded units : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hstart_le : start ≤ idx)
    (hrec : recorded ≤ idx) :
    units * ((if idx = 0 then compInitialIndex else idx) -
      accrualStart recorded (if idx = 0 then compInitialIndex else idx)) ≤
      units * (idx - legacyStart start recorded) := by sorry

theorem plan7_pendSum_upgrade_le (L : Legacy) (hWF : L.WellFormed) :
    pendSum (upgrade L) ≤ (L.accts.map L.pendingScaled).sum := by sorry

theorem plan7_unidx_upgrade_le (L : Legacy) :
    unidx (upgrade L) ≤ L.unindexedSupply + L.unindexedBorrow := by sorry

theorem plan7_owed_mul_bound (L : Legacy) :
    (L.accts.map L.pendingScaled).sum +
        (L.unindexedSupply + L.unindexedBorrow) * doubleScale ≤
      L.owed * doubleScale + (doubleScale - 1) := by sorry

theorem plan7_potF_upgrade_bound (L : Legacy) (hWF : L.WellFormed) :
    potF (upgrade L) ≤
      (upgrade L).credited * doubleScale + L.owed * doubleScale +
        (doubleScale - 1) := by sorry
```