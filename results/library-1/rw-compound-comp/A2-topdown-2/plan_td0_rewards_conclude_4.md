The scaled potential dominates `doubleScale * credited`, while `owed` is the pending sum divided by `doubleScale` plus the unindexed amounts. Combining the two given potential bounds therefore gives a scaled bound on the final credited amount; cancelling the scale, using the division remainder bound, yields the required unscaled bound.

```lean
theorem plan4_credited_le_potential (s : St) :
    doubleScale * s.credited ≤ td0_potential s := by
  unfold td0_potential
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem plan4_owed_eq (L : Legacy) :
    L.owed = (L.accts.map L.pendingScaled).sum / doubleScale +
      (L.unindexedSupply + L.unindexedBorrow) := by
  unfold Legacy.owed
  rw [Nat.add_assoc]

theorem plan4_bound_of_scaled_le (c c0 s u e : Nat) :
    doubleScale * c ≤
        doubleScale * c0 + s + doubleScale * u + doubleScale * e →
    c ≤ c0 + (s / doubleScale + u) + e := by
  sorry

theorem td0_rewards_conclude : ∀ (L : Legacy) (ops : List Op),
    td0_potential (run comptroller (upgrade L) ops) ≤
        td0_potential (upgrade L) + doubleScale * emitted (L.compSpeed, L.compSpeed) ops →
    td0_potential (upgrade L) ≤
        doubleScale * (upgrade L).credited + (L.accts.map L.pendingScaled).sum +
          doubleScale * (L.unindexedSupply + L.unindexedBorrow) →
    (run comptroller (upgrade L) ops).credited ≤
      (upgrade L).credited + L.owed + emitted (L.compSpeed, L.compSpeed) ops := by
  intro L ops h1 h2
  have hlow := plan4_credited_le_potential (run comptroller (upgrade L) ops)
  have htrans :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        td0_potential (upgrade L) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.le_trans hlow h1
  have hstep :
      td0_potential (upgrade L) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops ≤
        (doubleScale * (upgrade L).credited +
            (L.accts.map L.pendingScaled).sum +
            doubleScale * (L.unindexedSupply + L.unindexedBorrow)) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.add_le_add_right h2 _
  have hcomb :
      doubleScale * (run comptroller (upgrade L) ops).credited ≤
        doubleScale * (upgrade L).credited +
          (L.accts.map L.pendingScaled).sum +
          doubleScale * (L.unindexedSupply + L.unindexedBorrow) +
          doubleScale * emitted (L.compSpeed, L.compSpeed) ops :=
    Nat.le_trans htrans hstep
  have hbound := plan4_bound_of_scaled_le _ _ _ _ _ hcomb
  rw [plan4_owed_eq L]
  exact hbound
```