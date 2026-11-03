A per-account potential argument is needed, parallel to the global potential already used for `RewardsBounded`: show that `td0_potentialTo` increases by at most the COMP emitted by one operation while `td0_Inv` is preserved, lift this to whole runs by induction on `ops`, bound the potential at the upgraded state by the legacy pending and unindexed amounts, and combine these to obtain a scaled bound on `creditedTo`. The existing lemma `td0_account_bound_of_scaled` then removes the `doubleScale` factor and turns the pending/unindexed bound into `L.owedTo who`, giving `AccountBounded` directly.

```lean
theorem plan19_exec_potentialTo_step (sp : Nat × Nat) (s : St) (op : Op) (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (exec comptroller s op) who ≤
        td0_potentialTo s who + doubleScale * emittedBy sp op ∧
      td0_Inv (nextSpeeds sp op) (exec comptroller s op) := by sorry

theorem plan19_run_potentialTo_le (sp : Nat × Nat) (s : St) (ops : List Op) (who : Account) :
    td0_Inv sp s →
    td0_potentialTo (run comptroller s ops) who ≤
        td0_potentialTo s who + doubleScale * emitted sp ops ∧
      td0_Inv (speedsAfter sp ops) (run comptroller s ops) := by sorry

theorem plan19_potentialTo_upgrade_le (L : Legacy) (who : Account) :
    L.WellFormed →
    td0_potentialTo (upgrade L) who ≤
      doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who := by sorry

theorem plan19_scaled_creditedTo_run_le (L : Legacy) (ops : List Op) (who : Account) :
    L.WellFormed →
    doubleScale * (run comptroller (upgrade L) ops).creditedTo who ≤
      doubleScale * (upgrade L).creditedTo who +
        td0_pendingOf L who +
        doubleScale * td0_unindexedOf L who +
        doubleScale * emitted (L.compSpeed, L.compSpeed) ops := by sorry
```