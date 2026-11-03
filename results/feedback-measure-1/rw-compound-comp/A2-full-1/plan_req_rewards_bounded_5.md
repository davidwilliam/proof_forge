## Proof plan

Use `Pot` as a scaled potential: it counts credited COMP scaled by `doubleScale`, each account’s still-pending rewards, and the rewards emitted since each side’s index was last updated, also scaled. Crediting an account moves pending scaled rewards into `credited`: the integer division can only lose scaled value. Accruing an index converts unindexed emissions into pending rewards, with total pending growth bounded by the corresponding unindexed decrease. Thus every operation increases `Pot` by at most the rewards emitted during that operation. At the upgrade, account pending rewards are bounded by the legacy pending amount; crucially, `supplyStart`/`borrowStart` being `compInitialIndex` forces that value to be below the corresponding legacy index; up to one `doubleScale` division remainder. Combining the initial and run bounds with `Pot_credited_le` gives the desired unscaled bound.

```lean
theorem plan5_upgrade_pot_bound (L : Legacy) (hL : L.WellFormed) :
    Pot (upgrade L) ≤
      doubleScale * ((upgrade L).credited + L.owed) + (doubleScale - 1) := by
  sorry

theorem plan5_upgrade_consistent_speeds (L : Legacy) (hL : L.WellFormed) :
    Consistent (upgrade L) ∧
    (upgrade L).supplyState.speed = L.compSpeed ∧
    (upgrade L).borrowState.speed = L.compSpeed := by
  sorry

theorem plan5_supply_distributed_pot_le (s : St) (who : Account) (s' : St)
    (h : SupplyDistributed s who s') :
    Pot s' ≤ Pot s := by
  sorry

theorem plan5_borrow_distributed_pot_le (s : St) (who : Account) (s' : St)
    (h : BorrowDistributed s who s') :
    Pot s' ≤ Pot s := by
  sorry

theorem plan5_exec_step (s : St) (sp : Nat × Nat) (op : Op)
    (hCons : Consistent s)
    (hSpeed : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    Pot (exec comptroller s op) ≤
        Pot s + emittedBy sp op * doubleScale ∧
      Consistent (exec comptroller s op) ∧
      (exec comptroller s op).supplyState.speed = (nextSpeeds sp op).1 ∧
      (exec comptroller s op).borrowState.speed = (nextSpeeds sp op).2 := by
  sorry

theorem plan5_run_pot_bound (s : St) (sp : Nat × Nat) (ops : List Op)
    (hCons : Consistent s)
    (hSpeed : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    Pot (run comptroller s ops) ≤
        Pot s + emitted sp ops * doubleScale ∧
      Consistent (run comptroller s ops) ∧
      (run comptroller s ops).supplyState.speed = (speedsAfter sp ops).1 ∧
      (run comptroller s ops).borrowState.speed = (speedsAfter sp ops).2 := by
  sorry
```