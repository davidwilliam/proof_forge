## Proof plan

Use a scaled potential consisting of:

1. COMP already credited, multiplied by `doubleScale`;
2. each account’s pending supply and borrow rewards, using `accrualStart`; and
3. COMP emitted since each side’s index was last updated, multiplied by `doubleScale`.

At the upgrade, account pending rewards are bounded by `Legacy.pendingScaled`, so the initial potential is bounded by the initial credited amount plus `L.owed`, apart from the unavoidable division remainder. Every operation either leaves this potential unchanged, converts pending rewards into credited COMP without increasing it, or increases it only through block advancement—in proportion to `emittedBy`. Inducting over the operations therefore bounds the final potential, and hence the final credited COMP.

```lean
theorem plan6_accrualStart_le_index (recorded index : Nat) (h : recorded ≤ index) :
    accrualStart recorded index ≤ index := by
  sorry

theorem plan6_sum_le_of_forall_le (l : List Acct) (f g : Acct → Nat)
    (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  sorry

theorem plan6_upgrade_pending_le (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      L.pendingScaled a := by
  sorry

theorem plan6_initial_potential_le (L : Legacy) (hL : L.WellFormed) :
    (upgrade L).credited * doubleScale +
        ((upgrade L).accts.map fun a =>
          a.supply * ((upgrade L).supplyState.index -
            accrualStart a.supplierIndex (upgrade L).supplyState.index) +
          a.borrow * ((upgrade L).borrowState.index -
            accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum +
        (((upgrade L).blockNumber - (upgrade L).supplyState.block) *
            (upgrade L).supplyState.speed +
          ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
            (upgrade L).borrowState.speed) * doubleScale ≤
      ((upgrade L).credited + L.owed) * doubleScale + (doubleScale - 1) := by
  sorry

theorem plan6_exec_potential_step (s : St) (op : Op) (sp : Nat × Nat)
    (hcons : Consistent s)
    (hsp : s.supplyState.speed = sp.1 ∧ s.borrowState.speed = sp.2) :
    (exec comptroller s op).credited * doubleScale +
          ((exec comptroller s op).accts.map fun a =>
            a.supply * ((exec comptroller s op).supplyState.index -
              accrualStart a.supplierIndex
                (exec comptroller s op).supplyState.index) +
            a.borrow * ((exec comptroller s op).borrowState.index -
              accrualStart a.borrowerIndex
                (exec comptroller s op).borrowState.index)).sum +
          (((exec comptroller s op).blockNumber -
              (exec comptroller s op).supplyState.block) *
              (exec comptroller s op).supplyState.speed +
            ((exec comptroller s op).blockNumber -
              (exec comptroller s op).borrowState.block) *
              (exec comptroller s op).borrowState.speed) * doubleScale ≤
        (s.credited * doubleScale +
          (s.accts.map fun a =>
            a.supply * (s.supplyState.index -
              accrualStart a.supplierIndex s.supplyState.index) +
            a.borrow * (s.borrowState.index -
              accrualStart a.borrowerIndex s.borrowState.index)).sum +
          ((s.blockNumber - s.supplyState.block) * s.supplyState.speed +
            (s.blockNumber - s.borrowState.block) * s.borrowState.speed) *
            doubleScale) +
          emittedBy sp op * doubleScale ∧
      Consistent (exec comptroller s op) ∧
      (exec comptroller s op).supplyState.speed = (nextSpeeds sp op).1 ∧
      (exec comptroller s op).borrowState.speed = (nextSpeeds sp op).2 := by
  sorry

theorem plan6_run_potential_le (L : Legacy) (ops : List Op)
    (hL : L.WellFormed) :
    (run comptroller (upgrade L) ops).credited * doubleScale +
          ((run comptroller (upgrade L) ops).accts.map fun a =>
            a.supply * ((run comptroller (upgrade L) ops).supplyState.index -
              accrualStart a.supplierIndex
                (run comptroller (upgrade L) ops).supplyState.index) +
            a.borrow * ((run comptroller (upgrade L) ops).borrowState.index -
              accrualStart a.borrowerIndex
                (run comptroller (upgrade L) ops).borrowState.index)).sum +
          (((run comptroller (upgrade L) ops).blockNumber -
              (run comptroller (upgrade L) ops).supplyState.block) *
              (run comptroller (upgrade L) ops).supplyState.speed +
            ((run comptroller (upgrade L) ops).blockNumber -
              (run comptroller (upgrade L) ops).borrowState.block) *
              (run comptroller (upgrade L) ops).borrowState.speed) *
            doubleScale ≤
        ((upgrade L).credited + L.owed +
          emitted (L.compSpeed, L.compSpeed) ops) * doubleScale +
          (doubleScale - 1) := by
  sorry
```