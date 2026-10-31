**Proof plan.** Split the initial potential into its pending-rewards part and its unindexed-emission part. For each account, the upgraded index difference is bounded by the legacy pending difference, because `initSide` either leaves a nonzero index unchanged or initializes a zero index to `compInitialIndex`, while `accrualStart` never starts below the legacy `legacyStart`; summing this over all accounts bounds the pending sum by `(L.accts.map L.pendingScaled).sum`. Separately, after `upgrade` each side is either freshly initialized at the current block (zero unindexed emission) or keeps its old block and the common legacy speed, so the upgraded unindexed total is at most `L.unindexedSupply + L.unindexedBorrow`. The conclusion then follows by a purely arithmetic step: a quantity below `Pleg` contributes at most `Pleg / doubleScale * doubleScale + (doubleScale - 1)`, and unfolding `Legacy.owed` identifies the right-hand side.

```lean
theorem plan8_upgrade_pending_le_acc (L : Legacy) (a : Acct)
    (hL : L.WellFormed) (ha : a ∈ L.accts) :
    a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index) ≤
      L.pendingScaled a := by sorry

theorem plan8_pending_sum_le (L : Legacy) (hL : L.WellFormed) :
    ((upgrade L).accts.map fun a =>
      a.supply * ((upgrade L).supplyState.index -
        accrualStart a.supplierIndex (upgrade L).supplyState.index) +
      a.borrow * ((upgrade L).borrowState.index -
        accrualStart a.borrowerIndex (upgrade L).borrowState.index)).sum ≤
      (L.accts.map L.pendingScaled).sum := by sorry

theorem plan8_upgrade_unindexed_le (L : Legacy) :
    ((upgrade L).blockNumber - (upgrade L).supplyState.block) *
        (upgrade L).supplyState.speed +
      ((upgrade L).blockNumber - (upgrade L).borrowState.block) *
        (upgrade L).borrowState.speed ≤
      L.unindexedSupply + L.unindexedBorrow := by sorry

theorem plan8_arith_initial (C P Pleg U US UB : Nat)
    (hP : P ≤ Pleg) (hU : U ≤ US + UB) :
    C * doubleScale + P + U * doubleScale ≤
      (C + (Pleg / doubleScale + US + UB)) * doubleScale +
        (doubleScale - 1) := by sorry
```