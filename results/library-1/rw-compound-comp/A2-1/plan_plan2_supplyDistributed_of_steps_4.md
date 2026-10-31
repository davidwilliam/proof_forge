## Proof plan

The already-proved `plan2_updateSupply_accrueSide` identifies `mid` completely: it is `s` with its supply side replaced by `accrueSide …`. Hence `mid` has the same accounts as `s`—so `mid.acct who = s.acct who`—and its supply state is exactly that `accrueSide` term. Feeding `hdist` to the already-proved `plan2_dist_char_PROOFTEST4` gives the accrual bound and the final-state equation phrased in terms of `mid`; the two transfer lemmas below rewrite both from `mid`-terms to `s`-terms. The target then assembles `SupplyDistributed` from `updSupply_char_aux` (block bound), the transferred bound, and the transferred equation.

```lean
theorem plan4_updateSupply_acct_eq (s mid : St) (who : Account)
    (h : updateCompSupplyIndex s = some mid) :
    mid.acct who = s.acct who := by sorry

theorem plan4_updateSupply_supplyState_eq (s mid : St)
    (h : updateCompSupplyIndex s = some mid) :
    mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s) := by sorry

theorem plan4_supply_bound_transfer (s mid : St) (who : Account)
    (hacct : mid.acct who = s.acct who)
    (hstate : mid.supplyState = accrueSide s.supplyState s.blockNumber (totalSupply s))
    (hle : accrualStart (mid.acct who).supplierIndex mid.supplyState.index ≤
        mid.supplyState.index) :
    accrualStart (s.acct who).supplierIndex
        (accrueSide s.supplyState s.blockNumber (totalSupply s)).index ≤
      (accrueSide s.supplyState s.blockNumber (totalSupply s)).index := by sorry

theorem plan4_supply_eq_transfer (s mid s' : St) (who : Account)
    (hmid : mid = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s) })
    (heq : s' = { mid with
      accts := mid.accts.modify who fun a =>
        { a with
          supplierIndex := mid.supplyState.index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex mid.supplyState.index)
            mid.supplyState.index } }) :
    s' = { s with
      supplyState := accrueSide s.supplyState s.blockNumber (totalSupply s),
      accts := s.accts.modify who fun a =>
        { a with
          supplierIndex := (accrueSide s.supplyState s.blockNumber (totalSupply s)).index,
          accrued := a.accrued + creditFor a.supply
            (accrualStart a.supplierIndex
              (accrueSide s.supplyState s.blockNumber (totalSupply s)).index)
            (accrueSide s.supplyState s.blockNumber (totalSupply s)).index } } := by sorry
```