**Proof plan.** For the upgraded state, the accounts, credited amounts, block number, and speeds are unchanged. On each side there are two cases. If the legacy index is `0`, `initSide` sets it to `compInitialIndex`; the account's recorded index must then also be `0`, the legacy start must be `0`, and both the old and new pending gaps are `0`, while the upgraded unindexed term vanishes because the side block becomes the current block. If the legacy index is nonzero, `initSide` leaves it unchanged. When an account has no recorded index, its legacy start is either `0` or `compInitialIndex`, hence no larger than `accrualStart`; when it has a recorded index, the two starts agree. Thus each upgraded pending gap is at most the corresponding legacy pending gap. Multiplying by supply/borrow balances and adding the two sides bounds `td0_pendingScaledAcct` by `td0_pendingOf`, and the upgraded unindexed terms are bounded termwise by `td0_unindexedOf`. Combining these bounds in the definition of `td0_potentialTo` gives the result.

```lean
theorem plan2_legacyStart_le_accrualStart (start recorded index : Nat)
    (hstart : start = 0 ∨ start = compInitialIndex)
    (hle : start ≤ index) (hrec : recorded ≤ index) :
    legacyStart start recorded ≤ accrualStart recorded index := by sorry

theorem plan2_supply_gap_le (L : Legacy) (a : Acct)
    (hstart : L.supplyStart = 0 ∨ L.supplyStart = compInitialIndex)
    (hle : L.supplyStart ≤ L.supplyIndex)
    (ha : a.supplierIndex ≤ L.supplyIndex) :
    (initSide L.blockNumber
      (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.supplierIndex
          (initSide L.blockNumber
            (⟨L.supplyIndex, L.supplyBlock, L.compSpeed⟩ : Side)).index ≤
      L.supplyIndex - legacyStart L.supplyStart a.supplierIndex := by sorry

theorem plan2_borrow_gap_le (L : Legacy) (a : Acct)
    (hstart : L.borrowStart = 0 ∨ L.borrowStart = compInitialIndex)
    (hle : L.borrowStart ≤ L.borrowIndex)
    (ha : a.borrowerIndex ≤ L.borrowIndex) :
    (initSide L.blockNumber
      (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index -
        accrualStart a.borrowerIndex
          (initSide L.blockNumber
            (⟨L.borrowIndex, L.borrowBlock, L.compSpeed⟩ : Side)).index ≤
      L.borrowIndex - legacyStart L.borrowStart a.borrowerIndex := by sorry

theorem plan2_getD_index_le (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    (L.accts.getD who noAcct).supplierIndex ≤ L.supplyIndex ∧
    (L.accts.getD who noAcct).borrowerIndex ≤ L.borrowIndex := by sorry

theorem plan2_upgrade_pending_le (L : Legacy) (who : Account)
    (hWF : L.WellFormed) :
    td0_pendingScaledAcct (upgrade L) ((upgrade L).acct who) ≤
      td0_pendingOf L who := by sorry

theorem plan2_upgrade_unindexedTo_le (L : Legacy) (who : Account) :
    td0_unindexedTo (upgrade L) who ≤ td0_unindexedOf L who := by sorry
```