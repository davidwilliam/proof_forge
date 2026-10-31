Proof plan: Reduce `exec` case-by-case. Hooks and claims preserve the invariant because `accrueSide` never lowers an index, sets the side block to the current block, and preserves its speed; balance-only `List.modify` updates preserve recorded indices. `setSpeeds` uses the same accrual facts, while the side taken unchanged already has the requested speed, giving speeds `(a, b)`. `advance` and `drip` then follow directly by unfolding `Consistent` and using `omega` on block monotonicity.

```lean
theorem plan0_accrueSide_props (sd : Side) (now total : Nat) :
    sd.index ≤ (accrueSide sd now total).index ∧
      (accrueSide sd now total).block = now ∧
      (accrueSide sd now total).speed = sd.speed := by sorry

theorem plan0_withAcct_inv (sp : Nat × Nat) (s : St) (who : Account)
    (f : Acct → Acct)
    (hsi : ∀ a, (f a).supplierIndex = a.supplierIndex)
    (hbi : ∀ a, (f a).borrowerIndex = a.borrowerIndex) :
    td0_Inv sp s → td0_Inv sp (s.withAcct who f) := by sorry

theorem plan0_supplyDistributed_inv (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → SupplyDistributed s who s' → td0_Inv sp s' := by sorry

theorem plan0_borrowDistributed_inv (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → BorrowDistributed s who s' → td0_Inv sp s' := by sorry

theorem plan0_claimed_inv (sp : Nat × Nat) (s : St) (who : Account)
    (s' : St) :
    td0_Inv sp s → Claimed s who s' → td0_Inv sp s' := by sorry

theorem plan0_speedsSet_inv (sp : Nat × Nat) (s : St) (a b : Nat)
    (s' : St) :
    td0_Inv sp s → SpeedsSet s a b s' → td0_Inv (a, b) s' := by sorry
```